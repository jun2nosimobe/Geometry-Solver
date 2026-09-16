//! 🌟 探索の司令塔(BlackboardEngine)。
//!
//! どの定理をどの順で試すかのタスク待ち行列を回し、行き詰まったときの
//! 需要駆動の補助作図(resolve_*_demands)で図を伸ばす。1回の推論の単位は
//! run_step。

use std::collections::{BinaryHeap, VecDeque};

use crate::mmp_core::{ClassId, Definition, EGraph, EntityType, Fact};
use super::*;
use rustc_hash::FxHashMap;

pub struct BlackboardEngine {
    pub prover: ProverEngine,
    pub task_queue: BinaryHeap<MatchTask>,
    pub event_queue: VecDeque<Event>,
    // 🌟 UCB1バンディットの効果測定用のA/Bスイッチ。false にすると
    // schedule_full_sweep がシードなしタスクの優先度を常に0固定にする
    // (バンディット導入前の挙動に戻す)。既定は有効(true)。
    pub bandit_enabled: bool,
    // 🌟 シード付き再マッチング(schedule_matcher_task)を使うか。
    // run_step の Event::FactProven の腕に実測結果を書いてある通り、
    // 現状のファンアウトのまま有効にすると掛け合わせが明確に悪化するので
    // 既定は無効。--seeded-rematch で有効にできる。
    pub seeded_rematch_enabled: bool,
}

impl BlackboardEngine {
    pub fn new(prover: ProverEngine) -> Self {
        Self {
            prover,
            task_queue: BinaryHeap::new(),
            event_queue: VecDeque::new(),
            bandit_enabled: true,
            seeded_rematch_enabled: false,
        }
    }

    /// 🌟 eval.rs::log_conjecture_candidateが蓄積した「証明されていないが
    /// 数値的根拠のある予想」を処理する。実体はEGraph::process_pending_conjectures
    /// (mmp_core/eval.rs)に移した(MCTS(mcts.rs::run_step)がBlackboardEngineを
    /// 介さず、自分自身が発見した予想を同じrun_step呼び出しの中で直接
    /// 評価・反映できるようにするため)。ここは既存呼び出し元(main.rs)向けの
    /// 薄い委譲。
    pub fn process_pending_conjectures(&mut self, target: &Option<(String, Vec<ClassId>)>) -> usize {
        self.prover.egraph.process_pending_conjectures(target)
    }

    /// 🌟 ユーザー提案(「定理を無マージで動かし、conjectureのみでも定理を
    /// 適用させるモード」):予想(a≡b、まだ証明されていない数値的な偶然の
    /// 一致)を使い捨てのクローン上でのみ真だと仮定し、通常の定理探索
    /// エンジン(schedule_full_sweep + dfs_match、UCB1バンディットは無効化)を
    /// 限られた予算で走らせる。
    ///
    /// 既存のEGraph::estimate_conjecture_value(eval.rs)が合同閉包1回だけの
    /// 浅い見積もりに意図的に留めている(定理マッチングまで踏み込むと
    /// 組み合わせが指数的に増える恐れがあるため)のに対し、こちらは
    /// 「その仮定が実際に名前付き定理を連鎖的に発火させ、現実にはまだ
    /// 知られていない別の等式を導くか」を見るための、より深いプロービング。
    /// 現実のegraph(self.prover.egraph)は一切変更しない。
    ///
    /// 戻り値は「現実には(まだ)別々の代表元だが、この仮定の下での
    /// シミュレーションでは統合された」現実の代表元ペアの一覧――呼び出し側
    /// (discover.rs)がこれを新しい"条件付き"の予想としてconjecturesマップに
    /// 記録する想定(このメソッド自体は記録しない、純粋な問い合わせ)。
    /// 比較はreal_len未満(=シミュレーション内で新規に作られた補助構成では
    /// ない、現実にも存在する)代表元同士に限定する
    /// (EGraph::absorb_conjectures_fromと同じ理由)。
    pub fn probe_conjecture(&self, a: ClassId, b: ClassId, dfs_budget: usize, sweep_rounds: usize) -> Vec<(ClassId, ClassId)> {
        if self.prover.egraph.get_rep(a) == self.prover.egraph.get_rep(b) { return Vec::new(); }
        let real_len = self.prover.egraph.entities.len();

        let mut sim_prover = ProverEngine::new(self.prover.egraph.clone());
        sim_prover.theorems = self.prover.theorems.clone(); // Rc共有なのでコピーは軽い
        sim_prover.dfs_cap = dfs_budget as u64;
        let mut sim_engine = BlackboardEngine::new(sim_prover);
        sim_engine.bandit_enabled = false;

        if !sim_engine.prover.egraph.merge_entities_justified(a, b, crate::mmp_core::Justification::Trivial {
            reason: "仮説プロービング: 予想を一時的に真と仮定(discover.rs::probe_and_expand_conjectures)".to_string(),
        }) {
            return Vec::new();
        }
        sim_engine.prover.egraph.apply_congruence_closure();
        sim_engine.schedule_full_sweep();
        for _ in 0..sweep_rounds {
            if !sim_engine.run_step(dfs_budget) { break; }
        }

        // 現実に存在する代表元同士で、simでは統合されたが現実にはまだ
        // 別々、というペアを新しい条件付き結論として拾う。
        let mut discovered = Vec::new();
        let mut seen_reps: FxHashMap<ClassId, ClassId> = FxHashMap::default();
        for i in 0..real_len {
            let id = ClassId(i);
            if self.prover.egraph.get_rep(id) != id { continue; } // 現実側の代表元だけを見る(重複回避)
            let sim_rep = sim_engine.prover.egraph.get_rep(id);
            if let Some(&other_real_id) = seen_reps.get(&sim_rep) {
                discovered.push((other_real_id, id));
            } else {
                seen_reps.insert(sim_rep, id);
            }
        }
        discovered
    }

    pub fn schedule_full_sweep(&mut self) {
        // 🌟 ProverEngine::ProfileStatsのドキュメント参照: この関数自体が
        // 実際にどれだけの時間・頻度で呼ばれ、1回あたり何個の「空の
        // failed_pathsを持つシードなしタスク」を新規に作っているかを計測する。
        // 2度の撤回(DefinedBy遅延構築・スケジューラ精密化)がどちらも
        // 「この関数が重いはず」という推測止まりで終わった反省から、
        // 次に何か変える前にまずここを実測できるようにする。
        let sfs_start = std::time::Instant::now();
        self.prover.profile.sfs_calls += 1;

        // 🌟 FIX: シード注入済みのタスクは消さずに保持する!
        // 🐛 以前は「priority > 0」で判定していたが、UCB1バンディットの
        // 導入でシードなしタスクの優先度も +5 まで上がり得るようになったため、
        // priorityの値ではなく専用フラグ(is_seeded)で由来を判定する。
        let mut keep = Vec::new();
        for task in self.task_queue.drain() {
            if task.is_seeded { keep.push(task); }
        }
        self.task_queue = BinaryHeap::from(keep);

        // 🌟 UCB1バンディット: シードなし全探索タスクどうしの優先度を、
        // これまでの経験的な成功率(+探索ボーナス)で差別化する。
        // self.prover.theorems.iter() で theorems を借用したまま
        // self.prover.theorem_priority_bonus(&mut self.prover) は呼べない
        // (借用の競合)ため、先にインデックスごとの優先度だけを計算しておく。
        // bandit_enabled=false の場合は全定理を優先度0固定にし、導入前と
        // 同じ挙動に戻す(A/B比較用)。
        let theorem_count = self.prover.theorems.len();
        let priorities: Vec<i32> = if self.bandit_enabled {
            (0..theorem_count).map(|idx| self.prover.theorem_priority_bonus(idx)).collect()
        } else {
            vec![0; theorem_count]
        };

        // 🌟 型シグネチャ事前フィルタ(theorem_types_availableのドキュメント参照):
        // 借用チェッカの都合上(下のループはself.prover.theoremsを不変借用したまま
        // &mut self.proverを要求するtheorem_types_availableを呼べない)、
        // 先にインデックスごとの可否だけ計算しておく。
        let types_available: Vec<bool> = (0..theorem_count)
            .map(|idx| self.prover.theorem_types_available(idx))
            .collect();

        for idx in 0..self.prover.theorems.len() {
            if !types_available[idx] { continue; }
            let mut initial_bind = Bind::default();
            initial_bind.insert("Ang90".to_string(), self.prover.egraph.ang90);
            initial_bind.insert("Ang0".to_string(), self.prover.egraph.ang0);

            self.task_queue.push(MatchTask {
                priority: priorities[idx],
                theorem_idx: idx,
                bind: initial_bind,
                flip_states: FlipStates::default(),
                is_seeded: false,
            });
            self.prover.profile.sfs_tasks_created += 1;
        }
        self.prover.profile.sfs_time += sfs_start.elapsed();
    }

    fn schedule_matcher_task(&mut self, fact: &Fact) {
        let (fact_type, fact_objs) = match fact {
            Fact::Identical(a, b) => ("Identical", vec![*a, *b]),
            Fact::Connected(c, p) => ("Connected", vec![*c, *p]),
            Fact::Parallel(a, b) => ("Parallel", vec![*a, *b]),
        };

        for (idx, theorem) in self.prover.theorems.iter().enumerate() {
            for pat in &theorem.patterns {
                if let Pattern::Fact(def) = pat {
                    if def.fact_type == fact_type && def.args.len() == fact_objs.len() {
                        
                        // 🌟 FIX: Python版の _evaluate_patterns_with_seed_gen を再現[cite: 6]
                        // 発見された事実のオブジェクトの順列を作り、変数を事前バインド（シード化）する
                        let perms = match fact_type {
                            "Connected" => vec![fact_objs.clone()], // 有向関係なので順列なし
                            _ => get_permutations(&fact_objs),      // Identical 等は全順列
                        };

                        for perm in perms {
                            let mut bind = Bind::default();
                            // 定数ノードの事前バインド
                            bind.insert("Ang90".to_string(), self.prover.egraph.ang90);
                            bind.insert("Ang0".to_string(), self.prover.egraph.ang0);

                            // 🌟 シードの注入
                            for (i, v_name) in def.args.iter().enumerate() {
                                bind.insert(v_name.clone(), perm[i]);
                            }

                            // シード済みリーチフォーマットとしてタスクを積む
                            self.task_queue.push(MatchTask {
                                priority: 10,
                                theorem_idx: idx,
                                bind,
                                flip_states: FlipStates::default(),
                                                is_seeded: true,
                            });
                        }
                    }
                }
            }
        }
    }

    pub fn emit(&mut self, event: Event) {
        self.event_queue.push_back(event);
    }

    pub fn run_step(&mut self, budget: usize) -> bool {
        let mut applied_anything = false;
        let mut calls = 0;

        while calls < budget {
            while let Some(event) = self.event_queue.pop_front() {
                match event {
                    Event::NodeMerged => {
                        if self.prover.egraph.apply_congruence_closure() {
                            applied_anything = true;
                            self.event_queue.push_back(Event::NodeMerged);
                        }
                    },
                    Event::FactProven(fact) => {
                        // 🐛 ここは死んだ分岐。apply_conclusions は
                        // Connected の結論を適用した時点で既に self.facts へ push してから
                        // new_facts を返すので、以前ここにあった !contains の中に
                        // schedule_matcher_task を置く形だと条件は常に偽で、
                        // シード付き再マッチングの経路が一度も走っていなかった
                        // (--profile の「シード済みタスクのポップ数」が全問題で0回)。
                        //
                        // ⚠️ このバグ自体は新発見では無い。docs/atlas.html §04
                        // 「schedule_matcher_task の二重チェックバグ修正(reverted)」にある通り、
                        // 以前にも見つけられており、直す実験が5回試されて全部撤回されている
                        // (重複シード排除付き・5定理限定の許可リスト付きも含む)。
                        // 下の数字はその6回目にあたるもので、壁時計ではなく仕事量予算の下で
                        // 測り直した点だけが新しい。過去5回と同じく悪化するが、
                        // 今回はフラグとして残すことで再測定を安くする。
                        // 🌟 実測して既定を決めた: そのまま呼ぶようにすると
                        // 掛け合わせで 29/37・65秒 → 28/37・416秒(6.4倍)。
                        // 完全な損ではなく bench_2018chnwesternmop5 を新たに解く一方で、
                        // nine_point_full と bench_2005ctstp1 を落とす――schedule_matcher_task は
                        // (定理 × 一致するパターン × 全順列)の数だけ優先度10のタスクを
                        // 一気に積むため、全探索側のタスクを押しのけて予算を使い切ってしまう。
                        // simson 単体で見ると分かりやすい: 解けることは解けるが、
                        // 消費仕事量が 105,430 → 740,036 ステップ(7倍)になり、その 87.7% を
                        // シード済みタスク(1455回ポップ)が食う。
                        // 仕組み自体は無駄では無さそうなので、resolve_midpoint_demands と同じく
                        // フラグ(--seeded-rematch)で残し、ファンアウトの絞り方を別途試せるようにする。
                        if !self.prover.facts.contains(&fact) {
                            self.prover.facts.push(fact.clone());
                        }
                        if self.seeded_rematch_enabled {
                            self.schedule_matcher_task(&fact);
                        }
                    }
                }
            }

            if let Some(mut task) = self.task_queue.pop() {
                calls += 1;
                self.prover.dfs_calls = 0;
                // 🌟 task はcap到達時に self.task_queue.push(task) で再キューされ
                // 得るため(move)、後段のバンディット記録で使うフィールドは
                // Copy型としてここで先に控えておく。
                let task_theorem_idx = task.theorem_idx;
                let task_is_seeded = task.is_seeded;
                // 🌟 --trace 診断(trace.rs 参照): 発火を記録するのは
                // apply_conclusions だが、「どの優先度のタスクから発火したか」を
                // 知っているのはこちらだけなので、ポップのたびに手渡しておく。
                if let Some(t) = self.prover.trace.as_mut() {
                    t.current = (task.priority, task.is_seeded);
                    t.task_seq += 1;
                }
                // 🌟 theorems は Vec<Rc<TheoremDef>> なので、この clone() はもう
                // ディープコピーではなく参照カウントのインクリメントのみ(ポインタコピー相当)
                let theorem = self.prover.theorems[task.theorem_idx].clone();
                let mut new_binds = Vec::new();
                // 🌟 検証メモ: 当初は schedule_full_sweep() 由来のシードなしタスク
                // (priority<=0) だけ上限を 20,000 に下げる案を試したが、miquel の
                // 「有向角の加法性」「円周角の定理の逆」はまさにシードなし状態から
                // 20,000〜100,000回の間で成功しており、上限を下げるとリトライのたびに
                // failed_paths キャッシュが空の状態から探索をやり直すだけになって
                // かえって遅くなった(0.69s→1.15s)ため撤回した。
                // 上限自体は104行目のフィールド定義の通り常に100,000のまま。
                //
                // 🌟 ユーザー提案(「新規作図でfailed pathが破棄されるのは
                // ある程度どうしようもないが、接続の弱いfailed pathは型に
                // 関わらず保持できるはず」→続けて「タスクをまたいだグローバル
                // 化」)への対応。以前はfailed_pathsをMatchTask単位の寿命
                // (dfs_cap到達での再キュー間でしか持ち越せない)で持たせて
                // いたが、診断計測で判明した「dfs_matchの再訪問の38%はタスク
                // をまたいだもの」(UCB1がschedule_full_sweepのたびに同じ
                // 定理を新しいtask/新しいbindで何度も試す)を一切捕捉できて
                // いなかった。state_sigは元々bind内容だけで決まる(特定の
                // タスクインスタンスとは無関係な)ハッシュなので、
                // ProverEngine::global_failed_paths(theorem_idxごとの永続
                // マップ)へ昇格させ、このタスクの実行中だけ借用する
                // (std::mem::takeで一時的に取り出し、使い終わったら必ず
                // 書き戻す――dfs_matchが&mut selfを要求するため、self自身の
                // フィールドを借用しながら再帰呼び出しできない、という
                // 借用チェッカ上の制約を回避する常套手段)。
                self.prover.ensure_global_failed_paths();
                let mut failed_paths = std::mem::take(&mut self.prover.global_failed_paths[task.theorem_idx]);

                let mut dep_mask: u8 = 0;
                // 🌟 パターン列は定理の持ち物をそのまま借り、「どれがまだ
                // 生きているか」だけをビットで渡す(dfs_matchのドキュメント参照)。
                // タスク側でパターン列を複製して持つ必要も無くなった。
                let all_active: u64 = if theorem.patterns.len() >= 64 {
                    u64::MAX
                } else {
                    (1u64 << theorem.patterns.len()) - 1
                };
                self.prover.dfs_match(
                    &theorem,
                    &theorem.patterns,
                    all_active,
                    task.bind.clone(),
                    task.flip_states.clone(),
                    &mut failed_paths,
                    &mut dep_mask,
                    &mut |bind, flips| {
                        new_binds.push((bind.clone(), flips.clone()));
                    }
                );
                // 🌟 借用したグローバルキャッシュを書き戻す。dfs_cap到達で
                // 再キューされるかどうかに関わらず、この定理への次のどの
                // タスク(全く別のbindでも)からも再利用できるよう常に戻す
                // (以前のタスク単位保存は再キュー時にしか書き戻さなかった
                // ため、cap到達に至らず自然にタスクが完了したケースでは
                // せっかく積んだfailed_pathsがそのまま捨てられていた)。
                self.prover.global_failed_paths[task.theorem_idx] = failed_paths;
                // 🌟 コスト考慮型バンディット報酬のために、このタスク1回が
                // 実際に消費したdfs_call数を控えておく(次のタスクの
                // self.prover.dfs_calls = 0 まではこの値のまま変わらない)。
                let dfs_calls_used = self.prover.dfs_calls;
                if task_is_seeded {
                    self.prover.profile.seeded_pops += 1;
                    self.prover.profile.seeded_dfs_calls += dfs_calls_used;
                } else {
                    self.prover.profile.unseeded_pops += 1;
                    self.prover.profile.unseeded_dfs_calls += dfs_calls_used;
                }

                // 🌟 スケジューリング工夫: DFSが上限(100,000)に張り付いた場合、
                // このタスクは重すぎるためペナルティを与えて後回しにする。
                //
                // 🐛 バグ修正: 以前はキューが空(＝他に実行できるタスクが無い)の場合でも
                // 無条件に再キューしていた。この場合 e-graph も bind も何一つ変化しないまま
                // 全く同じ 100,000 回の探索を優先度が尽きるまで(最大5回)繰り返すだけになり、
                // 実測で simson 問題では1つの定理(有向角の加法性)のリトライだけで
                // 5秒の予算のうち3秒以上を無駄にしていた。他に実行可能なタスクが残っている
                // 場合のみ再キューし、無い場合はその場で諦めてリカバリーフェーズに委ねる。
                if self.prover.dfs_calls >= self.prover.dfs_cap {
                    if !self.task_queue.is_empty() {
                        task.priority -= 5;
                        if task.priority >= -20 { // 諦める閾値
                            // 🌟 failed_pathsは既にglobal_failed_pathsへ書き戻し
                            // 済み(このタスク固有の状態としてではなく、この
                            // 定理全体で共有される状態として)なので、ここでは
                            // タスク自体(bind/remaining_patterns)を再キューする
                            // だけでよい。
                            self.task_queue.push(task);
                        }
                    }
                }

                // 🌟 UCB1バンディット: このタスク(1回のdfs_match呼び出し)が
                // 実際に何か結論を適用できたかどうかを、シードなしタスクに限って
                // theorem_statsに反映する。「試したが何も生まなかった」も
                // 立派な学習対象(失敗)である。
                let mut task_succeeded = false;

                for (mut bind, flips) in new_binds {
                    // 🌟 1. まず現在のE-Graphの状態で、この結論がすでに満たされているかチェックする
                    if self.prover.is_already_proven(&theorem.conclusions, &bind, &flips) {
                        continue;
                    }

                    // 🌟 2. 結論が満たされていない場合のみ、足りない図形を作図する
                    if self.prover.execute_constructions(&theorem.name, &theorem.constructions, &mut bind) {

                        // 🌟 3. 作図後、もう一度チェック。ここで真になるなら「作図しただけでマージ済み」なのでスキップ
                        if self.prover.is_already_proven(&theorem.conclusions, &bind, &flips) {
                            continue;
                        }

                        println!("  🎯 [リーチ通知] 定理「{}」の前提条件がすべて満たされました！", theorem.name);
                        for (var_name, class_id) in &bind {
                            if var_name.starts_with("__") { continue; }
                            let entity_name = self.prover.egraph.entities[self.prover.egraph.get_rep(*class_id).0].name.clone();
                            println!("      - 割り当て: {} = {}", var_name, entity_name);
                        }

                        let (applied, generated_facts) = self.prover.apply_conclusions(&theorem, &bind, &flips);
                        if applied {
                            applied_anything = true;
                            task_succeeded = true;
                            self.emit(Event::NodeMerged);
                            for f in generated_facts { self.emit(Event::FactProven(f)); }
                        }
                    }
                }

                if !task_is_seeded {
                    self.prover.record_theorem_attempt(task_theorem_idx, task_succeeded, dfs_calls_used);
                }
            } else { break; }
        }
        applied_anything
    }

    // 🌟 フェーズ1.5: 交点を持つ2直線のペアから有向角(AnglePair)を自動生成
    pub fn resolve_angle_demands(&mut self) -> bool {
        let mut applied = false;
        let mut angle_pairs_to_create = Vec::new();

        // 🌟 処理前にグラフを最新状態に正規化し、直線の重複を完全に消す
        self.prover.egraph.apply_congruence_closure();

        for i in 0..self.prover.egraph.entities.len() {
            let pt_id = ClassId(i);
            if self.prover.egraph.get_rep(pt_id) != pt_id { continue; }
            if self.prover.egraph.entities[i].entity_type != EntityType::Point { continue; }

            // 🐛 FIX: line_infinity自身は普通の「直線」として数えない。
            // EntityType::Direction撤廃(方向はL∞に接続されたただのPoint)以降、
            // ここでのptがDirectionだと、その定義上line_infinityに必ず
            // 接続されている(=lines_on_ptに常にline_infinityを含む)ため、
            // 「Directionの直線+line_infinity」というペアから
            // AnglePair(その方向, DirectionOf(line_infinity))という無意味な
            // 退化した有向角を自動生成してしまっていた
            // (miquel_quadrilateralで実際に観測: EntityType::Angle撤廃で
            // これがEntityType::Scalarに合流したことで、他の定理の自己束縛
            // 候補プールを無駄な退化角で汚染し証明を妨げるまでになった)。
            let mut lines_on_pt = Vec::new();
            for comp in &self.prover.egraph.entities[i].components {
                for &sub_id in &comp.subobjects {
                    let sub_rep = self.prover.egraph.get_rep(sub_id);
                    if sub_rep == self.prover.egraph.line_infinity { continue; }
                    if self.prover.egraph.entities[sub_rep.0].entity_type == EntityType::Line {
                        lines_on_pt.push(sub_rep);
                    }
                }
            }
            lines_on_pt.sort_unstable_by_key(|id| id.0);
            lines_on_pt.dedup();

            if lines_on_pt.len() >= 2 {
                for l1 in 0..lines_on_pt.len() {
                    for l2 in (l1 + 1)..lines_on_pt.len() {
                        let d1 = self.get_or_create_direction(lines_on_pt[l1]);
                        let d2 = self.get_or_create_direction(lines_on_pt[l2]);
                        
                        let r_d1 = self.prover.egraph.get_rep(d1);
                        let r_d2 = self.prover.egraph.get_rep(d2);

                        // 🌟 FIX: 方向が同じ(平行/同一)な直線のペアで0度角を生成しない
                        if r_d1 == r_d2 { continue; }

                        // 🌟 FIX: allow_flip があるため、ID順でソートして片方のみを生成（数を半分に！）
                        let (d_min, d_max) = if r_d1.0 < r_d2.0 { (r_d1, r_d2) } else { (r_d2, r_d1) };
                        angle_pairs_to_create.push((d_min, d_max));
                    }
                }
            }
        }

        angle_pairs_to_create.sort_unstable_by_key(|(d1, d2)| (d1.0, d2.0));
        angle_pairs_to_create.dedup();

        for (d1, d2) in angle_pairs_to_create {
            let def = Definition::AnglePair(d1, d2);
            if !self.prover.egraph.memo.contains_key(&def) {
                let name = format!("AnglePair_{}_{}_(Auto)", self.prover.egraph.entities[d1.0].name, self.prover.egraph.entities[d2.0].name);
                let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Scalar);
                
                // 🌟 FIX: Auto生成されたAngleの重要度を下げ、無駄なヒューリスティック探索を抑制
                self.prover.egraph.entities[new_id.0].base_importance = 0.2;
                
                self.prover.egraph.apply_trivial_relations(new_id, &def);
                applied = true;
            }
        }

        if applied {
            println!("  💡 [スマート補完] 交点を持つ意味のある有向角を自動生成しました");
            self.schedule_full_sweep();
        }
        applied
    }

    fn get_or_create_direction(&mut self, line_id: ClassId) -> ClassId {
        let def = Definition::DirectionOf(line_id);
        if let Some(&dir_id) = self.prover.egraph.memo.get(&def) {
            return self.prover.egraph.get_rep(dir_id);
        }
        let name = format!("Dir_{}_(Fallback)", self.prover.egraph.entities[line_id.0].name);
        let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Point);
        self.prover.egraph.apply_trivial_relations(new_id, &def);
        new_id
    }

    // 🌟 フェーズ2: 論理エンジンが欲しがっていた補助線(Demand)を引く
    //
    // 🌟 ユーザー提案: 「点の組A,Bについて、線分ABの次数がdeg(A)+deg(B)という
    // 素朴な上界に比べて退化して小さい組は、何らかの隠れた定理・偶然の一致が
    // 効いている兆候として『相性が良い』」への対応で、頻度ベースのscoreに
    // measure_line_affinity(A,B)の退化量(deg_a+deg_b - deg_line、0未満は0に
    // 切り詰め)を加点として合成し、頻度だけでは見えない「単純な組み合わせに
    // 見えて実は特別な関係にある」ペアも優先的に試せるようにする。
    pub fn resolve_demands(&mut self) -> bool {
        if self.prover.construction_demands.is_empty() { return false; }

        const AFFINITY_MAX_D: usize = 4;
        const AFFINITY_WEIGHT: f64 = 2.0;
        let mut demands: Vec<((ClassId, ClassId), f64, Option<(usize, usize, usize)>)> = self.prover.construction_demands.iter()
            .map(|(&(p1, p2), &score)| {
                let affinity = self.prover.egraph.measure_line_affinity(p1, p2, AFFINITY_MAX_D);
                (( p1, p2), score, affinity)
            })
            .collect();
        demands.sort_by(|a, b| {
            let priority = |&(_, score, aff): &((ClassId, ClassId), f64, Option<(usize, usize, usize)>)| -> f64 {
                let bonus = aff.map_or(0.0, |(da, db, dab)| {
                    (da as f64 + db as f64 - dab as f64).max(0.0)
                });
                score + AFFINITY_WEIGHT * bonus
            };
            priority(b).partial_cmp(&priority(a)).unwrap_or(std::cmp::Ordering::Equal)
                .then_with(|| (a.0).0.0.cmp(&(b.0).0.0))
                .then_with(|| (a.0).1.0.cmp(&(b.0).1.0))
        });

        let mut applied = false;
        let mut count = 0;

        for ((p1, p2), score, affinity) in demands.into_iter() {
            let def = Definition::new_line(p1, p2);
            if !self.prover.egraph.memo.contains_key(&def) {
                let name = format!("Line_{}_{}_(Demand)", self.prover.egraph.entities[p1.0].name, self.prover.egraph.entities[p2.0].name);
                match affinity {
                    Some((da, db, dab)) if da + db > dab => {
                        println!("  💡 [オンデマンド作図] 要請により {} を生成 (需要: {:.1}, 相性◎: 次数{}+{}→{})", name, score, da, db, dab);
                    }
                    _ => {
                        println!("  💡 [オンデマンド作図] 要請により {} を生成 (需要: {:.1})", name, score);
                    }
                }
                let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Line);

                // 🌟 FIX: Demand線の重要度を下げ、推論の主軸がブレるのを防ぐ
                self.prover.egraph.entities[new_id.0].base_importance = 0.5;

                self.prover.egraph.apply_trivial_relations(new_id, &def);
                applied = true;
                count += 1;
                if count >= 3 { break; }
            }
        }

        self.prover.construction_demands.clear();
        if applied {
            // 🌟 FIX: 作図直後に合同閉包を強制実行し、既存の直線と即座にマージさせる！
            self.prover.egraph.apply_congruence_closure();
            self.schedule_full_sweep();
        }
        applied
    }

    // 🌟 フェーズ2.9: 目標駆動のオンデマンド作図(最後の砦、MCTSに頼る直前)。
    //
    // 背景(HAGeo-409ベンチマークで判明): resolve_demands/resolve_point_demands/
    // resolve_angle_demandsはいずれも「ある定理のDFSが実際にその組み合わせを
    // 束縛しようとして初めて需要として記録される」という反応的な仕組みで
    // 統一されている。これは無関係な直線・点を無差別に作り続ける組み合わせ
    // 爆発を避けるための健全な設計だが、逆に言うと「証明したい目標
    // (target_fact)には出てくるのに、重要度が低くどの定理からも一度も
    // 束縛されない孤立点」には永遠に需要が発生しないという穴がある
    // (実例: bench_2005usamop3のQ。B1,C1,Pとは共円関係の探索が活発に
    // 進む一方、Qは他の3点への直線が一度も引かれずグラフから孤立したまま
    // 探索がStallしていた)。
    //
    // 目標の引数に現れる点同士は「最終的に何らかの関係を証明したい」という
    // 意味で構造的に重要なはずなので、他の需要駆動フェーズが尽きた場合に
    // 限り(MCTSのような無方向な探索に頼る前の最後の一手として)、まだ
    // 直線で結ばれていない目標点のペアに無条件で補助線を引いてみる。
    // 需要の頻度・次数による絞り込みが無い分、resolve_demandsより無防備な
    // 最終手段なので、他の全ての需要駆動フェーズが失敗した後にだけ呼ぶこと。
    pub fn resolve_target_demands(&mut self, target: &Option<(String, Vec<ClassId>)>) -> bool {
        let Some((_, target_args)) = target else { return false; };

        let mut points: Vec<ClassId> = target_args.iter()
            .map(|&id| self.prover.egraph.get_rep(id))
            .filter(|&id| self.prover.egraph.entities[id.0].entity_type == EntityType::Point)
            .collect();
        points.sort_unstable_by_key(|id| id.0);
        points.dedup();

        let mut applied = false;
        let mut count = 0;
        'outer: for i in 0..points.len() {
            for j in (i + 1)..points.len() {
                let (p1, p2) = (points[i], points[j]);
                let def = Definition::new_line(p1, p2);
                if self.prover.egraph.memo.contains_key(&def) { continue; }
                // 🐛 FIX: p1,p2が既に何らかの直線を共有しているなら、その直線を
                // 差し置いて別の新しいLineThroughPointsエンティティを作っては
                // いけない。理論上は「2点が決める直線」は1本しかないので数値的にも
                // 同一のはずだが、新しい直線を作るとapply_trivial_relationsが
                // p1,p2それぞれにこの新しい直線への接続をもう1本追加してしまい、
                // 「この点は複数の互いに矛盾しうる接続を持つ」と見なされて
                // (has_extraneous_incidence)数値サンプリングが特定の直線上に
                // 座標を固定できなくなる(assign_free_point_coordsが安全側に倒れて
                // 無制約の乱数を返す)。実際にminiquelで、既にLineBC上にある
                // C,DについてLine(C,D)を新規に作った結果、Dの数値サンプリングが
                // 壊れてLineBCとの合流はおろか無関係な円の合流まで数値的健全性
                // チェックに軒並み却下される、という副作用が実測で見つかった。
                // find_common_lineで「既に共有する直線があるか」を確認し、あれば
                // 何もしない(その直線は既に存在するので、そもそも需要ではない)。
                if self.prover.egraph.find_common_line(&[p1, p2]).is_some() { continue; }
                let name = format!("Line_{}_{}_(TargetDemand)", self.prover.egraph.entities[p1.0].name, self.prover.egraph.entities[p2.0].name);
                println!("  💡 [目標駆動オンデマンド作図] 証明目標に現れる点を結ぶ {} を生成", name);
                let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Line);
                // 🌟 他のDemand系と同様、新規図形の重要度は下げて推論の主軸がブレるのを防ぐ
                self.prover.egraph.entities[new_id.0].base_importance = 0.5;
                self.prover.egraph.apply_trivial_relations(new_id, &def);
                applied = true;
                count += 1;
                if count >= 3 { break 'outer; }
            }
        }

        if applied {
            self.prover.egraph.apply_congruence_closure();
            self.schedule_full_sweep();
        }
        applied
    }

    /// 🌟 目標が「同じ直線上の2点が一致すること」のとき、その2点の複比を作る。
    ///
    /// EGraph::propagate_cross_ratio_uniqueness(複比の透視射影不変性の逆)は
    /// 「(A,B;C,P) と (A,B;C,Q) が同じ値なら P ≡ Q」を与えるが、そもそも
    /// その2つの複比が実体として存在しないと一度も発火しない――実測でも、
    /// 逆の規則を入れた直後は単体テストでは働くのにベンチマーク32問でも
    /// 自由作図の発見でも一度も呼ばれなかった。
    ///
    /// 発見される主張の多くは「3直線が1点で交わる」で、それは
    /// 「l1∩l2 と l1∩l3 が同じ点」= l1 上の2点の一致に翻訳される。
    /// そこで目標がまさにその形のときだけ、その直線上の他の3点を取って
    /// 2つの複比を作ってやる。あとは順方向の射影の定理(透視射影不変性)が
    /// その2つを等しいと示せれば、逆の規則が一致を結論する。
    ///
    /// 中点の需要(resolve_midpoint_demands)と同じく、目標に直接関係する
    /// ときだけ作るので、複比と無関係な問題には一切コストがかからない。
    pub fn resolve_cross_ratio_demands(&mut self, target: &Option<(String, Vec<ClassId>)>) -> bool {
        let Some((kind, args)) = target else { return false; };
        if kind != "Identical" || args.len() < 2 { return false; }
        let (p, q) = (self.prover.egraph.get_rep(args[0]), self.prover.egraph.get_rep(args[1]));
        if p == q { return false; }
        let is_point = |eg: &EGraph, id: ClassId| eg.entities[id.0].entity_type == EntityType::Point;
        if !is_point(&self.prover.egraph, p) || !is_point(&self.prover.egraph, q) { return false; }

        // 2点が共有する直線。そこに乗っている他の点から3つ選ぶ。
        let line = match self.prover.egraph.find_common_line(&[p, q]) { Some(l) => l, None => return false };
        if line == self.prover.egraph.line_infinity { return false; }
        let mut others: Vec<ClassId> = self.prover.egraph.entities[line.0].components.first()
            .map(|c| c.subobjects.clone()).unwrap_or_default()
            .into_iter()
            .map(|x| self.prover.egraph.get_rep(x))
            .filter(|&x| is_point(&self.prover.egraph, x) && x != p && x != q)
            .collect();
        others.sort_unstable_by_key(|id| id.0);
        others.dedup();
        if others.len() < 3 { return false; }
        // 図の要になっている点から選ぶ(熱の高い順)。
        others.sort_by(|&a, &b| self.prover.egraph.entities[b.0].heat_with_degree()
            .partial_cmp(&self.prover.egraph.entities[a.0].heat_with_degree())
            .unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| a.0.cmp(&b.0)));
        let (x, y, z) = (others[0], others[1], others[2]);

        let mut applied = false;
        for (fourth, label) in [(p, "P"), (q, "Q")] {
            let def = self.prover.egraph.normalize_definition(&Definition::CrossRatio(x, y, z, fourth));
            if self.prover.egraph.memo.contains_key(&def) { continue; }
            let name = format!("CR_{}_(TargetDemand)", label);
            println!("  💡 [目標駆動オンデマンド作図] 複比の一意性に持ち込むため {} を生成", name);
            let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Scalar);
            self.prover.egraph.entities[new_id.0].base_importance = 0.5;
            self.prover.egraph.apply_trivial_relations(new_id, &def);
            applied = true;
        }
        if applied {
            self.prover.egraph.apply_congruence_closure();
            self.schedule_full_sweep();
        }
        applied
    }

    // 🌟 フェーズ2.5: 交点(Point)の需要を解消する。2種類の需要源を合流させる:
    //   (a) match_defined_by_fact由来のpoint_construction_demands――今のところ
    //       どの定理も"Intersection"をDefinedByパターンとして問い合わせて
    //       いないため実質発火しないが、将来そのような定理を追加した時のために
    //       残してある。
    //   (b) このメソッド自身が行う、垂線の足に対する能動的なヒューリスティック
    //       走査(resolve_angle_demandsと同じ設計思想): 既存のPerpendicularLine
    //       (L_base, P)それぞれについて、それ自身とL_baseの交点(=Pから
    //       L_baseへの垂線の足)がまだ図形として存在しなければ需要とみなす。
    //       これは「2直線の任意の組み合わせ」のような組み合わせ爆発ではなく、
    //       既存のPerpendicularLineの数(三角形なら高々3本)に比例するだけの
    //       安全なスキャンで、直感的にも「垂線を引いたなら、その足は普通
    //       興味の対象になる」という妥当な着眼点。
    //       ユーザー要望: orthocenter/orthocenter_altでE,Fのような補助点を
    //       手で問題文に書かなくても発見できるようにしたい、への対応。
    //
    // 🌟 安全策: resolve_demands/resolve_angle_demandsと同じく、DFSが完全に
    // Stallしたリカバリーフェーズでのみ呼ばれる。新規点の重要度は下げて
    // 推論の主軸がブレるのを防ぐ。
    pub fn resolve_point_demands(&mut self) -> bool {
        // (b) 垂線の足の能動的スキャン。既存のdemandに合流させる。
        for i in 0..self.prover.egraph.entities.len() {
            let id = ClassId(i);
            if self.prover.egraph.get_rep(id) != id { continue; }
            if self.prover.egraph.entities[i].entity_type != EntityType::Line { continue; }
            let bases: Vec<ClassId> = self.prover.egraph.entities[i].components.iter()
                .flat_map(|c| c.definitions.iter())
                .filter_map(|d| if let Definition::PerpendicularLine(base, _) = d { Some(*base) } else { None })
                .collect();
            for base in bases {
                let base_rep = self.prover.egraph.get_rep(base);
                if base_rep == id { continue; }
                let key = if id.0 < base_rep.0 { (id, base_rep) } else { (base_rep, id) };
                self.prover.point_construction_demands.entry(key).or_insert(0.0);
            }
        }

        if self.prover.point_construction_demands.is_empty() { return false; }

        // 🌟 MMPの次数(measure_intersection_degree_candidate)で候補を
        // ランク付けする(ユーザー指摘: 添付のMMP解説PDFの「次数」概念、
        // および旧Python版に既にあったnumerical_degree)。次数が低い
        // (=単純な)候補を優先し、異常に高い候補(DEGREE_CAP超)は最初から
        // 除外する。中点のような「構造的には複合に見えても実際は次数が
        // 上がらない」構成は自然に許容されつつ、無関係な直線同士の交点を
        // 無差別に取り続けるような構成は次数が積み上がるため自然に
        // 足切りされる(実測でこの2つが明確に区別できることを
        // test_numerical_degree_*系のテストで確認済み)。
        // 次数が測定不能(Noneを表す適切なmoverが見つからない等)な場合は
        // 安全側に倒し、除外せず「不明」として通す。
        const DEGREE_CAP: usize = 4;
        const MAX_D: usize = 6;
        let mut demands: Vec<((ClassId, ClassId), f64, Option<usize>)> = self.prover.point_construction_demands.iter()
            .map(|(&(l1, l2), &score)| {
                let deg = self.prover.egraph.measure_intersection_degree_candidate(l1, l2, MAX_D);
                (( l1, l2), score, deg)
            })
            .filter(|&(_, _, deg)| deg.map_or(true, |d| d <= DEGREE_CAP))
            .collect();
        demands.sort_by(|a, b| {
            let da = a.2.unwrap_or(usize::MAX);
            let db = b.2.unwrap_or(usize::MAX);
            da.cmp(&db)
                .then_with(|| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal))
                .then_with(|| (a.0).0.0.cmp(&(b.0).0.0))
                .then_with(|| (a.0).1.0.cmp(&(b.0).1.0))
        });

        let mut applied = false;
        let mut count = 0;

        for ((l1, l2), score, deg) in demands.into_iter() {
            // 🌟 需要記録時からさらにマージが進んでいる可能性があるため、
            // normalize_definitionで現在の代表元へ正規化してから照合する。
            let def = self.prover.egraph.normalize_definition(&Definition::Intersection(l1, l2));
            let (l1, l2) = match def { Definition::Intersection(a, b) => (a, b), _ => (l1, l2) };
            if l1 == l2 { continue; }
            if !self.prover.egraph.memo.contains_key(&def) {
                let name = format!("Pt_{}_{}_(Demand)",
                    self.prover.egraph.entities[l1.0].name, self.prover.egraph.entities[l2.0].name);
                let deg_str = deg.map(|d| d.to_string()).unwrap_or_else(|| "不明".to_string());
                println!("  💡 [オンデマンド作図] 要請により {} (交点、次数{})を生成 (需要: {:.1})", name, deg_str, score);
                let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Point);

                // 🌟 Demand点の重要度を下げ、推論の主軸がブレるのを防ぐ(Demand線と同じ配慮)
                self.prover.egraph.entities[new_id.0].base_importance = 0.5;

                self.prover.egraph.apply_trivial_relations(new_id, &def);
                applied = true;
                count += 1;
                // 🌟 実測に基づくFIX: 当初は上限4(三角形の垂線3本+余裕1)にしていたが、
                // orthocenter/orthocenter_altで実験したところ、3本の垂線の足を
                // 一度に全部作ってしまうと(円の候補が3通りに増える等)DFSの
                // 探索が拡散し、逆に目標へ到達しにくくなることが判明した。
                // 上限を2に下げる(=最初のスタックでは最も需要が高い2点だけを
                // 作る)ことで、orthocenter(対称形、垂線の足なし)が4.5秒、
                // orthocenter_alt(補助点E,Fなし)が2.5秒で解けるようになった
                // ――3本目が本当に必要なら、次にまたStallした時に改めて
                // 需要として再スキャンされるので、完全性は失われない。
                if count >= 2 { break; }
            }
        }

        self.prover.point_construction_demands.clear();
        if applied {
            self.prover.egraph.apply_congruence_closure();
            self.schedule_full_sweep();
        }
        applied
    }

    /// 🌟 需要駆動の中点作図。
    ///
    /// ユーザー報告「まだ証明のパワーが弱い」の実測から入れた回復手段。
    /// 自由作図が見つけた「BC と、ABに平行でACの中点を通る直線と、CAに
    /// 平行でABの中点を通る直線が1点で交わる」(=中点連結定理そのもの)が、
    /// 20秒の予算のうち0.4秒で「行き詰まり」を返していた。切り分けたところ、
    /// 定理を足しても(射影・中心角)、候補capを3倍に広げても、退化熱を
    /// 入れても、MCTSに頼っても届かず、**BCの中点を図に足すだけで
    /// 決定的に証明できる**ことが分かった。足りなかったのは探索の幅でも
    /// 定理でもなく、1つの補助点だった。
    ///
    /// そこで「図に既に中点がいくつかあるなら、その端点になっている点の
    /// 集合について、まだ取られていない中点を補う」という一般の手を入れる。
    /// 人間が「他の中点も取ってみる」と考えるのと同じ動きで、中点連結定理の
    /// ように「3つの中点のうち2つしか図に無い」状況を埋める。中点が1つも
    /// 無い図では何もしない(中点と無関係な問題に中点を撒かないため)。
    ///
    /// 一度に作るのは需要の高い2点まで。resolve_point_demandsと同じ理由で、
    /// 一度に全部作ると探索が拡散して逆に届かなくなる――本当に必要なら
    /// 次のStallでまた候補に挙がるので、完全性は失われない。
    pub fn resolve_midpoint_demands(&mut self) -> bool {
        let eg = &self.prover.egraph;
        // 図に既にある中点の、端点になっている点を集める。
        let mut anchors: Vec<ClassId> = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for i in 0..eg.entities.len() {
            let id = ClassId(i);
            if eg.get_rep(id) != id { continue; }
            for c in &eg.entities[i].components {
                for d in &c.definitions {
                    if let Definition::Midpoint(a, b) = d {
                        for p in [eg.get_rep(*a), eg.get_rep(*b)] {
                            if seen.insert(p) { anchors.push(p); }
                        }
                    }
                }
            }
        }
        if anchors.len() < 3 { return false; }   // 補える組が無い
        anchors.sort_unstable_by_key(|id| id.0);

        // まだ取られていない中点の候補を、両端の熱の合計が高い順に。
        let mut candidates: Vec<(ClassId, ClassId, f64)> = Vec::new();
        for i in 0..anchors.len() {
            for j in (i + 1)..anchors.len() {
                let (a, b) = (anchors[i], anchors[j]);
                let def = eg.normalize_definition(&Definition::Midpoint(a, b));
                if eg.memo.contains_key(&def) { continue; }
                let heat = eg.entities[a.0].heat() + eg.entities[b.0].heat();
                candidates.push((a, b, heat));
            }
        }
        if candidates.is_empty() { return false; }
        candidates.sort_by(|x, y| y.2.partial_cmp(&x.2).unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| x.0.0.cmp(&y.0.0)).then_with(|| x.1.0.cmp(&y.1.0)));

        let mut applied = false;
        for (a, b, heat) in candidates.into_iter().take(2) {
            let def = self.prover.egraph.normalize_definition(&Definition::Midpoint(a, b));
            if self.prover.egraph.memo.contains_key(&def) { continue; }
            let name = format!("Mid_{}_{}_(Demand)",
                self.prover.egraph.entities[a.0].name, self.prover.egraph.entities[b.0].name);
            println!("  💡 [オンデマンド作図] 要請により {} (中点)を生成 (需要: {:.1})", name, heat);
            let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Point);
            // Demand線・Demand点と同じく重要度を下げ、推論の主軸がブレるのを防ぐ。
            self.prover.egraph.entities[new_id.0].base_importance = 0.5;
            self.prover.egraph.apply_trivial_relations(new_id, &def);
            applied = true;
        }
        if applied {
            self.prover.egraph.apply_congruence_closure();
            self.schedule_full_sweep();
        }
        applied
    }
}

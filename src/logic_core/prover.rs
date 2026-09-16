//! 🌟 証明器の状態そのもの(ProverEngine)と、定理の適用。
//!
//! e-graph・既知の事実・定理ごとのバンディット統計・失敗パスのキャッシュを
//! 保持し、マッチが成立した後の作図(execute_constructions)と結論の適用
//! (apply_conclusions)を行う。探索は matcher.rs、見積もりは cost.rs。

use std::rc::Rc;

use crate::mmp_core::{ClassId, Definition, EGraph, EntityType, Fact};
use super::*;
use rustc_hash::FxHashMap;

pub struct ProverEngine {
    pub egraph: EGraph,
    pub facts: Vec<Fact>,
    // 🌟 Rc化: 定理定義(文字列・パターン列を大量に持つ重い構造体)は実行中不変なので、
    // タスク処理のたびに丸ごとディープコピーする代わりに Rc でポインタ共有する
    pub theorems: Vec<Rc<TheoremDef>>,
    pub dfs_calls: u64,
    // 🐛 バグ修正: 以前は dfs_match の探索上限が常に100,000固定だった。
    // schedule_full_sweep() から生成される「シードなし(priority<=0)」タスクは、
    // 変数が全て未束縛のまま定理を試すため、変数の多い定理(例: 有向角の加法性)では
    // ほぼ必ず失敗するのに毎回上限いっぱいまで探索してしまい、しかも
    // schedule_full_sweep() は要求解決のたびに何度も呼ばれるため、
    // 同じ「失敗するだけの巨大探索」を繰り返して秒単位の時間を浪費していた
    // (simsonで実測: この1定理だけで5秒中3秒以上を消費)。
    // schedule_matcher_task() 由来のシード済みタスク(priority>=10)は
    // 既に変数の多くが具体的な値に束縛されているため速く失敗/成功するので
    // 上限は据え置き、シードなしタスクだけ上限を大幅に下げて早期に諦めさせる。
    pub dfs_cap: u64,
    // 🌟 ユーザー提案(「マッチングを熱の上位だけを見るようにしていた
    // パラメータを調整できないか」)への対応。熱で降順ソートした後に
    // 候補を打ち切る上限が複数箇所(match_identical_factの(None,None)
    // 自己束縛、match_connected_factの局所スキャン/(None,None)ジョイン)に
    // 40というマジックナンバーでハードコードされていたのを、CLIから
    // --heat-cap=Nで一括調整できるフィールドに切り出した(既定は従来通り
    // 40)。既存の3箇所は全て同じ値を共有してきた経緯があるため、当面は
    // 分離せず1つのつまみにまとめる。
    pub heat_cap: usize,
    // 🌟 同じ提案への対応。「二重自己束縛」定理(有向角の加法性のように
    // 同じ型への(None,None)自己束縛を2つ以上持つ、または円周角の定理の逆
    // のように自己束縛の下流に同じtarget_typeのDefinedByペアリングが
    // ぶら下がる定理)は、自己束縛のcapがそのまま下流の分岐係数(cap×cap)
    // になるため、通常より大きく絞った専用のcapを使ってきた。
    // --fanout-heat-cap=Nで調整できる。
    //
    // 🌟 実測診断(ユーザー提案「解く速度も見るべき、行き詰まったら幅を
    // 広げる」)の結果、既定値10→5に変更した。32問題×3回集計で77/96→
    // 80/96に改善する一方、orthocenter_altのように「dfs_capに一度も
    // 到達していないのに、必要な候補がcap5では最初から除外される」問題が
    // 新たに生まれることも判明した(--time=15でも変わらず、時間不足では
    // ない)。1つの固定値では両立しないため、既定は狭い(=速い)5から
    // 始め、main.rsのメインループが需要駆動の回復・MCTSより先にこの値を
    // 段階的に広げる(FANOUT_HEAT_CAP_CEILING参照)ことで、大半の問題は
    // 5のまま速く解きつつ、cap不足が真因の問題だけ追加コストを払って
    // 解けるようにしている。
    pub fanout_heat_cap: usize,
    pub construction_demands: FxHashMap<(ClassId, ClassId), f64>, // 🌟 Blackboardから移動
    // 🌟 「2直線は既にあるが、その交点がまだ図形として存在しない」ことへの
    // 需要。キーは2直線(ソート済み)。construction_demandsと同じ役割を
    // Intersection(点)に対して果たす。resolve_point_demandsが消費する。
    pub point_construction_demands: FxHashMap<(ClassId, ClassId), f64>,
    // 🌟 UCB1バンディット統計。theorems と同じインデックス(theorem_idx)で
    // 引く。theoremsはProverEngine::new後にmain.rs側で流し込まれるため、
    // ここでは空のまま初期化し、実際に使う直前にensure_theorem_statsで
    // theorems.len()に合わせてリサイズする。
    pub theorem_stats: Vec<TheoremBanditStats>,
    // 🌟 required_hard_typesのドキュメント参照。theoremsと同じインデックス
    // (theorem_idx)で引く。theorem_statsと同じく、theoremsが確定した後に
    // ensure_theorem_required_typesで遅延計算する(theorem.patternsは実行中
    // 不変なので、一度計算すれば使い回せる)。
    pub theorem_required_types: Vec<Vec<crate::mmp_core::EntityType>>,
    // 🌟 ユーザー提案(定理マッチングの最適化・案4): 定理横断の共有部分マッチ
    // キャッシュ、第一弾。match_connected_fact の Connected(child, parent)
    // 両方未束縛分岐は、実は「bindの中身に一切依存せず、(child_type, parent_type)
    // という型の組み合わせだけで結果が決まるジョイン演算」になっている
    // ――どの定理・どのタスクから呼ばれても、同じ型の組み合わせなら
    // 全く同じ (child_rep, parent_rep) のペア集合が返る。RETEのアルファ/
    // ベータメモリと同じ発想で、この結果を定理をまたいで共有キャッシュする。
    // キーは(child_type, parent_type)、値は(結果, キャッシュ時点での
    // child_typeのtype_generation, 同parent_typeのtype_generation)。
    // 案3で導入したEGraph::type_generationが「この型の候補集合・接続関係が
    // 変わったら必ず上がる」という健全な不変条件を満たすようになった
    // (4つのゲートウェイに集約済み)ため、そのままこのキャッシュの
    // 無効化判定に使い回せる。
    pub connected_join_cache: FxHashMap<(crate::mmp_core::EntityType, crate::mmp_core::EntityType), (Rc<Vec<(ClassId, ClassId)>>, u64, u64)>,
    // 🌟 同じ発想の第二弾: match_identical_fact の Identical(v1, v2) 両方
    // 未束縛(自己束縛)分岐も、「期待される型」だけで決まる候補列挙
    // (heatによる並べ替え前の生の候補集合)を、定理をまたいで共有できる。
    // キーはexpected_type、値は(結果, キャッシュ時点でのtype_generation)。
    // heat_bonusはバッチ中にも動的に変わるため、並べ替え・上位40件への
    // 絞り込みは呼び出しのたびに毎回この生のリストに対して行う
    // (キャッシュするのは「型で絞り込んだ後・heat基準で並べ替える前」の
    // 集合だけ)。
    pub identical_self_bind_cache: FxHashMap<crate::mmp_core::EntityType, (Rc<Vec<ClassId>>, u64)>,
    // 🌟 identical_self_bind_cacheをEntityType::Scalarについてだけ、
    // さらに「角度(AnglePair)由来かどうか」で2分割した専用キャッシュ。
    // EGraph::angle_generation/plain_scalar_generationのドキュメント
    // (mmp_core/mod.rs)参照。EntityType::Angle撤廃により長さ・積・複比・
    // 角度が全てEntityType::Scalarを共有するようになった結果、
    // identical_self_bind_cache(Scalar)はこれらどれか1つが新規生成
    // されるだけで無効化されてしまい、角度連鎖定理の自己束縛が
    // (逆に非角度の自己束縛も)キャッシュヒットしなくなっていた
    // (実測でベンチマーク合格率が69/96→57/96に悪化する回帰として
    // 顕在化した)。type_generation[Scalar]ではなくangle_generation/
    // plain_scalar_generationという、それぞれ角度側・非角度側の変化にしか
    // 反応しない専用カウンタで無効化判定することで、無関係な側の
    // 生成イベントに引きずられて再計算されるのを防ぐ。
    pub identical_self_bind_angle_cache: Option<(Rc<Vec<ClassId>>, u64)>,
    pub identical_self_bind_plain_scalar_cache: Option<(Rc<Vec<ClassId>>, u64)>,
    // 🌟 同じ発想の第三弾: defined_by_valid_nodes の「両方未束縛」分岐
    // (親変数もresult_varも未束縛で、期待される結果の型だけで全代表元を
    // 列挙するフォールバック)も、identical_self_bind_cacheと全く同じ形の
    // 「型→代表元集合」の問い合わせで、bindの中身にもtarget_typeにも依存
    // しない(target_typeはこの後defined_by_collect_matchesが実際の
    // Definitionで絞り込むための情報で、valid_nodesの列挙自体には使われて
    // いない)。よってキーはexpected_r_type(EntityType)のみでよく、
    // identical_self_bind_cacheと同じtype_generation方式でそのまま
    // 定理をまたいで共有できる。ただしidentical_self_bind_cacheは
    // base_importance>0.0のフィルタをかけているのに対し、この分岐は
    // フィルタなしで全代表元を返す(既存の挙動を変えないための別キャッシュ)。
    pub defined_by_full_scan_cache: FxHashMap<crate::mmp_core::EntityType, (Rc<Vec<ClassId>>, u64)>,
    // 🌟 ユーザー提案(「探索木のメモ化」の続き、docs/atlas.html §04-#3
    // 参照)への対応: 以前はMatchTask::cached_failed_pathsという
    // タスク単位の寿命でfailed_pathsを持ち越していたため、UCB1が同じ
    // 定理をschedule_full_sweepのたびに新しいtask/新しいbindで何度も
    // 試す(診断計測で判明した「dfs_matchの再訪問の38%がタスクをまたぐ」
    // 主因)ケースを一切捕捉できなかった。state_sig(dfs_match参照)は
    // 元々「このタスクのbind内容+flip状態」だけで決まる内容ベースの
    // ハッシュで、特定のMatchTaskインスタンスとは無関係だったため、
    // これをtheorem_idxごとの永続マップに昇格させるだけで、同じ定理への
    // 異なるタスクからの再訪問もそのまま共有キャッシュとして機能する。
    // 無効化はもうタスク単位の一括判定ではなく、エントリ自身が持つ
    // (mask, 挿入時の型generationスナップショット)を参照時に個別検証する
    // 方式(u8依存マスクの細分化と同じ発想をタスクをまたいで適用しただけ)。
    // 値の(u8, [u64;4])は(依存マスク, その時点でのALL_ENTITY_TYPES順の
    // type_generationスナップショット)――マスクが立っている型だけを
    // 比較すればよい。
    pub global_failed_paths: Vec<rustc_hash::FxHashMap<u64, (u8, [u64; 4])>>,
    // 🌟 ユーザー提案(「schedule_full_sweepの改善を続ける」)への対応: 2度の
    // 撤回(DefinedBy遅延構築・スケジューラ精密化)がいずれも「schedule_
    // full_sweepが重いはず」という推測から出発し、実測せずに手を入れて
    // 原因を特定できないまま終わった反省を踏まえ、まず実測用のカウンタを
    // 用意する。main.rsのメインループが各フェーズ(dfs_match本体・回復
    // フェーズ・MCTS)の実行時間を計測してここに積み上げ、--profileで
    // 終了時に集計を表示する(ProfileStatsのドキュメント参照)。
    pub profile: ProfileStats,
    /// 🌟 いま伸ばそうとしている枝が、どの種類のパターンから出たか。
    /// dfs_match の呼び出しには必ず1つの親の枝があるので、呼ぶ直前に
    /// ここへ種類を控えておき、dfs_match の入口で数える。これで二重計上
    /// なしに「どの結合が探索を吐いているか」が分かる ― 部分マッチ共有を
    /// どこに作るべきかを、当て推量ではなく実測で決めるための計測。
    pub branch_tag: u8,
    // 🌟 --trace 診断の発火ログ(trace.rs 参照)。None が既定で、
    // その場合は apply_conclusions が発火を一切記録しないので
    // 診断を使わない実行にはコストが無い。
    pub trace: Option<crate::trace::TraceLog>,
}

/// 🌟 ProverEngine::profileのドキュメント参照。schedule_full_sweep自体の
/// 呼び出し回数・所要時間・生成したシードなしタスク数、および
/// メインループの3大フェーズ(dfs_match本体/回復フェーズ/MCTS)の
/// 所要時間を集計する、実行時プロファイリング専用の構造体。
/// 証明の正しさには一切影響しない、純粋な計測用の副産物。
#[derive(Debug, Clone, Copy, Default)]
pub struct ProfileStats {
    pub sfs_calls: u64,
    pub sfs_time: std::time::Duration,
    pub sfs_tasks_created: u64,
    pub run_step_time: std::time::Duration,
    pub recovery_time: std::time::Duration,
    pub mcts_time: std::time::Duration,
    // 🌟 --statsの定理別UCB1統計はis_seeded=falseのタスクしか数えていない
    // (MatchTask::is_seededのドキュメント参照)。schedule_matcher_task由来の
    // シード済みタスクは新事実が証明されるたびに(理論上は該当する全定理×
    // 全パターン×全順列の分だけ)大量に生成され得るため、実際の総dfs_call数の
    // 内訳がシード済み側に偏っている可能性がある。ここでシード済み/シード
    // なし双方のタスクポップ数とdfs_call消費量を種別ごとに集計し、
    // 「少数の高コストな試行」なのか「大量の小さな試行の積み重ね」なのかを
    // 実測で切り分けられるようにする。
    pub seeded_pops: u64,
    pub seeded_dfs_calls: u64,
    pub unseeded_pops: u64,
    pub unseeded_dfs_calls: u64,
    /// 🌟 ProverEngine::branch_tag のドキュメント参照。種類ごとの枝の本数。
    pub branch_counts: [u64; 12],
}

impl ProverEngine {
    /// 🌟 これまでに消費した「仕事量」= dfs_match の呼び出し回数の累計。
    ///
    /// 探索の予算を壁時計の秒数で測ると、同じコード・同じ問題でも machine の
    /// 混み具合で結果が変わってしまう(実測で、同一バイナリの32問ベンチが
    /// 空いているときは 29/32・81秒、混んでいるときは 24/32・200秒になった)。
    /// 予算をこの数で測れば、何度流しても、どの machine で流しても同じ結果に
    /// なる。dfs_match は --profile の内訳でも実行時間の大半を占めるので、
    /// 実際の計算量のよい代理になる。
    pub fn work_done(&self) -> u64 {
        self.profile.seeded_dfs_calls + self.profile.unseeded_dfs_calls
    }

    pub fn new(egraph: EGraph) -> Self {
        Self {
            egraph,
            facts: Vec::new(),
            theorems: Vec::new(),
            dfs_calls: 0,
            dfs_cap: 100_000,
            heat_cap: 40,
            fanout_heat_cap: 5,
            construction_demands: FxHashMap::default(), // 🌟 追加
            point_construction_demands: FxHashMap::default(),
            theorem_stats: Vec::new(),
            theorem_required_types: Vec::new(),
            connected_join_cache: FxHashMap::default(),
            identical_self_bind_cache: FxHashMap::default(),
            identical_self_bind_angle_cache: None,
            identical_self_bind_plain_scalar_cache: None,
            defined_by_full_scan_cache: FxHashMap::default(),
            global_failed_paths: Vec::new(),
            profile: ProfileStats::default(),
            branch_tag: 0,
            trace: None,
        }
    }

    /// 🌟 global_failed_pathsのドキュメント参照。theorem_stats/theorem_
    /// required_typesと同じ「theoremsが確定してから初めて呼ばれた時点で
    /// theorems.len()に合わせて遅延リサイズする」パターン。
    pub(crate) fn ensure_global_failed_paths(&mut self) {
        if self.global_failed_paths.len() != self.theorems.len() {
            self.global_failed_paths.resize_with(self.theorems.len(), rustc_hash::FxHashMap::default);
        }
    }

    pub(crate) fn ensure_theorem_stats(&mut self) {
        if self.theorem_stats.len() != self.theorems.len() {
            self.theorem_stats.resize(self.theorems.len(), TheoremBanditStats::default());
        }
    }

    /// 🌟 required_hard_typesのドキュメント参照。theoremsが確定してから最初に
    /// 呼ばれた時点で1回だけ全定理分をまとめて計算し、以降は使い回す。
    pub(crate) fn ensure_theorem_required_types(&mut self) {
        if self.theorem_required_types.len() != self.theorems.len() {
            self.theorem_required_types = self.theorems.iter()
                .map(|t| required_hard_types(t))
                .collect();
        }
    }

    /// 🌟 定理の型シグネチャ事前フィルタ: この定理が前提の中で参照する
    /// 「軟らかくない(オンデマンド生成されない)」型のうち、e-graphに
    /// 実体が1つも無い型が1つでもあれば、この定理は全探索を試すだけ無駄
    /// なので false を返す(呼び出し側はタスクのスケジューリング自体を
    /// スキップする)。
    pub fn theorem_types_available(&mut self, idx: usize) -> bool {
        self.ensure_theorem_required_types();
        match self.theorem_required_types.get(idx) {
            Some(types) => types.iter().all(|&t| self.egraph.has_entity_of_type(t)),
            None => true,
        }
    }

    /// 🌟 UCB1スコアを MatchTask.priority (i32) に足し込める小さな整数
    /// ボーナスに変換する。schedule_matcher_task由来のシード済みタスク
    /// (priority=10)よりは必ず低くなるレンジ(-5..=5)にクランプすることで、
    /// 「発見済みの事実に基づく具体的な一手」を常に最優先しつつ、
    /// 同格のシードなし全探索タスクどうしの中では経験的に見込みの高い
    /// 定理から先に試せるようにする。
    pub fn theorem_priority_bonus(&mut self, idx: usize) -> i32 {
        self.ensure_theorem_stats();
        if idx >= self.theorem_stats.len() { return 0; }
        let total: u64 = self.theorem_stats.iter().map(|s| s.attempts).sum();
        let score = self.theorem_stats[idx].ucb1_score(total, 1.0);
        // 🌟 尺度を 5 倍から 50 倍に広げた。以前は clamp(-5, 5) だったため、
        // ucb1_score が 1.0 を超えるだけで上限に張り付き、ほぼ全ての定理が
        // 優先度 +5 になっていた(--trace で確認: 発火した定理の平均優先度が
        // どれも +5.0 付近)。つまりバンディットの学習結果が並べ替えに
        // 一切反映されていなかった。飽和を解けば実際に順序がつく。
        if !score.is_finite() { return 50; } // 未試行の定理は最優先で一度試す
        ((score * 50.0).round() as i32).clamp(-50, 50)
    }

    /// 🌟 schedule_full_sweep由来のシードなしタスクを実際にdfs_matchまで
    /// 走らせた結果をバンディット統計に反映する。シード済みタスク
    /// (is_seeded=true)はここでは記録しない(MatchTask::is_seededの
    /// ドキュメント参照)。
    ///
    /// コスト考慮型の報酬: dfs_calls_used(このタスク1回のdfs_match呼び出しが
    /// 実際に消費したdfs_call数)をdfs_capに対する比率(cost_ratio)として、
    /// - 成功時: 1.0 - 0.5*cost_ratio を 0.1 を下限にクランプ
    ///   (一瞬で成功すれば報酬1.0に近く、cap一杯まで探索してようやく
    ///   成功しても最低0.1は残る = 成功は常に失敗より高評価だが、
    ///   探索コストが高いほど徐々に割り引かれる)
    /// - 失敗時: -0.5*cost_ratio (0以下)
    ///   (何も見つからずに終わった場合、安く諦めたなら0に近く、
    ///   dfs_cap一杯まで無駄に探索したなら-0.5まで下がる)
    /// この結果、「dfs_cap一杯まで探索した末にようやく1回成功する」定理
    /// (以前の二値報酬では"成功"として高く評価されていた)を、実際の
    /// 探索コストに見合った低めのスコアに補正できる。
    pub fn record_theorem_attempt(&mut self, idx: usize, succeeded: bool, dfs_calls_used: u64) {
        self.ensure_theorem_stats();
        let cost_ratio = (dfs_calls_used as f64 / self.dfs_cap.max(1) as f64).min(1.0);
        let reward = if succeeded {
            (1.0 - 0.5 * cost_ratio).max(0.1)
        } else {
            -0.5 * cost_ratio
        };
        if let Some(stats) = self.theorem_stats.get_mut(idx) {
            stats.attempts += 1;
            stats.total_reward += reward;
            stats.total_dfs_calls += dfs_calls_used;
            if dfs_calls_used >= self.dfs_cap {
                stats.cap_hits += 1;
            }
        }
    }

    pub fn execute_constructions(
        &mut self,
        _theorem_name: &str, // 🌟 命名には親図形の実名を使うので、定理名はもう使わない(呼び出し側との互換のため残置)
        constructions: &[ConstructTemplate],
        bind: &mut Bind,
    ) -> bool {
        for constr in constructions {
            let mut parent_ids = Vec::new();
            for arg in &constr.args {
                if let Some(&id) = bind.get(arg) {
                    parent_ids.push(self.egraph.get_rep(id));
                } else {
                    return false;
                }
            }
            
            let def = match constr.def_type.as_str() {
                "LineThroughPoints" => Definition::new_line(parent_ids[0], parent_ids[1]),
                "DirectionOf" => Definition::DirectionOf(parent_ids[0]),
                "Midpoint" => {
                    let (a, b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::Midpoint(a, b)
                },
                "AnglePair" => Definition::AnglePair(parent_ids[0], parent_ids[1]),
                "Intersection" => {
                    let (l1, l2) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::Intersection(l1, l2)
                },
                "PerpendicularLine" => Definition::PerpendicularLine(parent_ids[0], parent_ids[1]),
                "TangentLine" => Definition::TangentLine(parent_ids[0], parent_ids[1]),
                "Circumcircle" => {
                    let mut arr = [parent_ids[0].0, parent_ids[1].0, parent_ids[2].0];
                    arr.sort_unstable();
                    Definition::Circumcircle(ClassId(arr[0]), ClassId(arr[1]), ClassId(arr[2]))
                },
                // 🌟 mmp_core/mod.rs::Definition::SecondIntersectionOfLineAndConic
                // のドキュメント参照。定理のconstructionsテンプレートから明示的に
                // (known_point, line, conic) → もう一方の交点、を作れるようにする。
                "SecondIntersectionOfLineAndConic" if parent_ids.len() == 3 =>
                    Definition::SecondIntersectionOfLineAndConic(parent_ids[0], parent_ids[1], parent_ids[2]),
                "RadicalAxis" if parent_ids.len() == 2 => Definition::RadicalAxis(parent_ids[0], parent_ids[1]),
                "SecondIntersectionOfCircles" if parent_ids.len() == 3 =>
                    Definition::SecondIntersectionOfCircles(parent_ids[0], parent_ids[1], parent_ids[2]),
                // 🌟 FIX: 不足していた作図定義を追加（これがないと return false で沈黙する）
                "LengthSq" => {
                    let (a, b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::LengthSq(a, b)
                },
                "ParallelLine" => Definition::ParallelLine(parent_ids[0], parent_ids[1]),
                // 🌟 CrossRatioのV4正規化(4元クライン群の畳み込み)は単純なソートより
                // 複雑なので、defined_by_valid_nodesと同じくmod.rs側のnormalize_definition
                // をそのまま呼ぶ(ロジックを1箇所に保つ)。
                "CrossRatio" => self.egraph.normalize_definition(
                    &Definition::CrossRatio(parent_ids[0], parent_ids[1], parent_ids[2], parent_ids[3])
                ),
                // 🌟 CrossRatioOfLines(線束の複比)もCrossRatioと同じV4正規化。
                "CrossRatioOfLines" => self.egraph.normalize_definition(
                    &Definition::CrossRatioOfLines(parent_ids[0], parent_ids[1], parent_ids[2], parent_ids[3])
                ),
                // 🌟 2つのScalarの積(順不同)。方冪の定理(PA・PB=PC・PD)のような
                // 「2辺の積」をconclusionsのIdenticalで比較できるようにする。
                "Product" => self.egraph.normalize_definition(
                    &Definition::Product(parent_ids[0], parent_ids[1])
                ),
                // 🌟 シュタイナーの定理の逆(射影版・円周角の定理の逆)が、
                // 複比が一致した6点のうち5点から二次曲線を構築するために使う。
                // Circumcircleと同じ「完全な順不同」なのでソートするだけ。
                "ConicThrough5Points" => {
                    let mut arr = [parent_ids[0].0, parent_ids[1].0, parent_ids[2].0, parent_ids[3].0, parent_ids[4].0];
                    arr.sort_unstable();
                    Definition::ConicThrough5Points(ClassId(arr[0]), ClassId(arr[1]), ClassId(arr[2]), ClassId(arr[3]), ClassId(arr[4]))
                }
                _ => return false,
            };

            // 🌟 FIX: 既に同じ定義のエンティティがキャッシュ（memo）に存在する場合は、
            // 新規作成せずに既存のIDを再利用して無限ループ・ゴミ生成を防ぐ
            let new_id = if let Some(&existing_id) = self.egraph.memo.get(&def) {
                self.egraph.get_rep(existing_id)
            } else {
                let entity_type = match constr.target_type.as_str() {
                    "Line" => EntityType::Line,
                    "Angle" => EntityType::Scalar,
                    "Circle" => EntityType::Conic,
                    "Scalar" => EntityType::Scalar, // 🌟 スカラー型の追加
                    "Conic" => EntityType::Conic,
                    // 🌟 EntityType::Direction撤廃(方向はL∞に接続された
                    // ただのPoint): "Point"はもちろん、旧"Direction"文字列も
                    // (theorems.rsを全て"Point"に置き換え済みだが)フォール
                    // バックとして自然にここに落ちる。
                    _ => EntityType::Point,
                };
                
                // 🐛 バグ修正: 以前はテンプレートの変数名(bind_to、例: "Ang_MH_CH")と
                // 定理名をそのまま繋げていたため、"Ang_MH_CH_直角三角形の斜辺の中線_(Auto)"
                // のように、実際にどの図形から作られたのか全く追跡できない名前になっていた。
                // match_defined_by の自動生成箇所と同じ規則で、実際に束縛された親図形の
                // 名前をそのまま繋げる(例: "AnglePair_H_C_(Auto)")ようにし、名前から
                // 構成を逆に辿れるようにする。
                let parent_names: Vec<String> = parent_ids.iter()
                    .map(|&id| self.egraph.entities[id.0].name.clone())
                    .collect();
                let prefix = if constr.def_type == "DirectionOf" { "Dir" } else { constr.def_type.as_str() };
                let name = format!("{}_{}_(Auto)", prefix, parent_names.join("_"));

                let prev_origin = self.egraph.set_origin(crate::mmp_core::EntityOrigin::Construct);
                let id = self.egraph.create_entity(name, def.clone(), entity_type);
                self.egraph.apply_trivial_relations(id, &def);
                self.egraph.set_origin(prev_origin);
                id
            };
            
            bind.insert(constr.bind_to.clone(), new_id);
        }
        true
    }

    /// 🌟 証明復元(explain)用: この定理が実際に使った前提事実だけを、
    /// bindを通じて具体的なClassIdに解決して集める。
    /// Python版はbind.values()を丸ごと前提として記録していたため、
    /// マッチの過程でたまたま一緒に束縛されていただけの無関係な図形まで
    /// 証明ツリーに混入していた(ユーザー指摘の「不要な定理が多く含まれる」原因)。
    /// ここではtheorem.patterns中のPattern::Fact節(実際に検証された前提)だけを
    /// 辿るので、そのような無関係な図形は含まれない。
    ///
    /// 🌟 "DefinedBy"前提は、fpd.target_type(例: "AnglePair"/"Midpoint")が
    /// 分かっている場合 "DefinedBy:AnglePair" のようにタグを付けて記録する。
    /// これはraw_proof::RawProofが「このDefinedBy前提はDefinition::AnglePairの
    /// どのインスタンスを指しているか」を、Definition単位の由来インデックスと
    /// 照合してピンポイントに特定するために必要な情報(単なる"DefinedBy"だけ
    /// では、AnglePair/Midpoint/LineThroughPointsなど複数の定義種別を
    /// 区別できない)。表示用のformat_justificationや他の消費側は文字列を
    /// そのまま前方一致/分割で扱うので、この変更で壊れることはない。
    pub(crate) fn compute_theorem_premises(theorem: &TheoremDef, bind: &Bind) -> Vec<(String, Vec<ClassId>)> {
        let mut premises = Vec::new();
        for pat in &theorem.patterns {
            if let Pattern::Fact(fpd) = pat {
                let resolved: Option<Vec<ClassId>> = fpd.args.iter().map(|a| bind.get(a).copied()).collect();
                if let Some(args) = resolved {
                    let fact_type = if fpd.fact_type == "DefinedBy" {
                        match &fpd.target_type {
                            Some(tt) => format!("DefinedBy:{}", tt),
                            None => fpd.fact_type.clone(),
                        }
                    } else {
                        fpd.fact_type.clone()
                    };
                    premises.push((fact_type, args));
                }
            }
        }
        premises
    }

    pub fn apply_conclusions(&mut self, theorem: &TheoremDef, bind: &Bind, flips: &FlipStates) -> (bool, Vec<Fact>) {
        let mut applied_anything = false;
        let mut new_facts = Vec::new();
        let theorem_name = theorem.name.as_str();
        let premises = Self::compute_theorem_premises(theorem, bind);
        // 🌟 --trace 診断(trace.rs 参照): この発火が実際に作った
        // マージ/接続を控えておく。後で証明を根から辿って得られる
        // 「実際に使われたマージ」の集合と突き合わせるための鍵で、
        // 定理名ではなくマージそのもので紐づけるのが要点。
        let tracing = self.trace.is_some();
        let mut traced_merges: Vec<(usize, usize)> = Vec::new();
        let mut traced_incidences: Vec<(usize, usize)> = Vec::new();

        for conc in &theorem.conclusions {
            match conc.fact_type.as_str() {
                "Identical" => {
                    if let (Some(&id1), Some(&id2)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1])) {

                        let r1 = self.egraph.get_rep(id1);
                        let r2 = self.egraph.get_rep(id2);
                        if r1 == r2 { continue; } // 既にマージ済みならスキップ

                        // 🌟 EntityType::Angle撤廃(is_already_proven側と同じ
                        // 理由。mmp_core/mod.rs::EntityTypeのドキュメント参照)
                        // により、型による絞り込みを外し常にf1==f2を確認する
                        // ようにした。FlipStatesは元々match_defined_by側で
                        // target_type=="AnglePair"の場合だけpopulateされる
                        // 型非依存の仕組みなので、角度以外のIdentical結論では
                        // f1・f2とも常にNone(→false)になり判定は変わらない。
                        let f1 = flips.get(&conc.args[0]).copied().unwrap_or(false);
                        let f2 = flips.get(&conc.args[1]).copied().unwrap_or(false);
                        if f1 != f2 { continue; } // 向きが違うならマージしない

                        let name1 = self.egraph.entities[r1.0].name.clone();
                        let name2 = self.egraph.entities[r2.0].name.clone();
                        let justification = crate::mmp_core::Justification::Theorem {
                            name: theorem_name.to_string(),
                            premises: premises.clone(),
                        };
                        if self.egraph.merge_entities_justified(r1, r2, justification) {
                            if tracing {
                                traced_merges.push(if r1.0 <= r2.0 { (r1.0, r2.0) } else { (r2.0, r1.0) });
                            }
                            println!("  🟢 [マージ実行] {} ≡ {} (理由: {})", name1, name2, theorem_name);
                            // 🌟 マージされた代表元の熱を上げて今後のDFSで優先させる[cite: 5]
                            // (EGraph::bump_heat_bonus経由: degeneration_groupsが計算済みなら
                            // 同じ退化グループの他のメンバーにも小さいボーナスを伝播する)
                            self.egraph.bump_heat_bonus(r1, 1.5);
                            applied_anything = true;
                        }
                    }
                }
                // 🌟 FIX: Connected によるE-Graphの物理リンク構築を追加
                // (Concyclic/Collinearを専用Factとして結論に持つのはやめ、
                // 「N点が同じ円/直線にConnectedである」という形に統一した)
                "Connected" => {
                    if let (Some(&child), Some(&parent)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1])) {
                        let c_rep = self.egraph.get_rep(child);
                        let p_rep = self.egraph.get_rep(parent);
                        let justification = crate::mmp_core::Justification::Theorem {
                            name: theorem_name.to_string(),
                            premises: premises.clone(),
                        };
                        self.egraph.link_logical_incidence_justified(c_rep, p_rep, justification);
                        if tracing {
                            traced_incidences.push(if c_rep.0 <= p_rep.0 { (c_rep.0, p_rep.0) } else { (p_rep.0, c_rep.0) });
                        }
                        applied_anything = true;
                        println!("  🟢 [リンク構築] {} ∈ {} (理由: {})",
                            self.egraph.entities[c_rep.0].name, self.egraph.entities[p_rep.0].name, theorem_name);

                        // 🐛 FIX: 以前はここでe-graphへの物理リンクを張るだけで、
                        // Fact::Connected を一切生成・記録していなかった。そのため
                        // schedule_matcher_task によるシード付き再マッチングが
                        // 一度も起きず、この新しい接続に依存する他の定理(円周角の定理など)
                        // が「シードなしの全探索(schedule_full_sweep)頼み」になって
                        // 見逃されることがあった(miquelで実際に退行した)。
                        // Identical/他のFactと同様にFactとして記録し、FactProvenイベント
                        // 経由でシード付き再マッチングが起きるようにする。
                        let fact = Fact::Connected(c_rep, p_rep);
                        if !self.facts.contains(&fact) {
                            self.facts.push(fact.clone());
                            new_facts.push(fact);
                        }
                    }
                },
                _ => {}
            }
        }
        if tracing {
            let work_at = self.work_done();
            let used = self.dfs_calls;
            if let Some(t) = self.trace.as_mut() {
                t.record(theorem_name, work_at, used, traced_merges, traced_incidences);
            }
        }
        (applied_anything, new_facts)
    }
}

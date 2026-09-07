use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};
use crate::action_space::{Action, ActionGenerator};

/// 🌟 MCTS本体。
///
/// 設計方針: このプロジェクトは(定理探索エンジン自体は)一貫して座標計算・
/// 代数計算を避け、構造(接続関係・次数)だけで証明を進める方針を取っている。
/// MCTSの行動評価もこれに合わせ、数値サンプリングによる次数推定などは
/// 一切使わず、以下だけを報酬源にする:
///   1. 合同閉包(apply_congruence_closure)によって実際に同値類が
///      いくつ減ったか(=新しい事実がいくつ従ったか)
///   2. 構成された図形自体の構造的な「面白さ」(既存のcalc_bind_heatと
///      同じ重要度指標 + 中点/垂線/外接円/調和共役点などの作図種ボーナス +
///      3点以上が乗る直線・円のような強い拘束へのボーナス)
///   3. 証明目標(target_fact)の図形への構造的な近さ(直接接続しているか)
///
/// クローンコスト: 1シミュレーションにつきe-graphを1回cloneする(旧実装から
/// 変わっていない)。全体を通してMCTSは「DFSマッチャーが完全に手詰まりに
/// なった時の最後の手段」としてのみ低頻度で呼ばれるため許容しているが、
/// 将来的にclone不要な取り消し(undo)機構に置き換える余地はある。
#[derive(Debug, Clone)]
pub struct MCTSNode {
    pub action: Option<Action>,
    pub parent: Option<usize>,
    pub children: Vec<usize>,
    pub visits: u32,
    pub total_score: f64,
    pub untried_actions: Vec<Action>,
    // 🌟 Progressive widening: get_possible_actionsが一度に生成した候補の
    // うち、まだ「解禁」していない残りをここに退避しておく
    // (MCTSSearchEngine::maybe_widen参照)。
    pub reserved_actions: Vec<Action>,
    pub depth: usize,
}

impl MCTSNode {
    pub fn ucb1(&self, parent_visits: u32, c: f64) -> f64 {
        if self.visits == 0 { return f64::INFINITY; }
        (self.total_score / self.visits as f64) + c * ((parent_visits as f64).ln() / self.visits as f64).sqrt()
    }
}

pub struct MCTSSearchEngine {
    pub nodes: Vec<MCTSNode>,
    pub action_gen: ActionGenerator,
    // 🌟 目標指向ヒューリスティック(action_space.rsのtarget_weight_bonus)の
    // 効果測定用A/Bスイッチ。falseにすると、get_possible_actionsに常に
    // targetの代わりにNoneを渡し、導入前(entity_weightのみによる完全に
    // 目標非依存のサンプリング)の挙動に戻す。既定は有効(true)。
    pub target_bias_enabled: bool,
}

const MAX_DEPTH: usize = 3;
const UCB_C: f64 = 1.4;

// 🌟 Progressive widening: 訪問数visitsのノードで「試して良い」候補手の数を
// ceil(WIDEN_C * (visits+1)^WIDEN_ALPHA)に制限する。get_possible_actions
// 自体は変えず(既存のnum_samples 12/30のままフルにサンプリングする)、
// 生成された候補プールのうち実際にuntried_actionsとして解禁する分だけを
// 絞り、残りはMCTSNode::reserved_actionsに退避する。まだ数回しか訪れて
// いないノードでは少数の候補だけを試し、訪問数が増えて「掘る価値がある」と
// わかってから徐々に幅を広げることで、見込みの薄い枝の組み合わせ爆発を
// 抑えつつ、有望な枝には十分な幅を与える。
const WIDEN_C: f64 = 3.0;
const WIDEN_ALPHA: f64 = 0.5;

impl MCTSSearchEngine {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            action_gen: ActionGenerator::new(),
            target_bias_enabled: true,
        }
    }

    /// 🌟 行動が参照するClassIdが、渡されたegraph上でまだ有効(entities.len()
    /// の範囲内)かを確認する。
    ///
    /// 🐛 背景: MCTSの木構造(self.nodes)は複数のシミュレーションをまたいで
    /// 永続する一方、各シミュレーションは`egraph.clone()`した使い捨ての
    /// sim_egraphの上で行動を適用・展開する。ある行動がどのクローン
    /// (どれだけ多くの補助構成が積み重なった状態)から生成されたかによって、
    /// その行動が参照するClassIdの「意味」は変わらなくても、down-stream の
    /// 処理(create_entity/construct_harmonic_conjugateが内部でget_repを
    /// 呼ぶ経路)が極めて稀に(スタックオーバーフローするほど巨大な組み合わせ
    /// 爆発ではなく、通常のストレステストで数十回に1回程度)
    /// `parents[curr]`の範囲外アクセスでpanicするケースが実際に観測された
    /// (根本原因はまだ完全には特定できていないが、この境界で防御することで
    /// 実害であるクラッシュ自体は確実に防げる)。行動を適用する前にここで
    /// 参照先が実在するかを確認し、無効なら(既存のmemo命中や生成失敗と同様)
    /// 静かにNoneを返して「この行動は今は適用できない」として扱う。
    fn action_refs_valid(egraph: &EGraph, action: &Action) -> bool {
        let ids: Vec<ClassId> = match action {
            Action::Construct(def) => def.get_parents(),
            Action::HarmonicConjugate(a, b, c) => vec![*a, *b, *c],
        };
        ids.iter().all(|id| id.0 < egraph.entities.len())
    }

    /// 行動を(クローン後の)e-graphに実際に適用し、生成物のIDを返す。
    fn apply_action(egraph: &mut EGraph, action: &Action) -> Option<ClassId> {
        if !Self::action_refs_valid(egraph, action) { return None; }
        match action {
            Action::Construct(def) => {
                if egraph.memo.contains_key(def) { return None; }
                let entity_type = def.default_entity_type();
                let parent_names: Vec<String> = def.get_parents().iter()
                    .map(|&id| egraph.entities[egraph.get_rep(id).0].name.clone())
                    .collect();
                let name = format!("{}_{}_(MCTS)", def.get_type_name(), parent_names.join("_"));
                let before_len = egraph.entities.len();
                let id = egraph.create_entity(name, def.clone(), entity_type);
                // 🌟 「無意味な中点の入れ子」対策: idがbefore_len以上(=hash consing
                // でヒットせず本当に新規作成された)場合にだけ、MCTS連鎖の深さ
                // (mcts_depth)を親の最大値+1として記録する。問題文で最初から
                // 与えられている点・直線はmcts_depth=0のままなので、そこから
                // 直接作った1段目の補助構成はmcts_depth=1、その産物の上に
                // さらに積んだ2段目は2、…と増えていく。action_space.rs側で
                // この値に上限を設け、MCTSがMCTS自身の産物の上にMCTS産物を
                // 際限なく積み重ねる(例:中点のまた中点のまた中点…)のを防ぐ。
                if id.0 >= before_len {
                    let depth = def.get_parents().iter()
                        .map(|&p| egraph.entities[egraph.get_rep(p).0].mcts_depth)
                        .max().unwrap_or(0) + 1;
                    egraph.entities[id.0].mcts_depth = depth;
                }
                egraph.apply_trivial_relations(id, def);
                Some(id)
            }
            Action::HarmonicConjugate(a, b, c) => {
                Some(egraph.construct_harmonic_conjugate(*a, *b, *c))
            }
        }
    }

    /// 🐛 FIX: apply_actionと同じ理由(action_refs_validのコメント参照)で、
    /// ここも無効なClassId参照に対してpanicせず、それとわかる文字列を返す
    /// ようにした(print_root_rankingは「採用前」に呼ばれるため、
    /// apply_action側のガードだけでは防げない)。
    fn describe_action(egraph: &EGraph, action: &Action) -> String {
        if !Self::action_refs_valid(egraph, action) {
            return "<無効な参照(既に失効した候補)>".to_string();
        }
        let name = |id: ClassId| egraph.entities[egraph.get_rep(id).0].name.clone();
        match action {
            Action::Construct(def) => egraph.format_definition(def),
            Action::HarmonicConjugate(a, b, c) => format!("HarmonicConjugate({}, {}; {})", name(*a), name(*b), name(*c)),
        }
    }

    // 🌟 EGraph::count_active_classes (query.rs) に集約した。予想候補の価値推定
    // (eval.rs::estimate_conjecture_value)でも同じロジックが必要になったため。

    fn allowed_width(visits: u32) -> usize {
        (WIDEN_C * ((visits + 1) as f64).powf(WIDEN_ALPHA)).ceil() as usize
    }

    /// 🌟 get_possible_actionsが生成した候補全量を、初期解禁分(untried_actions)と
    /// 未解禁分(reserved_actions)に分割する。ノード作成直後はvisits=0なので
    /// allowed_width(0)件までを解禁する。
    fn split_for_widening(mut actions: Vec<Action>) -> (Vec<Action>, Vec<Action>) {
        let initial_w = Self::allowed_width(0);
        if actions.len() <= initial_w {
            (actions, Vec::new())
        } else {
            let reserved = actions.split_off(initial_w);
            (actions, reserved)
        }
    }

    /// 🌟 ノードの現在の訪問数に応じて、reserved_actionsからuntried_actionsへ
    /// 候補を解禁する(Progressive widening本体)。選択フェーズでこのノードを
    /// 通過するたびに呼ぶ。
    fn maybe_widen(node: &mut MCTSNode) {
        if node.reserved_actions.is_empty() { return; }
        let target_w = Self::allowed_width(node.visits);
        let exposed = node.children.len() + node.untried_actions.len();
        if target_w > exposed {
            let take = (target_w - exposed).min(node.reserved_actions.len());
            for _ in 0..take {
                if let Some(a) = node.reserved_actions.pop() {
                    node.untried_actions.push(a);
                }
            }
        }
    }

    /// 🌟 構成された図形自体の構造的な「面白さ」。ActionGenerator::entity_weightと
    /// 同じ基礎重要度に加え、作図の種類・次数(共線/共円の強さ)でボーナスを足す。
    /// 旧Python版のScoringPolicy.get_selection_scoreのprop_bonusに相当するが、
    /// 数値的な次数(numerical_degree)は一切使わない構造版。
    fn structural_bonus(egraph: &EGraph, id: ClassId) -> f64 {
        let rep = egraph.get_rep(id);
        let e = &egraph.entities[rep.0];
        let mut bonus = ActionGenerator::entity_weight(e);

        if let Some(comp) = e.components.first() {
            for def in &comp.definitions {
                bonus += match def {
                    Definition::Midpoint(..) | Definition::PerpendicularLine(..) | Definition::ParallelLine(..)
                    | Definition::Circumcircle(..) | Definition::AnglePair(..) | Definition::HarmonicConjugateOf(..) => 3.0,
                    _ => 0.0,
                };
            }

            match e.entity_type {
                EntityType::Line | EntityType::Circle => {
                    let pts_on = comp.subobjects.iter()
                        .filter(|&&s| matches!(egraph.entities[egraph.get_rep(s).0].entity_type, EntityType::Point | EntityType::Direction))
                        .count();
                    if pts_on >= 3 { bonus += (pts_on as f64 - 2.0) * 5.0; }
                }
                EntityType::Point => {
                    let lc = comp.subobjects.iter()
                        .filter(|&&s| matches!(egraph.entities[egraph.get_rep(s).0].entity_type, EntityType::Line | EntityType::Circle))
                        .count();
                    if lc >= 2 { bonus += lc as f64 * 2.0; }
                }
                _ => {}
            }
        }
        bonus
    }

    /// 🌟 証明目標の図形への「引力」。代数を使わず、構造的な直接接続
    /// (is_connected)や完全一致だけを見る。
    fn target_bonus(egraph: &EGraph, id: ClassId, target: &Option<(String, Vec<ClassId>)>) -> f64 {
        let Some((_, targets)) = target else { return 0.0; };
        let rep = egraph.get_rep(id);
        let mut bonus = 0.0;
        for &t in targets {
            let t_rep = egraph.get_rep(t);
            if t_rep == rep { bonus += 50.0; }
            else if egraph.is_connected(rep, t_rep) { bonus += 10.0; }
        }
        bonus
    }

    fn target_reached(egraph: &EGraph, target: &Option<(String, Vec<ClassId>)>) -> bool {
        match target {
            Some((ftype, targets)) if ftype == "Identical" && targets.len() == 2 => {
                egraph.get_rep(targets[0]) == egraph.get_rep(targets[1])
            }
            Some((ftype, targets)) if ftype == "Concyclic" => {
                let reps: Vec<ClassId> = targets.iter().map(|&t| egraph.get_rep(t)).collect();
                egraph.points_share_a_circle(&reps)
            }
            _ => false,
        }
    }

    fn evaluate_step(
        egraph: &mut EGraph,
        new_id: Option<ClassId>,
        target: &Option<(String, Vec<ClassId>)>,
        classes_before: usize,
    ) -> f64 {
        egraph.apply_congruence_closure();

        if Self::target_reached(egraph, target) {
            return 1000.0;
        }

        let classes_after = egraph.count_active_classes();
        let merges = classes_before.saturating_sub(classes_after) as f64;
        let mut score = merges * 8.0;
        if let Some(id) = new_id {
            score += Self::structural_bonus(egraph, id);
            score += Self::target_bonus(egraph, id, target);
        }
        score
    }

    pub fn run_step(
        &mut self,
        egraph: &mut EGraph,
        target: &Option<(String, Vec<ClassId>)>,
        num_simulations: usize,
    ) -> bool {
        // 🌟 A/Bスイッチ: target_bias_enabled=falseなら、行動生成
        // (get_possible_actions)にだけ常にNoneを渡し、action_space.rs側の
        // target_weight_bonusを常に0にする(導入前の完全に目標非依存な
        // サンプリングに戻す)。報酬評価(evaluate_step経由のtarget_reached/
        // target_bonus)は引き続き本物のtargetを使う必要がある
        // (でないと「そもそも目標達成を検知できない」という別の変化まで
        // 混ざってしまい、行動生成だけの効果を測定できなくなる)ので、
        // 元のtargetとは別にgen_targetとして持つ。
        let gen_target: &Option<(String, Vec<ClassId>)> = if self.target_bias_enabled { target } else { &None };
        self.nodes.clear();
        let root_actions = self.action_gen.get_possible_actions(egraph, false, gen_target);
        if root_actions.is_empty() {
            println!("  🤖 [MCTS] 候補となる作図アクションが見つかりませんでした。");
            return false;
        }

        let (root_untried, root_reserved) = Self::split_for_widening(root_actions);
        self.nodes.push(MCTSNode {
            action: None, parent: None, children: Vec::new(),
            visits: 0, total_score: 0.0, untried_actions: root_untried, reserved_actions: root_reserved, depth: 0,
        });

        for sim_idx in 0..num_simulations {
            let mut sim_egraph = egraph.clone();
            let mut path = vec![0usize];
            let mut curr = 0usize;

            // 1. Selection: 展開済み(未試行行動なし)かつ子がある限りUCB1で降りる
            loop {
                // 🌟 Progressive widening: このノードをまた通過したので、
                // 訪問数に応じて候補の解禁幅を見直す。
                Self::maybe_widen(&mut self.nodes[curr]);
                if !(self.nodes[curr].untried_actions.is_empty() && !self.nodes[curr].children.is_empty()) {
                    break;
                }
                let parent_visits = self.nodes[curr].visits;
                curr = *self.nodes[curr].children.iter()
                    .max_by(|&&a, &&b| self.nodes[a].ucb1(parent_visits, UCB_C)
                        .partial_cmp(&self.nodes[b].ucb1(parent_visits, UCB_C)).unwrap())
                    .unwrap();
                path.push(curr);
                if let Some(action) = self.nodes[curr].action.clone() {
                    Self::apply_action(&mut sim_egraph, &action);
                    sim_egraph.apply_congruence_closure();
                }
            }

            // 2. Expansion + 3. Playout(浅いロールアウト) + 4. Backpropagation
            if !self.nodes[curr].untried_actions.is_empty() {
                let idx = (rand::random::<u32>() as usize) % self.nodes[curr].untried_actions.len();
                let action = self.nodes[curr].untried_actions.remove(idx);

                let classes_before = sim_egraph.count_active_classes();
                let new_id = Self::apply_action(&mut sim_egraph, &action);
                let reward = Self::evaluate_step(&mut sim_egraph, new_id, target, classes_before);

                let depth = self.nodes[curr].depth + 1;
                let generated = if depth < MAX_DEPTH && reward < 999.0 {
                    self.action_gen.get_possible_actions(&sim_egraph, true, gen_target)
                } else {
                    vec![]
                };
                let (untried, reserved) = Self::split_for_widening(generated);

                let child = MCTSNode {
                    action: Some(action), parent: Some(curr), children: Vec::new(),
                    visits: 0, total_score: 0.0, untried_actions: untried, reserved_actions: reserved, depth,
                };
                let child_idx = self.nodes.len();
                self.nodes.push(child);
                self.nodes[curr].children.push(child_idx);
                path.push(child_idx);

                // 浅いロールアウト: 残りの深さをランダム行動で軽く進め、遠い手ほど
                // 割り引く(重い数値計算はしない、純粋に構造報酬の和)。
                let mut rollout_reward = 0.0;
                let mut discount = 0.5;
                let mut d = depth;
                let mut found_target = reward >= 999.0;
                while !found_target && d < MAX_DEPTH {
                    let acts = self.action_gen.get_possible_actions(&sim_egraph, true, gen_target);
                    if acts.is_empty() { break; }
                    let pick = (rand::random::<u32>() as usize) % acts.len();
                    let a = acts[pick].clone();
                    let cb = sim_egraph.count_active_classes();
                    let nid = Self::apply_action(&mut sim_egraph, &a);
                    let r = Self::evaluate_step(&mut sim_egraph, nid, target, cb);
                    if r >= 999.0 { found_target = true; }
                    rollout_reward += r * discount;
                    discount *= 0.5;
                    d += 1;
                }

                let total_reward = reward + rollout_reward;
                for &node_idx in &path {
                    self.nodes[node_idx].visits += 1;
                    self.nodes[node_idx].total_score += total_reward;
                }
            } else {
                for &node_idx in &path {
                    self.nodes[node_idx].visits += 1;
                }
            }

            // 🌟 このシミュレーション用の使い捨てsim_egraphは次のループ反復で
            // 破棄される(新しくcloneし直される)ため、その中でlog_conjecture_candidate
            // が検出した予想候補を、破棄される前に現実のegraphへ合流させておく
            // (EGraph::absorb_conjectures_from参照)。これが無いと、MCTSの
            // シミュレーション内で起きた数値的な偶然の一致の情報がほぼ全て
            // 失われ、heat_bonusへのフィードバックが機能しなくなる。
            egraph.absorb_conjectures_from(&sim_egraph);

            // 🌟 直結: 以前はmain.rsのメインループ側だけがprocess_pending_conjectures
            // を呼んでおり、MCTS自身がこのrun_step呼び出しの中で発見した予想は、
            // このrun_stepが終わって呼び出し元に戻り、次のメインループの
            // ティックが回ってくるまでheat_bonusに反映されなかった
            // (=同じrun_step内の残りのシミュレーションには一切効かなかった)。
            // ここで20シミュレーションに1回、EGraph::process_pending_conjectures
            // を直接呼ぶことで、MCTSが自分の手番の中で見つけた「あと数個で
            // マッチングできそうな」予想を、同じ呼び出し内の後続シミュレーション
            // のentity_weight(=get_possible_actions/weighted_pickが読む値)に
            // 即座に反映させる。呼び出し1回あたりの評価件数上限(MAX_PER_CALL=3)
            // はprocess_pending_conjectures側でそのまま維持されるので、頻度を
            // 上げても評価コスト(クローン+合同閉包1回)は「20シミュレーションに
            // つき高々3件」に留まり、組み合わせ爆発は起きない。
            if sim_idx % 20 == 19 {
                egraph.process_pending_conjectures(target);
            }
        }
        // 🌟 num_simulationsが20未満の場合でも最低1回は反映させる。
        egraph.process_pending_conjectures(target);

        self.print_root_ranking(egraph);

        let best_idx = self.nodes[0].children.iter().max_by_key(|&&c| self.nodes[c].visits).copied();
        if let Some(best_idx) = best_idx {
            if let Some(action) = self.nodes[best_idx].action.clone() {
                println!("🤖 [MCTS] 最良の手を採用: {}", Self::describe_action(egraph, &action));
                if let Some(new_id) = Self::apply_action(egraph, &action) {
                    // 🌟 resolve_demands/resolve_angle_demandsのAuto/Demand生成物と
                    // 同様、MCTS発の補助図形は重要度を抑えて以後の探索の主軸が
                    // ブレないようにする。
                    egraph.entities[new_id.0].base_importance = 0.3;
                    egraph.apply_congruence_closure();
                    return true;
                }
            }
        }
        false
    }

    /// 🌟 ユーザー要望: 「完成したら、各項目でヒューリスティックな評価が
    /// どうなっているかを知りたい」に応えるための可視化。ルート直下の
    /// 候補手を訪問数(≒有望さ)順にランキング表示する。
    fn print_root_ranking(&self, egraph: &EGraph) {
        let mut ranked: Vec<&MCTSNode> = self.nodes[0].children.iter().map(|&c| &self.nodes[c]).collect();
        ranked.sort_by(|a, b| {
            b.visits.cmp(&a.visits)
                .then_with(|| b.total_score.partial_cmp(&a.total_score).unwrap_or(std::cmp::Ordering::Equal))
        });
        println!("  🌲 [MCTS] 候補手のヒューリスティック評価 (上位{}件 / 全{}件):",
            ranked.len().min(10), ranked.len());
        for (i, node) in ranked.iter().take(10).enumerate() {
            let avg = if node.visits > 0 { node.total_score / node.visits as f64 } else { 0.0 };
            let desc = node.action.as_ref().map(|a| Self::describe_action(egraph, a)).unwrap_or_default();
            println!("     {}. {:<45} 訪問={:<4} 平均スコア={:.2}", i + 1, desc, node.visits, avg);
        }
    }
}

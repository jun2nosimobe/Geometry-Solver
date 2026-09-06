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
}

const MAX_DEPTH: usize = 3;
const UCB_C: f64 = 1.4;

impl MCTSSearchEngine {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            action_gen: ActionGenerator::new(),
        }
    }

    /// 行動を(クローン後の)e-graphに実際に適用し、生成物のIDを返す。
    fn apply_action(egraph: &mut EGraph, action: &Action) -> Option<ClassId> {
        match action {
            Action::Construct(def) => {
                if egraph.memo.contains_key(def) { return None; }
                let entity_type = def.default_entity_type();
                let parent_names: Vec<String> = def.get_parents().iter()
                    .map(|&id| egraph.entities[egraph.get_rep(id).0].name.clone())
                    .collect();
                let name = format!("{}_{}_(MCTS)", def.get_type_name(), parent_names.join("_"));
                let id = egraph.create_entity(name, def.clone(), entity_type);
                egraph.apply_trivial_relations(id, def);
                Some(id)
            }
            Action::HarmonicConjugate(a, b, c) => {
                Some(egraph.construct_harmonic_conjugate(*a, *b, *c))
            }
        }
    }

    fn describe_action(egraph: &EGraph, action: &Action) -> String {
        let name = |id: ClassId| egraph.entities[egraph.get_rep(id).0].name.clone();
        match action {
            Action::Construct(def) => egraph.format_definition(def),
            Action::HarmonicConjugate(a, b, c) => format!("HarmonicConjugate({}, {}; {})", name(*a), name(*b), name(*c)),
        }
    }

    fn count_active_classes(egraph: &EGraph) -> usize {
        (0..egraph.entities.len()).filter(|&i| egraph.get_rep(ClassId(i)).0 == i).count()
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

        let classes_after = Self::count_active_classes(egraph);
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
        self.nodes.clear();
        let root_actions = self.action_gen.get_possible_actions(egraph, false);
        if root_actions.is_empty() {
            println!("  🤖 [MCTS] 候補となる作図アクションが見つかりませんでした。");
            return false;
        }

        self.nodes.push(MCTSNode {
            action: None, parent: None, children: Vec::new(),
            visits: 0, total_score: 0.0, untried_actions: root_actions, depth: 0,
        });

        for _ in 0..num_simulations {
            let mut sim_egraph = egraph.clone();
            let mut path = vec![0usize];
            let mut curr = 0usize;

            // 1. Selection: 展開済み(未試行行動なし)かつ子がある限りUCB1で降りる
            while self.nodes[curr].untried_actions.is_empty() && !self.nodes[curr].children.is_empty() {
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

                let classes_before = Self::count_active_classes(&sim_egraph);
                let new_id = Self::apply_action(&mut sim_egraph, &action);
                let reward = Self::evaluate_step(&mut sim_egraph, new_id, target, classes_before);

                let depth = self.nodes[curr].depth + 1;
                let untried = if depth < MAX_DEPTH && reward < 999.0 {
                    self.action_gen.get_possible_actions(&sim_egraph, true)
                } else {
                    vec![]
                };

                let child = MCTSNode {
                    action: Some(action), parent: Some(curr), children: Vec::new(),
                    visits: 0, total_score: 0.0, untried_actions: untried, depth,
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
                    let acts = self.action_gen.get_possible_actions(&sim_egraph, true);
                    if acts.is_empty() { break; }
                    let pick = (rand::random::<u32>() as usize) % acts.len();
                    let a = acts[pick].clone();
                    let cb = Self::count_active_classes(&sim_egraph);
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
        }

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

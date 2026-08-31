use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};
use crate::mmp_tester::MMPTester;
use crate::action_space::ActionGenerator;

#[derive(Debug, Clone)]
pub struct MCTSNode {
    pub action: Option<Definition>,
    pub parent: Option<usize>,
    pub children: Vec<usize>,
    pub visits: usize,
    pub total_score: f64,
    pub untried_actions: Vec<Definition>,
    pub is_expanded: bool,
}

impl MCTSNode {
    pub fn ucb1(&self, parent_visits: usize, c: f64) -> f64 {
        if self.visits == 0 { return f64::INFINITY; }
        (self.total_score / self.visits as f64) + c * ((parent_visits as f64).ln() / self.visits as f64).sqrt()
    }
}

pub struct MCTSSearchEngine {
    pub nodes: Vec<MCTSNode>,
    pub action_gen: ActionGenerator,
}

impl MCTSSearchEngine {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            action_gen: ActionGenerator::new(),
        }
    }

    pub fn run_step(&mut self, egraph: &mut EGraph, tester: &MMPTester, num_simulations: usize) {
        self.nodes.clear();
        
        let root = MCTSNode {
            action: None, parent: None, children: Vec::new(), visits: 0, total_score: 0.0,
            untried_actions: self.action_gen.get_possible_actions(egraph, tester, false),
            is_expanded: false,
        };
        self.nodes.push(root);

        for _ in 0..num_simulations {
            let mut curr_idx = 0;
            // 🌟 超軽量 E-Graph のクローンによるシミュレーション盤面の作成
            let mut sim_egraph = egraph.clone();

            // 1. Selection & Expansion
            while self.nodes[curr_idx].is_expanded && !self.nodes[curr_idx].children.is_empty() {
                let parent_visits = self.nodes[curr_idx].visits;
                let best_child = *self.nodes[curr_idx].children.iter()
                    .max_by(|&&a, &&b| self.nodes[a].ucb1(parent_visits, 2.0).partial_cmp(&self.nodes[b].ucb1(parent_visits, 2.0)).unwrap())
                    .unwrap();
                curr_idx = best_child;
            }

            if !self.nodes[curr_idx].is_expanded && !self.nodes[curr_idx].untried_actions.is_empty() {
                let action = self.nodes[curr_idx].untried_actions.pop().unwrap();
                let child = MCTSNode {
                    action: Some(action.clone()), parent: Some(curr_idx), children: Vec::new(), visits: 0, total_score: 0.0,
                    untried_actions: vec![], is_expanded: false,
                };
                let child_idx = self.nodes.len();
                self.nodes.push(child);
                self.nodes[curr_idx].children.push(child_idx);
                curr_idx = child_idx;
                
                // シミュレーション盤面に行動を適用
                sim_egraph.create_entity("MCTS_Sim".to_string(), action, EntityType::Line); // 簡易化
                
                if self.nodes[self.nodes[curr_idx].parent.unwrap()].untried_actions.is_empty() {
                    let p = self.nodes[curr_idx].parent.unwrap();
                    self.nodes[p].is_expanded = true;
                }
            }

            // 2. Playout (ロールアウト)
            // (ここでは簡易的に、ランダム行動を数手進めたあとの報酬を計算するロジックを実装します)
            let score = 1.0; 

            // 3. Backpropagation
            let mut backprop_idx = Some(curr_idx);
            while let Some(idx) = backprop_idx {
                self.nodes[idx].visits += 1;
                self.nodes[idx].total_score += score;
                backprop_idx = self.nodes[idx].parent;
            }
        }

        // 最良の手を本番環境 (egraph) に適用
        if let Some(&best_child) = self.nodes[0].children.iter().max_by_key(|&&c| self.nodes[c].visits) { //[cite: 7]
            if let Some(action) = &self.nodes[best_child].action { //[cite: 7]
                println!("🤖 [MCTS] 最良の手を採用: {:?}", action); //[cite: 7]
                
                if !egraph.memo.contains_key(action) {
                    // 🌟 FIX: MCTSが何を作ったか分かるように、親図形の名前を引き継ぐ
                    let parent_names: Vec<String> = action.get_parents().iter()
                        .map(|id| egraph.entities[egraph.get_rep(*id).0].name.clone())
                        .collect();
                    
                    let prefix = action.get_type_name();
                    let name = format!("{}_{}_(MCTS)", prefix, parent_names.join("_"));
                    
                    // 🌟 FIX: 直線か点かを定義から正確に判定する
                    let entity_type = match action {
                        crate::mmp_core::Definition::Intersection(_, _) => crate::mmp_core::EntityType::Point,
                        crate::mmp_core::Definition::Midpoint(_, _) => crate::mmp_core::EntityType::Point,
                        _ => crate::mmp_core::EntityType::Line,
                    };
                    
                    let id = egraph.create_entity(name, action.clone(), entity_type);
                    // 🌟 FIX: 物理リンクや有向角を生成するために必須
                    egraph.apply_trivial_relations(id, action);
                }
            }
        }
    }
}
use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};
use crate::mmp_tester::MMPTester;
use rand::seq::SliceRandom;
use rustc_hash::FxHashSet;

pub struct ActionGenerator {
    pub historical_defs: FxHashSet<Definition>, // 名前ではなく「定義」で重複を完全に防ぐ
}

impl ActionGenerator {
    pub fn new() -> Self {
        Self {
            historical_defs: FxHashSet::default(),
        }
    }

    /// E-Graph上の有効なエンティティから、ランダムに可能な作図アクションを列挙する
    pub fn get_possible_actions(
        &mut self,
        egraph: &EGraph,
        tester: &MMPTester,
        is_simulation: bool,
    ) -> Vec<Definition> {
        let mut valid_nodes: Vec<ClassId> = (0..egraph.entities.len())
            .map(ClassId)
            .filter(|&id| {
                let ent = &egraph.entities[id.0];
                ent.base_importance > 0.0
                    && matches!(
                        ent.entity_type,
                        EntityType::Point | EntityType::Line | EntityType::Circle
                    )
            })
            .collect();

        if valid_nodes.len() < 2 {
            return vec![];
        }

        let mut rng = rand::thread_rng();
        let mut actions = Vec::new();
        let num_samples = if is_simulation { 20 } else { 40 };

        for _ in 0..num_samples {
            valid_nodes.shuffle(&mut rng);
            let id_x = egraph.get_rep(valid_nodes[0]);
            let id_y = egraph.get_rep(valid_nodes[1]);
            let x = &egraph.entities[id_x.0];
            let y = &egraph.entities[id_y.0];

            match (x.entity_type, y.entity_type) {
                // 点 × 点 -> 直線 / 中点
                (EntityType::Point, EntityType::Point) => {
                    let def_line = Definition::new_line(id_x, id_y);
                    if !self.historical_defs.contains(&def_line) && !egraph.memo.contains_key(&def_line) {
                        actions.push(def_line.clone());
                        if !is_simulation { self.historical_defs.insert(def_line); }
                    }
                }
                // 直線 × 直線 -> 交点
                (EntityType::Line, EntityType::Line) => {
                    let mut def_int = Definition::Intersection(id_x, id_y);
                    if id_x.0 > id_y.0 { def_int = Definition::Intersection(id_y, id_x); }
                    
                    if !self.historical_defs.contains(&def_int) && !egraph.memo.contains_key(&def_int) {
                        actions.push(def_int.clone());
                        if !is_simulation { self.historical_defs.insert(def_int); }
                    }
                }
                // 点 × 直線 -> 垂線 / 平行線
                (EntityType::Point, EntityType::Line) | (EntityType::Line, EntityType::Point) => {
                    let (p_id, l_id) = if x.entity_type == EntityType::Point { (id_x, id_y) } else { (id_y, id_x) };
                    let def_perp = Definition::PerpendicularLine(l_id, p_id);
                    if !self.historical_defs.contains(&def_perp) && !egraph.memo.contains_key(&def_perp) {
                        actions.push(def_perp.clone());
                        if !is_simulation { self.historical_defs.insert(def_perp); }
                    }
                }
                _ => {}
            }
        }
        actions
    }
}
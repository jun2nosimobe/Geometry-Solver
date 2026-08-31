use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: ヴァリニョンの定理 (四角形の中点) ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    let d = egraph.create_entity("D".to_string(), Definition::FreePoint, EntityType::Point);

    let p = egraph.create_entity("P".to_string(), Definition::Midpoint(a, b), EntityType::Point);
    let q = egraph.create_entity("Q".to_string(), Definition::Midpoint(b, c), EntityType::Point);
    let r = egraph.create_entity("R".to_string(), Definition::Midpoint(c, d), EntityType::Point);
    let s = egraph.create_entity("S".to_string(), Definition::Midpoint(d, a), EntityType::Point);

    let l_pq = egraph.create_entity("Line_PQ".to_string(), Definition::new_line(p, q), EntityType::Line);
    let l_sr = egraph.create_entity("Line_SR".to_string(), Definition::new_line(s, r), EntityType::Line);

    let dir_pq = egraph.create_entity("Dir_PQ".to_string(), Definition::DirectionOf(l_pq), EntityType::Direction);
    let dir_sr = egraph.create_entity("Dir_SR".to_string(), Definition::DirectionOf(l_sr), EntityType::Direction);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![dir_pq, dir_sr])),
        initial_facts: vec![],
    }
}
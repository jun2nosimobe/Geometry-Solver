use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 九点円の定理 (部分) ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    
    let line_bc = egraph.create_entity("Line_BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let line_ca = egraph.create_entity("Line_CA".to_string(), Definition::new_line(c, a), EntityType::Line);
    let line_ab = egraph.create_entity("Line_AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    
    let mid_bc = egraph.create_entity("Mid_BC".to_string(), Definition::Midpoint(b, c), EntityType::Point);
    let mid_ca = egraph.create_entity("Mid_CA".to_string(), Definition::Midpoint(c, a), EntityType::Point);
    let mid_ab = egraph.create_entity("Mid_AB".to_string(), Definition::Midpoint(a, b), EntityType::Point);
    
    let perp_a = egraph.create_entity("Perp_A_BC".to_string(), Definition::PerpendicularLine(line_bc, a), EntityType::Line);
    let h_a = egraph.create_entity("H_A".to_string(), Definition::Intersection(line_bc, perp_a), EntityType::Point);
    
    egraph.apply_congruence_closure();
    
    ProblemSetup {
        target_fact: Some(("Concyclic".to_string(), vec![mid_bc, h_a, mid_ca, mid_ab])),
        initial_facts: vec![],
    }
}
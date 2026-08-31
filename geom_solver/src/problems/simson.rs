use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: シムソンの定理 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    
    let line_bc = egraph.create_entity("LineBC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let line_ca = egraph.create_entity("LineCA".to_string(), Definition::new_line(c, a), EntityType::Line);
    let line_ab = egraph.create_entity("LineAB".to_string(), Definition::new_line(a, b), EntityType::Line);
    
    let circ_abc = egraph.create_entity("Circum_ABC".to_string(), Definition::Circumcircle(a, b, c), EntityType::Circle);
    let p = egraph.create_entity("P".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(p, circ_abc);
    
    let perp_d = egraph.create_entity("Perp_P_BC".to_string(), Definition::PerpendicularLine(line_bc, p), EntityType::Line);
    let d = egraph.create_entity("D".to_string(), Definition::Intersection(line_bc, perp_d), EntityType::Point);
    
    let perp_e = egraph.create_entity("Perp_P_CA".to_string(), Definition::PerpendicularLine(line_ca, p), EntityType::Line);
    let e = egraph.create_entity("E".to_string(), Definition::Intersection(line_ca, perp_e), EntityType::Point);
    
    let perp_f = egraph.create_entity("Perp_P_AB".to_string(), Definition::PerpendicularLine(line_ab, p), EntityType::Line);
    let f = egraph.create_entity("F".to_string(), Definition::Intersection(line_ab, perp_f), EntityType::Point);
    
    let line_de = egraph.create_entity("Line_DE".to_string(), Definition::new_line(d, e), EntityType::Line);
    let line_fd = egraph.create_entity("Line_FD".to_string(), Definition::new_line(f, d), EntityType::Line);
    
    let dir_de = egraph.create_entity("Dir_DE".to_string(), Definition::DirectionOf(line_de), EntityType::Direction);
    let dir_fd = egraph.create_entity("Dir_FD".to_string(), Definition::DirectionOf(line_fd), EntityType::Direction);
    
    egraph.apply_congruence_closure();
    
    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![dir_de, dir_fd])),
        initial_facts: vec![],
    }
}
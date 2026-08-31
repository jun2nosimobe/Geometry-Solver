use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 外接円の接線と垂足三角形 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let l_ab = egraph.create_entity("Line_AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let l_bc = egraph.create_entity("Line_BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let l_ca = egraph.create_entity("Line_CA".to_string(), Definition::new_line(c, a), EntityType::Line);

    let circ = egraph.create_entity("Circ_ABC".to_string(), Definition::Circumcircle(a, b, c), EntityType::Circle);
    let tan_a = egraph.create_entity("Tan_A".to_string(), Definition::TangentLine(circ, a), EntityType::Line);

    let perp_b = egraph.create_entity("Perp_B".to_string(), Definition::PerpendicularLine(l_ca, b), EntityType::Line);
    let perp_c = egraph.create_entity("Perp_C".to_string(), Definition::PerpendicularLine(l_ab, c), EntityType::Line);

    let d = egraph.create_entity("D".to_string(), Definition::Intersection(l_ca, perp_b), EntityType::Point);
    let e = egraph.create_entity("E".to_string(), Definition::Intersection(l_ab, perp_c), EntityType::Point);

    let l_de = egraph.create_entity("Line_DE".to_string(), Definition::new_line(d, e), EntityType::Line);

    let dir_tan_a = egraph.create_entity("Dir_Tan_A".to_string(), Definition::DirectionOf(tan_a), EntityType::Direction);
    let dir_de = egraph.create_entity("Dir_DE".to_string(), Definition::DirectionOf(l_de), EntityType::Direction);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![dir_tan_a, dir_de])),
        initial_facts: vec![],
    }
}
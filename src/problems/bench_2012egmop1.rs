use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::geo_helpers::{foot, circumcenter, direction_of, angle_pair};
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2012 EGMO Problem 1 (difficulty 1.3)
/// 三角形ABCの外心をOとする。D,E,Fをそれぞれ「OからBCへの垂線の足」
/// 「DからCOへの垂線の足」「DからBOへの垂線の足」とする。KをAFEの外心とする。
/// このときDK⊥BCであることを示す。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2012 EGMO P1 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let o = circumcenter(egraph, a, b, c, "O");

    let line_bc = egraph.create_entity("Line_BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let d = foot(egraph, o, line_bc, "D");

    let line_co = egraph.create_entity("Line_CO".to_string(), Definition::new_line(c, o), EntityType::Line);
    let e = foot(egraph, d, line_co, "E");

    let line_bo = egraph.create_entity("Line_BO".to_string(), Definition::new_line(b, o), EntityType::Line);
    let f = foot(egraph, d, line_bo, "F");

    let k = circumcenter(egraph, a, f, e, "K");

    let line_dk = egraph.create_entity("Line_DK".to_string(), Definition::new_line(d, k), EntityType::Line);

    let dir_dk = direction_of(egraph, line_dk, "DK");
    let dir_bc = direction_of(egraph, line_bc, "BC");
    let ang = angle_pair(egraph, dir_dk, dir_bc, "DK_BC");

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![ang, egraph.ang90])),
        initial_facts: vec![],
    }
}

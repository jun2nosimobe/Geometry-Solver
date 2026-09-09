use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::geo_helpers::foot;
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2018 Silk Road Problem 1 (difficulty 1.4)
/// 鋭角三角形ABCで、CH⊥AB、HL∥AC、HK∥BCとなる点H,L,Kを取る。
/// 三角形HBLの垂線の足P,Q(H,Bから)と、三角形AKHの垂線の足X,Y(A,Hから)が
/// 一直線上にあることを示す。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2018 Silk Road P1 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let ab = egraph.create_entity("AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let h = foot(egraph, c, ab, "H");

    let ac = egraph.create_entity("AC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let l1 = egraph.create_entity("l1".to_string(), Definition::ParallelLine(ac, h), EntityType::Line);
    let bc = egraph.create_entity("BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let l = egraph.create_entity("L".to_string(), Definition::Intersection(l1, bc), EntityType::Point);

    let l2 = egraph.create_entity("l2".to_string(), Definition::ParallelLine(bc, h), EntityType::Line);
    let k = egraph.create_entity("K".to_string(), Definition::Intersection(l2, ac), EntityType::Point);

    let bl = egraph.create_entity("BL".to_string(), Definition::new_line(b, l), EntityType::Line);
    let p = foot(egraph, h, bl, "P");

    let hl = egraph.create_entity("HL".to_string(), Definition::new_line(h, l), EntityType::Line);
    let q = foot(egraph, b, hl, "Q");

    let hk = egraph.create_entity("HK".to_string(), Definition::new_line(h, k), EntityType::Line);
    let x = foot(egraph, a, hk, "X");

    let ak = egraph.create_entity("AK".to_string(), Definition::new_line(a, k), EntityType::Line);
    let y = foot(egraph, h, ak, "Y");

    let line_pq = egraph.create_entity("Line_PQ".to_string(), Definition::new_line(p, q), EntityType::Line);
    let line_xy = egraph.create_entity("Line_XY".to_string(), Definition::new_line(x, y), EntityType::Line);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![line_pq, line_xy])),
        initial_facts: vec![],
    }
}

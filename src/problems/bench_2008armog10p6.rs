use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::geo_helpers::{circumcenter, foot, direction_of};
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2008 All-Russian MO grade10 P6 (difficulty 2.2)
///
/// 不等辺三角形ABCの高さAA1とCC1がHで交わり、Oは外心、B0はACの中点。
/// 直線BOが辺ACとPで交わり、直線BHとA1C1がQで交わる。
/// このときHB0とPQが平行であることを示す。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2008 ARMO g10 P6 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let line_bc = egraph.create_entity("Line_BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let line_ab = egraph.create_entity("Line_AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let line_ac = egraph.create_entity("Line_AC".to_string(), Definition::new_line(a, c), EntityType::Line);

    let a1 = foot(egraph, a, line_bc, "A1");
    let c1 = foot(egraph, c, line_ab, "C1");

    // H: 高さAA1とCC1の交点(垂線そのものを使う。A1==Aのような退化でも直線が消えない)。
    let alt_a = egraph.create_entity("Alt_A".to_string(), Definition::PerpendicularLine(line_bc, a), EntityType::Line);
    let alt_c = egraph.create_entity("Alt_C".to_string(), Definition::PerpendicularLine(line_ab, c), EntityType::Line);
    let h = egraph.create_entity("H".to_string(), Definition::Intersection(alt_a, alt_c), EntityType::Point);

    let o = circumcenter(egraph, a, b, c, "O");
    let b0 = egraph.create_entity("B0".to_string(), Definition::Midpoint(a, c), EntityType::Point);

    let line_bo = egraph.create_entity("Line_BO".to_string(), Definition::new_line(b, o), EntityType::Line);
    let p = egraph.create_entity("P".to_string(), Definition::Intersection(line_bo, line_ac), EntityType::Point);

    let line_bh = egraph.create_entity("Line_BH".to_string(), Definition::new_line(b, h), EntityType::Line);
    let line_a1c1 = egraph.create_entity("Line_A1C1".to_string(), Definition::new_line(a1, c1), EntityType::Line);
    let q = egraph.create_entity("Q".to_string(), Definition::Intersection(line_bh, line_a1c1), EntityType::Point);

    let line_b0h = egraph.create_entity("Line_B0H".to_string(), Definition::new_line(b0, h), EntityType::Line);
    let line_pq = egraph.create_entity("Line_PQ".to_string(), Definition::new_line(p, q), EntityType::Line);

    egraph.apply_congruence_closure();

    let dir_b0h = direction_of(egraph, line_b0h, "B0H");
    let dir_pq = direction_of(egraph, line_pq, "PQ");

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![dir_b0h, dir_pq])),
        initial_facts: vec![],
    }
}

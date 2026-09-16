use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::geo_helpers::{foot, direction_of, angle_pair};
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2000 USA TST Problem 2 (difficulty 2.3)
///
/// 円に内接する四角形ABCDについて、対角線ACとBDの交点から
/// AB, CDに下ろした垂線の足をE, Fとする。このときEFは
/// ADの中点とBCの中点を通る直線に垂直であることを示す。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2000 USA TST P2 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    let omega = egraph.create_entity("Omega".to_string(), Definition::Circumcircle(a, b, c), EntityType::Conic);
    let d = egraph.create_entity("D".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(d, omega);

    let line_ac = egraph.create_entity("Line_AC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let line_bd = egraph.create_entity("Line_BD".to_string(), Definition::new_line(b, d), EntityType::Line);
    let p = egraph.create_entity("P".to_string(), Definition::Intersection(line_ac, line_bd), EntityType::Point);

    let line_ab = egraph.create_entity("Line_AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let e = foot(egraph, p, line_ab, "E");
    let line_cd = egraph.create_entity("Line_CD".to_string(), Definition::new_line(c, d), EntityType::Line);
    let f = foot(egraph, p, line_cd, "F");

    let m = egraph.create_entity("M".to_string(), Definition::Midpoint(a, d), EntityType::Point);
    let n = egraph.create_entity("N".to_string(), Definition::Midpoint(b, c), EntityType::Point);

    let line_ef = egraph.create_entity("Line_EF".to_string(), Definition::new_line(e, f), EntityType::Line);
    let line_mn = egraph.create_entity("Line_MN".to_string(), Definition::new_line(m, n), EntityType::Line);

    egraph.apply_congruence_closure();

    let dir_ef = direction_of(egraph, line_ef, "EF");
    let dir_mn = direction_of(egraph, line_mn, "MN");
    let ang = angle_pair(egraph, dir_ef, dir_mn, "EF_MN");

    egraph.apply_congruence_closure();

    let ang90 = egraph.ang90;
    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![ang, ang90])),
        initial_facts: vec![],
    }
}

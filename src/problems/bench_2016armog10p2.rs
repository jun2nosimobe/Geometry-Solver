use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::geo_helpers::{circumcenter, direction_of};
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2016 All-Russian MO grade10 P2 (difficulty 2.3)
///
/// 円に内接する四角形ABCDの対角線AC, BDがPで交わる。BC上の点Qは
/// PQ⊥ACを満たす。このとき三角形APDの外心と三角形BQDの外心を結ぶ直線が
/// ADに平行であることを示す。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2016 ARMO g10 P2 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    let omega = egraph.create_entity("Omega".to_string(), Definition::Circumcircle(a, b, c), EntityType::Conic);
    let d = egraph.create_entity("D".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(d, omega);

    let line_ac = egraph.create_entity("Line_AC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let line_bd = egraph.create_entity("Line_BD".to_string(), Definition::new_line(b, d), EntityType::Line);
    let p = egraph.create_entity("P".to_string(), Definition::Intersection(line_ac, line_bd), EntityType::Point);

    let perp_p_ac = egraph.create_entity("Perp_P_AC".to_string(), Definition::PerpendicularLine(line_ac, p), EntityType::Line);
    let line_bc = egraph.create_entity("Line_BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let q = egraph.create_entity("Q".to_string(), Definition::Intersection(line_bc, perp_p_ac), EntityType::Point);

    let oa = circumcenter(egraph, a, p, d, "Oa");
    let ob = circumcenter(egraph, b, q, d, "Ob");

    let line_oaob = egraph.create_entity("Line_OaOb".to_string(), Definition::new_line(oa, ob), EntityType::Line);
    let line_ad = egraph.create_entity("Line_AD".to_string(), Definition::new_line(a, d), EntityType::Line);

    egraph.apply_congruence_closure();

    let dir_oaob = direction_of(egraph, line_oaob, "OaOb");
    let dir_ad = direction_of(egraph, line_ad, "AD");

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![dir_oaob, dir_ad])),
        initial_facts: vec![],
    }
}

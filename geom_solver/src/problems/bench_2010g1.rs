use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::geo_helpers::foot;
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2010 IMO Shortlist G1 (difficulty 1.6)
/// 鋭角三角形ABCの垂線の足をD,E,F(それぞれBC,CA,AB上)とする。直線EFと
/// 外接円の交点の一つをPとし、直線BPとDFの交点をQとする。AP=AQを示す。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2010 IMO Shortlist G1 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let bc = egraph.create_entity("BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let d = foot(egraph, a, bc, "D");
    let ac = egraph.create_entity("AC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let e = foot(egraph, b, ac, "E");
    let ab = egraph.create_entity("AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let f = foot(egraph, c, ab, "F");

    let ef = egraph.create_entity("EF".to_string(), Definition::new_line(e, f), EntityType::Line);
    let circ_abc = egraph.create_entity("Circ_ABC".to_string(), Definition::Circumcircle(a, b, c), EntityType::Circle);
    let p = egraph.create_entity("P".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(p, ef);
    egraph.link_logical_incidence(p, circ_abc);

    let bp = egraph.create_entity("BP".to_string(), Definition::new_line(b, p), EntityType::Line);
    let df = egraph.create_entity("DF".to_string(), Definition::new_line(d, f), EntityType::Line);
    let q = egraph.create_entity("Q".to_string(), Definition::Intersection(bp, df), EntityType::Point);

    let dist_ap = egraph.create_entity("Dist_AP".to_string(), Definition::LengthSq(a, p), EntityType::Scalar);
    let dist_aq = egraph.create_entity("Dist_AQ".to_string(), Definition::LengthSq(a, q), EntityType::Scalar);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![dist_ap, dist_aq])),
        initial_facts: vec![],
    }
}

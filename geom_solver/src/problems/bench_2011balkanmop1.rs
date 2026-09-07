use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::geo_helpers::{foot, direction_of, angle_pair};
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2011 Balkan MO P1 (difficulty 1.7)
/// 円に内接する四角形ABCD(対角線の交点E)。AB,CDの中点をF,Gとし、
/// Gを通りABに平行な直線をlとする。Eからlへおろした垂線の足をH、
/// EからCDへおろした垂線の足をKとする。EFとHKが垂直であることを示す。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2011 Balkan MO P1 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    let circ_abc = egraph.create_entity("Circ_ABC".to_string(), Definition::Circumcircle(a, b, c), EntityType::Circle);
    let d = egraph.create_entity("D".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(d, circ_abc);

    let ac = egraph.create_entity("AC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let bd = egraph.create_entity("BD".to_string(), Definition::new_line(b, d), EntityType::Line);
    let e = egraph.create_entity("E".to_string(), Definition::Intersection(ac, bd), EntityType::Point);

    let f = egraph.create_entity("F".to_string(), Definition::Midpoint(a, b), EntityType::Point);
    let g = egraph.create_entity("G".to_string(), Definition::Midpoint(c, d), EntityType::Point);

    let ab = egraph.create_entity("AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let l = egraph.create_entity("l".to_string(), Definition::ParallelLine(ab, g), EntityType::Line);
    let h = foot(egraph, e, l, "H");

    let cd = egraph.create_entity("CD".to_string(), Definition::new_line(c, d), EntityType::Line);
    let k = foot(egraph, e, cd, "K");

    let ef = egraph.create_entity("EF".to_string(), Definition::new_line(e, f), EntityType::Line);
    let hk = egraph.create_entity("HK".to_string(), Definition::new_line(h, k), EntityType::Line);

    let dir_ef = direction_of(egraph, ef, "EF");
    let dir_hk = direction_of(egraph, hk, "HK");
    let ang = angle_pair(egraph, dir_ef, dir_hk, "EF_HK");

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![ang, egraph.ang90])),
        initial_facts: vec![],
    }
}

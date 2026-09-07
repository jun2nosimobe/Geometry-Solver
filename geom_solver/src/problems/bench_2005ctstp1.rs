use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::geo_helpers::foot;
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2005 China TST P1 (difficulty 1.8)
/// 三角形ABC内部の点Pから3辺BC,CA,ABへの垂線の足をD,E,Fとする。
/// Aから直線BP,CPへの垂線の足をそれぞれM,Nとする。
/// ME,NF,BCが共点であることを示す(T=EM∩BCとして、F,N,Tが一直線上に
/// あることを示す形で表現する)。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2005 China TST P1 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    let p = egraph.create_entity("P".to_string(), Definition::FreePoint, EntityType::Point);

    let bc = egraph.create_entity("BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let d = foot(egraph, p, bc, "D");
    let ac = egraph.create_entity("AC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let e = foot(egraph, p, ac, "E");
    let ab = egraph.create_entity("AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let f = foot(egraph, p, ab, "F");

    let bp = egraph.create_entity("BP".to_string(), Definition::new_line(b, p), EntityType::Line);
    let m = foot(egraph, a, bp, "M");
    let cp = egraph.create_entity("CP".to_string(), Definition::new_line(c, p), EntityType::Line);
    let n = foot(egraph, a, cp, "N");

    let em = egraph.create_entity("EM".to_string(), Definition::new_line(e, m), EntityType::Line);
    let fn_ = egraph.create_entity("FN".to_string(), Definition::new_line(f, n), EntityType::Line);

    let t = egraph.create_entity("T".to_string(), Definition::Intersection(em, bc), EntityType::Point);

    // D自体は本質的にはこの問題の主張には使わないが、原文の作図に忠実に残す
    let _ = d;

    let ft = egraph.create_entity("FT".to_string(), Definition::new_line(f, t), EntityType::Line);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![fn_, ft])),
        initial_facts: vec![],
    }
}

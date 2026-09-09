use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::geo_helpers::{foot, direction_of, angle_pair};
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2011 Armenia MO g10 P6 (difficulty 1.5)
/// 鋭角三角形ABCの垂線BB1,CC1をそれぞれ延長し、その上に∠PAQ=90°となる
/// ようにP,Qを取る(構成上、l=PerpendicularLine(AP,A)上にQを取ることで
/// ∠PAQ=90°は自動的に成立する)。三角形APQの頂点Aからの垂線の足をFと
/// するとき、∠BFC=90°であることを示す。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2011 Armenia MO g10 P6 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let ab = egraph.create_entity("AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let ac = egraph.create_entity("AC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let b1 = foot(egraph, b, ac, "B1");
    let c1 = foot(egraph, c, ab, "C1");

    let bb1 = egraph.create_entity("BB1".to_string(), Definition::new_line(b, b1), EntityType::Line);
    let p = egraph.create_entity("P".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(p, bb1);

    let ap = egraph.create_entity("AP".to_string(), Definition::new_line(a, p), EntityType::Line);
    let l = egraph.create_entity("l".to_string(), Definition::PerpendicularLine(ap, a), EntityType::Line);

    let cc1 = egraph.create_entity("CC1".to_string(), Definition::new_line(c, c1), EntityType::Line);
    let q = egraph.create_entity("Q".to_string(), Definition::Intersection(cc1, l), EntityType::Point);

    let pq = egraph.create_entity("PQ".to_string(), Definition::new_line(p, q), EntityType::Line);
    let f = foot(egraph, a, pq, "F");

    let bf = egraph.create_entity("BF".to_string(), Definition::new_line(b, f), EntityType::Line);
    let fc = egraph.create_entity("FC".to_string(), Definition::new_line(f, c), EntityType::Line);

    let dir_bf = direction_of(egraph, bf, "BF");
    let dir_fc = direction_of(egraph, fc, "FC");
    let ang = angle_pair(egraph, dir_bf, dir_fc, "BFC");

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![ang, egraph.ang90])),
        initial_facts: vec![],
    }
}

use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

/// 🌟 パップスの定理: 2直線上にそれぞれ3点A,B,CとA',B',C'を取る。
/// BC'とB'C、AC'とA'C、AB'とA'Bの交点X,Y,Zは共線。
///
/// 円錐曲線も長さも角度も使わない純粋な接続幾何の主張で、射影幾何の
/// 土台そのもの(パスカルの定理の退化形でもある)。このエンジンの射影側
/// (複比の透視射影不変性とその逆)がどこまで効くかを見るための問題。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: パップスの定理 ===");
    // 1本目の直線と、その上の3点。
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let l1 = egraph.create_entity("L1".to_string(), Definition::new_line(a, b), EntityType::Line);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(c, l1);

    // 2本目の直線と、その上の3点。
    let a2 = egraph.create_entity("Ap".to_string(), Definition::FreePoint, EntityType::Point);
    let b2 = egraph.create_entity("Bp".to_string(), Definition::FreePoint, EntityType::Point);
    let l2 = egraph.create_entity("L2".to_string(), Definition::new_line(a2, b2), EntityType::Line);
    let c2 = egraph.create_entity("Cp".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(c2, l2);

    let cross = |eg: &mut EGraph, p: crate::mmp_core::ClassId, q: crate::mmp_core::ClassId,
                     r: crate::mmp_core::ClassId, s: crate::mmp_core::ClassId, name: &str| {
        let m1 = eg.create_entity(format!("{}_1", name), Definition::new_line(p, q), EntityType::Line);
        let m2 = eg.create_entity(format!("{}_2", name), Definition::new_line(r, s), EntityType::Line);
        eg.create_entity(name.to_string(), Definition::Intersection(m1, m2), EntityType::Point)
    };
    let x = cross(egraph, b, c2, b2, c, "X");
    let y = cross(egraph, a, c2, a2, c, "Y");
    let z = cross(egraph, a, b2, a2, b, "Z");

    let xy = egraph.create_entity("XY".to_string(), Definition::new_line(x, y), EntityType::Line);
    let xz = egraph.create_entity("XZ".to_string(), Definition::new_line(x, z), EntityType::Line);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![xy, xz])),
        initial_facts: vec![],
    }
}

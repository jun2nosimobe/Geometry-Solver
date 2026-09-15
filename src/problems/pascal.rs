use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

/// 🌟 パスカルの定理: 円周上の6点A..Fについて、向かい合う辺
/// (AB,DE)/(BC,EF)/(CD,FA) の交点X,Y,Zは共線。
///
/// シュタイナーの定理(二次曲線上の6点の複比不変性)が既に定理集合にある
/// ので、それを実際に使いこなせるかを測る問題。パップスの円錐曲線版。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: パスカルの定理 (円に内接する六角形) ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    let circ = egraph.create_entity("Circ".to_string(), Definition::Circumcircle(a, b, c), EntityType::Conic);

    let on_circle = |eg: &mut EGraph, name: &str| -> ClassId {
        let p = eg.create_entity(name.to_string(), Definition::FreePoint, EntityType::Point);
        eg.link_logical_incidence(p, circ);
        p
    };
    let d = on_circle(egraph, "D");
    let e = on_circle(egraph, "E");
    let f = on_circle(egraph, "F");

    let cross = |eg: &mut EGraph, p: ClassId, q: ClassId, r: ClassId, s: ClassId, name: &str| {
        let m1 = eg.create_entity(format!("{}_1", name), Definition::new_line(p, q), EntityType::Line);
        let m2 = eg.create_entity(format!("{}_2", name), Definition::new_line(r, s), EntityType::Line);
        eg.create_entity(name.to_string(), Definition::Intersection(m1, m2), EntityType::Point)
    };
    let x = cross(egraph, a, b, d, e, "X");
    let y = cross(egraph, b, c, e, f, "Y");
    let z = cross(egraph, c, d, f, a, "Z");

    let xy = egraph.create_entity("XY".to_string(), Definition::new_line(x, y), EntityType::Line);
    let xz = egraph.create_entity("XZ".to_string(), Definition::new_line(x, z), EntityType::Line);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![xy, xz])),
        initial_facts: vec![],
    }
}

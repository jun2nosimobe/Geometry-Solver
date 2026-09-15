use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

/// 🌟 デザルグの定理: 2つの三角形ABCとA'B'C'が点Oから透視の位置にある
/// (AA',BB',CC'がOで交わる)なら、対応する辺の交点X,Y,Zは共線。
///
/// 「点からの透視 ⟹ 直線からの透視」という射影幾何の骨格。前提の側が
/// 共点性、結論の側が共線性で、エンジンにとっては接続だけで閉じた主張。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: デザルグの定理 ===");
    let o = egraph.create_entity("O".to_string(), Definition::FreePoint, EntityType::Point);

    // Oを通る3本の直線の上に、それぞれ2点ずつ取る。
    let ray = |eg: &mut EGraph, name: &str| -> (ClassId, ClassId) {
        let p = eg.create_entity(format!("{}1", name), Definition::FreePoint, EntityType::Point);
        let line = eg.create_entity(format!("Ray_{}", name), Definition::new_line(o, p), EntityType::Line);
        let q = eg.create_entity(format!("{}2", name), Definition::FreePoint, EntityType::Point);
        eg.link_logical_incidence(q, line);
        (p, q)
    };
    let (a, a2) = ray(egraph, "A");
    let (b, b2) = ray(egraph, "B");
    let (c, c2) = ray(egraph, "C");

    let cross = |eg: &mut EGraph, p: ClassId, q: ClassId, r: ClassId, s: ClassId, name: &str| {
        let m1 = eg.create_entity(format!("{}_1", name), Definition::new_line(p, q), EntityType::Line);
        let m2 = eg.create_entity(format!("{}_2", name), Definition::new_line(r, s), EntityType::Line);
        eg.create_entity(name.to_string(), Definition::Intersection(m1, m2), EntityType::Point)
    };
    let x = cross(egraph, a, b, a2, b2, "X");
    let y = cross(egraph, b, c, b2, c2, "Y");
    let z = cross(egraph, c, a, c2, a2, "Z");

    let xy = egraph.create_entity("XY".to_string(), Definition::new_line(x, y), EntityType::Line);
    let xz = egraph.create_entity("XZ".to_string(), Definition::new_line(x, z), EntityType::Line);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![xy, xz])),
        initial_facts: vec![],
    }
}

use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2015 Asia Pacific MO Problem 1 (difficulty 1.7)
///
/// 三角形ABCの辺BC上に点Dをとる。Dを通る直線が辺ABをX、半直線ACをYで
/// 切る。三角形BXDの外接円が三角形ABCの外接円ωとB以外の点Zで再び交わる。
/// 直線ZD, ZYがωと再び交わる点をV, Wとする。このときAB = VWであることを示す。
///
/// 🌟 方冪の定理を主題とする問題としてHAGeo-409から採った。人間の標準解は
/// Zを中心とするスパイラル相似(= 方冪による ZD·ZV と ZY·ZW の比較)を使う。
/// 2019 ISL G1 が「接線+方冪」なのに対し、こちらは「2円の交点+方冪」なので、
/// SecondIntersectionOfCircles と RadicalAxis の側の経路を踏む。
///
/// 結論の AB = VW は、このエンジンの語彙では長さの二乗の一致として書く
/// (平方根を持たない有限体上で扱うため。geom-solverの計量語彙の方針)。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2015 APMO P1 (方冪) ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let line_ab = egraph.create_entity("Line_AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let line_ac = egraph.create_entity("Line_AC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let line_bc = egraph.create_entity("Line_BC".to_string(), Definition::new_line(b, c), EntityType::Line);

    // D: BC上の自由点。Dを通る直線は「D と AB 上の自由点 X を結ぶ直線」として置く
    // (原題の「Dを通る任意の直線」と同じ自由度: 方向が1自由度ぶん自由)。
    let d = egraph.create_entity("D".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(d, line_bc);
    let x = egraph.create_entity("X".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(x, line_ab);
    let line_xy = egraph.create_entity("Line_XY".to_string(), Definition::new_line(d, x), EntityType::Line);
    let y = egraph.create_entity("Y".to_string(), Definition::Intersection(line_xy, line_ac), EntityType::Point);

    let omega = egraph.create_entity("Omega".to_string(), Definition::Circumcircle(a, b, c), EntityType::Conic);
    let circ_bdx = egraph.create_entity("Circ_BDX".to_string(), Definition::Circumcircle(b, d, x), EntityType::Conic);

    // Z: ωと円BDXのB以外の交点。
    let z = egraph.create_entity("Z".to_string(),
        Definition::SecondIntersectionOfCircles(b, circ_bdx, omega), EntityType::Point);

    // V: 直線ZDとωのZ以外の交点。W: 直線ZYとωのZ以外の交点。
    let line_zd = egraph.create_entity("Line_ZD".to_string(), Definition::new_line(z, d), EntityType::Line);
    let v = egraph.create_entity("V".to_string(),
        Definition::SecondIntersectionOfLineAndConic(z, line_zd, omega), EntityType::Point);
    let line_zy = egraph.create_entity("Line_ZY".to_string(), Definition::new_line(z, y), EntityType::Line);
    let w = egraph.create_entity("W".to_string(),
        Definition::SecondIntersectionOfLineAndConic(z, line_zy, omega), EntityType::Point);

    egraph.apply_congruence_closure();

    let len_ab = egraph.create_entity("Len_AB".to_string(), Definition::LengthSq(a, b), EntityType::Scalar);
    let len_vw = egraph.create_entity("Len_VW".to_string(), Definition::LengthSq(v, w), EntityType::Scalar);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![len_ab, len_vw])),
        initial_facts: vec![],
    }
}

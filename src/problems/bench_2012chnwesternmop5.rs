use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::geo_helpers::{circumcenter, foot};
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2012 China Western MO Problem 5 (difficulty 2.0)
///
/// 鋭角三角形ABCの外心をO、垂心をHとする。AD⊥BC(DはBC上)、EFはAOの
/// 垂直二等分線でEはBC上。このとき三角形ADEの外接円がOHの中点を通ることを示す。
///
/// 円との交点を使わない作図なので、そのまま写し取れる。結論は
/// 「A, D, E, N が共円」(N = OHの中点)。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2012 China Western MO P5 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let o = circumcenter(egraph, a, b, c, "O");

    // 垂心: BCへの垂線(Aから)とACへの垂線(Bから)の交点。
    let line_bc = egraph.create_entity("Line_BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let line_ac = egraph.create_entity("Line_AC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let alt_a = egraph.create_entity("Alt_A".to_string(), Definition::PerpendicularLine(line_bc, a), EntityType::Line);
    let alt_b = egraph.create_entity("Alt_B".to_string(), Definition::PerpendicularLine(line_ac, b), EntityType::Line);
    let h = egraph.create_entity("H".to_string(), Definition::Intersection(alt_a, alt_b), EntityType::Point);

    // D: AからBCへの垂線の足。
    let d = foot(egraph, a, line_bc, "D");

    // AOの垂直二等分線とBCの交点がE。
    let line_ao = egraph.create_entity("Line_AO".to_string(), Definition::new_line(a, o), EntityType::Line);
    let mid_ao = egraph.create_entity("Mid_AO".to_string(), Definition::Midpoint(a, o), EntityType::Point);
    let perp_bis_ao = egraph.create_entity("PerpBis_AO".to_string(),
        Definition::PerpendicularLine(line_ao, mid_ao), EntityType::Line);
    let e = egraph.create_entity("E".to_string(), Definition::Intersection(perp_bis_ao, line_bc), EntityType::Point);

    let n = egraph.create_entity("N".to_string(), Definition::Midpoint(o, h), EntityType::Point);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Concyclic".to_string(), vec![a, d, e, n])),
        initial_facts: vec![],
    }
}

/// 🌟 証明の筋書き(sketch.rs)。F = AOの中点(Mid_AO)、K = AHの中点とする。
/// AEは円ADEの直径(∠ADE = 90°)で、EF ⊥ AO なので F もこの円に乗る。
/// だから「N が円ADF に乗る」を示せばよく、ADFN は AD ∥ FN・DN = AF の
/// 等脚台形になっている(DN は九点円の半径 = R/2、AF = R/2)。
pub const SKETCH: &str = r#"
aux point K mid A H
step parallel Mid_AO N A Foot_D        | 三角形OAHの中点連結: FN ∥ AH(= AD)
step equal_length N K A Mid_AO         | 三角形HAOの中点連結: NK = AO/2 = AF
step equal_length N Foot_D N K         | Nは九点円の中心で、DとKは九点円上
step concyclic A Foot_D Mid_AO N       | AD ∥ FN かつ DN = AF の等脚台形
step concyclic A Foot_D E Mid_AO       | ∠ADE = ∠AFE = 90°(AEが直径)
"#;

use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

/// 🌟 UCB1バンディットの検証用に、既存の nine_point.rs (4点の部分版) を
/// 拡張した「完全版」九点円の定理。3辺の中点・3つの垂足・3つのオイラー点
/// (各頂点と垂心を結ぶ線分の中点)、計9点が全て同一円上にあることを示す
/// (九点円の定理の完全形)。部分版が4点で証明できていたのに対し、
/// こちらは9点全てを対象にすることで定理適用の連鎖が大幅に長くなり、
/// schedule_full_sweep がより多く呼ばれる(=UCB1バンディットが学習する
/// 機会が増える)ことを狙っている。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 九点円の定理 (完全版・9点) ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let line_bc = egraph.create_entity("Line_BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let line_ca = egraph.create_entity("Line_CA".to_string(), Definition::new_line(c, a), EntityType::Line);
    let line_ab = egraph.create_entity("Line_AB".to_string(), Definition::new_line(a, b), EntityType::Line);

    // 3辺の中点
    let mid_bc = egraph.create_entity("Mid_BC".to_string(), Definition::Midpoint(b, c), EntityType::Point);
    let mid_ca = egraph.create_entity("Mid_CA".to_string(), Definition::Midpoint(c, a), EntityType::Point);
    let mid_ab = egraph.create_entity("Mid_AB".to_string(), Definition::Midpoint(a, b), EntityType::Point);

    // 3本の垂線とその足
    let perp_a = egraph.create_entity("Perp_A_BC".to_string(), Definition::PerpendicularLine(line_bc, a), EntityType::Line);
    let perp_b = egraph.create_entity("Perp_B_CA".to_string(), Definition::PerpendicularLine(line_ca, b), EntityType::Line);
    let perp_c = egraph.create_entity("Perp_C_AB".to_string(), Definition::PerpendicularLine(line_ab, c), EntityType::Line);

    let h_a = egraph.create_entity("H_A".to_string(), Definition::Intersection(line_bc, perp_a), EntityType::Point);
    let h_b = egraph.create_entity("H_B".to_string(), Definition::Intersection(line_ca, perp_b), EntityType::Point);
    let h_c = egraph.create_entity("H_C".to_string(), Definition::Intersection(line_ab, perp_c), EntityType::Point);

    // 垂心: 2本の垂線の交点として直接作図する(3本の共点性そのものは
    // ここでは証明しない。orthocenter.rs が扱う別の問題)。
    let ortho = egraph.create_entity("H".to_string(), Definition::Intersection(perp_a, perp_b), EntityType::Point);

    // オイラー点: 各頂点と垂心を結ぶ線分の中点
    let euler_a = egraph.create_entity("E_A".to_string(), Definition::Midpoint(a, ortho), EntityType::Point);
    let euler_b = egraph.create_entity("E_B".to_string(), Definition::Midpoint(b, ortho), EntityType::Point);
    let euler_c = egraph.create_entity("E_C".to_string(), Definition::Midpoint(c, ortho), EntityType::Point);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Concyclic".to_string(), vec![
            mid_bc, mid_ca, mid_ab, h_a, h_b, h_c, euler_a, euler_b, euler_c,
        ])),
        initial_facts: vec![],
    }
}

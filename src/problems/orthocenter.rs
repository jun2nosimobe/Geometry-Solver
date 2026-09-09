use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

// 🌟 垂心の存在 (Existence of the Orthocenter)
// 三角形ABCの3本の垂線(頂点から対辺への垂線)は1点で交わる、という古典的な補題。
// AoPSなどでも最初期に出てくる易しい定理で、PerpendicularLine/Intersection/Identical
// という既存の語彙だけで表現できるため、複雑な問題(シムソン等)とは別に
// エンジンの基礎的な安定性を測るベンチマークとして追加する。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 垂心の存在 (三角形の3本の垂線は1点で交わる) ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let l_bc = egraph.create_entity("Line_BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let l_ca = egraph.create_entity("Line_CA".to_string(), Definition::new_line(c, a), EntityType::Line);
    let l_ab = egraph.create_entity("Line_AB".to_string(), Definition::new_line(a, b), EntityType::Line);

    // 頂点A, B, Cからそれぞれ対辺へ下ろした垂線
    let alt_a = egraph.create_entity("Alt_A".to_string(), Definition::PerpendicularLine(l_bc, a), EntityType::Line);
    let alt_b = egraph.create_entity("Alt_B".to_string(), Definition::PerpendicularLine(l_ca, b), EntityType::Line);
    let alt_c = egraph.create_entity("Alt_C".to_string(), Definition::PerpendicularLine(l_ab, c), EntityType::Line);

    // 「Alt_AとAlt_Bの交点」と「Alt_BとAlt_Cの交点」が一致する、という形で
    // 3線の共点性(=垂心の存在)を表現する
    let h_ab = egraph.create_entity("H_AltA_AltB".to_string(), Definition::Intersection(alt_a, alt_b), EntityType::Point);
    let h_bc = egraph.create_entity("H_AltB_AltC".to_string(), Definition::Intersection(alt_b, alt_c), EntityType::Point);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![h_ab, h_bc])),
        initial_facts: vec![],
    }
}

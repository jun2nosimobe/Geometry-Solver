use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

// 🌟 垂心の存在(別証明ルート): H = Intersection(Alt_B, Alt_C) として先に
// 垂心の候補点を1つの交点だけで定義し、直線AHを補助線として引いて、
// それが「Aから対辺BCへ下ろした垂線」Alt_Aと一致することを示す。
//
// orthocenter.rs(2本の交点が一致することを示す対称な定式化)と数学的な
// 本質は同じだが、こちらは「AとHを結ぶ」という補助構成(LineThroughPoints)
// を証明の主役として明示的に問題文に組み込む点が異なる。MCTS/ヒューリス
// ティックな探索に頼らず、DFSマッチャー+需要駆動の補助線機構だけで
// 到達できるかどうかを確認するためのベンチマーク。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 垂心の存在 (別証明ルート: AHを補助線として引く) ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let l_bc = egraph.create_entity("Line_BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let l_ca = egraph.create_entity("Line_CA".to_string(), Definition::new_line(c, a), EntityType::Line);
    let l_ab = egraph.create_entity("Line_AB".to_string(), Definition::new_line(a, b), EntityType::Line);

    // BとCから対辺へ下ろした垂線だけを先に引き、その交点をHとする
    let alt_b = egraph.create_entity("Alt_B".to_string(), Definition::PerpendicularLine(l_ca, b), EntityType::Line);
    let alt_c = egraph.create_entity("Alt_C".to_string(), Definition::PerpendicularLine(l_ab, c), EntityType::Line);
    let h = egraph.create_entity("H".to_string(), Definition::Intersection(alt_b, alt_c), EntityType::Point);

    // 🌟 補助点: BとCから対辺へ下ろした垂線の足(垂心三角形の頂点)。
    // ∠BEC=∠BFC=90°(定義から自明)なので、B,C,E,Fが同一円周上にある
    // ことを「円周角の定理の逆」で示せる。これを起点に、有向角の交替律→
    // 同位角による平行判定という既存の定理チェーンでDir_Line_AH ≡ Dir_Alt_A
    // (したがってLine_AH ≡ Alt_A、1点Aと方向を共有)まで辿り着けるはず、
    // というのがこの問題の"別証明ルート"の核心。
    let e = egraph.create_entity("E".to_string(), Definition::Intersection(alt_b, l_ca), EntityType::Point);
    let f = egraph.create_entity("F".to_string(), Definition::Intersection(alt_c, l_ab), EntityType::Point);

    // 補助線: AとHを結ぶ直線
    let line_ah = egraph.create_entity("Line_AH".to_string(), Definition::new_line(a, h), EntityType::Line);

    // Aから対辺BCへ下ろした「正しい」垂線(比較対象)
    let alt_a = egraph.create_entity("Alt_A".to_string(), Definition::PerpendicularLine(l_bc, a), EntityType::Line);

    egraph.apply_congruence_closure();

    ProblemSetup {
        // Line_AH ≡ Alt_A が示せれば、AH ⟂ BC (=Hが3本目の垂線上にもある)が言え、
        // 3本の垂線の共点性が証明されたことになる。
        target_fact: Some(("Identical".to_string(), vec![line_ah, alt_a])),
        initial_facts: vec![],
    }
}

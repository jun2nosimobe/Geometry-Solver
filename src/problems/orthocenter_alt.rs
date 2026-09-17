use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

// 🌟 垂心の存在(別証明ルート): H = Intersection(Alt_B, Alt_C) を垂心の候補として1つの交点だけで定義し、直線AHを
// 補助線として引いて、それが「Aから対辺BCへ下ろした垂線」Alt_Aと一致することを示す。
// orthocenter.rs(2本の交点が一致することを示す対称な定式化)と本質は同じだが、「AとHを結ぶ」補助構成を問題文に
// 組み込む点が異なる。垂線の足E,Fは問題文に書かず、需要駆動の作図(resolve_point_demands)が自動で作ることを確かめる。
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

    // 補助線: AとHを結ぶ直線
    // (BとCから対辺への垂線の足E,Fは、ファイル冒頭のコメントの通り
    // resolve_point_demandsが自動的に発見・作図するため、ここでは
    // 一切宣言しない)
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

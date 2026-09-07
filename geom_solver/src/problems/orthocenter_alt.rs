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
//
// 🌟 履歴: 当初はB,Cから対辺への垂線の足E,Fをこの問題ファイル自身が
// 明示的に作図していた(円周角の定理の逆→有向角の交替律→同位角による
// 平行判定という定理チェーンの起点として必要だったため)。その後
// BlackboardEngine::resolve_point_demands(既存のPerpendicularLineそれぞれに
// ついて、それ自身とその基準線との交点=垂線の足が図形として存在しなければ
// 需要とみなし、DFSがStallした際に能動的に作図する汎用ヒューリスティック)
// を実装したことで、E,Fを問題文に一切書かなくても自動発見・自動作図
// されるようになったため、この2点の手動宣言は削除した(ユーザー要望:
// 補助点なしでこの問題を解けるようにしたい、への対応)。純粋なDFS
// (--mctsなし)のみで2.5秒前後で証明が完了する。
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

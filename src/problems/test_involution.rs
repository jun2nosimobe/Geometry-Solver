use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

// 🌟 「対合定理」(共点4直線+1つの横断線)を2回使う、対合らしい使い方の
// テスト問題。点Oを通る共点4直線を、2本の異なる横断線L1,L2で切ったとき、
// それぞれの交点が作る複比が一致することを示す。
//
// 「複比の透視射影不変性(点→線束)/対合定理」定理を、横断線L1側とL2側の
// それぞれについて1回ずつ(計2回)適用すると、どちらもCrossRatioOfLines
// (line1..line4)という共通のハブに等しいと分かるので、e-graphの推移律
// (合同閉包)だけでCrossRatio(A,B,C,D)とCrossRatio(A2,B2,C2,D2)が
// 自動的に同一視される――これが「対合」の実体で、新しい定理を1つも
// 追加せずに既存の最小構成の定理だけから得られることを確認する。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 対合定理(2本の横断線)テスト ===");
    let o = egraph.create_entity("O".to_string(), Definition::FreePoint, EntityType::Point);
    let x1 = egraph.create_entity("X1".to_string(), Definition::FreePoint, EntityType::Point);
    let x2 = egraph.create_entity("X2".to_string(), Definition::FreePoint, EntityType::Point);
    let x3 = egraph.create_entity("X3".to_string(), Definition::FreePoint, EntityType::Point);
    let x4 = egraph.create_entity("X4".to_string(), Definition::FreePoint, EntityType::Point);

    let line1 = egraph.create_entity("Line_O_X1".to_string(), Definition::new_line(o, x1), EntityType::Line);
    let line2 = egraph.create_entity("Line_O_X2".to_string(), Definition::new_line(o, x2), EntityType::Line);
    let line3 = egraph.create_entity("Line_O_X3".to_string(), Definition::new_line(o, x3), EntityType::Line);
    let line4 = egraph.create_entity("Line_O_X4".to_string(), Definition::new_line(o, x4), EntityType::Line);

    // 1本目の横断線L1(P,Qを通る)
    let p = egraph.create_entity("P".to_string(), Definition::FreePoint, EntityType::Point);
    let q = egraph.create_entity("Q".to_string(), Definition::FreePoint, EntityType::Point);
    let l1 = egraph.create_entity("L1".to_string(), Definition::new_line(p, q), EntityType::Line);

    // 2本目の横断線L2(R,Sを通る、L1とは別の直線)
    let r = egraph.create_entity("R".to_string(), Definition::FreePoint, EntityType::Point);
    let s = egraph.create_entity("S".to_string(), Definition::FreePoint, EntityType::Point);
    let l2 = egraph.create_entity("L2".to_string(), Definition::new_line(r, s), EntityType::Line);

    let a = egraph.create_entity("A".to_string(), Definition::Intersection(line1, l1), EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::Intersection(line2, l1), EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::Intersection(line3, l1), EntityType::Point);
    let d = egraph.create_entity("D".to_string(), Definition::Intersection(line4, l1), EntityType::Point);

    let a2 = egraph.create_entity("A2".to_string(), Definition::Intersection(line1, l2), EntityType::Point);
    let b2 = egraph.create_entity("B2".to_string(), Definition::Intersection(line2, l2), EntityType::Point);
    let c2 = egraph.create_entity("C2".to_string(), Definition::Intersection(line3, l2), EntityType::Point);
    let d2 = egraph.create_entity("D2".to_string(), Definition::Intersection(line4, l2), EntityType::Point);

    egraph.apply_congruence_closure();

    let cr1 = egraph.create_entity("CR_ABCD".to_string(), Definition::CrossRatio(a, b, c, d), EntityType::Scalar);
    let cr2 = egraph.create_entity("CR_A2B2C2D2".to_string(), Definition::CrossRatio(a2, b2, c2, d2), EntityType::Scalar);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![cr1, cr2])),
        initial_facts: vec![],
    }
}

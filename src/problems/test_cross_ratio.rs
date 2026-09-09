use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

// 🌟 Phase 2: 複比の透視射影不変性のテスト問題。
// 点Oから4本の直線(Line_O_X1..X4)を引き、それぞれを2直線L1,L2と交わらせて
// L1上にA,B,C,D、L2上にA',B',C',Dを作る。これは定義によりOを中心とする
// 透視図法の対応点なので、「複比の透視射影不変性」定理1本だけで
// 複比(A,B;C,D)と(A',B';C',D')が等しいことが証明できるはず。
//
// A,A'を結ぶ直線(Line_A_Ap等)は明示的に構成する(需要駆動の補助線機構には
// 頼らず、定理のマッチング自体をピンポイントで検証するため)。A,A'は
// 構成上どちらも既にLine_O_X1上にあるので、合同閉包の「2点共有」局所伝播
// (LineUniqueness)によりLine_A_ApはLine_O_X1へ自動的に統合されるはず。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 複比の透視射影不変性テスト ===");
    let o = egraph.create_entity("O".to_string(), Definition::FreePoint, EntityType::Point);
    let x1 = egraph.create_entity("X1".to_string(), Definition::FreePoint, EntityType::Point);
    let x2 = egraph.create_entity("X2".to_string(), Definition::FreePoint, EntityType::Point);
    let x3 = egraph.create_entity("X3".to_string(), Definition::FreePoint, EntityType::Point);
    let x4 = egraph.create_entity("X4".to_string(), Definition::FreePoint, EntityType::Point);

    let p = egraph.create_entity("P".to_string(), Definition::FreePoint, EntityType::Point);
    let q = egraph.create_entity("Q".to_string(), Definition::FreePoint, EntityType::Point);
    let r = egraph.create_entity("R".to_string(), Definition::FreePoint, EntityType::Point);
    let s = egraph.create_entity("S".to_string(), Definition::FreePoint, EntityType::Point);

    let l1 = egraph.create_entity("L1".to_string(), Definition::new_line(p, q), EntityType::Line);
    let l2 = egraph.create_entity("L2".to_string(), Definition::new_line(r, s), EntityType::Line);

    let line1 = egraph.create_entity("Line_O_X1".to_string(), Definition::new_line(o, x1), EntityType::Line);
    let line2 = egraph.create_entity("Line_O_X2".to_string(), Definition::new_line(o, x2), EntityType::Line);
    let line3 = egraph.create_entity("Line_O_X3".to_string(), Definition::new_line(o, x3), EntityType::Line);
    let line4 = egraph.create_entity("Line_O_X4".to_string(), Definition::new_line(o, x4), EntityType::Line);

    let a = egraph.create_entity("A".to_string(), Definition::Intersection(line1, l1), EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::Intersection(line2, l1), EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::Intersection(line3, l1), EntityType::Point);
    let d = egraph.create_entity("D".to_string(), Definition::Intersection(line4, l1), EntityType::Point);

    let ap = egraph.create_entity("Ap".to_string(), Definition::Intersection(line1, l2), EntityType::Point);
    let bp = egraph.create_entity("Bp".to_string(), Definition::Intersection(line2, l2), EntityType::Point);
    let cp = egraph.create_entity("Cp".to_string(), Definition::Intersection(line3, l2), EntityType::Point);
    let dp = egraph.create_entity("Dp".to_string(), Definition::Intersection(line4, l2), EntityType::Point);

    // 「複比の透視射影不変性」定理のDefinedByパターンが要求する
    // Line_A_Ap等(A,A'を結ぶ直線)を明示的に構成する。
    egraph.create_entity("Line_A_Ap".to_string(), Definition::new_line(a, ap), EntityType::Line);
    egraph.create_entity("Line_B_Bp".to_string(), Definition::new_line(b, bp), EntityType::Line);
    egraph.create_entity("Line_C_Cp".to_string(), Definition::new_line(c, cp), EntityType::Line);
    egraph.create_entity("Line_D_Dp".to_string(), Definition::new_line(d, dp), EntityType::Line);

    egraph.apply_congruence_closure();

    let cr1 = egraph.create_entity("CR_ABCD".to_string(), Definition::CrossRatio(a, b, c, d), EntityType::Scalar);
    let cr2 = egraph.create_entity("CR_ApBpCpDp".to_string(), Definition::CrossRatio(ap, bp, cp, dp), EntityType::Scalar);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![cr1, cr2])),
        initial_facts: vec![],
    }
}

use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

// 🌟 「シュタイナーの定理(接線版)/接弦定理(射影版)」のテスト問題。
// P1..P5の5点で二次曲線Conicを作る(test_steiner.rsと同じ)が、こちらは
// もう1点Qを別途置く代わりに、P1における接線T1をそのまま使う――
// シュタイナーの定理の「Q→P1」極限(P1における接線=P1を通る弦の極限)
// そのものを直接検証する。
// P1から見たP2,P3,P4,T1への直線束の複比と、P5から見たP2,P3,P4,P1への
// 直線束の複比が一致することを「シュタイナーの定理(接線版)」定理1本
// だけで証明できるはず。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: シュタイナーの定理(接線版)テスト ===");
    let p1 = egraph.create_entity("P1".to_string(), Definition::FreePoint, EntityType::Point);
    let p2 = egraph.create_entity("P2".to_string(), Definition::FreePoint, EntityType::Point);
    let p3 = egraph.create_entity("P3".to_string(), Definition::FreePoint, EntityType::Point);
    let p4 = egraph.create_entity("P4".to_string(), Definition::FreePoint, EntityType::Point);
    let p5 = egraph.create_entity("P5".to_string(), Definition::FreePoint, EntityType::Point);

    let conic = egraph.create_entity(
        "Conic".to_string(),
        Definition::ConicThrough5Points(p1, p2, p3, p4, p5),
        EntityType::Conic,
    );

    let t1 = egraph.create_entity("T1".to_string(), Definition::TangentLine(conic, p1), EntityType::Line);

    // P1から見たP2,P3,P4への3直線 + 接線T1
    let l1_p2 = egraph.create_entity("L1_P2".to_string(), Definition::new_line(p1, p2), EntityType::Line);
    let l1_p3 = egraph.create_entity("L1_P3".to_string(), Definition::new_line(p1, p3), EntityType::Line);
    let l1_p4 = egraph.create_entity("L1_P4".to_string(), Definition::new_line(p1, p4), EntityType::Line);

    // P5から見たP2,P3,P4,P1への4直線
    let l5_p2 = egraph.create_entity("L5_P2".to_string(), Definition::new_line(p5, p2), EntityType::Line);
    let l5_p3 = egraph.create_entity("L5_P3".to_string(), Definition::new_line(p5, p3), EntityType::Line);
    let l5_p4 = egraph.create_entity("L5_P4".to_string(), Definition::new_line(p5, p4), EntityType::Line);
    let l5_p1 = egraph.create_entity("L5_P1".to_string(), Definition::new_line(p5, p1), EntityType::Line);

    egraph.apply_congruence_closure();

    let cr_p1 = egraph.create_entity(
        "CR_P1".to_string(),
        Definition::CrossRatioOfLines(l1_p2, l1_p3, l1_p4, t1),
        EntityType::Scalar,
    );
    let cr_p5 = egraph.create_entity(
        "CR_P5".to_string(),
        Definition::CrossRatioOfLines(l5_p2, l5_p3, l5_p4, l5_p1),
        EntityType::Scalar,
    );

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![cr_p1, cr_p5])),
        initial_facts: vec![],
    }
}

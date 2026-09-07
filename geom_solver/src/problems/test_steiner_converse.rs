use crate::mmp_core::{Definition, EGraph, EntityType, Fact};
use crate::problems::ProblemSetup;

// 🌟 「シュタイナーの定理の逆」(射影版・円周角の定理の逆)のテスト問題。
// P1..P5(二次曲線の生成元候補)とQは全て自由な点(座標としてQがP1..P5と
// 共通の二次曲線に乗る保証は無い)だが、「P1から見た複比とP5から見た複比が
// 等しい」という前提だけをinitial_facts経由で直接与える
// (test_isosceles_converse.rsと同じ手法)。この前提だけからQが
// ConicThrough5Points(P1..P5)にConnectedであることが導けるかを検証する。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: シュタイナーの定理の逆テスト ===");
    let p1 = egraph.create_entity("P1".to_string(), Definition::FreePoint, EntityType::Point);
    let p2 = egraph.create_entity("P2".to_string(), Definition::FreePoint, EntityType::Point);
    let p3 = egraph.create_entity("P3".to_string(), Definition::FreePoint, EntityType::Point);
    let p4 = egraph.create_entity("P4".to_string(), Definition::FreePoint, EntityType::Point);
    let p5 = egraph.create_entity("P5".to_string(), Definition::FreePoint, EntityType::Point);
    let q = egraph.create_entity("Q".to_string(), Definition::FreePoint, EntityType::Point);

    let l1_p2 = egraph.create_entity("L1_P2".to_string(), Definition::new_line(p1, p2), EntityType::Line);
    let l1_p3 = egraph.create_entity("L1_P3".to_string(), Definition::new_line(p1, p3), EntityType::Line);
    let l1_p4 = egraph.create_entity("L1_P4".to_string(), Definition::new_line(p1, p4), EntityType::Line);
    let l1_q = egraph.create_entity("L1_Q".to_string(), Definition::new_line(p1, q), EntityType::Line);

    let l5_p2 = egraph.create_entity("L5_P2".to_string(), Definition::new_line(p5, p2), EntityType::Line);
    let l5_p3 = egraph.create_entity("L5_P3".to_string(), Definition::new_line(p5, p3), EntityType::Line);
    let l5_p4 = egraph.create_entity("L5_P4".to_string(), Definition::new_line(p5, p4), EntityType::Line);
    let l5_q = egraph.create_entity("L5_Q".to_string(), Definition::new_line(p5, q), EntityType::Line);

    egraph.apply_congruence_closure();

    let cr_p1 = egraph.create_entity(
        "CR_P1".to_string(),
        Definition::CrossRatioOfLines(l1_p2, l1_p3, l1_p4, l1_q),
        EntityType::Scalar,
    );
    let cr_p5 = egraph.create_entity(
        "CR_P5".to_string(),
        Definition::CrossRatioOfLines(l5_p2, l5_p3, l5_p4, l5_q),
        EntityType::Scalar,
    );

    egraph.apply_congruence_closure();

    let conic = egraph.create_entity(
        "Conic".to_string(),
        Definition::ConicThrough5Points(p1, p2, p3, p4, p5),
        EntityType::Conic,
    );

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Connected".to_string(), vec![q, conic])),
        initial_facts: vec![Fact::new_identical(cr_p1, cr_p5)],
    }
}

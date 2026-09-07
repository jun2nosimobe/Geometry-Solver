use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

// 🌟 シュタイナーの定理(二次曲線上の6点による複比の不変性)のテスト問題。
// P1..P5の5点で二次曲線Conicを作り、Conic上にもう1点Q(座標としての裏付けは
// 無いが「Conic上にある」という前提をlink_logical_incidenceで直接与える。
// sample_point_on_conic経由で数値的にも正しく検証される)を置く。
// P1から見たP2,P3,P4,Qへの直線束の複比と、P5から見た同じ4点への直線束の
// 複比が一致することを「シュタイナーの定理」定理1本だけで証明できるはず。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: シュタイナーの定理テスト ===");
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

    let q = egraph.create_entity("Q".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(q, conic);

    // P1から見たP2,P3,P4,Qへの4直線
    let l1_p2 = egraph.create_entity("L1_P2".to_string(), Definition::new_line(p1, p2), EntityType::Line);
    let l1_p3 = egraph.create_entity("L1_P3".to_string(), Definition::new_line(p1, p3), EntityType::Line);
    let l1_p4 = egraph.create_entity("L1_P4".to_string(), Definition::new_line(p1, p4), EntityType::Line);
    let l1_q = egraph.create_entity("L1_Q".to_string(), Definition::new_line(p1, q), EntityType::Line);

    // P5から見た同じP2,P3,P4,Qへの4直線
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

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![cr_p1, cr_p5])),
        initial_facts: vec![],
    }
}

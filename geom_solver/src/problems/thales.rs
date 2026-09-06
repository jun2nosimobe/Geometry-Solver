use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

// 🌟 タレスの定理 (半円の弧に立つ角は直角)
// 有名な定理の中では垂心よりずっと素直な例題として選んだ。
// A, B を直径の両端、O をその中点(=円の中心)とし、Pを「OP=OA」を満たす点
// (=円周上の点)とする。このとき ∠APB = 90° であることを示す。
//
// 「OP=OA」だけを仮定として与えれば(OB=OAはMidpointの定義から数値的には
// 自明だが、エンジンは自動導出しないので明示する必要はない。この定理の
// 前提として必要なのは Dist(O,A)=Dist(O,P) の一本だけ)、
// 「直角三角形の斜辺の中線の逆」がそのまま∠APBが直角であることを結論する。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: タレスの定理 (半円の弧に立つ角は直角) ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let o = egraph.create_entity("O".to_string(), Definition::Midpoint(a, b), EntityType::Point);
    let p = egraph.create_entity("P".to_string(), Definition::FreePoint, EntityType::Point);

    // 🌟 仮定: Pは中心O、半径OAの円周上にある(OP = OA)
    let dist_oa = egraph.create_entity("Dist_OA".to_string(), Definition::LengthSq(o, a), EntityType::Scalar);
    let dist_op = egraph.create_entity("Dist_OP".to_string(), Definition::LengthSq(o, p), EntityType::Scalar);
    egraph.merge_entities(dist_oa, dist_op);

    let l_pa = egraph.create_entity("L_PA".to_string(), Definition::new_line(p, a), EntityType::Line);
    let l_pb = egraph.create_entity("L_PB".to_string(), Definition::new_line(p, b), EntityType::Line);
    let dir_pa = egraph.create_entity("Dir_PA".to_string(), Definition::DirectionOf(l_pa), EntityType::Direction);
    let dir_pb = egraph.create_entity("Dir_PB".to_string(), Definition::DirectionOf(l_pb), EntityType::Direction);
    let ang_p = egraph.create_entity("Ang_APB".to_string(), Definition::AnglePair(dir_pa, dir_pb), EntityType::Angle);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![ang_p, egraph.ang90])),
        initial_facts: vec![],
    }
}

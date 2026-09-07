use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

// 🌟 方冪の定理(PA・PB=PC・PD)のテスト問題。
// 新しい専用定理は追加せず、既存の「円周角の定理」+新設の「共点二弦の
// 相似(方冪の定理の基礎)」の2つを鎖状に適用するだけで証明できることを
// 検証する(「対合定理」を独自定理として複製せず既存定理の組み合わせで
// 得たのと同じ発想)。
//
// A,B,C,Dを共円にし(cyclic_quad.rsと同じ手法)、弦AB,CDの交点をPとする。
// 円周角の定理が∠DAB=∠DCB(AとCから見た弧DBの円周角)を与え、それを
// 「共点二弦の相似」がPA・PB=PC・PDへと橋渡しする。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 方冪の定理(射影幾何経由)テスト ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    let d = egraph.create_entity("D".to_string(), Definition::FreePoint, EntityType::Point);

    let circ = egraph.create_entity("Circ".to_string(), Definition::Circumcircle(a, b, c), EntityType::Circle);
    egraph.link_logical_incidence(d, circ); // Dも同じ円に乗せる

    let line_ab = egraph.create_entity("LineAB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let line_cd = egraph.create_entity("LineCD".to_string(), Definition::new_line(c, d), EntityType::Line);
    // 円周角の定理(∠DAB=∠DCB)と「共点二弦の相似」の両方が必要とする
    // 4本の直線(AD, AB, CD, CB)を明示的に構成しておく。
    egraph.create_entity("LineAD".to_string(), Definition::new_line(a, d), EntityType::Line);
    egraph.create_entity("LineCB".to_string(), Definition::new_line(c, b), EntityType::Line);

    let p = egraph.create_entity("P".to_string(), Definition::Intersection(line_ab, line_cd), EntityType::Point);

    egraph.apply_congruence_closure();

    let len_pa = egraph.create_entity("Len_PA".to_string(), Definition::LengthSq(p, a), EntityType::Scalar);
    let len_pb = egraph.create_entity("Len_PB".to_string(), Definition::LengthSq(p, b), EntityType::Scalar);
    let len_pc = egraph.create_entity("Len_PC".to_string(), Definition::LengthSq(p, c), EntityType::Scalar);
    let len_pd = egraph.create_entity("Len_PD".to_string(), Definition::LengthSq(p, d), EntityType::Scalar);
    let prod_ab = egraph.create_entity("Prod_PA_PB".to_string(), Definition::Product(len_pa, len_pb), EntityType::Scalar);
    let prod_cd = egraph.create_entity("Prod_PC_PD".to_string(), Definition::Product(len_pc, len_pd), EntityType::Scalar);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![prod_ab, prod_cd])),
        initial_facts: vec![],
    }
}

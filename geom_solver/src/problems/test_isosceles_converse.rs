use crate::mmp_core::{Definition, EGraph, EntityType, Fact};
use crate::problems::ProblemSetup;

// 🌟 「二等辺三角形の底角の逆」(底角が等しい⟹二辺が等しい)のテスト問題。
// A,B,Cは完全に自由な点(座標としてはAB=ACである保証は全く無い)だが、
// 「底角(Ang_B, Ang_C)が等しい」という前提だけをinitial_facts経由で直接
// 与える(test_right_midpoint.rsが「Ang_A=Ang90」を同じ形で与えるのと
// 同じ手法 ―― 実際の座標では一般に成り立たない特別な仮定を、問題の
// 前提として明示的に注入する)。この前提だけからAB²=AC²(Dist_AB=Dist_AC)
// が導けるかどうかを検証する。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 二等辺三角形の底角の逆テスト ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let l_ab = egraph.create_entity("LineAB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let l_ac = egraph.create_entity("LineAC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let l_bc = egraph.create_entity("LineBC".to_string(), Definition::new_line(b, c), EntityType::Line);

    let dir_ab = egraph.create_entity("DirAB".to_string(), Definition::DirectionOf(l_ab), EntityType::Direction);
    let dir_ac = egraph.create_entity("DirAC".to_string(), Definition::DirectionOf(l_ac), EntityType::Direction);
    let dir_bc = egraph.create_entity("DirBC".to_string(), Definition::DirectionOf(l_bc), EntityType::Direction);

    let ang_b = egraph.create_entity("Ang_B".to_string(), Definition::AnglePair(dir_ab, dir_bc), EntityType::Angle);
    let ang_c = egraph.create_entity("Ang_C".to_string(), Definition::AnglePair(dir_bc, dir_ac), EntityType::Angle);

    egraph.apply_congruence_closure();

    let dist_ab = egraph.create_entity("Dist_AB".to_string(), Definition::LengthSq(a, b), EntityType::Scalar);
    let dist_ac = egraph.create_entity("Dist_AC".to_string(), Definition::LengthSq(a, c), EntityType::Scalar);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![dist_ab, dist_ac])),
        initial_facts: vec![Fact::new_identical(ang_b, ang_c)],
    }
}

use crate::mmp_core::{Definition, EGraph, EntityType, Fact};
use crate::problems::ProblemSetup;

pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 同位角による平行判定テスト ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    let d = egraph.create_entity("D".to_string(), Definition::FreePoint, EntityType::Point);
    let e = egraph.create_entity("E".to_string(), Definition::FreePoint, EntityType::Point);
    let f = egraph.create_entity("F".to_string(), Definition::FreePoint, EntityType::Point);

    let l_ab = egraph.create_entity("L_AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let l_cd = egraph.create_entity("L_CD".to_string(), Definition::new_line(c, d), EntityType::Line);
    let l_ef = egraph.create_entity("L_EF".to_string(), Definition::new_line(e, f), EntityType::Line);

    let dir_ab = egraph.create_entity("Dir_AB".to_string(), Definition::DirectionOf(l_ab), EntityType::Point);
    let dir_cd = egraph.create_entity("Dir_CD".to_string(), Definition::DirectionOf(l_cd), EntityType::Point);
    let dir_ef = egraph.create_entity("Dir_EF".to_string(), Definition::DirectionOf(l_ef), EntityType::Point);

    let ang1 = egraph.create_entity("Ang_AB_EF".to_string(), Definition::AnglePair(dir_ab, dir_ef), EntityType::Scalar);
    let ang2 = egraph.create_entity("Ang_CD_EF".to_string(), Definition::AnglePair(dir_cd, dir_ef), EntityType::Scalar);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![dir_ab, dir_cd])), // ABとCDの方向が等しいことを証明
        initial_facts: vec![
            Fact::new_identical(ang1, ang2) // 2つの有向角が等しいことを初期条件として与える
        ],
    }
}
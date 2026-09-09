use crate::mmp_core::{Definition, EGraph, EntityType, Fact};
use crate::problems::ProblemSetup;

pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 直角三角形の斜辺の中線テスト ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let l_ab = egraph.create_entity("L_AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let l_ac = egraph.create_entity("L_AC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let l_bc = egraph.create_entity("L_BC".to_string(), Definition::new_line(b, c), EntityType::Line);

    let dir_ab = egraph.create_entity("Dir_AB".to_string(), Definition::DirectionOf(l_ab), EntityType::Point);
    let dir_ac = egraph.create_entity("Dir_AC".to_string(), Definition::DirectionOf(l_ac), EntityType::Point);
    let dir_bc = egraph.create_entity("Dir_BC".to_string(), Definition::DirectionOf(l_bc), EntityType::Point);

    let ang_a = egraph.create_entity("Ang_A".to_string(), Definition::AnglePair(dir_ab, dir_ac), EntityType::Scalar);
    let m = egraph.create_entity("M".to_string(), Definition::Midpoint(b, c), EntityType::Point);

    let l_am = egraph.create_entity("L_AM".to_string(), Definition::new_line(a, m), EntityType::Line);
    let dir_am = egraph.create_entity("Dir_AM".to_string(), Definition::DirectionOf(l_am), EntityType::Point);

    let ang_mab = egraph.create_entity("Ang_MAB".to_string(), Definition::AnglePair(dir_am, dir_ab), EntityType::Scalar);
    let ang_mba = egraph.create_entity("Ang_MBA".to_string(), Definition::AnglePair(dir_ab, dir_bc), EntityType::Scalar);

    egraph.apply_congruence_closure();

    ProblemSetup {
        // 🌟 中線によって二等辺三角形ができるため、底角が等しくなることをターゲットにする
        target_fact: Some(("Identical".to_string(), vec![ang_mab, ang_mba])),
        initial_facts: vec![
            Fact::new_identical(ang_a, egraph.ang90)
        ],
    }
}
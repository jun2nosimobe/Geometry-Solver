use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

/// 🌟 平行四辺形の対角線は互いに二等分する(--rules=parallelogram の証人)。
/// 三角形 ABC に、C を通り AB に平行な直線と A を通り BC に平行な直線を引いて交点 D をとると ABCD は平行四辺形で、
/// AC の中点と BD の中点は一致する。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 平行四辺形の対角線 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let ab = egraph.create_entity("AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let bc = egraph.create_entity("BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let l_cd = egraph.create_entity("L_CD".to_string(), Definition::ParallelLine(ab, c), EntityType::Line);
    let l_da = egraph.create_entity("L_DA".to_string(), Definition::ParallelLine(bc, a), EntityType::Line);
    let d = egraph.create_entity("D".to_string(), Definition::Intersection(l_cd, l_da), EntityType::Point);

    let m_ac = egraph.create_entity("M_AC".to_string(), Definition::Midpoint(a, c), EntityType::Point);
    let m_bd = egraph.create_entity("M_BD".to_string(), Definition::Midpoint(b, d), EntityType::Point);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![m_ac, m_bd])),
        initial_facts: vec![],
    }
}

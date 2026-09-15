use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

/// 🌟 ニュートン=ガウス線: 完全四辺形の3本の対角線の中点は共線。
///
/// 4点A,B,C,Dから作る4直線AB,BC,CD,DAについて、E=AB∩CD、F=BC∩DAとすると、
/// 対角線AC,BD,EFの中点M1,M2,M3が一直線に並ぶ。
///
/// 中点(アフィン)と交点(射影)が混ざった主張で、中点連結定理まわりと
/// 需要駆動の中点作図(resolve_midpoint_demands)が効くかを見る問題。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: ニュートン=ガウス線 (完全四辺形の対角線の中点) ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    let d = egraph.create_entity("D".to_string(), Definition::FreePoint, EntityType::Point);

    let ab = egraph.create_entity("AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let bc = egraph.create_entity("BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let cd = egraph.create_entity("CD".to_string(), Definition::new_line(c, d), EntityType::Line);
    let da = egraph.create_entity("DA".to_string(), Definition::new_line(d, a), EntityType::Line);

    let e = egraph.create_entity("E".to_string(), Definition::Intersection(ab, cd), EntityType::Point);
    let f = egraph.create_entity("F".to_string(), Definition::Intersection(bc, da), EntityType::Point);

    let m1 = egraph.create_entity("M1".to_string(), Definition::Midpoint(a, c), EntityType::Point);
    let m2 = egraph.create_entity("M2".to_string(), Definition::Midpoint(b, d), EntityType::Point);
    let m3 = egraph.create_entity("M3".to_string(), Definition::Midpoint(e, f), EntityType::Point);

    let l12 = egraph.create_entity("M1M2".to_string(), Definition::new_line(m1, m2), EntityType::Line);
    let l13 = egraph.create_entity("M1M3".to_string(), Definition::new_line(m1, m3), EntityType::Line);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![l12, l13])),
        initial_facts: vec![],
    }
}

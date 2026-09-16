use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::geo_helpers::{circumcenter, foot, direction_of};
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2022 Balkan MO Problem 1 (difficulty 2.0)
///
/// 鋭角三角形ABC(CA≠CB)の外接円をω、外心をOとする。ωのA, Bにおける接線
/// t_A, t_B の交点をXとする。OからCXに下ろした垂線の足をYとする。Cを通り
/// ABに平行な直線がt_AとZで交わる。このときYZがACの中点を通ることを示す。
///
/// 円との交点を一切使わない(接線は「中心と接点を結ぶ直線への垂線」として
/// 書ける)ので、この作図はそのまま写し取れる。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2022 Balkan MO P1 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let o = circumcenter(egraph, a, b, c, "O");

    // ωのA/Bにおける接線 = OA/OBに垂直でA/Bを通る直線。
    let line_oa = egraph.create_entity("Line_OA".to_string(), Definition::new_line(o, a), EntityType::Line);
    let ta = egraph.create_entity("Tan_A".to_string(), Definition::PerpendicularLine(line_oa, a), EntityType::Line);
    let line_ob = egraph.create_entity("Line_OB".to_string(), Definition::new_line(o, b), EntityType::Line);
    let tb = egraph.create_entity("Tan_B".to_string(), Definition::PerpendicularLine(line_ob, b), EntityType::Line);
    let x = egraph.create_entity("X".to_string(), Definition::Intersection(ta, tb), EntityType::Point);

    let line_cx = egraph.create_entity("Line_CX".to_string(), Definition::new_line(c, x), EntityType::Line);
    let y = foot(egraph, o, line_cx, "Y");

    let line_ab = egraph.create_entity("Line_AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let par_c = egraph.create_entity("Par_C_AB".to_string(), Definition::ParallelLine(line_ab, c), EntityType::Line);
    let z = egraph.create_entity("Z".to_string(), Definition::Intersection(par_c, ta), EntityType::Point);

    let m = egraph.create_entity("M".to_string(), Definition::Midpoint(a, c), EntityType::Point);

    let line_yz = egraph.create_entity("Line_YZ".to_string(), Definition::new_line(y, z), EntityType::Line);
    let _ = direction_of(egraph, line_yz, "YZ");

    egraph.apply_congruence_closure();

    // 目標: M が直線YZ 上にある(共線)。
    ProblemSetup {
        target_fact: Some(("Connected".to_string(), vec![m, line_yz])),
        initial_facts: vec![],
    }
}

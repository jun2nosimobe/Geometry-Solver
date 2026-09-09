use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::geo_helpers::{circumcenter, direction_of, angle_pair};
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2012 EGMO Problem 1 (difficulty 1.3)
/// 三角形ABCの外心をOとする。D,E,FをそれぞれBC,CA,AB上の点とし、
/// DE⊥CO、DF⊥BOを満たすとする。KをAFEの外心とする。
/// このときDK⊥BCであることを示す。
///
/// 🐛 FIX: 以前はDを「OからBCへの垂線の足」として定義していたが、これは
/// 原題(https://www.egmo.org/egmos/egmo1/paper-day1-bg-English.pdf)に
/// 無い余計な制約だった。原題ではDはBC上の自由な点であり、E,Fはそこから
/// (DE⊥CO, DF⊥BOという条件で)決まる。Dをfoot(O,line_bc)に固定していた
/// ため、実際には「D=BCの中点」という特殊ケースしか検証していなかった
/// (ユーザー指摘: 中心角の定理を追加した動作検証のため、ここで原題通りに
/// 修正する)。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2012 EGMO P1 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let o = circumcenter(egraph, a, b, c, "O");

    // D: BC上の自由点(Oからの垂線の足という制約は課さない)
    let line_bc = egraph.create_entity("Line_BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let d = egraph.create_entity("D".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(d, line_bc);

    // E: CA上にあり、DE⊥COを満たす点(line_caと「Dを通りCOに垂直な直線」の交点)
    let line_ca = egraph.create_entity("Line_CA".to_string(), Definition::new_line(c, a), EntityType::Line);
    let line_co = egraph.create_entity("Line_CO".to_string(), Definition::new_line(c, o), EntityType::Line);
    let perp_d_co = egraph.create_entity("Perp_D_CO".to_string(), Definition::PerpendicularLine(line_co, d), EntityType::Line);
    let e = egraph.create_entity("E".to_string(), Definition::Intersection(line_ca, perp_d_co), EntityType::Point);

    // F: AB上にあり、DF⊥BOを満たす点(line_abと「Dを通りBOに垂直な直線」の交点)
    let line_ab = egraph.create_entity("Line_AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let line_bo = egraph.create_entity("Line_BO".to_string(), Definition::new_line(b, o), EntityType::Line);
    let perp_d_bo = egraph.create_entity("Perp_D_BO".to_string(), Definition::PerpendicularLine(line_bo, d), EntityType::Line);
    let f = egraph.create_entity("F".to_string(), Definition::Intersection(line_ab, perp_d_bo), EntityType::Point);

    let k = circumcenter(egraph, a, f, e, "K");

    let line_dk = egraph.create_entity("Line_DK".to_string(), Definition::new_line(d, k), EntityType::Line);

    let dir_dk = direction_of(egraph, line_dk, "DK");
    let dir_bc = direction_of(egraph, line_bc, "BC");
    let ang = angle_pair(egraph, dir_dk, dir_bc, "DK_BC");

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![ang, egraph.ang90])),
        initial_facts: vec![],
    }
}

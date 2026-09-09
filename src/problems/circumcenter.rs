use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

// 🌟 外心の存在 (Existence of the Circumcenter)
// 三角形ABCの3辺の垂直二等分線は1点で交わる、という古典的な補題。
// 垂心の存在(orthocenter.rs)と対になる、既存語彙だけで書ける易しいベンチマーク。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 外心の存在 (三角形の3辺の垂直二等分線は1点で交わる) ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let l_bc = egraph.create_entity("Line_BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let l_ca = egraph.create_entity("Line_CA".to_string(), Definition::new_line(c, a), EntityType::Line);
    let l_ab = egraph.create_entity("Line_AB".to_string(), Definition::new_line(a, b), EntityType::Line);

    let mid_bc = egraph.create_entity("Mid_BC".to_string(), Definition::Midpoint(b, c), EntityType::Point);
    let mid_ca = egraph.create_entity("Mid_CA".to_string(), Definition::Midpoint(c, a), EntityType::Point);
    let mid_ab = egraph.create_entity("Mid_AB".to_string(), Definition::Midpoint(a, b), EntityType::Point);

    // 各辺の垂直二等分線 (辺の中点を通り、辺に垂直な直線)
    let pb_bc = egraph.create_entity("PerpBisector_BC".to_string(), Definition::PerpendicularLine(l_bc, mid_bc), EntityType::Line);
    let pb_ca = egraph.create_entity("PerpBisector_CA".to_string(), Definition::PerpendicularLine(l_ca, mid_ca), EntityType::Line);
    let pb_ab = egraph.create_entity("PerpBisector_AB".to_string(), Definition::PerpendicularLine(l_ab, mid_ab), EntityType::Line);

    // 「PerpBisector_BCとPerpBisector_CAの交点」と「PerpBisector_CAとPerpBisector_ABの交点」
    // が一致する、という形で3線の共点性(=外心の存在)を表現する
    let o1 = egraph.create_entity("O_BC_CA".to_string(), Definition::Intersection(pb_bc, pb_ca), EntityType::Point);
    let o2 = egraph.create_entity("O_CA_AB".to_string(), Definition::Intersection(pb_ca, pb_ab), EntityType::Point);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![o1, o2])),
        initial_facts: vec![],
    }
}

use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

/// 🌟 完全四辺形のミケル点の定理: 一般の位置にある4直線は、そのうち3本ずつを
/// 選ぶことで4つの三角形を作る(4本から1本を除く4通り)。この4つの三角形の
/// 外接円は、すべて1点(ミケル点)を通る。
///
/// 既存の miquel.rs(三角形+辺上の3点、3円がミケル点で交わることを証明)を
/// 「4直線・4個の三角形・4円」に一般化したもの。ミケル点が2円
/// (直線{1,2,3}の三角形の外接円 と 直線{1,2,4}の三角形の外接円)の交点として
/// 作図されるところまでは既存のmiquel.rsと全く同じ手法だが、目標を
/// 「直線{2,3,4}の三角形」(ミケル点の作図に使った2つの三角形のどちらとも
/// 頂点をほとんど共有しない、最も遠い三角形)の外接円上にあることの証明に
/// 設定することで、円をまたぐ角度の連鎖がより長くなり、nine_point_fullとは
/// 異なる形でUCB1バンディットの学習機会を増やすことを狙っている。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 完全四辺形のミケル点の定理 ===");

    // 4本の一般の位置にある直線(それぞれ独立な2点で定義)
    let p1 = egraph.create_entity("P1".to_string(), Definition::FreePoint, EntityType::Point);
    let p2 = egraph.create_entity("P2".to_string(), Definition::FreePoint, EntityType::Point);
    let p3 = egraph.create_entity("P3".to_string(), Definition::FreePoint, EntityType::Point);
    let p4 = egraph.create_entity("P4".to_string(), Definition::FreePoint, EntityType::Point);
    let p5 = egraph.create_entity("P5".to_string(), Definition::FreePoint, EntityType::Point);
    let p6 = egraph.create_entity("P6".to_string(), Definition::FreePoint, EntityType::Point);
    let p7 = egraph.create_entity("P7".to_string(), Definition::FreePoint, EntityType::Point);
    let p8 = egraph.create_entity("P8".to_string(), Definition::FreePoint, EntityType::Point);

    let l1 = egraph.create_entity("L1".to_string(), Definition::new_line(p1, p2), EntityType::Line);
    let l2 = egraph.create_entity("L2".to_string(), Definition::new_line(p3, p4), EntityType::Line);
    let l3 = egraph.create_entity("L3".to_string(), Definition::new_line(p5, p6), EntityType::Line);
    let l4 = egraph.create_entity("L4".to_string(), Definition::new_line(p7, p8), EntityType::Line);

    // 4直線の6つの交点(4つの三角形の頂点になる)
    let p12 = egraph.create_entity("P12".to_string(), Definition::Intersection(l1, l2), EntityType::Point);
    let p13 = egraph.create_entity("P13".to_string(), Definition::Intersection(l1, l3), EntityType::Point);
    let p14 = egraph.create_entity("P14".to_string(), Definition::Intersection(l1, l4), EntityType::Point);
    let p23 = egraph.create_entity("P23".to_string(), Definition::Intersection(l2, l3), EntityType::Point);
    let p24 = egraph.create_entity("P24".to_string(), Definition::Intersection(l2, l4), EntityType::Point);
    let p34 = egraph.create_entity("P34".to_string(), Definition::Intersection(l3, l4), EntityType::Point);

    // 4本のうち3本を選んでできる4つの三角形の外接円のうち、まず2つを作図する
    let circ_123 = egraph.create_entity("Circ_123".to_string(), Definition::Circumcircle(p12, p13, p23), EntityType::Conic);
    let circ_124 = egraph.create_entity("Circ_124".to_string(), Definition::Circumcircle(p12, p14, p24), EntityType::Conic);

    // ミケル点: 上記2円の交点として作図する(miquel.rsと同じ手法)
    let m = egraph.create_entity("M".to_string(), Definition::Intersection(circ_123, circ_124), EntityType::Point);
    egraph.link_logical_incidence(m, circ_123);
    egraph.link_logical_incidence(m, circ_124);

    egraph.apply_congruence_closure();

    // 🌟 目標: ミケル点Mは、残る2つの三角形のうち最も離れた
    // (直線{2,3,4}による)三角形の外接円上にもあることを示す。
    // (直線{1,3,4}の三角形はP13経由でCirc_123と、P14経由でCirc_124と
    // それぞれ1点だけ共有するのに対し、直線{2,3,4}の三角形はP23経由で
    // Circ_123と、P24経由でCirc_124と共有するので、対称性の意味では
    // 同程度の難度だが、この一般化がnine_point_fullとは異なる経路で
    // 円の合流を要求することを確認する目的でこちらを選んだ)
    ProblemSetup {
        target_fact: Some(("Concyclic".to_string(), vec![m, p23, p24, p34])),
        initial_facts: vec![],
    }
}

use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::geo_helpers::circumcenter;
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2018 CHN Western MO P5 (difficulty 1.4)
/// 鋭角三角形ABC(AB<AC)の外心をOとし、BCの中点をMとする。三角形AOMの
/// 外接円が直線ABと再び交わる点をD、線分ACと交わる点をEとする。
/// DM=ECであることを示す。
///
/// D・E は円 AOM と直線 AB・AC の「A でないほうの交点」として作図する(来歴 #76)。以前は「直線上かつ円上」の自由点として
/// 置いていたので、有限体では座標が置けず(平方根が要る)、目標の検算も定理の結論の数値監査も判定不能・誤警報になり、
/// 「解けた」ことを数値で確かめられなかった(基準でも監査で偽のマージが2件出ていた)。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2018 CHN Western MO P5 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    let o = circumcenter(egraph, a, b, c, "O");
    let m = egraph.create_entity("M".to_string(), Definition::Midpoint(b, c), EntityType::Point);
    let circ_amo = egraph.create_entity("Circ_AMO".to_string(), Definition::Circumcircle(a, m, o), EntityType::Conic);
    let ab = egraph.create_entity("AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let d = egraph.create_entity("D".to_string(), Definition::SecondIntersectionOfLineAndConic(a, ab, circ_amo), EntityType::Point);
    let ac = egraph.create_entity("AC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let e = egraph.create_entity("E".to_string(), Definition::SecondIntersectionOfLineAndConic(a, ac, circ_amo), EntityType::Point);
    let dist_dm = egraph.create_entity("Dist_DM".to_string(), Definition::LengthSq(d, m), EntityType::Scalar);
    let dist_ec = egraph.create_entity("Dist_EC".to_string(), Definition::LengthSq(e, c), EntityType::Scalar);
    egraph.apply_congruence_closure();
    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![dist_dm, dist_ec])),
        initial_facts: vec![],
    }
}

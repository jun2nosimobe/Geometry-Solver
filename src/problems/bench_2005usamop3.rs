use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2005 USAMO P3 (difficulty 1.8)
/// 鋭角三角形ABCの辺BC上に2点P,Qを取る。C1を「APBC1が円に内接し、
/// QC1∥CA」となるように取り、B1を「APCB1が円に内接し、QB1∥BA」となる
/// ように取る。このときB1,C1,P,Qが共円であることを示す。
///
/// 原題の写し方を直した(来歴 #67): 以前は C1 を「円 ABP 上かつ Q を通り CA に平行な直線上」の自由点、B1 も同様に置いていたが、
/// どちらの制約も2点を与えるので、前提を満たす4通りの組のうち2通りでしか結論が成り立たず(原題は凸四角形で分岐を決める)、
/// 健全な証明が原理的に存在しなかった。有限体では2つの制約を同時に満たす点が置けず、目標の検算も判定不能だった。
/// 今は分岐を作図で決める: C1 を円 ABP 上の自由点とし、Q = BC ∩ (C1 を通り CA に平行な直線)。B1 は「円 C1PQ と、Q を通り
/// AB に平行な直線の、Q でないほうの交点」で、目標は「B1 が円 ACP 上」(= B1,C1,P,Q が共円かつ B1 が円 ACP 上という原題の主張)。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2005 USAMO P3 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let bc = egraph.create_entity("BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let p = egraph.create_entity("P".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(p, bc);

    let circ_abp = egraph.create_entity("Circ_ABP".to_string(), Definition::Circumcircle(a, b, p), EntityType::Conic);
    let c1 = egraph.create_entity("C1".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(c1, circ_abp);

    let ac = egraph.create_entity("AC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let l1 = egraph.create_entity("l1".to_string(), Definition::ParallelLine(ac, c1), EntityType::Line);
    let q = egraph.create_entity("Q".to_string(), Definition::Intersection(l1, bc), EntityType::Point);

    let ab = egraph.create_entity("AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let l2 = egraph.create_entity("l2".to_string(), Definition::ParallelLine(ab, q), EntityType::Line);
    let circ_c1pq = egraph.create_entity("Circ_C1PQ".to_string(), Definition::Circumcircle(c1, p, q), EntityType::Conic);
    let b1 = egraph.create_entity("B1".to_string(),
        Definition::SecondIntersectionOfLineAndConic(q, l2, circ_c1pq), EntityType::Point);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Concyclic".to_string(), vec![a, c, p, b1])),
        initial_facts: vec![],
    }
}

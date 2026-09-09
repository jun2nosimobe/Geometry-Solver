use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2005 USAMO P3 (difficulty 1.8)
/// 鋭角三角形ABCの辺BC上に2点P,Qを取る。C1を「APBC1が円に内接し、
/// QC1∥CA」となるように取り、B1を「APCB1が円に内接し、QB1∥BA」となる
/// ように取る。このときB1,C1,P,Qが共円であることを示す。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2005 USAMO P3 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let bc = egraph.create_entity("BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let p = egraph.create_entity("P".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(p, bc);
    let q = egraph.create_entity("Q".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(q, bc);

    let ac = egraph.create_entity("AC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let l1 = egraph.create_entity("l1".to_string(), Definition::ParallelLine(ac, q), EntityType::Line);
    let circ_abp = egraph.create_entity("Circ_ABP".to_string(), Definition::Circumcircle(a, b, p), EntityType::Conic);
    let c1 = egraph.create_entity("C1".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(c1, circ_abp);
    egraph.link_logical_incidence(c1, l1);

    let ab = egraph.create_entity("AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let l2 = egraph.create_entity("l2".to_string(), Definition::ParallelLine(ab, q), EntityType::Line);
    let circ_acp = egraph.create_entity("Circ_ACP".to_string(), Definition::Circumcircle(a, c, p), EntityType::Conic);
    let b1 = egraph.create_entity("B1".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(b1, circ_acp);
    egraph.link_logical_incidence(b1, l2);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Concyclic".to_string(), vec![b1, c1, p, q])),
        initial_facts: vec![],
    }
}

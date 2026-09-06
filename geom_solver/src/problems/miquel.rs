use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: ミケルの定理 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    
    let line_bc = egraph.create_entity("LineBC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let line_ca = egraph.create_entity("LineCA".to_string(), Definition::new_line(c, a), EntityType::Line);
    let line_ab = egraph.create_entity("LineAB".to_string(), Definition::new_line(a, b), EntityType::Line);
    
    let d = egraph.create_entity("D".to_string(), Definition::FreePoint, EntityType::Point);
    let e = egraph.create_entity("E".to_string(), Definition::FreePoint, EntityType::Point);
    let f = egraph.create_entity("F".to_string(), Definition::FreePoint, EntityType::Point);
    
    egraph.link_logical_incidence(d, line_bc);
    egraph.link_logical_incidence(e, line_ca);
    egraph.link_logical_incidence(f, line_ab);
    
    let circ_aef = egraph.create_entity("CircAEF".to_string(), Definition::Circumcircle(a, e, f), EntityType::Circle);
    let circ_bfd = egraph.create_entity("CircBFD".to_string(), Definition::Circumcircle(b, f, d), EntityType::Circle);
    
    let m = egraph.create_entity("M".to_string(), Definition::Intersection(circ_aef, circ_bfd), EntityType::Point);
    egraph.link_logical_incidence(m, circ_aef);
    egraph.link_logical_incidence(m, circ_bfd);
    
    egraph.apply_congruence_closure();
    
    // 🌟 以前はB,D,Cの共線やA,M,E,F/B,M,D,Fの共円を専用Factとして明示的に
    // 登録していたが、共線はどの定理からも参照されておらず不要だった。
    // 共円もCircumcircleの定義とlink_logical_incidenceによる構造的な接続
    // (a,e,fはCircAEFの定義から、b,f,dはCircBFDの定義から、Mは上のlink_logical_incidence
    // から)だけで「円周角の定理」のConnectedベースの前提を満たすので、
    // 別途Factを登録する必要が無くなった。
    ProblemSetup {
        target_fact: Some(("Concyclic".to_string(), vec![m, c, d, e])),
        initial_facts: vec![],
    }
}
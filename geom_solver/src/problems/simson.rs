use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;
use crate::problems::Fact;

pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: シムソンの定理 ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    
    let line_bc = egraph.create_entity("LineBC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let line_ca = egraph.create_entity("LineCA".to_string(), Definition::new_line(c, a), EntityType::Line);
    let line_ab = egraph.create_entity("LineAB".to_string(), Definition::new_line(a, b), EntityType::Line);
    
    let circ_abc = egraph.create_entity("Circum_ABC".to_string(), Definition::Circumcircle(a, b, c), EntityType::Circle);
    let p = egraph.create_entity("P".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(p, circ_abc);
    // 🐛 バグ修正: link_logical_incidence は「PがCircum_ABC上にある」という構造的な
    // 接続情報を作るだけで、「円周角の定理」がまず要求する Fact::Concyclic を
    // 生成しない。そのため A,B,C,P が Concyclic であるという最も基本的な仮定が
    // 一度もFactとして登録されず、この与えられた外接円に対して「円周角の定理」が
    // 一度も(リーチにすら)発火していなかった。miquel.rs 等の他の問題では
    // 円の交点から生じるConcyclicを initial_facts で明示的に登録しており、
    // simsonでも同様に「Pは外接円ABC上にある」という仮定を事実として明示する。
    
    let perp_d = egraph.create_entity("Perp_P_BC".to_string(), Definition::PerpendicularLine(line_bc, p), EntityType::Line);
    let d = egraph.create_entity("D".to_string(), Definition::Intersection(line_bc, perp_d), EntityType::Point);
    
    let perp_e = egraph.create_entity("Perp_P_CA".to_string(), Definition::PerpendicularLine(line_ca, p), EntityType::Line);
    let e = egraph.create_entity("E".to_string(), Definition::Intersection(line_ca, perp_e), EntityType::Point);
    
    let perp_f = egraph.create_entity("Perp_P_AB".to_string(), Definition::PerpendicularLine(line_ab, p), EntityType::Line);
    let f = egraph.create_entity("F".to_string(), Definition::Intersection(line_ab, perp_f), EntityType::Point);
    
    let line_de = egraph.create_entity("Line_DE".to_string(), Definition::new_line(d, e), EntityType::Line);
    let line_fd = egraph.create_entity("Line_FD".to_string(), Definition::new_line(f, d), EntityType::Line);
    
    let dir_de = egraph.create_entity("Dir_DE".to_string(), Definition::DirectionOf(line_de), EntityType::Direction);
    let dir_fd = egraph.create_entity("Dir_FD".to_string(), Definition::DirectionOf(line_fd), EntityType::Direction);
    
    egraph.apply_congruence_closure();
    
    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![dir_de, dir_fd])),
        initial_facts: vec![
            Fact::new_concyclic(a, b, c, p), // 🌟 Pが外接円ABC上にあるという仮定を明示的に登録
        ],
    }
}
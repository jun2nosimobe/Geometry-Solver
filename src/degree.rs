//! `geom_solver degree <問題名>`: 実体の次数のベクトルを表にする(mmp_core/natural_degree.rs)。
//! 列は自由点(前提の直線・円の上の点は曲線の媒介変数)ごとの成分 ― その自由点だけを一般の直線の上で動かしたときの次数 ―
//! と、その和(各自由点の超平面類の和についての次数)。

use crate::mmp_core::{ClassId, EGraph, EntityType, Fact, Justification};

const USAGE: &str = "使い方: geom_solver degree <問題名> [--only=名前,…]";

pub fn run(args: &[String]) {
    let Some(problem) = args.get(2).filter(|a| !a.starts_with("--")) else { println!("{}", USAGE); return };
    let only: Option<Vec<String>> = args.iter().find_map(|a| a.strip_prefix("--only="))
        .map(|v| v.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect());

    let mut eg = EGraph::new();
    let setup = crate::problems::load_problem(problem, &mut eg);
    for fact in &setup.initial_facts {
        match fact {
            Fact::Identical(a, b) => { eg.merge_entities_justified(*a, *b, Justification::Given); }
            Fact::Connected(c, p) => { eg.link_logical_incidence_justified(*c, *p, Justification::Given); }
        }
    }
    eg.apply_congruence_closure();
    eg.freeze_premise_incidences();

    let blocks = eg.degree_blocks();
    let curve_bound: Vec<bool> = blocks.iter().map(|&b| eg.has_extraneous_incidence(eg.get_rep(b))).collect();
    let linf = eg.get_rep(eg.line_infinity);
    let (ci, cj) = (eg.get_rep(eg.circ_i), eg.get_rep(eg.circ_j));
    let entities: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
        .filter(|&e| eg.get_rep(e) == e && eg.entities[e.0].is_active() && e != linf && e != ci && e != cj)
        .filter(|&e| matches!(eg.entities[e.0].entity_type, EntityType::Point | EntityType::Line | EntityType::Conic))
        .filter(|&e| only.as_ref().is_none_or(|o| o.iter().any(|n| *n == eg.entities[e.0].name)))
        .collect();

    let width = entities.iter().map(|&e| eg.entities[e.0].name.chars().count()).max().unwrap_or(4).clamp(4, 40);
    print!("{:<w$} {:<6}", "実体", "型", w = width);
    for (i, &b) in blocks.iter().enumerate() {
        let name: String = eg.entities[b.0].name.chars().take(5).collect();
        print!(" {:>6}", if curve_bound[i] { format!("{}*", name) } else { name });
    }
    println!(" {:>6}", "和");
    for &e in &entities {
        let ty = match eg.entities[e.0].entity_type { EntityType::Point => "点", EntityType::Line => "直線", EntityType::Conic => "二次曲線", _ => "" };
        let name: String = eg.entities[e.0].name.chars().take(width).collect();
        print!("{:<w$} {:<6}", name, ty, w = width);
        match eg.multidegree(e) {
            Some(v) => {
                for d in &v { print!(" {:>6}", if *d == 0 { "·".to_string() } else { d.to_string() }); }
                println!(" {:>6}", v.iter().sum::<u32>());
            }
            None => { for _ in &blocks { print!(" {:>6}", "?"); } println!(" {:>6}", "?"); }
        }
    }
    println!("(* は前提の直線・円の上の自由点で、成分はその曲線の媒介変数についての次数。? は記号計算で値を作れない作図。)");
}

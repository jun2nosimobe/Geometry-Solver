//! `geom_solver degree <問題名>`: 動点法の次数を表にする。自由点ごとの次数(その点だけを一般の位置の直線の上で動かし、
//! 他の自由点は固定)と、選んだ自由点を全部同時に(共通の媒介変数 t で)動かしたときの次数(総次数)。

use crate::mmp_core::{ClassId, EGraph, EntityType, Fact, Justification};

const USAGE: &str = "使い方: geom_solver degree <問題名> [--movers=A,B,…] [--max-d=次数] [--only=名前,…]";

pub fn run(args: &[String]) {
    let Some(problem) = args.get(2).filter(|a| !a.starts_with("--")) else { println!("{}", USAGE); return };
    let flag = |k: &str| args.iter().find_map(|a| a.strip_prefix(k).map(|s| s.to_string()));
    let list = |k: &str| flag(k).map(|v| v.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect::<Vec<_>>());
    let max_d: usize = flag("--max-d=").and_then(|v| v.parse().ok()).unwrap_or(8);

    let mut eg = EGraph::new();
    let setup = crate::problems::load_problem(problem, &mut eg);
    for fact in &setup.initial_facts {
        match fact {
            Fact::Identical(a, b) => { eg.merge_entities_justified(*a, *b, Justification::Given); }
            Fact::Connected(c, p) => { eg.link_logical_incidence_justified(*c, *p, Justification::Given); }
        }
    }
    eg.apply_congruence_closure();

    let name_of = |eg: &EGraph, id: ClassId| eg.entities[eg.get_rep(id).0].name.clone();
    let mut free: Vec<ClassId> = eg.all_free_points().into_iter().map(|p| eg.get_rep(p)).collect();
    free.sort_by_key(|p| p.0);
    free.dedup();
    let movers: Vec<ClassId> = match list("--movers=") {
        Some(names) => names.iter().filter_map(|n| free.iter().copied().find(|&p| name_of(&eg, p) == *n)
            .or_else(|| { println!("⚠️ 自由点 {} が見つかりません(自由点: {})", n, free.iter().map(|&p| name_of(&eg, p)).collect::<Vec<_>>().join(" ")); None })).collect(),
        None => free.iter().copied().filter(|&p| !eg.has_extraneous_incidence(p)).collect(),
    };
    let on_curve: Vec<String> = free.iter().copied().filter(|&p| eg.has_extraneous_incidence(p)).map(|p| name_of(&eg, p)).collect();
    println!("動かす自由点: {}", movers.iter().map(|&p| name_of(&eg, p)).collect::<Vec<_>>().join(" "));
    if !on_curve.is_empty() { println!("(前提の曲線に乗っていて動かせない自由点: {})", on_curve.join(" ")); }

    let only = list("--only=");
    let linf = eg.get_rep(eg.line_infinity);
    let (ci, cj) = (eg.get_rep(eg.circ_i), eg.get_rep(eg.circ_j));
    let entities: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
        .filter(|&e| eg.get_rep(e) == e && eg.entities[e.0].is_active() && e != linf && e != ci && e != cj)
        .filter(|&e| matches!(eg.entities[e.0].entity_type, EntityType::Point | EntityType::Line | EntityType::Conic))
        .filter(|&e| only.as_ref().is_none_or(|o| o.iter().any(|n| *n == eg.entities[e.0].name)))
        .collect();

    let show = |d: Option<usize>| match d { Some(d) if d >= max_d => format!("≥{}", max_d), Some(d) => d.to_string(), None => "?".to_string() };
    let width = entities.iter().map(|&e| eg.entities[e.0].name.chars().count()).max().unwrap_or(4).clamp(4, 40);
    print!("{:<w$} {:<6}", "実体", "型", w = width);
    for &m in &movers { print!(" {:>5}", name_of(&eg, m)); }
    println!(" {:>6}", "全部");
    for &e in &entities {
        let ty = match eg.entities[e.0].entity_type { EntityType::Point => "点", EntityType::Line => "直線", EntityType::Conic => "二次曲線", _ => "" };
        let name: String = eg.entities[e.0].name.chars().take(width).collect();
        print!("{:<w$} {:<6}", name, ty, w = width);
        for &m in &movers { print!(" {:>5}", show(eg.measure_degree_moving(e, &[m], max_d))); }
        println!(" {:>6}", show(eg.measure_degree_moving(e, &movers, max_d)));
    }
    println!("(? は測れなかったもの: 前提の曲線に乗る点を動かす必要がある・評価できない配置。≥{} は上限 --max-d に達したもの)", max_d);
}

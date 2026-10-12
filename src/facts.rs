//! `geom_solver facts <問題名>`: 図の中で成り立つ事実(定理)を次数の順に並べて数える(mmp_core/fact_census.rs)。
//! 次数ごとの事実の数(種類別・既知か)と目標の次数を表にし、要約の1行 FACTS を出す(bench/facts.sh が集める)。

use std::collections::BTreeMap;
use std::time::Instant;

use crate::mmp_core::{EGraph, Fact, Justification};

const USAGE: &str = "使い方: geom_solver facts <問題名> [--list=件数] [--max-points=点の数]";
const KINDS: [&str; 11] = ["接続(直線)", "接続(円)", "共線", "共円", "平行", "垂直", "等長", "等角", "同じ点", "同じ直線", "?"];

pub fn run(args: &[String]) {
    let Some(problem) = args.get(2).filter(|a| !a.starts_with("--")) else { println!("{}", USAGE); return };
    let flag = |k: &str| args.iter().find_map(|a| a.strip_prefix(k).map(|s| s.to_string()));
    let list: usize = flag("--list=").and_then(|v| v.parse().ok()).unwrap_or(0);
    let max_points: usize = flag("--max-points=").and_then(|v| v.parse().ok()).unwrap_or(90);

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
    let t0 = Instant::now();
    let c = eg.fact_census(setup.target_fact.as_ref(), max_points);
    let secs = t0.elapsed().as_secs_f64();

    // 次数ごとの表(未知の事実を種類別に、既知は合計だけ)。
    let mut table: BTreeMap<u32, ([usize; 11], usize)> = BTreeMap::new();
    for f in &c.facts {
        let e = table.entry(f.degree).or_default();
        if f.known { e.1 += 1; } else { e.0[KINDS.iter().position(|k| *k == f.kind).unwrap_or(10)] += 1; }
    }
    println!("媒介変数 {} 個、点 {}・直線 {}・円 {}(値を作れなかった実体 {})、実体の次数の最大 {}{}",
        c.params, c.points, c.lines, c.conics, c.failed, c.max_degree,
        if c.skipped.is_empty() { String::new() } else { format!("({})", c.skipped.join("、")) });
    print!("{:>4} ", "次数");
    for k in &KINDS[..10] { print!("{:>8}", k); }
    println!("{:>8}{:>8}", "既知", "未知の累計");
    let mut cum = 0usize;
    for (d, (n, known)) in &table {
        let unknown: usize = n.iter().sum();
        cum += unknown;
        let mark = if c.goal_degree == Some(*d) { " ← 目標" } else { "" };
        print!("{:>4} ", d);
        for x in &n[..10] { print!("{:>8}", if *x == 0 { "·".to_string() } else { x.to_string() }); }
        println!("{:>8}{:>8}{}", known, cum, mark);
    }
    if let Some(g) = c.goal_degree && !table.contains_key(&g) { println!("目標の次数 {}", g); }
    if list > 0 {
        println!("--- 未知の事実(次数の低い順に {} 件) ---", list);
        let name = |x: crate::mmp_core::ClassId| eg.entities[x.0].name.clone();
        for f in c.facts.iter().filter(|f| !f.known).take(list) {
            println!("  {:>4}  {:<10} {}", f.degree, f.kind, f.objs.iter().map(|&x| name(x)).collect::<Vec<_>>().join(" "));
        }
    }
    let unknown: Vec<&crate::mmp_core::CensusFact> = c.facts.iter().filter(|f| !f.known).collect();
    let below = c.goal_degree.map(|g| unknown.iter().filter(|f| f.degree < g).count());
    println!("FACTS\t{}\tgoal_degree={}\tgoal_true={}\tparams={}\tobjects={}\tmax_degree={}\tfacts={}\tunknown={}\tunknown_below_goal={}\tsecs={:.2}",
        problem, c.goal_degree.map_or("-".to_string(), |g| g.to_string()), c.goal_true.map_or("-".to_string(), |b| b.to_string()),
        c.params, c.points + c.lines + c.conics, c.max_degree, c.facts.len(), unknown.len(), below.map_or("-".to_string(), |b| b.to_string()), secs);
}

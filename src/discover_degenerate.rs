//! 🌟 padic_eval.rsの退化一致検出を、実際の問題設定(problems/*.rs)に対して
//! 一通り走らせるCLIドライバ。
//! 使い方: geom_solver discover-degenerate <problem_name> [--seed=N]
//!         [--min-hits=N]

use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};
use crate::padic_eval::find_degeneration_specific_coincidences;

/// egraph内の全自由点(Definition::FreePoint かつ EntityType::Point)の
/// ClassIdを、名前と一緒に列挙する。
fn list_free_points(egraph: &EGraph) -> Vec<(ClassId, String)> {
    let mut out = Vec::new();
    for i in 0..egraph.entities.len() {
        let id = ClassId(i);
        if egraph.get_rep(id) != id { continue; }
        let e = &egraph.entities[i];
        if e.entity_type == EntityType::Point && matches!(e.original_definition, Definition::FreePoint) {
            out.push((id, e.name.clone()));
        }
    }
    out
}

pub fn run(args: &[String]) {
    let problem_name = args.get(2).cloned().unwrap_or_else(|| "orthocenter".to_string());
    let seed: u64 = args.iter()
        .find_map(|a| a.strip_prefix("--seed="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(12345);
    // 🌟 何回もの独立な乱数drawで一致が再現する場合だけ報告する
    // (Schwartz-Zippelの偶然一致率は1/998244353と極めて小さいとはいえ、
    // 複数drawでの再現性を要求するとさらに安心できる)。
    let min_hits: u32 = args.iter()
        .find_map(|a| a.strip_prefix("--min-hits="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(2);
    let trials: u32 = min_hits.max(2);

    let mut egraph = EGraph::new();
    let _setup = crate::problems::load_problem(&problem_name, &mut egraph);
    egraph.apply_congruence_closure();

    let free_points = list_free_points(&egraph);
    println!("🚀 退化探索を開始します (問題: {}, 自由点: {}個, 乱数draw: {}回/ペア)",
        problem_name, free_points.len(), trials);
    for (id, name) in &free_points {
        println!("  自由点: {} (id={})", name, id.0);
    }

    let mut any_found = false;
    for i in 0..free_points.len() {
        for j in (i + 1)..free_points.len() {
            let (a_id, a_name) = &free_points[i];
            let (b_id, b_name) = &free_points[j];
            // 複数の独立な乱数drawで再現する組だけを数える。
            let mut counts: std::collections::HashMap<(ClassId, ClassId), u32> = std::collections::HashMap::new();
            for t in 0..trials {
                let hits = find_degeneration_specific_coincidences(&egraph, seed.wrapping_add(t as u64 * 7919), (*a_id, *b_id));
                for pair in hits { *counts.entry(pair).or_insert(0) += 1; }
            }
            let mut reproducible: Vec<_> = counts.into_iter().filter(|&(_, c)| c >= min_hits).collect();
            reproducible.sort_by_key(|&((x, y), _)| (x.0, y.0));
            if !reproducible.is_empty() {
                any_found = true;
                println!("\n🔎 {} ≡ {} という退化のもとで:", a_name, b_name);
                for ((x, y), c) in reproducible {
                    println!("  {} ≡ {}  ({}/{} 回のdrawで再現)", egraph.entities[x.0].name, egraph.entities[y.0].name, c, trials);
                }
            }
        }
    }
    if !any_found {
        println!("\n(この問題・この自由点ペアの組み合わせでは、再現性のある退化固有の一致は見つかりませんでした)");
    }
}

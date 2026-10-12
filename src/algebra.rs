//! `geom_solver algebra <問題名>`: 目標を記号計算で示せるかを試す。探索はしない(問題の作図と前提だけで示す)。
//! --method=wu: Wu の方法(有理的な作図を代入、mmp_core/symbolic.rs)。与えた前提は作図から恒等的に従うものだけ認める。
//! --method=cert: 次数を区切った多項式の線形結合(mmp_core/certificate.rs)。作図でない前提も仮説に入る。
//! 1行の要約 ALGEBRA を出す(bench/algebra.sh が集める)。

use std::time::Instant;

use crate::mmp_core::{EGraph, Fact, Justification};

const USAGE: &str = "使い方: geom_solver algebra <問題名> [--method=wu|cert] [--max-terms=項の数] [--max-mults=回数] [--max-d=次数] [--max-rows=行の数]";

pub fn run(args: &[String]) {
    let Some(problem) = args.get(2).filter(|a| !a.starts_with("--")) else { println!("{}", USAGE); return };
    let flag = |k: &str| args.iter().find_map(|a| a.strip_prefix(k).map(|s| s.to_string()));
    let method = flag("--method=").unwrap_or_else(|| "wu".to_string());
    let max_terms: usize = flag("--max-terms=").and_then(|v| v.parse().ok()).unwrap_or(2_000_000);
    let max_mults: u64 = flag("--max-mults=").and_then(|v| v.parse().ok()).unwrap_or(2_000_000_000);
    let max_d: u32 = flag("--max-d=").and_then(|v| v.parse().ok()).unwrap_or(5);
    let max_rows: usize = flag("--max-rows=").and_then(|v| v.parse().ok()).unwrap_or(300_000);

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
    let Some((kind, targs)) = setup.target_fact.clone() else { println!("ALGEBRA\t{}\tno-target", problem); return };
    let t0 = Instant::now();
    let verdict = |r: Option<bool>| match r { Some(true) => "proved", Some(false) => "nonzero", None => "gave-up" };
    if method == "cert" {
        let (r, nvars, nhyps, rows, d, fail) = eg.certificate_prove(&kind, &targs, max_d, max_rows);
        println!("ALGEBRA\t{}\t{}\t{:.3}\tvars={}\thyps={}\trows={}\td={}\t{}", problem, verdict(r), t0.elapsed().as_secs_f64(), nvars, nhyps, rows, d, fail.unwrap_or_default());
        return;
    }
    let (r, nvars, peak, mults, fail) = eg.symbolic_prove(&kind, &targs, max_terms, max_mults);
    println!("ALGEBRA\t{}\t{}\t{:.3}\tvars={}\tpeak_terms={}\tmults={}\t{}", problem, verdict(r), t0.elapsed().as_secs_f64(), nvars, peak, mults, fail.unwrap_or_default());
}

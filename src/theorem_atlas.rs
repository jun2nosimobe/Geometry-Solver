//! 🌟 `geom_solver theorem-atlas [問題名]`: 登録されている全定理の構造を JSON で出す(docs/gen_theorem_atlas.py が
//! docs/theorems.html に組み立てる)。定理の一覧をコードから作るので、ページが定理の定義とずれない。
//!
//! 出すもの: パターン(役割つき)・作図・結論・変数とパターンの数・証人・lint の指摘、それに「見積もりの順序」 ―
//! 問題の図の上で ProverEngine::estimate_cost を実際に呼び、dfs_match と同じ貪欲な選び方(いちばん安いパターン、
//! 同点なら先頭)で、束縛が空の状態からパターンが消費される順序と各段の見積もりを再現する。束縛した変数には、
//! その型の代表元(隣接数が中央値の実体)を当てるので、値は実際の探索の典型的な1本の枝の近似。

use crate::logic_core::{Bind, Conclusion, DefRole, Flip, Pattern, ProverEngine, Refinement, SelfBindPool, TheoremDef};
use crate::mmp_core::{ClassId, EGraph, EntityType};
use crate::theorems::{theorem_set, TheoremSetOptions};

fn esc(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 2);
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

fn refinement(r: Refinement) -> &'static str {
    match r {
        Refinement::Default => "",
        Refinement::Direction => "方向",
        Refinement::Circle => "円",
        Refinement::CircularPoint => "円周点",
        Refinement::InfinityLine => "無限遠直線",
    }
}

/// パターン1本を読みやすい文字列にする。(種類, 本文)
pub fn render_pattern(p: &Pattern) -> (&'static str, String) {
    match p {
        Pattern::Identical { a, b, pool } => {
            let pool = match pool { SelfBindPool::Any => "", SelfBindPool::Angle => "[角度]", SelfBindPool::CrossRatioOfLines => "[線束の複比]" };
            ("一致", format!("{} ≡ {} {}", a, b, pool).trim_end().to_string())
        }
        Pattern::Connected { child, parent, child_ref, parent_ref } => {
            let cr = refinement(*child_ref);
            let pr = refinement(*parent_ref);
            let c = if cr.is_empty() { child.clone() } else { format!("{}({})", child, cr) };
            let q = if pr.is_empty() { parent.clone() } else { format!("{}({})", parent, pr) };
            ("接続", format!("{} ∈ {}", c, q))
        }
        Pattern::DefinedBy { kind, parents, result, flip, role } => {
            let role_s = match role { DefRole::Lookup => "照合", DefRole::Build => "その場で作る", DefRole::Demand => "需要を立てる" };
            let flip_s = match flip { Flip::Fixed => String::new(), Flip::Free => " 〔向きは自由〕".to_string(), Flip::Grouped(g) => format!(" 〔向きの組 {}〕", g) };
            (role_s, format!("{} = {}({}){}", result, kind.label(), parents.join(", "), flip_s))
        }
        Pattern::Distinct(v) => ("制約", format!("相異なる({})", v.join(", "))),
        Pattern::NonDegenerate(v) => ("非退化", format!("図の上でも相異なる({})", v.join(", "))),
        Pattern::Order(v) => ("制約", format!("順序 {}", v.join(" < "))),
        Pattern::OrderNonStrict(v) => ("制約", format!("順序 {}", v.join(" ≤ "))),
        Pattern::Not(inner) => ("否定", format!("¬[{}]", render_pattern(inner).1)),
    }
}

/// 型ごとの代表元: 隣接(subobjects)の数が中央値の代表元。
fn representatives(eg: &EGraph) -> Vec<(EntityType, ClassId)> {
    let mut out = Vec::new();
    for ty in [EntityType::Point, EntityType::Line, EntityType::Conic, EntityType::Scalar] {
        let mut v: Vec<(usize, ClassId)> = eg.iter_reps_of_type(ty)
            .map(|id| (eg.entities[id.0].components.first().map_or(0, |c| c.subobjects.len()), id)).collect();
        if v.is_empty() { continue; }
        v.sort_unstable_by_key(|x| (x.0, x.1.0));
        out.push((ty, v[v.len() / 2].1));
    }
    out
}

/// 束縛が空の状態から、dfs_match と同じ貪欲な選び方でパターンを消費する順序と見積もり。
fn plan(prover: &ProverEngine, t: &TheoremDef, reps: &[(EntityType, ClassId)]) -> Vec<(usize, f64)> {
    let mut bind: Bind = Bind::default();
    bind.insert("Ang90".to_string(), prover.egraph.ang90);
    bind.insert("Ang0".to_string(), prover.egraph.ang0);
    let mut active: Vec<usize> = (0..t.patterns.len()).collect();
    let mut steps = Vec::new();
    while !active.is_empty() {
        let mut best = (active[0], f64::INFINITY);
        for &i in &active {
            let c = prover.estimate_cost(&t.patterns[i], &bind, t);
            if c < best.1 { best = (i, c); }
        }
        steps.push(best);
        active.retain(|&i| i != best.0);
        if let Some(args) = t.patterns[best.0].fact_args() {
            for v in args {
                if bind.contains_key(v.as_str()) { continue; }
                let ty = t.entities.get(v.as_str()).copied().unwrap_or(EntityType::Point);
                if let Some(&(_, id)) = reps.iter().find(|(tt, _)| *tt == ty) { bind.insert(v.clone(), id); }
            }
        }
    }
    steps
}

pub fn run(args: &[String]) {
    let problem = args.get(2).cloned().unwrap_or_else(|| "nine_point_full".to_string());
    let default_names: Vec<String> = theorem_set(&TheoremSetOptions::default()).into_iter().map(|t| t.name).collect();
    let all = theorem_set(&TheoremSetOptions {
        projective: true, length_bridge: true, central_angle: true, chord: true, parallelogram: true, spiral: true, spiral_opp: true,
        ar_replaces_chord: false,
    });
    let rule_of = |name: &str| -> &'static str {
        if default_names.iter().any(|n| n == name) { return "既定"; }
        if crate::theorems::AR_REPLACED_THEOREMS.contains(&name) { return "--chord-theorems(AR が置き換え)"; }
        if name.starts_with("等しい円周角") { "--rules=chord" }
        else if name.starts_with("平行四辺形") { "--rules=parallelogram" }
        else if name.starts_with("スパイラル相似") { "--rules=spiral" }
        else { "?" }
    };

    let mut eg = EGraph::new();
    let _ = crate::problems::load_problem(&problem, &mut eg);
    let reps = representatives(&eg);
    let mut prover = ProverEngine::new(eg);
    prover.theorems = all.iter().cloned().map(std::rc::Rc::new).collect();

    let mut out = String::new();
    out.push_str(&format!("{{\"plan_problem\":{},\"theorems\":[\n", esc(&problem)));
    for (ti, t) in all.iter().enumerate() {
        let pats: Vec<String> = t.patterns.iter().map(|p| {
            let (k, s) = render_pattern(p);
            format!("[{},{}]", esc(k), esc(&s))
        }).collect();
        let cons: Vec<String> = t.constructions.iter()
            .map(|c| esc(&format!("{} = {}({})", c.bind_to, c.kind.label(), c.args.join(", ")))).collect();
        let concl: Vec<String> = t.conclusions.iter().map(|c| match c {
            Conclusion::Identical(a, b) => esc(&format!("{} ≡ {}", a, b)),
            Conclusion::Connected(a, b) => esc(&format!("{} ∈ {}", a, b)),
        }).collect();
        let lint: Vec<String> = crate::theorem_lint::lint(t).into_iter()
            .map(|f| format!("[{},{}]", esc(f.kind.label()), esc(&f.detail))).collect();
        let witness = crate::theorem_lint::WITNESS.iter().find(|(n, _)| *n == t.name).map(|(_, p)| *p);
        let steps: Vec<String> = plan(&prover, t, &reps).into_iter()
            .map(|(i, c)| format!("[{},{}]", i, if c.is_finite() { format!("{:.1}", c) } else { "null".to_string() })).collect();
        out.push_str(&format!(
            "{{\"index\":{},\"name\":{},\"group\":{},\"vars\":{},\"patterns\":[{}],\"constructions\":[{}],\"conclusions\":[{}],\"lint\":[{}],\"witness\":{},\"plan\":[{}]}}{}\n",
            ti, esc(&t.name), esc(rule_of(&t.name)), t.entities.len(), pats.join(","), cons.join(","), concl.join(","),
            lint.join(","), witness.map_or("null".to_string(), esc), steps.join(","),
            if ti + 1 < all.len() { "," } else { "" }));
    }
    out.push_str("]}\n");
    print!("{}", out);
}

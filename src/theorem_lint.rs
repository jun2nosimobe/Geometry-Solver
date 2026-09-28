//! 🌟 定理のステートメントが、書き方の規約に沿っているかを静的に調べる。
//!
//! 狙いは「定理を読んでも分からない挙動」を書いた時点で見えるようにすること。いまの
//! `TheoremDef` からは、そのパターンが補助作図を要求するのか・その場で図形を作るのか・
//! 役割の入れ替えで同じ結論を何通りも出すのかが読み取れない(来歴 §04)。
//!
//! この段階では**報告するだけ**で、何も失敗させない。規約を決める前に、いまの定理が
//! どの項目にどれだけ引っかかるかを数えるためのもの。

// 規約を決めるまでは lint のテストからしか呼ばない。
#![allow(dead_code)]

use crate::logic_core::{Conclusion, Construction, DefRole, Pattern, TheoremDef};
use crate::mmp_core::{DefKind, ParentSymmetry};

/// 規約から外れている箇所1件。
pub struct Finding {
    pub theorem: String,
    pub kind: Kind,
    pub detail: String,
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Kind {
    /// 補助作図の需要を出しうるパターン(親が揃って候補が空のとき)。
    RaisesDemand,
    /// 宣言した役割と、その種類で実際に起きることが食い違っている。
    RoleMismatch,
    /// マッチの途中でその場に図形を作りうるパターン。
    BuildsOnDemand,
    /// 入れ替えても定理が変わらない変数の組なのに、Order で間引いていない。
    UnbrokenSymmetry,
    /// 変数・パターンが多い。
    Oversized,
    /// 需要を消費する側はあるのに、それを立てる定理が1つも無い。
    UnsuppliedDemand,
    /// この定理が発火することを確かめる問題が無い。
    NoWitness,
    /// 使われていない語彙。
    DeadVocabulary,
}

impl Kind {
    pub fn label(self) -> &'static str {
        match self {
            Kind::RaisesDemand => "需要を出す",
            Kind::RoleMismatch => "役割の宣言が実際と違う",
            Kind::BuildsOnDemand => "その場で作る",
            Kind::UnbrokenSymmetry => "対称性が残っている",
            Kind::Oversized => "規模が大きい",
            Kind::UnsuppliedDemand => "需要の供給元が無い",
            Kind::NoWitness => "証人が無い",
            Kind::DeadVocabulary => "使われない語彙",
        }
    }
}

/// 変数・パターンがこれを超えたら大きいと見なす。
/// 探索の費用は未束縛の変数の数に対して指数的なので、大きい定理は1本で探索を食い潰す。
const VAR_BUDGET: usize = 20;
const PATTERN_BUDGET: usize = 20;

/// 🌟 定理の証人: その定理が発火しないと解けない問題。
///
/// 今回の教訓(来歴 §04):定理を書き換えたとき、規模・役割・束縛の閉包といった**静的な検査は
/// 全部通るのに、必要な形の実体が図に供給されないせいで一度も発火しない**ということが起きる。
/// 供給は実行時の性質なので、静的には捕まえられない ― 実際に解かせるのが唯一の確実な検査。
///
/// 問題名がその定理を名指ししているものだけを載せている。証人の無い定理は
/// lint の「証人が無い」欄に出るので、新しい問題を足すときに埋めること。
const WITNESS: &[(&str, &str)] = &[
    ("スパイラル相似の中点対応", "test_spiral_similarity"),
    ("共点二弦の相似(方冪の定理の基礎)", "test_power_of_point"),
    ("シュタイナーの定理(二次曲線上の6点の複比不変性)", "test_steiner"),
    ("シュタイナーの定理の逆(射影版・円周角の定理の逆)", "test_steiner_converse"),
    ("シュタイナーの定理(接線版)/接弦定理(射影版)", "test_steiner_tangent"),
    ("複比の透視射影不変性(点→線束)/対合定理(共点4直線+横断線)", "test_involution"),
    ("複比の透視射影不変性(線束→点)", "test_cross_ratio"),
    ("二等辺三角形の底角の逆", "test_isosceles_converse"),
    ("直角三角形の斜辺の中線", "test_right_midpoint"),
    ("同位角による平行判定(右共通)", "test_parallel"),
    ("中点連結定理", "varignon"),
    ("円周角の定理", "thales"),
];

/// 🌟 いま上限を超えている定理。分割の検討は §05 b34。
/// **新しい定理をここに足さないこと** ― 足す前に分割できないかを考える。
const OVERSIZED_KNOWN: &[&str] = &[
    "円周角の定理",
    "共点二弦の相似(方冪の定理の基礎)",
    "スパイラル相似の中点対応",
    "シュタイナーの定理の逆(射影版・円周角の定理の逆)",
];

/// マッチャが親を全部束縛した時点で需要を立てる DefKind(logic_core::matcher)。
fn raises_demand(kind: DefKind) -> bool {
    matches!(kind, DefKind::LineThroughPoints | DefKind::Intersection)
}

/// 定理全体を、変数名だけを取り替えられる正規形の文字列にする。
/// 対称な引数(Distinct・Identical・親が Unordered な DefinedBy)は並べ替えて揃える。
fn canonical(t: &TheoremDef, swap: Option<(&str, &str)>) -> String {
    let rename = |v: &String| -> String {
        match swap {
            Some((a, b)) if v == a => b.to_string(),
            Some((a, b)) if v == b => a.to_string(),
            _ => v.clone(),
        }
    };
    let mut lines: Vec<String> = Vec::new();
    for p in &t.patterns {
        lines.push(match p {
            Pattern::Identical { a, b, pool } => {
                let mut xs = [rename(a), rename(b)];
                xs.sort();
                format!("Identical {:?} {:?}", xs, pool)
            }
            Pattern::Connected { child, parent, child_ref, parent_ref } =>
                format!("Connected {} {} {:?} {:?}", rename(child), rename(parent), child_ref, parent_ref),
            Pattern::DefinedBy { kind, parents, result, flip, role } => {
                let mut ps: Vec<String> = parents.iter().map(rename).collect();
                if kind.parent_symmetry() == ParentSymmetry::Unordered { ps.sort(); }
                format!("DefinedBy {:?} {:?} {} {:?} {:?}", kind, ps, rename(result), flip, role)
            }
            Pattern::Distinct(vs) => {
                let mut xs: Vec<String> = vs.iter().map(rename).collect();
                xs.sort();
                format!("Distinct {:?}", xs)
            }
            Pattern::Order(vs) => format!("Order {:?}", vs.iter().map(rename).collect::<Vec<_>>()),
            Pattern::OrderNonStrict(vs) => format!("OrderLe {:?}", vs.iter().map(rename).collect::<Vec<_>>()),
            Pattern::Not(_) => "Not".to_string(),
        });
    }
    lines.sort();
    let mut out = lines.join("\n");
    let mut tail: Vec<String> = Vec::new();
    for Construction { kind, args, bind_to } in &t.constructions {
        let mut ps: Vec<String> = args.iter().map(rename).collect();
        if kind.parent_symmetry() == ParentSymmetry::Unordered { ps.sort(); }
        tail.push(format!("Build {:?} {:?} {}", kind, ps, rename(bind_to)));
    }
    for c in &t.conclusions {
        tail.push(match c {
            Conclusion::Identical(a, b) => {
                let mut xs = [rename(a), rename(b)];
                xs.sort();
                format!("ConclIdentical {:?}", xs)
            }
            Conclusion::Connected(a, b) => format!("ConclConnected {} {}", rename(a), rename(b)),
        });
    }
    tail.sort();
    out.push('\n');
    out.push_str(&tail.join("\n"));
    out
}

/// u と v が Order / OrderNonStrict で既に並べ替えを潰されているか。
fn ordered_together(t: &TheoremDef, u: &str, v: &str) -> bool {
    t.patterns.iter().any(|p| match p {
        Pattern::Order(vs) | Pattern::OrderNonStrict(vs) =>
            vs.iter().any(|x| x == u) && vs.iter().any(|x| x == v),
        _ => false,
    })
}

/// 定理1つを調べる。
pub fn lint(t: &TheoremDef) -> Vec<Finding> {
    let mut out = Vec::new();
    let mut add = |kind: Kind, detail: String| {
        out.push(Finding { theorem: t.name.clone(), kind, detail });
    };

    for (i, p) in t.patterns.iter().enumerate() {
        match p {
            Pattern::DefinedBy { kind, parents, role, .. } => {
                // demand_by は、その需要を消費する resolve_* がある種類にしか書けない。
                let consumed = raises_demand(*kind) && parents.len() == 2;
                match role {
                    DefRole::Demand if !consumed =>
                        add(Kind::RoleMismatch, format!("#{} demand_by({:?}) だが、この需要を消費する resolve_* が無い", i, kind)),
                    DefRole::Build => add(Kind::BuildsOnDemand, format!("#{} {:?}", i, kind)),
                    DefRole::Demand => add(Kind::RaisesDemand, format!("#{} {:?}({})", i, kind, parents.join(","))),
                    DefRole::Lookup => {}
                }
            }
            Pattern::Not(_) => add(Kind::DeadVocabulary, format!("#{} Pattern::Not", i)),
            _ => {}
        }
    }

    if !WITNESS.iter().any(|(name, _)| *name == t.name) {
        add(Kind::NoWitness, "発火を確かめる問題が紐づいていない".to_string());
    }

    if t.entities.len() > VAR_BUDGET {
        add(Kind::Oversized, format!("変数{}個(上限{})", t.entities.len(), VAR_BUDGET));
    }
    if t.patterns.len() > PATTERN_BUDGET {
        add(Kind::Oversized, format!("パターン{}本(上限{})", t.patterns.len(), PATTERN_BUDGET));
    }

    // 入れ替えても定理が変わらない(=自己同型になる)変数の組を探す。
    let base = canonical(t, None);
    let mut names: Vec<&String> = t.entities.keys().collect();
    names.sort();
    for i in 0..names.len() {
        for j in (i + 1)..names.len() {
            let (u, v) = (names[i].as_str(), names[j].as_str());
            if t.entities[u] != t.entities[v] { continue; }
            if ordered_together(t, u, v) { continue; }
            if canonical(t, Some((u, v))) == base {
                add(Kind::UnbrokenSymmetry, format!("{} <-> {}", u, v));
            }
        }
    }
    out
}

/// 定理集合ぜんぶを調べて、読みやすい表にする。
pub fn report(theorems: &[TheoremDef]) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    let all: Vec<Finding> = theorems.iter().flat_map(lint).collect();
    let kinds = [Kind::RoleMismatch, Kind::UnsuppliedDemand, Kind::NoWitness, Kind::UnbrokenSymmetry, Kind::Oversized,
                 Kind::BuildsOnDemand, Kind::RaisesDemand, Kind::DeadVocabulary];

    let _ = writeln!(s, "定理 {} 件を検査した。", theorems.len());

    // 需要を消費する側(blackboard の resolve_*)はあるのに、それを立てる定理が
    // 1つも無い種類。交点の需要はここで空振りしていた(来歴 §04 #64)。
    let mut all = all;
    for kind in [DefKind::LineThroughPoints, DefKind::Intersection] {
        let supplied = theorems.iter().flat_map(|t| t.patterns.iter()).any(|p| matches!(
            p, Pattern::DefinedBy { kind: k, role: DefRole::Demand, .. } if *k == kind));
        if !supplied {
            all.push(Finding {
                theorem: "(定理集合ぜんぶ)".to_string(),
                kind: Kind::UnsuppliedDemand,
                detail: format!("{:?} の需要を立てる定理が1つも無いので、対応する resolve_* は空振りする", kind),
            });
        }
    }
    for k in kinds {
        let hits: Vec<&Finding> = all.iter().filter(|f| f.kind == k).collect();
        let theorems_hit: std::collections::BTreeSet<&str> =
            hits.iter().map(|f| f.theorem.as_str()).collect();
        let _ = writeln!(s, "\n[{}] {}件 / {}定理", k.label(), hits.len(), theorems_hit.len());
        for f in hits.iter().take(40) {
            let _ = writeln!(s, "    {:<34} {}", trunc(&f.theorem, 34), f.detail);
        }
        if hits.len() > 40 { let _ = writeln!(s, "    ... 他 {} 件", hits.len() - 40); }
    }
    s
}

fn trunc(s: &str, n: usize) -> String {
    if s.chars().count() <= n { s.to_string() } else { s.chars().take(n).collect() }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn all_theorems() -> Vec<TheoremDef> {
        crate::theorems::theorem_set(&crate::theorems::TheoremSetOptions {
            projective: true, length_bridge: true, central_angle: true,
        })
    }

    /// 規約の実態を表にして出す(`cargo test -- --nocapture lint_report`)。
    #[test]
    fn theorem_format_lint_report() {
        let all = all_theorems();
        println!("\n{}", report(&all));
        assert!(!all.is_empty(), "定理が1つも読めていない");
    }

    /// 🌟 宣言した役割(match_by / build_by / demand_by)が、その種類で実際に起きることと
    /// 合っていること。ここが食い違うと「定理を読んでも挙動が分からない」状態に戻る。
    #[test]
    fn every_theorem_declares_its_definedby_role_correctly() {
        let all = all_theorems();
        let bad: Vec<String> = all.iter().flat_map(lint)
            .filter(|f| f.kind == Kind::RoleMismatch)
            .map(|f| format!("{}: {}", f.theorem, f.detail))
            .collect();
        assert!(bad.is_empty(), "役割の宣言が実際と違う:\n{}", bad.join("\n"));
    }

    /// 🌟 変数・パターンの数が上限を超える定理を、黙って増やさない。
    /// 超えているものは OVERSIZED_KNOWN に書いてあるものだけ。
    #[test]
    fn no_new_oversized_theorem() {
        let all = all_theorems();
        let bad: Vec<String> = all.iter().flat_map(lint)
            .filter(|f| f.kind == Kind::Oversized && !OVERSIZED_KNOWN.contains(&f.theorem.as_str()))
            .map(|f| format!("{}: {}", f.theorem, f.detail))
            .collect();
        assert!(bad.is_empty(),
            "上限(変数{}・パターン{})を超える定理が増えた。分割できないか検討すること:\n{}",
            VAR_BUDGET, PATTERN_BUDGET, bad.join("\n"));
    }

    /// 🌟 証人の問題が今も解けること。定理を書き換えて「静的には正しいが一度も発火しない」
    /// 形になっていないかを、実際に解かせて確かめる唯一の検査。
    #[test]
    fn every_witnessed_theorem_still_fires() {
        let names: Vec<String> = all_theorems().iter().map(|t| t.name.clone()).collect();
        let opts = crate::solve::SolveOptions::parse(&["--steps=600000".to_string()])
            .expect("既定のオプションは読めるはず");
        for (theorem, problem) in WITNESS {
            assert!(names.iter().any(|n| n == theorem),
                "証人の表に、もう存在しない定理「{}」が載っている", theorem);
            assert!(crate::solve::run(problem, &opts),
                "「{}」の証人 {} が解けない。定理が一度も発火していない可能性が高い", theorem, problem);
        }
    }

    /// 🌟 OVERSIZED_KNOWN が実態と合っていること(分割して収まったら消す)。
    #[test]
    fn oversized_known_list_is_current() {
        let all = all_theorems();
        let actual: std::collections::BTreeSet<String> = all.iter().flat_map(lint)
            .filter(|f| f.kind == Kind::Oversized)
            .map(|f| f.theorem.clone()).collect();
        for name in OVERSIZED_KNOWN {
            assert!(actual.contains(*name),
                "「{}」はもう上限を超えていない。OVERSIZED_KNOWN から消すこと", name);
        }
    }
}

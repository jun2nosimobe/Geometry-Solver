//! 🌟 マージの監査(`--audit-merges`): 全てのマージと接続を、実行する直前に数値で確かめ、出どころ(規則)ごとに数える。
//! 探索は変えない(乱数も消費しない)。偽が出た最初のマージが、その問題の偽の連鎖の根。

use super::{ClassId, EGraph, Justification};
use std::collections::BTreeMap;

#[derive(Debug, Default)]
pub struct MergeCensus {
    /// 出どころ -> [真, 偽, 判定不能]。
    pub per_source: BTreeMap<String, [u64; 3]>,
    /// これまでに確かめたマージ・接続の数(偽の行に通し番号として出す)。
    pub seq: u64,
    false_printed: usize,
    unknown_printed: usize,
    /// 使い捨ての複製(予想の評価など)の監査は数えない。
    silent: bool,
}

impl Clone for MergeCensus {
    fn clone(&self) -> Self { Self { silent: true, ..Self::default() } }
}

impl MergeCensus {
    const MAX_PRINTED: usize = 40;
}

fn source_label(j: &Justification) -> String {
    match j {
        Justification::Given => "前提".into(),
        Justification::Theorem { name, .. } => format!("定理: {name}"),
        Justification::Congruence { .. } => "合同閉包".into(),
        Justification::LineUniqueness { .. } => "伝播: 直線の一意性".into(),
        Justification::PointUniqueness { .. } => "伝播: 交点の一意性".into(),
        Justification::ConicUniqueness { .. } => "伝播: 二次曲線の一意性".into(),
        Justification::Trivial { reason } => format!("自明: {reason}"),
    }
}

impl EGraph {
    /// マージ(incidence = false)または接続(incidence = true、a が点で b が曲線)の直前に呼ぶ。
    pub(crate) fn census_record(&mut self, a: ClassId, b: ClassId, incidence: bool, j: &Justification) {
        if self.merge_census.as_ref().is_none_or(|c| c.silent) { return; }
        let (ra, rb) = (self.get_rep(a), self.get_rep(b));
        if ra == rb { return; }
        let verdict = self.without_consuming_rng(|eg| if incidence {
            eg.numeric_incidence_check(ra, rb, 2)
        } else {
            eg.numeric_plausibility_check(ra, rb, 2)
        });
        let label = source_label(j);
        let (na, nb) = (self.entities[ra.0].name.clone(), self.entities[rb.0].name.clone());
        let Some(c) = self.merge_census.as_mut() else { return };
        c.seq += 1;
        let slot = match verdict { Some(true) => 0, Some(false) => 1, None => 2 };
        c.per_source.entry(label.clone()).or_default()[slot] += 1;
        if verdict == Some(false) && c.false_printed < MergeCensus::MAX_PRINTED {
            c.false_printed += 1;
            println!("MERGE_CENSUS_FALSE\t{}\t{}\t{} {} {}", c.seq, label, na, if incidence { "∈" } else { "≡" }, nb);
        }
        // 判定不能は監査の死角(偽でも素通りする)。どの規則で起きているかを追えるよう、最初の数件を出す。
        if verdict.is_none() && c.unknown_printed < MergeCensus::MAX_PRINTED {
            c.unknown_printed += 1;
            println!("MERGE_CENSUS_UNKNOWN\t{}\t{}\t{} {} {}", c.seq, label, na, if incidence { "∈" } else { "≡" }, nb);
            if std::env::var("GS_DEBUG_CENSUS").is_ok() {
                let dbg = self.without_consuming_rng(|eg| eg.debug_numeric_unknown(ra, rb));
                println!("  CENSUS_DEBUG {}", dbg);
            }
        }
    }
}

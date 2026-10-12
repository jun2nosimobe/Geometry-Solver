//! 🌟 次数の順に事実を確定していく探索(`--degree-search`、計画の段階3)。定理の照合(今の探索)は使わない。
//!
//! 図の事実(fact_census の一覧。候補は値の比較で選ぶ)を、共通の写像の次数 d の低い順に見ていく。次数 d ごとに
//! (1) 次数 d の未知の事実の角・長さの実体を足し、合同閉包と代数的な追跡(AR)で閉じる。
//! (2) それでも分からない次数 d の事実を Wu の方法(掛け算の上限 1000·2^(d/2) 回)で確かめて e-graph に入れる(根拠
//!     「代数計算(Wu の方法)」)。これが「次数 d より低い事実から線形には従わない、次数 d の新しい事実」。
//! 目標の次数まで来るか目標が分かったら止まり、目標が分かっていなければ残りの予算の全部で目標を Wu の方法で試す。
//! 既定(`--no-degree-first` で外す)では、この段を予算の 1/4 までで止め、最後の Wu の方法の試みはせずに定理の照合に続ける。

use crate::mmp_core::{CensusFact, ClassId, Definition, EGraph};

use super::{BlackboardEngine, WuTry, WU_MULTS_PER_WORK};

const MAX_TERMS: usize = 1_000_000;

/// 次数ごとの結果: 事実の数、見る前から分かっていた数、AR で分かった数、Wu の方法で示した数、示せなかった数。
#[derive(Debug, Clone, Default)]
pub struct DegreeLevel {
    pub degree: u32,
    pub facts: usize,
    pub known: usize,
    pub by_ar: usize,
    pub by_wu: usize,
    pub unproved: usize,
}

impl BlackboardEngine {
    /// 次数の順に事実を確定していく。目標が分かったら true。then_search なら仕事量が予算の 1/4 に達したら止め、最後に目標を
    /// Wu の方法で試すことはしない(この後に定理の照合が続く)。
    pub fn degree_search(&mut self, target: &(String, Vec<ClassId>), then_search: bool) -> (bool, Vec<DegreeLevel>) {
        let phase_limit = if then_search { self.work_limit / 4 } else { self.work_limit };
        let census = self.prover.egraph.fact_census(Some(target), 90);
        let goal_degree = census.goal_degree.unwrap_or(u32::MAX);
        let mut memo = self.wu.as_mut().map(|w| std::mem::take(&mut w.memo)).unwrap_or_default();
        // Wu の方法が使えるか(与えた前提が作図から従うか)を最初に1度だけ確かめる。
        let (ok, mults, why) = self.prover.egraph.symbolic_premises_with(MAX_TERMS, self.wu_remaining(), &mut memo);
        self.prover.egraph.spiral_prop_work += mults / WU_MULTS_PER_WORK;
        let wu_ok = ok == Some(true);
        if !wu_ok { println!("  📶 [次数の順の探索] Wu の方法は使えない({})", why.unwrap_or_default()); }

        let mut levels: Vec<DegreeLevel> = Vec::new();
        let mut degrees: Vec<u32> = census.facts.iter().map(|f| f.degree).filter(|&d| d <= goal_degree).collect();
        degrees.sort_unstable();
        degrees.dedup();
        for d in degrees {
            if self.goal_reached(target) || self.wu_remaining() == 0 || self.prover.work_done() >= phase_limit { break; }
            let facts: Vec<&CensusFact> = census.facts.iter().filter(|f| f.degree == d).collect();
            let mut lv = DegreeLevel { degree: d, facts: facts.len(), ..Default::default() };
            let unknown: Vec<&CensusFact> = facts.iter().copied().filter(|f| !self.prover.egraph.census_known(f)).collect();
            lv.known = facts.len() - unknown.len();
            // (1) 角・長さの実体を足して AR で閉じる。
            for f in &unknown { self.prover.egraph.census_materialize(f); }
            self.prover.egraph.apply_congruence_closure();
            self.run_ar();
            let rest: Vec<&CensusFact> = unknown.iter().copied().filter(|f| !self.prover.egraph.census_known(f)).collect();
            lv.by_ar = unknown.len() - rest.len();
            // (2) 残りを Wu の方法で確かめる。
            let cap = 1000u64 << (d.min(60) / 2);
            for f in rest {
                if self.prover.egraph.census_known(f) { lv.by_ar += 1; continue; }
                let remaining = self.wu_remaining();
                if !wu_ok || remaining == 0 { lv.unproved += 1; continue; }
                let Some((kind, args)) = self.census_target(f) else { lv.unproved += 1; continue };
                let cap = cap.min(remaining);
                let (r, mults, _) = self.prover.egraph.symbolic_fact_with(&kind, &args, MAX_TERMS, cap, &mut memo);
                self.prover.egraph.spiral_prop_work += mults.min(cap) / WU_MULTS_PER_WORK;
                if r == Some(true) && self.close_by_wu(&kind, &args) { lv.by_wu += 1; } else { lv.unproved += 1; }
            }
            println!("  📶 [次数 {}] 事実 {}(既知 {}、AR で {}、Wu の方法で {}、示せない {})", d, lv.facts, lv.known, lv.by_ar, lv.by_wu, lv.unproved);
            levels.push(lv);
        }
        if let Some(w) = self.wu.as_mut() { w.memo = memo; }
        if !then_search && !self.goal_reached(target) && wu_ok { self.try_wu(target, WuTry::Last); }
        (self.goal_reached(target), levels)
    }

    fn goal_reached(&self, target: &(String, Vec<ClassId>)) -> bool {
        matches!(self.prover.egraph.goal_status(Some(target)), crate::mmp_core::GoalStatus::Reached)
    }

    /// Wu の方法に使える残りの掛け算の回数(予算の残り)。
    fn wu_remaining(&self) -> u64 {
        self.work_limit.saturating_sub(self.prover.work_done()).saturating_mul(WU_MULTS_PER_WORK)
    }

    /// 事実を Wu の方法で確かめる形(種類, 実体)にする。要る実体(2点を通る直線・方向・有向角・長さの2乗)は作る。
    fn census_target(&mut self, f: &CensusFact) -> Option<(String, Vec<ClassId>)> {
        let eg = &mut self.prover.egraph;
        let make = |eg: &mut EGraph, def: Definition| { let ty = def.default_entity_type(); eg.create_entity(format!("census_{}", eg.entities.len()), def, ty) };
        let dir = |eg: &mut EGraph, l: ClassId| { let l = eg.get_rep(l); make(eg, Definition::DirectionOf(l)) };
        let id = |k: &str, v: Vec<ClassId>| Some((k.to_string(), v));
        match (f.kind, f.objs.as_slice()) {
            ("接続(直線)" | "接続(円)", [p, c]) => id("Connected", vec![*p, *c]),
            ("同じ点" | "同じ直線", [a, b]) => id("Identical", vec![*a, *b]),
            ("共線", [a, b, c]) => {
                let (ra, rb) = (eg.get_rep(*a), eg.get_rep(*b));
                let line = make(eg, Definition::LineThroughPoints(ra, rb));
                id("Connected", vec![*c, line])
            }
            ("共円", ps) if ps.len() >= 4 => id("Concyclic", ps.to_vec()),
            ("平行", [a, b]) => { let (x, y) = (dir(eg, *a), dir(eg, *b)); id("Identical", vec![x, y]) }
            ("垂直", [a, b]) => {
                let (x, y) = (dir(eg, *a), dir(eg, *b));
                let ang = make(eg, Definition::AnglePair(x, y));
                id("Identical", vec![ang, eg.ang90])
            }
            ("等長", [a, b, c, d]) => {
                let (ra, rb, rc, rd) = (eg.get_rep(*a), eg.get_rep(*b), eg.get_rep(*c), eg.get_rep(*d));
                let (x, y) = (make(eg, Definition::LengthSq(ra, rb)), make(eg, Definition::LengthSq(rc, rd)));
                id("Identical", vec![x, y])
            }
            ("等角", [a, b, c, d]) => {
                let (da, db, dc, dd) = (dir(eg, *a), dir(eg, *b), dir(eg, *c), dir(eg, *d));
                let (x, y) = (make(eg, Definition::AnglePair(da, db)), make(eg, Definition::AnglePair(dc, dd)));
                id("Identical", vec![x, y])
            }
            _ => None,
        }
    }
}

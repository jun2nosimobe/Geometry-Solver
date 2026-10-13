//! 🌟 次数の順に事実を確定していく探索(`--degree-search`、計画の段階3)。定理の照合(今の探索)は使わない。
//!
//! 図の事実(fact_census の一覧。候補は値の比較で選ぶ)を、共通の写像の次数 d の低い順に見ていく。次数 d ごとに
//! (1) 次数 d の未知の事実の角・長さの実体を足し、合同閉包と代数的な追跡(AR)で閉じる。
//! (2) それでも分からない次数 d の事実のうち、同じ点・同じ直線と、既知の事実の乗法的関係(mmp_core/units.rs の原子のベクトル)の
//!     張る空間に入らないもの(独立なもの)と、張る空間に入るのに AR が出せなかったものを、記号計算(掛け算の上限 1000·2^(d/2) 回)で
//!     示して e-graph に入れる(根拠「代数計算(乗法的関係)」)。段の中で示した事実で従属になったものは次の AR に任せる。
//! 目標の次数まで見て目標が分からなければ、補助作図を次数の低い順に足し(mmp_core/aux_census.rs: 目標を目標より低い次数の関係の
//! 張る空間に入れる候補だけ、同じ次数の中では目標に近い順)、図の事実を数え直してもう一度回す(AUX_ROUNDS 回まで)。それでも分からなければ、残りの予算の
//! 全部で目標を Wu の方法で試す。
//! 既定(`--no-degree-first` で外す)では、この段を予算の 1/4 までで止め、最後の Wu の方法の試みはせずに定理の照合に続ける。

use crate::mmp_core::{AuxKind, Census, CensusFact, ClassId, Definition, EGraph, Eliminator, EntityOrigin, EntityType, WuMemo};

use super::{BlackboardEngine, WuTry, MULT_THEOREM, WU_MULTS_PER_WORK};

const MAX_TERMS: usize = 1_000_000;
/// 補助作図を足して数え直す回数・1回に足す数・増えを測る候補の数(次数の低い順)。
const AUX_ROUNDS: usize = 3;
const AUX_PER_ROUND: usize = 1;
const AUX_EVAL: usize = 400;
/// 補助点の次数の上限は目標の次数のこの倍(切り上げ)。GS_AUX_DEGREE_FACTOR で変えられる(調べる用。inf で上限なし)。
const AUX_DEGREE_FACTOR: f64 = 2.0;

fn aux_max_degree(goal: u32) -> u32 {
    let f = std::env::var("GS_AUX_DEGREE_FACTOR").ok().and_then(|x| x.parse::<f64>().ok()).unwrap_or(AUX_DEGREE_FACTOR);
    if !f.is_finite() || goal == u32::MAX { return u32::MAX; }
    (goal as f64 * f).ceil() as u32
}

/// 次数ごとの結果: 事実の数、見る前から分かっていた数、AR で分かった数、記号計算で示した数(独立な関係)、示せなかった数、
/// 既知の事実から線形に従うので AR に任せた数。
#[derive(Debug, Clone, Default)]
pub struct DegreeLevel {
    pub degree: u32,
    pub facts: usize,
    pub known: usize,
    pub by_ar: usize,
    pub by_wu: usize,
    pub unproved: usize,
    pub dependent: usize,
    /// 既知の事実から線形に従うのに AR が出せなかったので、記号計算で示しにいった数(示した数・示せない数にも入る)。
    pub ar_missed: usize,
    /// 何回目の補助作図の後か(0 は図のまま)。
    pub round: usize,
}

impl BlackboardEngine {
    /// 次数の順に事実を確定していく。目標が分かったら true。then_search なら仕事量が予算の 1/4 に達したら止め、最後に目標を
    /// Wu の方法で試すことはしない(この後に定理の照合が続く)。
    pub fn degree_search(&mut self, target: &(String, Vec<ClassId>), then_search: bool) -> (bool, Vec<DegreeLevel>) {
        let phase_limit = if then_search { self.work_limit / 4 } else { self.work_limit };
        let mut memo = self.wu.as_mut().map(|w| std::mem::take(&mut w.memo)).unwrap_or_default();
        // Wu の方法が使えるか(与えた前提が作図から従うか)を最初に1度だけ確かめる。
        let (ok, mults, why) = self.prover.egraph.symbolic_premises_with(MAX_TERMS, self.wu_remaining(), &mut memo);
        self.prover.egraph.spiral_prop_work += mults / WU_MULTS_PER_WORK;
        let wu_ok = ok == Some(true);
        if !wu_ok { println!("  📶 [次数の順の探索] Wu の方法は使えない({})", why.unwrap_or_default()); }

        let mut levels: Vec<DegreeLevel> = Vec::new();
        let mut census = self.prover.egraph.fact_census(Some(target), 90);
        let goal_degree = census.goal_degree.unwrap_or(u32::MAX);
        for round in 0..=AUX_ROUNDS {
            if round > 0 {
                if self.goal_reached(target) || self.wu_remaining() == 0 || self.prover.work_done() >= phase_limit { break; }
                // 補助作図: 目標を低い次数の関係の張る空間に入れる候補のうち、一番低い次数のものを目標に近い順に。
                // 「既知」は段で示した事実を含むように判定し直す。
                let known: Vec<bool> = census.facts.iter().map(|f| self.prover.egraph.census_known(f)).collect();
                for (f, k) in census.facts.iter_mut().zip(known) { f.known = k; }
                let cands = self.prover.egraph.aux_candidates(&census, target, aux_max_degree(goal_degree), AUX_EVAL);
                let mut added = 0;
                for c in cands.iter().take(AUX_PER_ROUND) {
                    let names: Vec<String> = c.kinds.iter().filter_map(|&k| self.add_degree_aux(k)).collect();
                    if names.is_empty() { continue; }
                    println!("  📐 [次数の順の補助作図] {}(次数 {}、目標を低い次数の関係で張るのに足した事実 {}、目標から {} 段)", names.join("・"), c.degree, c.gain, c.goal_dist);
                    added += 1;
                }
                if added == 0 { break; }
                census = self.prover.egraph.fact_census(Some(target), 90);
            }
            self.degree_levels(&census, target, goal_degree, phase_limit, wu_ok, &mut memo, round, &mut levels);
            if self.goal_reached(target) { break; }
        }
        if let Some(w) = self.wu.as_mut() { w.memo = memo; }
        if !then_search && !self.goal_reached(target) && wu_ok { self.try_wu(target, WuTry::Last); }
        (self.goal_reached(target), levels)
    }

    /// 図の事実を目標の次数まで、次数の低い順に確定していく(1回分)。
    #[allow(clippy::too_many_arguments)]
    fn degree_levels(&mut self, census: &Census, target: &(String, Vec<ClassId>), goal_degree: u32, phase_limit: u64, wu_ok: bool,
                     memo: &mut WuMemo, round: usize, levels: &mut Vec<DegreeLevel>) {
        // 事実の乗法的関係のベクトルと、既知の事実の張る空間。
        let (_, vecs) = self.prover.egraph.unit_relations(&census.facts);
        let mut known_span = Eliminator::default();
        let mut in_span = vec![false; census.facts.len()];
        let mut pending_ar = false;
        let mut degrees: Vec<u32> = census.facts.iter().map(|f| f.degree).filter(|&d| d <= goal_degree).collect();
        degrees.sort_unstable();
        degrees.dedup();
        for d in degrees {
            if self.goal_reached(target) || self.wu_remaining() == 0 || self.prover.work_done() >= phase_limit { break; }
            let facts: Vec<usize> = (0..census.facts.len()).filter(|&i| census.facts[i].degree == d).collect();
            let mut lv = DegreeLevel { degree: d, facts: facts.len(), round, ..Default::default() };
            let unknown: Vec<usize> = facts.iter().copied().filter(|&i| !self.prover.egraph.census_known(&census.facts[i])).collect();
            lv.known = facts.len() - unknown.len();
            // (1) 角・長さの実体を足して AR で閉じる。
            for &i in &unknown { self.prover.egraph.census_materialize(&census.facts[i]); }
            self.prover.egraph.apply_congruence_closure();
            self.run_ar();
            pending_ar = false;
            let mut rest: Vec<usize> = unknown.iter().copied().filter(|&i| !self.prover.egraph.census_known(&census.facts[i])).collect();
            lv.by_ar = unknown.len() - rest.len();
            // (2) 同じ点・同じ直線と、既知の事実の張る空間に入らない(独立な)ものを記号計算で示す。原子の少ないものから。
            for (i, f) in census.facts.iter().enumerate() {
                if !in_span[i] && let Some(v) = &vecs[i] && self.prover.egraph.census_known(f) { known_span.insert(v); in_span[i] = true; }
            }
            let identity = |i: usize| matches!(census.facts[i].kind, "同じ点" | "同じ直線");
            rest.sort_by_key(|&i| (!identity(i), vecs[i].as_ref().map_or(usize::MAX, |v| v.len())));
            let cap = 1000u64 << (d.min(60) / 2);
            let mut proved_any = false;
            // AR を回した後でも分からないのに、既知の事実から線形に従っていたもの(AR が e-graph の接続などとして出せなかった)。
            let missed: Vec<bool> = rest.iter().map(|&i| vecs[i].as_ref().is_some_and(|v| known_span.depends(v))).collect();
            for (k, i) in rest.into_iter().enumerate() {
                let f = &census.facts[i];
                if self.prover.egraph.census_known(f) { lv.by_ar += 1; continue; }
                if missed[k] {
                    lv.ar_missed += 1;
                    if std::env::var("GS_DEBUG_MISSED").is_ok() {
                        let eg = &self.prover.egraph;
                        let name = |f: &CensusFact| format!("{}({})", f.kind, f.objs.iter().map(|o| eg.entities[o.0].name.clone()).collect::<Vec<_>>().join(" "));
                        println!("AR_MISSED	{}	{}	{}", f.kind, f.degree, name(f));
                        // どの既知の事実の何倍の和か。
                        let mut pe = crate::mmp_core::ProvEliminator::default();
                        for j in 0..census.facts.len() { if in_span[j] && let Some(v) = &vecs[j] { pe.insert(v, j); } }
                        if let Some(v) = &vecs[i] && let Some(src) = pe.explain(v) {
                            for (j, c) in src { let (a, b) = crate::mmp_core::rational(c); println!("AR_MISSED_USES	{}/{}	{}", a, b, name(&census.facts[j])); }
                        }
                    }
                }
                else if let Some(v) = &vecs[i] && known_span.depends(v) { lv.dependent += 1; continue; }
                let remaining = self.wu_remaining();
                if !wu_ok || remaining == 0 { lv.unproved += 1; continue; }
                let Some((kind, args)) = self.census_target(f) else { lv.unproved += 1; continue };
                let cap = cap.min(remaining);
                let (r, mults, _) = self.prover.egraph.symbolic_fact_with(&kind, &args, MAX_TERMS, cap, memo);
                self.prover.egraph.spiral_prop_work += mults.min(cap) / WU_MULTS_PER_WORK;
                if r == Some(true) && self.close_by_wu(&kind, &args, MULT_THEOREM) {
                    lv.by_wu += 1;
                    proved_any = true;
                    if let Some(v) = &vecs[i] { known_span.insert(v); in_span[i] = true; }
                } else {
                    lv.unproved += 1;
                    if std::env::var("GS_DEBUG_UNPROVED").is_ok() {
                        let eg = &self.prover.egraph;
                        println!("UNPROVED	{}	{}	{}	{:?}	{}", f.kind, f.degree, f.objs.iter().map(|o| eg.entities[o.0].name.clone()).collect::<Vec<_>>().join(" "), r, mults);
                    }
                }
            }
            // 従属な事実は、次の次数の AR(と段の終わりの AR)に導かせる。
            pending_ar |= proved_any;
            println!("  📶 [次数 {}{}] 事実 {}(既知 {}、AR で {}、乗法的関係を示した {}、示せない {}、従属なので AR に任せた {}、従属だが AR が出せず示しにいった {})",
                d, if round > 0 { format!("・補助作図 {} 回の後", round) } else { String::new() },
                lv.facts, lv.known, lv.by_ar, lv.by_wu, lv.unproved, lv.dependent, lv.ar_missed);
            levels.push(lv);
        }
        if pending_ar { self.prover.egraph.apply_congruence_closure(); self.run_ar(); }
    }

    /// 次数の順の補助作図を作る。作ったら名前を返す。
    fn add_degree_aux(&mut self, kind: AuxKind) -> Option<String> {
        let name = |eg: &EGraph, x: ClassId| eg.entities[x.0].name.clone();
        let eg = &self.prover.egraph;
        let (n, def) = match kind {
            AuxKind::Midpoint(a, b) => (format!("Mid_{}_{}_(Deg)", name(eg, a), name(eg, b)), Definition::Midpoint(a, b)),
            AuxKind::Intersection(l1, l2) => (format!("X_{}_{}_(Deg)", name(eg, l1), name(eg, l2)), Definition::Intersection(l1, l2)),
            AuxKind::Foot(p, l) => {
                let (pn, ln) = (name(eg, p), name(eg, l));
                let perp = self.add_aux(format!("Perp_{}_{}_(Deg)", pn, ln), Definition::PerpendicularLine(l, p), EntityType::Line, EntityOrigin::DegreeAux, None)?;
                (format!("Foot_{}_{}_(Deg)", pn, ln), Definition::Intersection(l, perp))
            }
            AuxKind::Second(p, l, c) => (format!("Second_{}_{}_{}_(Deg)", name(eg, p), name(eg, l), name(eg, c)), Definition::SecondIntersectionOfLineAndConic(p, l, c)),
        };
        self.add_aux(n.clone(), def, EntityType::Point, EntityOrigin::DegreeAux, None)?;
        Some(n)
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

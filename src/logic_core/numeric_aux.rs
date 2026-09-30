//! 🌟 数値で選ぶ補助作図(`--numeric-aux`)。
//!
//! 補助作図の候補(2直線の交点・中点・点を通る垂線や平行線と直線の交点・直線や円との第2交点)を、図に足さずに
//! 固定座標(mmp_core/fixed_coords.rs)の上だけで試作し、**作った結果として新しい一致が生まれる**ものだけを作る:
//! 既にある直線・円に乗る、既にある点と重なる、熱い点どうしと新しく共円・共線になる。
//! 需要(マッチが欲しがって空振りした回数)は探索の副作用で、何を作ると何が起きるかは見ていない(改善候補 b33)。
//! 本当に効く補助作図は、作ると図に新しい一致が生まれるもの ― それを座標で先に確かめる(b36、CEGAR の点版)。
//! 固定座標では候補1つの評価が値の計算1回で済む。

use super::BlackboardEngine;
use crate::mmp_calculators;
use crate::mmp_core::{point_lies_on, ClassId, Definition, EntityOrigin, EntityType};
use crate::mmp_math::ModInt;

/// 候補を作る元にする熱い点・直線の数。
const HOT_POINTS: usize = 12;
const HOT_LINES: usize = 14;
/// 全体の上限(図が膨らみ続けると1回の run_step が長くなる)。
const TOTAL: usize = 40;
/// 最後の手(手が全部尽きたとき)で作る数と点数の下限(新しい一致を1つも生まないものは作らない)。
pub(crate) const LAST_PER_STALL: usize = 3;
pub(crate) const LAST_MIN_SCORE: u32 = 2;
/// 行き詰まりのたびに試すときは、新しい一致を多く生む候補だけを少しだけ作る(作りすぎると他の解の道筋を乱す)。
pub(crate) const EARLY_PER_STALL: usize = 2;
pub(crate) const EARLY_MIN_SCORE: u32 = 6;

#[derive(Clone, Debug)]
enum Cand {
    Inter(ClassId, ClassId),
    Mid(ClassId, ClassId),
    /// 点 p を通り直線 l に垂直な直線と、直線 m の交点(m = l なら垂線の足)。
    PerpInter { l: ClassId, p: ClassId, m: ClassId },
    /// 点 p を通り直線 l に平行な直線と、直線 m の交点。
    ParInter { l: ClassId, p: ClassId, m: ClassId },
    /// 点 p を通る直線 line と二次曲線 conic のもう一方の交点。
    SecondLC { p: ClassId, line: ClassId, conic: ClassId },
    /// 点 p を共有する2円のもう一方の交点。
    SecondCC { p: ClassId, c1: ClassId, c2: ClassId },
}

impl Cand {
    /// 定義に使った曲線(これに乗るのは当たり前なので数えない)。
    fn defining_curves(&self) -> Vec<ClassId> {
        match *self {
            Cand::Inter(a, b) => vec![a, b],
            Cand::Mid(..) => vec![],
            Cand::PerpInter { m, .. } | Cand::ParInter { m, .. } => vec![m],
            Cand::SecondLC { line, conic, .. } => vec![line, conic],
            Cand::SecondCC { c1, c2, .. } => vec![c1, c2],
        }
    }
    fn defining_points(&self) -> Vec<ClassId> {
        match *self {
            Cand::Inter(..) => vec![],
            Cand::Mid(a, b) => vec![a, b],
            Cand::PerpInter { p, .. } | Cand::ParInter { p, .. } | Cand::SecondLC { p, .. } | Cand::SecondCC { p, .. } => vec![p],
        }
    }
}

impl BlackboardEngine {
    /// 補助作図の候補を座標で試作し、新しい一致を最も多く生むものを作る。固定座標が使えない問題では何もしない。
    pub fn resolve_numeric_aux(&mut self, min_score: u32, per_stall: usize) -> bool {
        if self.numeric_aux_added >= TOTAL { return false; }
        let eg = &self.prover.egraph;
        if !eg.fixed_active() { return false; }
        let ks = eg.fixed_samples();
        let linf = eg.line_infinity;
        let reps_of = |ty: EntityType| -> Vec<ClassId> {
            (0..eg.entities.len()).map(ClassId)
                .filter(|&id| eg.get_rep(id) == id && eg.entities[id.0].entity_type == ty && eg.entities[id.0].is_active())
                .filter(|&id| id != linf && !(ty == EntityType::Point && eg.is_connected(id, linf)))
                .collect()
        };
        let by_heat = |mut v: Vec<ClassId>, n: usize| -> Vec<ClassId> {
            v.sort_by(|a, b| eg.entities[b.0].heat().partial_cmp(&eg.entities[a.0].heat())
                .unwrap_or(std::cmp::Ordering::Equal).then_with(|| a.0.cmp(&b.0)));
            v.truncate(n);
            v
        };
        let points = reps_of(EntityType::Point);
        let lines = reps_of(EntityType::Line);
        let conics = reps_of(EntityType::Conic);
        let hp = by_heat(points.clone(), HOT_POINTS);
        let hl = by_heat(lines.clone(), HOT_LINES);

        // 全標本での値。値の定まらないものは比べる相手から外す。
        let values = |ids: &[ClassId]| -> Vec<(ClassId, Vec<Vec<ModInt>>)> {
            ids.iter().filter_map(|&id| {
                let v: Option<Vec<Vec<ModInt>>> = (0..ks).map(|k| eg.class_value(id, k)).collect();
                v.map(|v| (id, v))
            }).collect()
        };
        let pts_v = values(&points);
        let lines_v = values(&lines);
        let conics_v = values(&conics);
        let hp_v = values(&hp);

        // 熱い点どうしの、まだ図に無い直線と円(新しい共線・共円の相手)。
        let mut new_lines: Vec<Vec<Vec<ModInt>>> = Vec::new();
        for i in 0..hp_v.len() {
            for j in (i + 1)..hp_v.len() {
                let (a, b) = (hp_v[i].0, hp_v[j].0);
                if lines.iter().any(|&l| eg.is_connected(a, l) && eg.is_connected(b, l)) { continue; }
                let v: Option<Vec<Vec<ModInt>>> = (0..ks).map(|k| {
                    let r = mmp_calculators::calc_line_through_points(&hp_v[i].1[k], &hp_v[j].1[k]);
                    (!r.is_empty()).then_some(r)
                }).collect();
                if let Some(v) = v { new_lines.push(v); }
            }
        }
        let mut new_circles: Vec<Vec<Vec<ModInt>>> = Vec::new();
        for i in 0..hp_v.len() {
            for j in (i + 1)..hp_v.len() {
                for l in (j + 1)..hp_v.len() {
                    let (a, b, c) = (hp_v[i].0, hp_v[j].0, hp_v[l].0);
                    if conics.iter().any(|&q| eg.is_connected(a, q) && eg.is_connected(b, q) && eg.is_connected(c, q)) { continue; }
                    let v: Option<Vec<Vec<ModInt>>> = (0..ks).map(|k| {
                        let r = mmp_calculators::calc_circumcircle(&hp_v[i].1[k], &hp_v[j].1[k], &hp_v[l].1[k]);
                        (!r.is_empty() && r.iter().any(|x| x.0 != 0)).then_some(r)
                    }).collect();
                    if let Some(v) = v { new_circles.push(v); }
                }
            }
        }

        // 候補を並べる(既に図にあるものは除く)。
        let has = |d: Definition| eg.live_memo(&eg.normalize_definition(&d));
        let mut cands: Vec<Cand> = Vec::new();
        for i in 0..hl.len() {
            for j in (i + 1)..hl.len() {
                if !has(Definition::Intersection(hl[i], hl[j])) { cands.push(Cand::Inter(hl[i], hl[j])); }
            }
        }
        for i in 0..hp.len() {
            for j in (i + 1)..hp.len() {
                if !has(Definition::Midpoint(hp[i], hp[j])) { cands.push(Cand::Mid(hp[i], hp[j])); }
            }
        }
        for &p in &hp {
            for &l in &hl {
                for &m in &hl {
                    cands.push(Cand::PerpInter { l, p, m });
                    if m != l && !eg.is_connected(p, l) { cands.push(Cand::ParInter { l, p, m }); }
                }
            }
        }
        for &c in &conics {
            let on_c: Vec<ClassId> = points.iter().copied().filter(|&p| eg.is_connected(p, c)).collect();
            for &p in &on_c {
                for &line in &lines {
                    if eg.is_connected(p, line) && !has(Definition::SecondIntersectionOfLineAndConic(p, line, c)) {
                        cands.push(Cand::SecondLC { p, line, conic: c });
                    }
                }
                for &c2 in &conics {
                    if c2.0 > c.0 && eg.is_connected(p, c2) && !has(Definition::SecondIntersectionOfCircles(p, c, c2)) {
                        cands.push(Cand::SecondCC { p, c1: c, c2 });
                    }
                }
            }
        }

        let eq_all = |a: &[Vec<ModInt>], b: &[Vec<ModInt>]| (0..ks).all(|k| crate::mmp_core::EGraph::numeric_values_proportional(&a[k], &b[k]));
        let mut scored: Vec<(u32, f64, Cand)> = Vec::new();
        for cand in cands {
            let Some(x) = (0..ks).map(|k| self.candidate_value(&cand, k)).collect::<Option<Vec<Vec<ModInt>>>>() else { continue };
            // 無限遠点(平行な2直線の交点)は既存の方向なので作らない。
            if x.iter().any(|v| v.len() != 3 || v[2].0 == 0) { continue; }
            let curves = cand.defining_curves();
            let parents = cand.defining_points();
            // 当たり前の接続(定義に使った曲線と図の上で同じ曲線、中点なら両端を通る直線)は数えない。
            let curve_vals: Vec<Vec<Vec<ModInt>>> = curves.iter().filter_map(|&c| (0..ks).map(|k| eg.class_value(c, k)).collect()).collect();
            let parent_vals: Vec<Vec<Vec<ModInt>>> = parents.iter().filter_map(|&q| (0..ks).map(|k| eg.class_value(q, k)).collect()).collect();
            let trivial_line = |lv: &[Vec<ModInt>]| -> bool {
                curve_vals.iter().any(|cv| eq_all(cv, lv))
                    || (matches!(cand, Cand::Mid(..)) && parent_vals.len() == 2
                        && parent_vals.iter().all(|pv| (0..ks).all(|k| point_lies_on(&pv[k], &lv[k], EntityType::Line))))
            };
            let mut score = 0u32;
            let mut is_existing = false;
            for (q, qv) in &pts_v {
                if !eq_all(&x, qv) { continue; }
                // 定義に使った曲線に既に乗っている点と重なるなら、それはただの既存の点。
                if parents.contains(q) || curves.iter().all(|&c| eg.is_connected(*q, c)) { is_existing = true; break; }
                score += 2;
            }
            if is_existing { continue; }
            for (l, lv) in &lines_v {
                if !curves.contains(l) && !trivial_line(lv) && (0..ks).all(|k| point_lies_on(&x[k], &lv[k], EntityType::Line)) { score += 1; }
            }
            for (c, cv) in &conics_v {
                if !curves.contains(c) && !curve_vals.iter().any(|v| eq_all(v, cv)) && (0..ks).all(|k| point_lies_on(&x[k], &cv[k], EntityType::Conic)) { score += 3; }
            }
            for lv in &new_lines {
                if !trivial_line(lv) && (0..ks).all(|k| point_lies_on(&x[k], &lv[k], EntityType::Line)) { score += 1; }
            }
            for cv in &new_circles {
                if (0..ks).all(|k| point_lies_on(&x[k], &cv[k], EntityType::Conic)) { score += 2; }
            }
            if score < min_score { continue; }
            let heat: f64 = parents.iter().chain(curves.iter()).map(|id| eg.entities[id.0].heat()).sum();
            scored.push((score, heat, cand));
        }
        scored.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal))
            .then_with(|| format!("{:?}", a.2).cmp(&format!("{:?}", b.2))));

        let mut applied = false;
        let mut made = 0;
        for (score, _, cand) in scored {
            if made >= per_stall || self.numeric_aux_added >= TOTAL { break; }
            if self.materialize_candidate(&cand, score) {
                made += 1;
                self.numeric_aux_added += 1;
                applied = true;
            }
        }
        if applied { self.settle_and_resweep(); }
        applied
    }

    /// 候補の(標本 k での)値。図には何も足さない。
    fn candidate_value(&self, cand: &Cand, k: usize) -> Option<Vec<ModInt>> {
        let eg = &self.prover.egraph;
        let def_val = |d: Definition| eg.fixed_def_value(&d, k);
        let meet = |a: Vec<ModInt>, m: ClassId| -> Option<Vec<ModInt>> {
            let r = mmp_calculators::calc_intersection(&a, &eg.class_value(m, k)?);
            (!r.is_empty() && r.iter().any(|x| x.0 != 0)).then_some(r)
        };
        match *cand {
            Cand::Inter(a, b) => def_val(Definition::Intersection(a, b)),
            Cand::Mid(a, b) => def_val(Definition::Midpoint(a, b)),
            Cand::PerpInter { l, p, m } => meet(def_val(Definition::PerpendicularLine(l, p))?, m),
            Cand::ParInter { l, p, m } => meet(def_val(Definition::ParallelLine(l, p))?, m),
            Cand::SecondLC { p, line, conic } => def_val(Definition::SecondIntersectionOfLineAndConic(p, line, conic)),
            Cand::SecondCC { p, c1, c2 } => def_val(Definition::SecondIntersectionOfCircles(p, c1, c2)),
        }
    }

    /// 候補を図に足す(垂線・平行線が要るならそれも)。値の定まらない作図は add_aux が見送る。
    fn materialize_candidate(&mut self, cand: &Cand, score: u32) -> bool {
        let name_of = |s: &Self, id: ClassId| s.prover.egraph.entities[id.0].name.clone();
        let tag = format!("(NumericAux{})", score);
        let (name, def, origin) = match *cand {
            Cand::Inter(a, b) => (format!("Pt_{}_{}_{}", name_of(self, a), name_of(self, b), tag), Definition::Intersection(a, b), EntityOrigin::PointDemand),
            Cand::Mid(a, b) => (format!("Mid_{}_{}_{}", name_of(self, a), name_of(self, b), tag), Definition::Midpoint(a, b), EntityOrigin::MidDemand),
            Cand::PerpInter { l, p, m } | Cand::ParInter { l, p, m } => {
                let perp = matches!(cand, Cand::PerpInter { .. });
                let ldef = if perp { Definition::PerpendicularLine(l, p) } else { Definition::ParallelLine(l, p) };
                let norm = self.prover.egraph.normalize_definition(&ldef);
                let aux_line = match self.prover.egraph.memo.get(&norm).copied() {
                    Some(id) => { self.prover.egraph.revive(id); self.prover.egraph.get_rep(id) }
                    None => {
                        let lname = format!("{}_{}_{}_{}", if perp { "Perp" } else { "Par" }, name_of(self, l), name_of(self, p), tag);
                        match self.add_aux(lname, ldef, EntityType::Line, EntityOrigin::LineDemand, Some(0.5)) { Some(id) => id, None => return false }
                    }
                };
                let aux_line = self.prover.egraph.get_rep(aux_line);
                let m = self.prover.egraph.get_rep(m);
                if aux_line == m { return false; }
                (format!("Pt_{}_{}_{}", name_of(self, aux_line), name_of(self, m), tag), Definition::Intersection(aux_line, m), EntityOrigin::PointDemand)
            }
            Cand::SecondLC { p, line, conic } => (format!("Second_{}_{}_{}", name_of(self, p), name_of(self, line), tag),
                Definition::SecondIntersectionOfLineAndConic(p, line, conic), EntityOrigin::SecondDemand),
            Cand::SecondCC { p, c1, c2 } => (format!("Second_{}_{}_{}", name_of(self, p), name_of(self, c1), tag),
                Definition::SecondIntersectionOfCircles(p, c1, c2), EntityOrigin::SecondDemand),
        };
        if self.prover.egraph.live_memo(&self.prover.egraph.normalize_definition(&def)) { return false; }
        println!("  💡 [数値で選ぶ補助作図] {} を生成(新しい一致の点数 {})", name, score);
        self.add_aux(name, def, EntityType::Point, origin, Some(0.5)).is_some()
    }
}

//! 検算専用の代数的な置き方(backlog b46)。前提どおりに自由点を置くのに平方根などが要る図(直線と円の両方に乗る点、
//! 2つの円に乗る点、「OP = OA」や直角のような方程式で与えた前提)でも、固定座標を置けるようにする。
//!
//! 前提を持つ自由点を1つの媒介変数 t で動かし(前提の直線の上、既知の点を通る二次曲線の上、無ければ任意の直線の上)、
//! 残りの前提を t の有理関数として標本から復元して、その分子の根を有限体の上で求める(2次なら平方根にあたる)。
//! 求めた座標は検算(固定座標)にだけ使い、次数の評価(動点法)には使わない ― 代数的な点の次数は計算が面倒になる。
//! 今の置き方で前提が成り立つ図では呼ばない(探索の結果を変えない)。

use super::eval::modint_construct;
use super::fixed_coords::point_lies_on;
use super::{ClassId, Definition, EGraph, EntityType};
use crate::mmp_math::{ModInt, PRIME};
use rustc_hash::FxHashMap;

pub(crate) type Vars = FxHashMap<String, ModInt>;

/// 置き方専用の乱数(探索の乱数は消費しない)。
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> ModInt {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        ModInt::new((self.0 % (PRIME as u64 - 2)) as i64 + 2)
    }
}

// ---------- 有限体の上の多項式(係数は低次から) ----------

type Poly = Vec<ModInt>;

fn trim(mut a: Poly) -> Poly {
    while a.last().is_some_and(|c| c.0 == 0) { a.pop(); }
    a
}

fn pmul(a: &Poly, b: &Poly) -> Poly {
    if a.is_empty() || b.is_empty() { return Vec::new(); }
    let mut out = vec![ModInt::new(0); a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() { out[i + j] += x * y; }
    }
    trim(out)
}

/// (商, 余り)。m は 0 でないこと。
fn pdivmod(a: &Poly, m: &Poly) -> (Poly, Poly) {
    let m = trim(m.clone());
    let mut r = trim(a.clone());
    if r.len() < m.len() { return (Vec::new(), r); }
    let inv = m[m.len() - 1].inv();
    let mut q = vec![ModInt::new(0); r.len() - m.len() + 1];
    while r.len() >= m.len() && !r.is_empty() {
        let shift = r.len() - m.len();
        let c = r[r.len() - 1] * inv;
        q[shift] = c;
        for (i, &x) in m.iter().enumerate() { r[shift + i] -= c * x; }
        r = trim(r);
    }
    (trim(q), r)
}

fn pgcd(a: &Poly, b: &Poly) -> Poly {
    let (mut a, mut b) = (trim(a.clone()), trim(b.clone()));
    while !b.is_empty() {
        let (_, r) = pdivmod(&a, &b);
        a = b;
        b = r;
    }
    if let Some(&lead) = a.last() { let inv = lead.inv(); a.iter_mut().for_each(|c| *c *= inv); }
    a
}

/// base^e mod m。
fn ppow_mod(base: &Poly, mut e: u64, m: &Poly) -> Poly {
    let mut result: Poly = vec![ModInt::new(1)];
    let mut b = pdivmod(base, m).1;
    while e > 0 {
        if e & 1 == 1 { result = pdivmod(&pmul(&result, &b), m).1; }
        b = pdivmod(&pmul(&b, &b), m).1;
        e >>= 1;
    }
    result
}

fn psub(a: &Poly, b: &Poly) -> Poly {
    let n = a.len().max(b.len());
    let mut out = vec![ModInt::new(0); n];
    for (i, &x) in a.iter().enumerate() { out[i] += x; }
    for (i, &x) in b.iter().enumerate() { out[i] -= x; }
    trim(out)
}

fn peval(a: &Poly, t: ModInt) -> ModInt {
    a.iter().rev().fold(ModInt::new(0), |acc, &c| acc * t + c)
}

/// f の有限体の中の根(重複なし)。gcd(f, t^p − t) で1次因子の積を取り出し、(t+a)^((p−1)/2) − 1 との gcd で分ける。
fn roots(f: &Poly, rng: &mut Rng) -> Vec<ModInt> {
    let f = trim(f.clone());
    if f.len() <= 1 { return Vec::new(); }
    let x: Poly = vec![ModInt::new(0), ModInt::new(1)];
    let g = pgcd(&f, &psub(&ppow_mod(&x, PRIME as u64, &f), &x));
    let mut out = Vec::new();
    split(&g, rng, &mut out, 0);
    out.sort_by_key(|r| r.0);
    out
}

fn split(g: &Poly, rng: &mut Rng, out: &mut Vec<ModInt>, depth: usize) {
    if g.len() <= 1 || depth > 64 { return; }
    if g.len() == 2 { out.push(-g[0] / g[1]); return; }
    for _ in 0..32 {
        let a = rng.next();
        let h = pgcd(g, &psub(&ppow_mod(&vec![a, ModInt::new(1)], (PRIME as u64 - 1) / 2, g), &vec![ModInt::new(1)]));
        if h.len() > 1 && h.len() < g.len() {
            split(&h, rng, out, depth + 1);
            split(&pdivmod(g, &h).0, rng, out, depth + 1);
            return;
        }
    }
}

/// 標本 (t_k, h_k) から h = N/D(次数 ≤ d)を復元する。前半で解いて、残りの標本で確かめる。
fn reconstruct(samples: &[(ModInt, ModInt)], d: usize) -> Option<(Poly, Poly)> {
    let n_eq = 2 * d + 1;
    if samples.len() < n_eq + 2 { return None; }
    let cols = 2 * d + 2;
    let mut m: Vec<Vec<ModInt>> = samples[..n_eq].iter().map(|&(t, h)| {
        let mut row = Vec::with_capacity(cols);
        let mut p = ModInt::new(1);
        for _ in 0..=d { row.push(p); p *= t; }
        let mut p = ModInt::new(1);
        for _ in 0..=d { row.push(-(h * p)); p *= t; }
        row
    }).collect();
    // 行簡約して、主成分の無い列を1つ 1 にした解を取る。
    let mut pivots = Vec::new();
    let mut r = 0;
    for c in 0..cols {
        let Some(i) = (r..m.len()).find(|&i| m[i][c].0 != 0) else { continue };
        m.swap(r, i);
        let inv = m[r][c].inv();
        for x in m[r].iter_mut() { *x *= inv; }
        for i in 0..m.len() {
            if i != r && m[i][c].0 != 0 {
                let f = m[i][c];
                for j in 0..cols { let v = m[r][j]; m[i][j] -= f * v; }
            }
        }
        pivots.push(c);
        r += 1;
        if r == m.len() { break; }
    }
    let free = (0..cols).find(|c| !pivots.contains(c))?;
    let mut sol = vec![ModInt::new(0); cols];
    sol[free] = ModInt::new(1);
    for (row, &pc) in pivots.iter().enumerate() { sol[pc] = -m[row][free]; }
    let (num, den) = (trim(sol[..=d].to_vec()), trim(sol[d + 1..].to_vec()));
    if den.is_empty() { return None; }
    for &(t, h) in &samples[n_eq..] {
        if (peval(&num, t) - h * peval(&den, t)).0 != 0 { return None; }
    }
    Some((num, den))
}

// ---------- 前提と置き方 ----------

#[derive(Clone, Copy, Debug)]
enum Constraint {
    /// 探索の前にマージした組(元の定義どうしの値が比例する)。
    Merge(ClassId, ClassId),
    /// 自由点が前提の曲線に乗る。
    OnCurve(ClassId, ClassId),
}

impl EGraph {
    /// 前提どおりの座標を標本の数だけ作る(置けなければ None)。前提を持つ自由点を、作った順に1つずつ解いて置く。
    pub(crate) fn algebraic_premise_samples(&self) -> Option<Vec<Vars>> {
        let points: Vec<ClassId> = {
            let mut v: Vec<ClassId> = self.all_free_points().into_iter().map(|p| self.get_rep(p)).collect();
            v.sort_by_key(|p| p.0);
            v.dedup();
            v
        };
        let constraints = self.premise_constraints();
        let mut owned: FxHashMap<usize, Vec<Constraint>> = FxHashMap::default();
        for c in &constraints {
            if let Some(o) = self.constraint_owner(c) { owned.entry(o.0).or_default().push(*c); }
        }
        // 自由点ごとに、それに依存する実体(置いた点が退化した配置を作っていないかを見る)。
        let mut dependents: FxHashMap<usize, Vec<ClassId>> = FxHashMap::default();
        for i in 0..self.entities.len() {
            let mut seen = rustc_hash::FxHashSet::default();
            let mut anc = Vec::new();
            self.original_free_ancestors(ClassId(i), &mut seen, &mut anc);
            for a in anc { dependents.entry(a.0).or_default().push(ClassId(i)); }
        }
        let lines_and_points: Vec<ClassId> = (0..self.entities.len()).map(ClassId)
            .filter(|&e| matches!(self.entities[e.0].entity_type, EntityType::Point | EntityType::Line)).collect();
        // 有限体では交点が無いこともある(判別式が平方剰余でない)ので、置けなければ乱数を変えて最初から置き直す。
        (0..self.fixed_samples()).map(|k| (0..40u64).find_map(|attempt| {
            let mut rng = Rng(0x9E37_79B9_7F4A_7C15 ^ ((k as u64 + 1) * 0xD1B5_4A32_D192_ED03) ^ attempt.wrapping_mul(0x2545_F491_4F6C_DD1D));
            let mut vars = Vars::default();
            for &p in &points {
                let cs = owned.get(&p.0).cloned().unwrap_or_default();
                let deps = dependents.get(&p.0).cloned().unwrap_or_default();
                let dep_set: rustc_hash::FxHashSet<usize> = deps.iter().map(|d| d.0).collect();
                let others: Vec<ClassId> = lines_and_points.iter().copied().filter(|e| !dep_set.contains(&e.0) && *e != p).collect();
                if !self.place_solving(p, &cs, &deps, &others, &mut vars, &mut rng) {
                    if std::env::var("GS_DEBUG_ALG").is_ok() {
                        println!("  ALG_DEBUG 置けない点 {} 前提 {:?}", self.entities[p.0].name, cs.iter().map(|c| self.describe_constraint(c)).collect::<Vec<_>>());
                    }
                    return None;
                }
            }
            if std::env::var("GS_DEBUG_ALG").is_ok() {
                for c in &constraints { if !self.constraint_holds(c, &vars) { println!("  ALG_DEBUG 最後に成り立たない前提 {}", self.describe_constraint(c)); } }
            }
            constraints.iter().all(|c| self.constraint_holds(c, &vars)).then_some(vars)
        })).collect()
    }

    fn premise_constraints(&self) -> Vec<Constraint> {
        let mut out = Vec::new();
        for i in 0..self.entities.len() {
            let rep = self.get_rep(ClassId(i));
            if rep.0 == i { continue; }
            let skip = |id: ClassId| matches!(self.entities[id.0].original_definition, Definition::FreePoint | Definition::GivenPoint | Definition::ConstantHomogeneous(..))
                && id != self.ang90 && id != self.ang0;
            if skip(ClassId(i)) || skip(rep) { continue; }
            out.push(Constraint::Merge(ClassId(i), rep));
        }
        if let Some(pairs) = &self.premise_incidences {
            for &(p, c) in pairs { out.push(Constraint::OnCurve(self.get_rep(p), c)); }
        }
        out
    }

    /// 前提を解く担当の自由点: 関わる自由点のうち最後に作ったもの(それより前の点は置き済み)。
    fn constraint_owner(&self, c: &Constraint) -> Option<ClassId> {
        let ids = match *c { Constraint::Merge(a, b) => vec![a, b], Constraint::OnCurve(p, curve) => vec![p, curve] };
        let mut anc = Vec::new();
        let mut seen = rustc_hash::FxHashSet::default();
        for id in ids { self.original_free_ancestors(id, &mut seen, &mut anc); }
        anc.into_iter().max_by_key(|p| p.0)
    }

    fn original_free_ancestors(&self, id: ClassId, seen: &mut rustc_hash::FxHashSet<usize>, out: &mut Vec<ClassId>) {
        if !seen.insert(id.0) { return; }
        match &self.entities[id.0].original_definition {
            Definition::FreePoint => out.push(self.get_rep(id)),
            Definition::GivenPoint | Definition::ConstantHomogeneous(..) => {}
            def => for q in def.get_parents() { self.original_free_ancestors(q, seen, out); },
        }
    }

    /// 元の定義から(マージに依存せず)値を作る。
    fn original_value(&self, id: ClassId, vars: &Vars, memo: &mut FxHashMap<usize, Option<Vec<ModInt>>>) -> Option<Vec<ModInt>> {
        if let Some(v) = memo.get(&id.0) { return v.clone(); }
        let v = match &self.entities[id.0].original_definition {
            // 虚円点のような定数(ConstantHomogeneous)は定義どおりに計算する(ここで値を作らないと有向角が定まらず、角の前提を
            // 比べずに素通りさせていた)。
            Definition::FreePoint | Definition::GivenPoint => self.constant_or_free_value(id, vars),
            def => {
                let def = def.clone();
                modint_construct(self, &def, &mut |q| self.original_value(q, vars, memo))
            }
        };
        memo.insert(id.0, v.clone());
        v
    }

    fn constraint_holds(&self, c: &Constraint, vars: &Vars) -> bool {
        let mut memo = FxHashMap::default();
        match *c {
            Constraint::Merge(a, b) => match (self.original_value(a, vars, &mut memo), self.original_value(b, vars, &mut memo)) {
                (Some(x), Some(y)) => Self::numeric_values_proportional(&x, &y),
                _ => true, // 値が定まらない組は(今の検算と同じく)比べない
            },
            Constraint::OnCurve(p, curve) => match (self.original_value(p, vars, &mut memo), self.original_value(curve, vars, &mut memo)) {
                (Some(x), Some(v)) => point_lies_on(&x, &v, self.entities[curve.0].entity_type),
                _ => false,
            },
        }
    }

    /// 前提の残差(0 なら成り立つ)。比例は 2×2 小行列式の乱数の重みつきの和、接続は曲線の式への代入。
    fn residual(&self, c: &Constraint, vars: &Vars, weights: &[ModInt]) -> Option<ModInt> {
        let mut memo = FxHashMap::default();
        match *c {
            Constraint::Merge(a, b) => {
                let (x, y) = (self.original_value(a, vars, &mut memo)?, self.original_value(b, vars, &mut memo)?);
                if x.len() != y.len() { return None; }
                let mut s = ModInt::new(0);
                let mut w = 0;
                for i in 0..x.len() {
                    for j in (i + 1)..x.len() { s += weights[w % weights.len()] * (x[i] * y[j] - x[j] * y[i]); w += 1; }
                }
                Some(s)
            }
            Constraint::OnCurve(p, curve) => {
                let (x, v) = (self.original_value(p, vars, &mut memo)?, self.original_value(curve, vars, &mut memo)?);
                if x.len() < 3 { return None; }
                let (px, py, pz) = (x[0], x[1], x[2]);
                match self.entities[curve.0].entity_type {
                    EntityType::Line if v.len() >= 3 => Some(v[0] * px + v[1] * py + v[2] * pz),
                    EntityType::Conic if v.len() >= 6 =>
                        Some(v[0] * px * px + v[1] * px * py + v[2] * py * py + v[3] * px * pz + v[4] * py * pz + v[5] * pz * pz),
                    _ => None,
                }
            }
        }
    }

    fn set_point(&self, p: ClassId, (x, y): (ModInt, ModInt), vars: &mut Vars) {
        let name = &self.entities[self.get_rep(p).0].name;
        vars.insert(format!("{}_x", name), x);
        vars.insert(format!("{}_y", name), y);
    }

    /// 自由点 p を、担当の前提 cs を全て満たすように置く。
    /// 置いた点に依存する実体が退化していないか: 値がゼロベクトル、または直線が等方的(虚円点を通る)。等方的な直線の
    /// 有向角は退化した値になり、角の前提が見かけ上成り立ってしまう(test_parallel で正しい平行を偽と判定した)。
    fn nondegenerate(&self, deps: &[ClassId], vars: &Vars) -> bool {
        let mut memo = FxHashMap::default();
        deps.iter().all(|&e| match self.original_value(e, vars, &mut memo) {
            None => true,
            Some(v) => {
                if v.iter().all(|x| x.0 == 0) { return false; }
                match self.entities[e.0].entity_type {
                    EntityType::Line if v.len() >= 3 && (v[0].0 != 0 || v[1].0 != 0) => (v[0] * v[0] + v[1] * v[1]).0 != 0,
                    _ => true,
                }
            }
        })
    }

    /// 置いた点 p が、p に依存しない既存の点と重なったり、前提でない既存の直線に乗ったりしていないか(第2交点として既知の
    /// 点そのものを選ぶ、3点が共線の退化した三角形を選ぶ、などを捨てる)。
    fn generic_position(&self, p: ClassId, others: &[ClassId], premise_curves: &[ClassId], vars: &Vars) -> bool {
        let mut memo = FxHashMap::default();
        let Some(pv) = self.original_value(p, vars, &mut memo) else { return false };
        if pv.len() < 3 || pv[2].0 == 0 { return true; }
        others.iter().all(|&e| {
            let Some(v) = self.original_value(e, vars, &mut memo) else { return true };
            match self.entities[e.0].entity_type {
                EntityType::Point => v.len() < 3 || v[2].0 == 0 || !Self::numeric_values_proportional(&pv, &v),
                EntityType::Line => premise_curves.iter().any(|&c| self.get_rep(c) == self.get_rep(e))
                    || !point_lies_on(&pv, &v, EntityType::Line),
                _ => true,
            }
        })
    }

    fn place_solving(&self, p: ClassId, cs: &[Constraint], deps: &[ClassId], others: &[ClassId], vars: &mut Vars, rng: &mut Rng) -> bool {
        let premise_curves: Vec<ClassId> = cs.iter().filter_map(|c| match *c { Constraint::OnCurve(q, curve) if q == p => Some(curve), _ => None }).collect();
        if cs.is_empty() {
            for _ in 0..8 {
                self.set_point(p, (rng.next(), rng.next()), vars);
                if self.nondegenerate(deps, vars) && self.generic_position(p, others, &premise_curves, vars) { return true; }
            }
            return false;
        }
        // 媒介変数 t で動く点 P(t) を決める: 前提の直線の上、既知の点を通る二次曲線の上、無ければ任意の直線の上。
        let mut memo = FxHashMap::default();
        let mut used: Option<usize> = None;
        let mut param: Option<Box<dyn Fn(ModInt) -> Option<(ModInt, ModInt)>>> = None;
        for (i, c) in cs.iter().enumerate() {
            let Constraint::OnCurve(q, curve) = *c else { continue };
            if q != p || self.entities[curve.0].entity_type != EntityType::Line { continue };
            let Some(l) = self.original_value(curve, vars, &mut memo) else { continue };
            let (a, b, cc) = (l[0], l[1], l[2]);
            let base = if b.0 != 0 { (ModInt::new(0), -cc / b) } else if a.0 != 0 { (-cc / a, ModInt::new(0)) } else { continue };
            let dir = (b, -a);
            param = Some(Box::new(move |t| Some((base.0 + t * dir.0, base.1 + t * dir.1))));
            used = Some(i);
            break;
        }
        if param.is_none() {
            for (i, c) in cs.iter().enumerate() {
                let Constraint::OnCurve(q, curve) = *c else { continue };
                if q != p || self.entities[curve.0].entity_type != EntityType::Conic { continue };
                let (Some(v), Some(k)) = (self.original_value(curve, vars, &mut memo),
                    self.conic_known_point(curve).and_then(|k| self.original_value(k, vars, &mut memo))) else { continue };
                if v.len() < 6 || k.len() < 3 || k[2].0 == 0 { continue; }
                let (kx, ky) = (k[0] / k[2], k[1] / k[2]);
                param = Some(Box::new(move |t| {
                    // K + s(1, t) と二次曲線の、K でない方の交点。
                    let (ux, uy) = (ModInt::new(1), t);
                    let q2 = v[0] * ux * ux + v[1] * ux * uy + v[2] * uy * uy;
                    let l1 = ModInt::new(2) * v[0] * kx * ux + v[1] * (kx * uy + ky * ux) + ModInt::new(2) * v[2] * ky * uy + v[3] * ux + v[4] * uy;
                    if q2.0 == 0 { return None; }
                    let s = -l1 / q2;
                    Some((kx + s * ux, ky + s * uy))
                }));
                used = Some(i);
                break;
            }
        }
        let param = param.unwrap_or_else(|| {
            let (bx, by, dx, dy) = (rng.next(), rng.next(), rng.next(), rng.next());
            Box::new(move |t| Some((bx + t * dx, by + t * dy)))
        });
        let rest: Vec<Constraint> = cs.iter().enumerate().filter(|(i, _)| Some(*i) != used).map(|(_, c)| *c).collect();

        // 乱数の2点で既に成り立つ前提(定義から従うもの)は解かない。
        let weights: Vec<ModInt> = (0..16).map(|_| rng.next()).collect();
        let probe: Vec<ModInt> = (0..2).map(|_| rng.next()).collect();
        let mut real = Vec::new();
        for c in &rest {
            let holds = probe.iter().all(|&t| match param(t) {
                Some(xy) => { self.set_point(p, xy, vars); self.constraint_holds(c, vars) }
                None => false,
            });
            if !holds { real.push(*c); }
        }
        let try_t = |t: ModInt, vars: &mut Vars| -> bool {
            let Some(xy) = param(t) else { return false };
            self.set_point(p, xy, vars);
            cs.iter().all(|c| self.constraint_holds(c, vars)) && self.nondegenerate(deps, vars)
                && self.generic_position(p, others, &premise_curves, vars)
        };
        if std::env::var("GS_DEBUG_ALG").is_ok() {
            println!("  ALG_DEBUG 点 {} 前提 {} 件(媒介変数に使った {:?}) 解く前提 {:?}", self.entities[p.0].name, cs.len(),
                used.map(|i| self.describe_constraint(&cs[i])), real.iter().map(|c| self.describe_constraint(c)).collect::<Vec<_>>());
        }
        let Some(first) = real.first().copied() else {
            for _ in 0..8 { if try_t(rng.next(), vars) { return true; } }
            return false;
        };
        // 残差を t の有理関数として復元し、分子の根を試す。
        let mut samples = Vec::new();
        for _ in 0..40 {
            let t = rng.next();
            let Some(xy) = param(t) else { continue };
            self.set_point(p, xy, vars);
            if let Some(h) = self.residual(&first, vars, &weights) { samples.push((t, h)); }
            if samples.len() >= 26 { break; }
        }
        for d in 1..=10 {
            let Some((num, den)) = reconstruct(&samples, d) else { continue };
            for r in roots(&num, rng) {
                if peval(&den, r).0 == 0 { continue; }
                if try_t(r, vars) { return true; }
            }
            return false;
        }
        false
    }

    fn describe_constraint(&self, c: &Constraint) -> String {
        match *c {
            Constraint::Merge(a, b) => format!("{} ≡ {}", self.entities[a.0].name, self.entities[b.0].name),
            Constraint::OnCurve(p, q) => format!("{} ∈ {}", self.entities[p.0].name, self.entities[q.0].name),
        }
    }

    /// 二次曲線の定義から、それに乗っていることが保証された(無限遠でない)点。
    fn conic_known_point(&self, conic: ClassId) -> Option<ClassId> {
        match &self.entities[conic.0].original_definition {
            Definition::Circumcircle(p1, _, _) => Some(*p1),
            Definition::CircleCenterPoint(_, p) => Some(*p),
            Definition::ConicThrough5Points(p1, p2, p3, p4, p5) => [*p1, *p2, *p3, *p4, *p5].into_iter().find(|&q| !self.is_connected(q, self.line_infinity)),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn m(v: i64) -> ModInt { ModInt::new(v) }

    /// (t − 3)(t − 5)(t² + 7) の根は、有限体の中にあるものだけが出る。
    #[test]
    fn roots_of_a_product_of_linear_factors() {
        let f = pmul(&pmul(&vec![m(-3), m(1)], &vec![m(-5), m(1)]), &vec![m(7), m(0), m(1)]);
        let mut rng = Rng(12345);
        let r = roots(&f, &mut rng);
        assert!(r.contains(&m(3)) && r.contains(&m(5)));
        for x in &r { assert_eq!(peval(&f, *x).0, 0); }
    }

    /// 有理関数 (t² − 2)/(t + 1) を標本から復元できる。
    #[test]
    fn reconstructs_a_rational_function() {
        let samples: Vec<(ModInt, ModInt)> = (2..30).map(|t| { let t = m(t); (t, (t * t - m(2)) / (t + m(1))) }).collect();
        let (num, den) = (1..=4).find_map(|d| reconstruct(&samples, d)).expect("復元できるはず");
        for t in [m(100), m(12345)] { assert_eq!((peval(&num, t) / peval(&den, t)).0, ((t * t - m(2)) / (t + m(1))).0); }
    }
}

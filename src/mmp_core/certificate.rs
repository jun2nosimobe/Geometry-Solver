//! 🌟 次数を区切った多項式の線形結合による証明(Nullstellensatz の証拠を線形代数で探す、Macaulay 行列)。
//!
//! 点の座標を変数にし(作った点も代入せずに変数のまま)、作図と前提を低い次数の多項式 h_i(仮説)で書く。目標 g が
//! g = Σ q_i h_i(deg q_i ≤ D − deg h_i)と書けるかを、{m·h_i}(m は次数 D − deg h_i 以下の単項式)の張る空間に g が入るか
//! として法 P = 2⁶¹ − 1 の掃き出しで調べる。入れば、仮説の成り立つ全ての配置で g = 0(法 P の合同式として)。
//! Wu の方法(symbolic.rs)と違い、作図でない前提(与えた等式・接続)も仮説に入れられる。作図は代入しないので式は膨らまないが、
//! 証拠の次数 D が大きいと行列が大きくなる。退化した配置の成分では g が 0 にならないことがあり、その場合は証拠が見つからない。
//!
//! 仮説の書き方(自由点の最初の2つは相似で (0,0)・(1,0) に置く):
//! - 中点はそのまま代入(1次)。交点・もう一方の交点・外接円の中心などは変数にして条件を仮説に。
//! - 直線は (通る点, 方向)、円は (中心, 半径の2乗) の式で持ち、点 X が乗る条件は cross(X − 通る点, 方向) と |X − 中心|² − 半径²。
//! - 直線と円のもう一方の交点 X(既知の点 K): X は直線の上、(X + K − 2O)·方向 = 0(X ≠ K の解だけを取る一次の条件)。
//! - 2円のもう一方の交点 X: (X − K)·(O2 − O1) = 0、cross(X + K − 2O1, O2 − O1) = 0(K の中心線に関する鏡映)。

use rustc_hash::{FxHashMap, FxHashSet};

use super::{ClassId, Definition, EGraph, EntityType, Justification};

const P: u64 = (1 << 61) - 1;
fn mulm(a: u64, b: u64) -> u64 {
    let r = (a as u128) * (b as u128);
    let s = ((r as u64) & P) + ((r >> 61) as u64);
    if s >= P { s - P } else { s }
}
fn addm(a: u64, b: u64) -> u64 { let s = a + b; if s >= P { s - P } else { s } }
fn negm(a: u64) -> u64 { if a == 0 { 0 } else { P - a } }
fn powm(mut a: u64, mut e: u64) -> u64 { let mut r = 1; while e > 0 { if e & 1 == 1 { r = mulm(r, a); } a = mulm(a, a); e >>= 1; } r }
fn invm(a: u64) -> u64 { powm(a, P - 2) }
fn constm(x: i64) -> u64 { x.rem_euclid(P as i64) as u64 }

/// 単項式: 変数ごとの次数を 4 ビットずつ(変数 32 個まで、各次数 15 まで)。
type Mono = u128;
const MAX_VARS: usize = 32;
fn mono_deg(m: Mono) -> u32 { (0..MAX_VARS).map(|i| ((m >> (4 * i)) & 15) as u32).sum() }

#[derive(Clone, Debug, Default, PartialEq)]
struct Poly(FxHashMap<Mono, u64>);

impl Poly {
    fn c(x: i64) -> Poly { let mut t = FxHashMap::default(); let x = constm(x); if x != 0 { t.insert(0, x); } Poly(t) }
    fn var(i: usize) -> Poly { let mut t = FxHashMap::default(); t.insert(1u128 << (4 * i), 1); Poly(t) }
    fn is_zero(&self) -> bool { self.0.is_empty() }
    fn deg(&self) -> u32 { self.0.keys().map(|&m| mono_deg(m)).max().unwrap_or(0) }
    fn add(&self, o: &Poly) -> Poly {
        let mut t = self.0.clone();
        for (&m, &c) in &o.0 { let e = t.entry(m).or_insert(0); *e = addm(*e, c); if *e == 0 { t.remove(&m); } }
        Poly(t)
    }
    fn neg(&self) -> Poly { Poly(self.0.iter().map(|(&m, &c)| (m, negm(c))).collect()) }
    fn sub(&self, o: &Poly) -> Poly { self.add(&o.neg()) }
    fn scale(&self, k: u64) -> Poly { if k == 0 { return Poly::default(); } Poly(self.0.iter().map(|(&m, &c)| (m, mulm(c, k))).collect()) }
    fn mul(&self, o: &Poly) -> Option<Poly> {
        if self.deg() + o.deg() > 15 { return None; }
        let mut t: FxHashMap<Mono, u64> = FxHashMap::default();
        for (&m1, &c1) in &self.0 { for (&m2, &c2) in &o.0 { let e = t.entry(m1 + m2).or_insert(0); *e = addm(*e, mulm(c1, c2)); } }
        t.retain(|_, c| *c != 0);
        Some(Poly(t))
    }
}

type Pt = (Poly, Poly);
fn psub(a: &Pt, b: &Pt) -> Pt { (a.0.sub(&b.0), a.1.sub(&b.1)) }
fn cross2(a: &Pt, b: &Pt) -> Option<Poly> { Some(a.0.mul(&b.1)?.sub(&a.1.mul(&b.0)?)) }
fn dot2(a: &Pt, b: &Pt) -> Option<Poly> { Some(a.0.mul(&b.0)?.add(&a.1.mul(&b.1)?)) }
fn perp(a: &Pt) -> Pt { (a.1.neg(), a.0.clone()) }

/// 実体の式。
#[derive(Clone)]
enum E {
    Point(Pt),
    /// 方向(無限遠点)。
    Dir(Pt),
    Line(Pt, Pt),
    Circle(Pt, Poly),
    /// 比のスカラー (分子, 分母)。
    Scalar(Poly, Poly),
}

pub(crate) struct Cert<'a> {
    eg: &'a EGraph,
    memo: FxHashMap<usize, E>,
    nvars: usize,
    fixed: usize,
    hyps: Vec<Poly>,
    /// 非退化の因子(0 でない配置だけを考える: 交わる2直線が平行でない、2点が別、3点が一直線でないなど)。
    nondeg: Vec<Poly>,
    fail: Option<String>,
    visiting: FxHashSet<usize>,
}

impl<'a> Cert<'a> {
    pub(crate) fn new(eg: &'a EGraph) -> Self {
        Cert { eg, memo: FxHashMap::default(), nvars: 0, fixed: 0, hyps: Vec::new(), nondeg: Vec::new(), fail: None, visiting: FxHashSet::default() }
    }
    fn give_up<T>(&mut self, why: String) -> Option<T> { self.fail.get_or_insert(why); None }
    fn new_point(&mut self) -> Option<Pt> {
        if self.nvars + 2 > MAX_VARS { return self.give_up(format!("変数が {} 個を超える", MAX_VARS)); }
        self.nvars += 2;
        Some((Poly::var(self.nvars - 2), Poly::var(self.nvars - 1)))
    }
    fn hyp(&mut self, p: Option<Poly>) -> Option<()> {
        let Some(p) = p else { return self.give_up("仮説の次数が 15 を超える".into()) };
        if !p.is_zero() { self.hyps.push(p); }
        Some(())
    }
    fn nd(&mut self, p: Option<Poly>) { if let Some(p) = p && !p.is_zero() && p.deg() > 0 { self.nondeg.push(p); } }
    fn point(&mut self, id: ClassId) -> Option<Pt> {
        match self.value(id)? { E::Point(p) => Some(p), _ => self.give_up(format!("{} が点でない", self.eg.entities[id.0].name)) }
    }
    fn line(&mut self, id: ClassId) -> Option<(Pt, Pt)> {
        match self.value(id)? { E::Line(b, d) => Some((b, d)), _ => self.give_up(format!("{} が直線でない", self.eg.entities[id.0].name)) }
    }
    fn circle(&mut self, id: ClassId) -> Option<(Pt, Poly)> {
        match self.value(id)? { E::Circle(o, r) => Some((o, r)), _ => self.give_up(format!("{} が円でない", self.eg.entities[id.0].name)) }
    }
    fn dir(&mut self, id: ClassId) -> Option<Pt> {
        match self.value(id)? { E::Dir(d) => Some(d), _ => self.give_up(format!("{} が方向でない", self.eg.entities[id.0].name)) }
    }

    fn value(&mut self, id: ClassId) -> Option<E> {
        if let Some(v) = self.memo.get(&id.0) { return Some(v.clone()); }
        if !self.visiting.insert(id.0) { return self.give_up("定義が循環".into()); }
        let v = self.compute(id);
        self.visiting.remove(&id.0);
        let v = v?;
        self.memo.insert(id.0, v.clone());
        Some(v)
    }

    fn compute(&mut self, id: ClassId) -> Option<E> {
        let eg = self.eg;
        if id == eg.ang90 { return Some(E::Scalar(Poly::c(1), Poly::c(0))); }
        if id == eg.ang0 { return Some(E::Scalar(Poly::c(0), Poly::c(1))); }
        let def = eg.entities[id.0].original_definition.clone();
        Some(match def {
            Definition::FreePoint => {
                let rep = eg.get_rep(id);
                let constrained = eg.premise_incidences.as_ref().is_some_and(|ps| ps.iter().any(|(p, _)| eg.get_rep(*p) == rep));
                if !constrained && self.fixed < 2 {
                    self.fixed += 1;
                    E::Point((Poly::c(if self.fixed == 1 { 0 } else { 1 }), Poly::c(0)))
                } else {
                    let p = self.new_point()?;
                    // 前提の曲線に乗る条件は、点の値を記録してから仮説にする(曲線が点自身に依存しないとは限らない)。
                    self.memo.insert(id.0, E::Point(p.clone()));
                    let curves: Vec<ClassId> = eg.premise_incidences.as_ref().map(|ps| ps.iter().filter(|(q, _)| eg.get_rep(*q) == rep).map(|(_, c)| *c).collect()).unwrap_or_default();
                    for c in curves { let h = self.incidence(&p, c)?; self.hyp(Some(h))?; }
                    E::Point(p)
                }
            }
            Definition::Midpoint(a, b) => {
                let (a, b) = (self.point(a)?, self.point(b)?);
                let h = invm(2);
                E::Point((a.0.add(&b.0).scale(h), a.1.add(&b.1).scale(h)))
            }
            Definition::LineThroughPoints(a, b) => { let (a, b) = (self.point(a)?, self.point(b)?); let d = psub(&b, &a); self.nd(dot2(&d, &d)); E::Line(a, d) }
            Definition::PerpendicularLine(l, p) => { let ((_, d), p) = (self.line(l)?, self.point(p)?); E::Line(p, perp(&d)) }
            Definition::ParallelLine(l, p) => { let ((_, d), p) = (self.line(l)?, self.point(p)?); E::Line(p, d) }
            Definition::DirectionOf(l) => { let (_, d) = self.line(l)?; E::Dir(d) }
            Definition::PerpDirectionOf(d) => { let d = self.dir(d)?; E::Dir(perp(&d)) }
            Definition::Intersection(l1, l2) => {
                let ((b1, d1), (b2, d2)) = (self.line(l1)?, self.line(l2)?);
                self.nd(cross2(&d1, &d2));
                let x = self.new_point()?;
                self.hyp(cross2(&psub(&x, &b1), &d1))?;
                self.hyp(cross2(&psub(&x, &b2), &d2))?;
                E::Point(x)
            }
            Definition::CircleCenterPoint(o, p) => { let (o, p) = (self.point(o)?, self.point(p)?); let r = dot2(&psub(&p, &o), &psub(&p, &o)); E::Circle(o, r?) }
            Definition::Circumcircle(a, b, c) => {
                let (a, b, c) = (self.point(a)?, self.point(b)?, self.point(c)?);
                self.nd(cross2(&psub(&b, &a), &psub(&c, &a)));
                let o = self.new_point()?;
                let (oa, ob, oc) = (psub(&a, &o), psub(&b, &o), psub(&c, &o));
                let (ra, rb, rc) = (dot2(&oa, &oa)?, dot2(&ob, &ob)?, dot2(&oc, &oc)?);
                self.hyp(Some(ra.sub(&rb)))?;
                self.hyp(Some(ra.sub(&rc)))?;
                E::Circle(o, ra)
            }
            Definition::TangentLine(c, p) => { let ((o, _), p) = (self.circle(c)?, self.point(p)?); let d = perp(&psub(&p, &o)); E::Line(p, d) }
            Definition::SecondIntersectionOfLineAndConic(k, l, c) => {
                let (k, (_, d), (o, _)) = (self.point(k)?, self.line(l)?, self.circle(c)?);
                self.nd(dot2(&d, &d));
                let x = self.new_point()?;
                self.hyp(cross2(&psub(&x, &k), &d))?;
                let s = (x.0.add(&k.0).sub(&o.0.scale(2)), x.1.add(&k.1).sub(&o.1.scale(2)));
                self.hyp(dot2(&s, &d))?;
                E::Point(x)
            }
            Definition::SecondIntersectionOfCircles(k, c1, c2) => {
                let (k, (o1, _), (o2, _)) = (self.point(k)?, self.circle(c1)?, self.circle(c2)?);
                let x = self.new_point()?;
                let d = psub(&o2, &o1);
                self.nd(dot2(&d, &d));
                self.hyp(dot2(&psub(&x, &k), &d))?;
                let s = (x.0.add(&k.0).sub(&o1.0.scale(2)), x.1.add(&k.1).sub(&o1.1.scale(2)));
                self.hyp(cross2(&s, &d))?;
                E::Point(x)
            }
            Definition::RadicalAxis(c1, c2) => {
                let ((o1, r1), (o2, r2)) = (self.circle(c1)?, self.circle(c2)?);
                let x = self.new_point()?;
                let (x1, x2) = (psub(&x, &o1), psub(&x, &o2));
                self.hyp(Some(dot2(&x1, &x1)?.sub(&r1).sub(&dot2(&x2, &x2)?).add(&r2)))?;
                self.hyp(cross2(&x1, &psub(&o2, &o1)))?;
                E::Line(x, perp(&psub(&o2, &o1)))
            }
            Definition::AnglePair(d1, d2) => {
                let (a, b) = (self.dir(d1)?, self.dir(d2)?);
                self.nd(cross2(&a, &b));
                E::Scalar(cross2(&a, &b)?, dot2(&a, &b)?)
            }
            Definition::LengthSq(a, b) => { let d = psub(&self.point(a)?, &self.point(b)?); E::Scalar(dot2(&d, &d)?, Poly::c(1)) }
            Definition::Product(a, b) => {
                let (E::Scalar(n1, d1), E::Scalar(n2, d2)) = (self.value(a)?, self.value(b)?) else { return self.give_up("積の因子がスカラーでない".into()) };
                E::Scalar(n1.mul(&n2)?, d1.mul(&d2)?)
            }
            other => return self.give_up(format!("証拠の探索に無い作図 {}", other.get_type_name())),
        })
    }

    fn incidence(&mut self, p: &Pt, c: ClassId) -> Option<Poly> {
        match self.value(c)? {
            E::Line(b, d) => cross2(&psub(p, &b), &d),
            E::Circle(o, r) => { let x = psub(p, &o); Some(dot2(&x, &x)?.sub(&r)) }
            _ => self.give_up("点・直線・円でない曲線".into()),
        }
    }

    /// 2つの値が等しいことの多項式(0 になるべきもの)。
    fn equal(&mut self, a: &E, b: &E) -> Option<Vec<Poly>> {
        Some(match (a, b) {
            (E::Point(p), E::Point(q)) => { let d = psub(p, q); vec![d.0, d.1] }
            (E::Dir(p), E::Dir(q)) => vec![cross2(p, q)?],
            (E::Line(b1, d1), E::Line(b2, d2)) => vec![cross2(d1, d2)?, cross2(&psub(b2, b1), d1)?],
            (E::Scalar(n1, d1), E::Scalar(n2, d2)) => vec![n1.mul(d2)?.sub(&n2.mul(d1)?)],
            (E::Circle(o1, r1), E::Circle(o2, r2)) => { let d = psub(o1, o2); vec![d.0, d.1, r1.sub(r2)] }
            _ => return self.give_up("等式の両辺の種類が違う".into()),
        })
    }

    /// 作図でない前提(与えた等式・作図した点の接続)を仮説に足す。
    fn add_premises(&mut self) -> Option<()> {
        let eg = self.eg;
        let edges: Vec<(ClassId, ClassId)> = eg.proof_edges.values().filter(|e| matches!(e.justification, Justification::Given)).map(|e| (e.from, e.to)).collect();
        for (a, b) in edges {
            let (va, vb) = (self.value(a)?, self.value(b)?);
            for h in self.equal(&va, &vb)? { self.hyp(Some(h))?; }
        }
        let free = eg.premise_incidences.clone().unwrap_or_default();
        let links: Vec<(ClassId, ClassId)> = eg.incidence_provenance.iter().filter(|(_, j)| matches!(j, Justification::Given)).map(|(&k, _)| k).collect();
        for (a, b) in links {
            let (p, c) = if eg.entities[a.0].entity_type == EntityType::Point { (a, b) } else { (b, a) };
            if free.iter().any(|&(q, d)| eg.get_rep(q) == eg.get_rep(p) && eg.get_rep(d) == eg.get_rep(c)) { continue; }
            let pt = self.point(p)?;
            let h = self.incidence(&pt, c)?;
            self.hyp(Some(h))?;
        }
        Some(())
    }

    /// 目標の多項式(全て 0 になるべきもの)。
    fn goal(&mut self, kind: &str, args: &[ClassId]) -> Option<Vec<Poly>> {
        match (kind, args) {
            ("Identical", [a, b]) => { let (va, vb) = (self.value(*a)?, self.value(*b)?); self.equal(&va, &vb) }
            ("Connected", [p, c]) => { let pt = self.point(*p)?; Some(vec![self.incidence(&pt, *c)?]) }
            ("Concyclic", [a, b, c, d]) => {
                let pts = [self.point(*a)?, self.point(*b)?, self.point(*c)?, self.point(*d)?];
                // A を原点に移した 3×3 の行列式 [x² + y², x, y]。
                let rows: Option<Vec<[Poly; 3]>> = pts[1..].iter().map(|q| { let v = psub(q, &pts[0]); Some([dot2(&v, &v)?, v.0, v.1]) }).collect();
                let m = rows?;
                let t1 = m[0][0].mul(&m[1][1].mul(&m[2][2])?.sub(&m[1][2].mul(&m[2][1])?))?;
                let t2 = m[0][1].mul(&m[1][0].mul(&m[2][2])?.sub(&m[1][2].mul(&m[2][0])?))?;
                let t3 = m[0][2].mul(&m[1][0].mul(&m[2][1])?.sub(&m[1][1].mul(&m[2][0])?))?;
                Some(vec![t1.sub(&t2).add(&t3)])
            }
            _ => self.give_up(format!("目標 {} ×{} は証拠の探索に無い", kind, args.len())),
        }
    }
}

/// {m·h} の張る空間(法 P の掃き出し、行は主成分の列で引く)。列の順は (次数, 単項式) の大きい方から。
/// 掃き出しの行(列の鍵と係数、鍵の大きい順)。
type Row = Vec<((u32, Mono), u64)>;
struct Span { rows: FxHashMap<(u32, Mono), Row>, nrows: usize, limit: usize }

impl Span {
    fn key(m: Mono) -> (u32, Mono) { (mono_deg(m), m) }
    fn to_row(p: &Poly) -> Vec<((u32, Mono), u64)> {
        let mut r: Vec<((u32, Mono), u64)> = p.0.iter().map(|(&m, &c)| (Self::key(m), c)).collect();
        r.sort_unstable_by_key(|e| std::cmp::Reverse(e.0));
        r
    }
    /// 行を既存の行で簡約する(主成分の列が既にあれば消す)。残りを返す。
    fn reduce(&self, mut r: Vec<((u32, Mono), u64)>) -> Vec<((u32, Mono), u64)> {
        let mut i = 0;
        while i < r.len() {
            let (k, c) = r[i];
            if let Some(piv) = self.rows.get(&k) {
                // r −= c·piv(piv の主成分は 1)。
                let mut out = Vec::with_capacity(r.len() + piv.len());
                out.extend_from_slice(&r[..i]);
                let (mut a, mut b) = (i, 0);
                while a < r.len() || b < piv.len() {
                    if b == piv.len() || (a < r.len() && r[a].0 > piv[b].0) { out.push(r[a]); a += 1; continue; }
                    let v = mulm(negm(c), piv[b].1);
                    if a < r.len() && r[a].0 == piv[b].0 {
                        let s = addm(r[a].1, v);
                        if s != 0 { out.push((r[a].0, s)); }
                        a += 1;
                    } else { out.push((piv[b].0, v)); }
                    b += 1;
                }
                r = out;
            } else { i += 1; }
        }
        r
    }
    fn insert(&mut self, p: &Poly) -> bool {
        let r = self.reduce(Self::to_row(p));
        let Some(&(k, c)) = r.first() else { return true };
        let inv = invm(c);
        self.rows.insert(k, r.into_iter().map(|(kk, v)| (kk, mulm(v, inv))).collect());
        self.nrows += 1;
        self.nrows <= self.limit
    }
}

fn monomials_up_to(nvars: usize, d: u32) -> Vec<Mono> {
    let mut out = vec![0u128];
    let mut frontier = vec![0u128];
    for _ in 0..d {
        let mut next = Vec::new();
        for &m in &frontier {
            // 変数の添字が減らない順に足す(重複を避ける)。
            let last = (0..nvars).rev().find(|&i| (m >> (4 * i)) & 15 != 0).unwrap_or(0);
            for i in last..nvars { next.push(m + (1u128 << (4 * i))); }
        }
        out.extend_from_slice(&next);
        frontier = next;
    }
    out
}

impl EGraph {
    /// 目標を次数 max_d までの証拠で示す。(結果, 変数の数, 仮説の数, 行の数, 使った次数, 諦めた理由)。
    pub(crate) fn certificate_prove(&self, kind: &str, args: &[ClassId], max_d: u32, max_rows: usize)
        -> (Option<bool>, usize, usize, usize, u32, Option<String>) {
        let mut c = Cert::new(self);
        let goals = c.goal(kind, args).and_then(|g| { c.add_premises()?; Some(g) });
        let Some(goals) = goals else { return (None, c.nvars, c.hyps.len(), 0, 0, c.fail) };
        let goals: Vec<Poly> = goals.into_iter().filter(|g| !g.is_zero()).collect();
        if goals.is_empty() { return (Some(true), c.nvars, c.hyps.len(), 0, 0, None); }
        let gdeg = goals.iter().map(|g| g.deg()).max().unwrap_or(0);
        // 掛ける非退化の因子の候補: 1、因子1つずつ、全部の積(次数が 8 以下なら)。
        let mut factors: Vec<Poly> = vec![Poly::c(1)];
        let mut seen: Vec<Poly> = Vec::new();
        for f in &c.nondeg { if !seen.contains(f) { seen.push(f.clone()); factors.push(f.clone()); } }
        if seen.len() > 1 {
            let mut all = Poly::c(1);
            let mut ok = true;
            for f in &seen { match all.mul(f) { Some(p) if p.deg() <= 8 => all = p, _ => { ok = false; break; } } }
            if ok { factors.push(all); }
        }
        let mut last_rows = 0;
        for d in gdeg.max(2)..=max_d {
            let mut span = Span { rows: FxHashMap::default(), nrows: 0, limit: max_rows };
            for h in &c.hyps {
                let hd = h.deg();
                if hd > d { continue; }
                for m in monomials_up_to(c.nvars, d - hd) {
                    let mut mp = Poly::default(); mp.0.insert(m, 1);
                    let Some(row) = mp.mul(h) else { continue };
                    if !span.insert(&row) { return (None, c.nvars, c.hyps.len(), span.nrows, d, Some(format!("行が {} を超える", max_rows))); }
                }
            }
            last_rows = span.nrows;
            let ok = goals.iter().all(|g| factors.iter().any(|f| f.deg() + g.deg() <= d
                && g.mul(f).is_some_and(|gs| span.reduce(Span::to_row(&gs)).is_empty())));
            if ok { return (Some(true), c.nvars, c.hyps.len(), span.nrows, d, None); }
        }
        (Some(false), c.nvars, c.hyps.len(), last_rows, max_d, None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn membership_by_linear_algebra() {
        // h = x − y、g = x² − y² = (x + y)·h は次数2で見つかる。g' = x² + y² は見つからない。
        let (x, y) = (Poly::var(0), Poly::var(1));
        let h = x.sub(&y);
        let mut span = Span { rows: FxHashMap::default(), nrows: 0, limit: 1000 };
        for m in monomials_up_to(2, 1) { let mut mp = Poly::default(); mp.0.insert(m, 1); span.insert(&mp.mul(&h).unwrap()); }
        let g = x.mul(&x).unwrap().sub(&y.mul(&y).unwrap());
        assert!(span.reduce(Span::to_row(&g)).is_empty());
        let g2 = x.mul(&x).unwrap().add(&y.mul(&y).unwrap());
        assert!(!span.reduce(Span::to_row(&g2)).is_empty());
        assert_eq!(mulm(invm(7), 7), 1);
    }
}

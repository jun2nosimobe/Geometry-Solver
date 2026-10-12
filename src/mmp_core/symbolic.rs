//! 🌟 記号計算による証明(Wu の方法の、有理的な作図の場合)。
//!
//! 作図を元の定義どおりに、同次座標の成分が自由な媒介変数の多項式(係数は法 P = 2⁶¹ − 1 の有限体)になるように組み立て、
//! 目標の式(2つの実体の比例・4点の共円の行列式など)が多項式として恒等的に 0 になるかを見る。HAGeo の読み込みは平方根の要る
//! 作図を受け付けないので、作図は全て媒介変数の有理式で、作図の順に代入していく Wu の方法(主変数について一次の三角化)と同じ。
//! 恒等式は法 P の合同式として示す(ユーザー方針: 十分大きい法の合同式で示せればよい)。乱数の点での値の一致とは違い、多項式
//! そのものが 0 になることを確かめる。値の定まらない配置(非退化条件)は固定座標で確かめる(呼び出し側)。
//! 自由点は、相似で動かせるので最初の2つを (0,0)・(1,0) に置き、残りは2変数。前提の直線の上の点は1変数(直線の原点からの垂線の
//! 足から方向に沿って)、前提の円の上の点は1変数(円の既知の点を通る傾き t の直線のもう一方の交点)。

use rustc_hash::FxHashMap;

use super::{ClassId, Definition, EGraph, EntityType};

pub(crate) const P: u64 = (1 << 61) - 1;

pub(crate) fn mulm(a: u64, b: u64) -> u64 {
    let r = (a as u128) * (b as u128);
    let s = ((r as u64) & P) + ((r >> 61) as u64);
    if s >= P { s - P } else { s }
}
pub(crate) fn addm(a: u64, b: u64) -> u64 { let s = a + b; if s >= P { s - P } else { s } }
pub(crate) fn negm(a: u64) -> u64 { if a == 0 { 0 } else { P - a } }
fn constm(x: i64) -> u64 { x.rem_euclid(P as i64) as u64 }
fn powm(mut a: u64, mut e: u64) -> u64 { let mut r = 1; while e > 0 { if e & 1 == 1 { r = mulm(r, a); } a = mulm(a, a); e >>= 1; } r }
pub(crate) fn invm(a: u64) -> u64 { powm(a, P - 2) }

/// 単項式: 変数ごとの次数を 16 ビットずつ詰めたもの(変数は MAX_VARS 個まで、各次数 65535 まで)。
type Mono = u128;
pub(crate) const MAX_VARS: usize = 8;

/// 計算の上限(項の数と、項の掛け算の回数)。超えたら諦める。
pub(crate) struct Budget {
    pub max_terms: usize,
    pub max_mults: u64,
    pub mults: u64,
    pub peak_terms: usize,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Poly {
    terms: FxHashMap<Mono, u64>,
    /// 変数ごとの次数の上限(掛け算で次数のビットがあふれないか見る)。
    maxdeg: [u16; MAX_VARS],
}

fn exps(m: Mono) -> [u16; MAX_VARS] {
    let mut e = [0u16; MAX_VARS];
    for (i, x) in e.iter_mut().enumerate() { *x = (m >> (16 * i)) as u16; }
    e
}

impl Poly {
    fn constant(c: i64) -> Poly {
        let mut terms = FxHashMap::default();
        let c = constm(c);
        if c != 0 { terms.insert(0, c); }
        Poly { terms, maxdeg: [0; MAX_VARS] }
    }
    fn var(i: usize) -> Poly {
        let mut terms = FxHashMap::default();
        terms.insert(1u128 << (16 * i), 1);
        let mut maxdeg = [0; MAX_VARS];
        maxdeg[i] = 1;
        Poly { terms, maxdeg }
    }
    pub(crate) fn is_zero(&self) -> bool { self.terms.is_empty() }
    fn add(&self, o: &Poly) -> Poly {
        let mut t = self.terms.clone();
        for (&m, &c) in &o.terms {
            let e = t.entry(m).or_insert(0);
            *e = addm(*e, c);
            if *e == 0 { t.remove(&m); }
        }
        let mut maxdeg = self.maxdeg;
        for (d, &e) in maxdeg.iter_mut().zip(o.maxdeg.iter()) { *d = (*d).max(e); }
        Poly { terms: t, maxdeg }
    }
    fn neg(&self) -> Poly { Poly { terms: self.terms.iter().map(|(&m, &c)| (m, negm(c))).collect(), maxdeg: self.maxdeg } }
    fn sub(&self, o: &Poly) -> Poly { self.add(&o.neg()) }
    fn scale(&self, k: i64) -> Poly {
        let k = constm(k);
        if k == 0 { return Poly::default(); }
        Poly { terms: self.terms.iter().map(|(&m, &c)| (m, mulm(c, k))).collect(), maxdeg: self.maxdeg }
    }
    fn mul(&self, o: &Poly, b: &mut Budget) -> Option<Poly> {
        if self.is_zero() || o.is_zero() { return Some(Poly::default()); }
        if self.maxdeg.iter().zip(o.maxdeg.iter()).any(|(&a, &b)| a as u32 + b as u32 > 65535) { return None; }
        let n = (self.terms.len() as u64) * (o.terms.len() as u64);
        b.mults += n;
        if b.mults > b.max_mults { return None; }
        let mut t: FxHashMap<Mono, u64> = FxHashMap::default();
        t.reserve(self.terms.len().max(o.terms.len()));
        for (&m1, &c1) in &self.terms {
            for (&m2, &c2) in &o.terms {
                let e = t.entry(m1 + m2).or_insert(0);
                *e = addm(*e, mulm(c1, c2));
            }
        }
        t.retain(|_, c| *c != 0);
        if t.len() > b.max_terms { return None; }
        b.peak_terms = b.peak_terms.max(t.len());
        let mut p = Poly { terms: t, maxdeg: [0; MAX_VARS] };
        p.refresh_degrees();
        Some(p)
    }

    fn refresh_degrees(&mut self) {
        let mut d = [0u16; MAX_VARS];
        for &m in self.terms.keys() { for (x, e) in d.iter_mut().zip(exps(m)) { *x = (*x).max(e); } }
        self.maxdeg = d;
    }
}

/// 同次座標(と比のスカラー)の成分に共通する単項式を割る(値は比だけが意味を持つ)。割らないと交点を重ねるたびに z の積などの
/// 共通因子が溜まり、項は少ないのに次数があふれた。
fn strip_monomial(v: &mut V) {
    let mut lo = [u16::MAX; MAX_VARS];
    let mut any = false;
    for p in v.iter() {
        for &m in p.terms.keys() { any = true; for (x, e) in lo.iter_mut().zip(exps(m)) { *x = (*x).min(e); } }
    }
    if !any || lo.iter().all(|&x| x == 0) { return; }
    let shift: Mono = lo.iter().enumerate().map(|(i, &e)| (e as u128) << (16 * i)).sum();
    for p in v.iter_mut() {
        p.terms = p.terms.iter().map(|(&m, &c)| (m - shift, c)).collect();
        p.refresh_degrees();
    }
}

pub(crate) type V = Vec<Poly>;

// --- 一変数(線モード: 媒介変数の空間の一般の直線 u = u0 + t·w の上)の計算。多項式は t = 変数0 だけ。 ---

/// t の係数の列(次数の低い順、最高次は 0 でない。0 は空)。
fn dense(p: &Poly) -> Vec<u64> {
    let mut v = vec![0u64; p.maxdeg[0] as usize + 1];
    for (&m, &c) in &p.terms { v[(m & 0xFFFF) as usize] = c; }
    while v.last() == Some(&0) { v.pop(); }
    v
}
fn sparse(v: &[u64]) -> Poly {
    let terms: FxHashMap<Mono, u64> = v.iter().enumerate().filter(|(_, c)| **c != 0).map(|(k, &c)| (k as u128, c)).collect();
    let mut p = Poly { terms, maxdeg: [0; MAX_VARS] };
    p.refresh_degrees();
    p
}
/// a を b で割った (商, 余り)。
fn ddivrem(a: &[u64], b: &[u64]) -> (Vec<u64>, Vec<u64>) {
    let lb = b.len();
    if a.len() < lb { return (Vec::new(), a.to_vec()); }
    let inv = invm(b[lb - 1]);
    let mut r = a.to_vec();
    let mut q = vec![0u64; a.len() + 1 - lb];
    while r.len() >= lb {
        let c = mulm(r[r.len() - 1], inv);
        let s = r.len() - lb;
        q[s] = c;
        for i in 0..lb { r[s + i] = addm(r[s + i], negm(mulm(c, b[i]))); }
        r.pop();
        while r.last() == Some(&0) { r.pop(); }
    }
    (q, r)
}
fn dgcd(a: &[u64], b: &[u64]) -> Vec<u64> {
    let (mut x, mut y) = (a.to_vec(), b.to_vec());
    while !y.is_empty() { let r = ddivrem(&x, &y).1; x = y; y = r; }
    if let Some(&l) = x.last() { let inv = invm(l); for c in x.iter_mut() { *c = mulm(*c, inv); } }
    x
}
/// 同次座標(と比のスカラー)の成分の最大公約式で割る(線モード)。一般の直線の上では、多変数の成分が共有する因子だけが残る。
fn reduce_line(v: &mut V) {
    let ds: Vec<Vec<u64>> = v.iter().map(dense).collect();
    let mut g: Vec<u64> = Vec::new();
    for d in &ds {
        if d.is_empty() { continue; }
        g = if g.is_empty() { d.clone() } else { dgcd(&g, d) };
        if g.len() == 1 { return; }
    }
    if g.len() <= 1 { return; }
    for (p, d) in v.iter_mut().zip(ds.iter()) { if !d.is_empty() { *p = sparse(&ddivrem(d, &g).0); } }
}
fn free_budget() -> Budget { Budget { max_terms: usize::MAX, max_mults: u64::MAX, mults: 0, peak_terms: 0 } }
/// 線モード: 直線 (a, b, c) の方向 (b, −a) を公約式で割ったもの。
pub(crate) fn line_direction(l: &V) -> V { let mut v = vec![l[1].clone(), l[0].neg()]; reduce_line(&mut v); v }
/// 線モード: 2点の距離の2乗 (分子, 分母) を公約式で割ったもの。
pub(crate) fn length_sq(a: &V, b: &V) -> V {
    let bg = &mut free_budget();
    let m = |x: &Poly, y: &Poly, bg: &mut Budget| x.mul(y, bg).unwrap_or_default();
    let dx = m(&a[0], &b[2], bg).sub(&m(&b[0], &a[2], bg));
    let dy = m(&a[1], &b[2], bg).sub(&m(&b[1], &a[2], bg));
    let (az, bz) = (m(&a[2], &a[2], bg), m(&b[2], &b[2], bg));
    let mut v = vec![m(&dx, &dx, bg).add(&m(&dy, &dy, bg)), m(&az, &bz, bg)];
    reduce_line(&mut v);
    v
}
/// 線モード: 2方向 (dx, dy) の有向角の (cross, dot) を公約式で割ったもの。
pub(crate) fn angle_of_directions(d1: &V, d2: &V) -> V {
    let bg = &mut free_budget();
    let m = |x: &Poly, y: &Poly, bg: &mut Budget| x.mul(y, bg).unwrap_or_default();
    let mut v = vec![m(&d1[0], &d2[1], bg).sub(&m(&d2[0], &d1[1], bg)), m(&d1[0], &d2[0], bg).add(&m(&d1[1], &d2[1], bg))];
    reduce_line(&mut v);
    v
}
/// 一変数: 2点を通る直線・2直線の交点(外積)を公約式で割ったもの。
pub(crate) fn join_reduced(a: &V, b: &V) -> V { let mut v = cross(a, b, &mut free_budget()).unwrap_or_default(); reduce_line(&mut v); v }
/// 一変数: 3点を通る円(係数6つ)を公約式で割ったもの。3点が一直線なら直線と無限遠直線の組(x² + y² の係数が 0)。
pub(crate) fn circle_reduced(a: &V, b: &V, c: &V) -> V {
    let bg = &mut free_budget();
    let m = |x: &Poly, y: &Poly, bg: &mut Budget| x.mul(y, bg).unwrap_or_default();
    let rows: Vec<[Poly; 4]> = [a, b, c].iter().map(|p| [m(&p[0], &p[0], bg).add(&m(&p[1], &p[1], bg)), m(&p[0], &p[2], bg), m(&p[1], &p[2], bg), m(&p[2], &p[2], bg)]).collect();
    let minor = |cols: [usize; 3], bg: &mut Budget| -> Poly {
        let e = |i: usize, j: usize| &rows[i][cols[j]];
        let t1 = m(e(0, 0), &m(e(1, 1), e(2, 2), bg).sub(&m(e(1, 2), e(2, 1), bg)), bg);
        let t2 = m(e(0, 1), &m(e(1, 0), e(2, 2), bg).sub(&m(e(1, 2), e(2, 0), bg)), bg);
        let t3 = m(e(0, 2), &m(e(1, 0), e(2, 1), bg).sub(&m(e(1, 1), e(2, 0), bg)), bg);
        t1.sub(&t2).add(&t3)
    };
    let al = minor([1, 2, 3], bg);
    let mut v = vec![al.clone(), Poly::default(), al, minor([0, 2, 3], bg).neg(), minor([0, 1, 3], bg), minor([0, 1, 2], bg).neg()];
    reduce_line(&mut v);
    v
}
/// 一変数: 複比 (A,B;C,D) = [ACR][DBR] / ([CBR][ADR]) を公約式で割ったもの(R は一般の位置の定点。共点の4直線なら
/// 双対の平面の共線の4点として同じ式)。
pub(crate) fn cross_ratio_reduced(a: &V, b: &V, c: &V, d: &V) -> V {
    let bg = &mut free_budget();
    let r: V = vec![Poly::constant(314_159), Poly::constant(271_828), Poly::constant(1)];
    let det = |x: &V, y: &V, bg: &mut Budget| -> Poly {
        let n = cross(x, y, bg).unwrap_or_default();
        let m = |p: &Poly, q: &Poly, bg: &mut Budget| p.mul(q, bg).unwrap_or_default();
        m(&n[0], &r[0], bg).add(&m(&n[1], &r[1], bg)).add(&m(&n[2], &r[2], bg))
    };
    let m = |p: &Poly, q: &Poly, bg: &mut Budget| p.mul(q, bg).unwrap_or_default();
    let (ac, db, cb, ad) = (det(a, c, bg), det(d, b, bg), det(c, b, bg), det(a, d, bg));
    let mut v = vec![m(&ac, &db, bg), m(&cb, &ad, bg)];
    reduce_line(&mut v);
    v
}
/// 線モードの値の次数(成分の次数の最大)。maxdeg は上限(足し算で最高次が消えても下がらない)なので項から数える。
pub(crate) fn line_degree(v: &V) -> u32 { v.iter().flat_map(|p| p.terms.keys()).map(|&m| (m & 0xFFFF) as u32).max().unwrap_or(0) }
/// 線モードの値を t で評価する。
pub(crate) fn line_eval(v: &V, t: u64) -> Vec<u64> {
    v.iter().map(|p| { let d = dense(p); d.iter().rev().fold(0u64, |acc, &c| addm(mulm(acc, t), c)) }).collect()
}

fn cross(a: &V, b: &V, bg: &mut Budget) -> Option<V> {
    Some(vec![
        a[1].mul(&b[2], bg)?.sub(&a[2].mul(&b[1], bg)?),
        a[2].mul(&b[0], bg)?.sub(&a[0].mul(&b[2], bg)?),
        a[0].mul(&b[1], bg)?.sub(&a[1].mul(&b[0], bg)?),
    ])
}

/// 二次曲線 (a,b,c,d,e,f)(ax² + bxy + cy² + dxz + eyz + fz²)の2倍の行列 M2 で、uᵀ M2 v。
fn is_zero_vec(v: &V) -> bool { v.iter().all(|p| p.is_zero()) }

fn bilinear(q: &V, u: &V, v: &V, bg: &mut Budget) -> Option<Poly> {
    let two = |p: &Poly| p.scale(2);
    let m = [[two(&q[0]), q[1].clone(), q[3].clone()], [q[1].clone(), two(&q[2]), q[4].clone()], [q[3].clone(), q[4].clone(), two(&q[5])]];
    let mut s = Poly::default();
    for i in 0..3 {
        let mut row = Poly::default();
        for j in 0..3 { row = row.add(&m[i][j].mul(&v[j], bg)?); }
        s = s.add(&u[i].mul(&row, bg)?);
    }
    Some(s)
}

/// 直線 l と二次曲線 q のうち、既知の点 k でない方の交点: Q を l の無限遠点として (QᵀM2Q)K − 2(KᵀM2Q)Q。
fn second_on_conic(k: &V, l: &V, q: &V, bg: &mut Budget) -> Option<V> {
    let qd = vec![l[1].clone(), l[0].neg(), Poly::default()];
    let a = bilinear(q, &qd, &qd, bg)?;
    let b = bilinear(q, k, &qd, bg)?.scale(2);
    (0..3).map(|i| Some(a.mul(&k[i], bg)?.sub(&b.mul(&qd[i], bg)?))).collect::<Option<V>>()
}

/// 2つの円(x² と y² の係数が等しく xy が 0)の根軸。
fn radical_axis(c1: &V, c2: &V, bg: &mut Budget) -> Option<V> {
    (3..6).map(|i| Some(c2[0].mul(&c1[i], bg)?.sub(&c1[0].mul(&c2[i], bg)?))).collect::<Option<V>>()
}

/// 媒介変数の置き方。
#[derive(Clone, Copy)]
enum Params {
    /// Wu の方法: 媒介変数を多項式の変数にする(最初の2つの自由点は相似で (0,0)・(1,0))。
    Variables,
    /// 線モード: 全ての媒介変数を一般の直線 u = u0 + t·w の上に(乱数の状態)。
    Line(u64),
    /// 塊モード: 自由点 moving(元の定義が自由点の実体)の媒介変数だけを一般の直線の上で動かし、他の自由点は一般の定数に置く。
    /// 値の t の次数が、配置空間 Π(P² か P¹) の Picard 群でのその塊の成分(次数のベクトルの成分)。None なら全て定数。
    Block(Option<ClassId>),
}

/// 塊モードの値の覚え(実体ごとの値と自由点の値)。次数の計算で、呼び出しをまたいで使い回す(元の定義は変わらない)。
#[derive(Clone, Default)]
pub(crate) struct SymMemo {
    memo: FxHashMap<usize, Option<V>>,
    free: FxHashMap<usize, V>,
}

/// Wu の方法(変数モード)の途中の値。上限に達して諦めた試みの続きから計算するため、値の出来た実体・自由点の変数・変数の数を残す
/// (値は作図の元の定義と前提の曲線だけで決まるので、探索が進んでも使い回せる)。
#[derive(Clone, Debug, Default)]
pub(crate) struct WuMemo {
    memo: FxHashMap<usize, Option<V>>,
    free: FxHashMap<usize, V>,
    fixed_points: usize,
    nvars: usize,
}

/// 自由点 id の k 番目の媒介変数の、一般の位置の定数と方向(塊モード)。実体の番号から決まる(どの呼び出しでも同じ)。
fn generic_param(id: usize, k: usize, salt: u64) -> u64 {
    let mut z = (id as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (k as u64).wrapping_mul(0xC2B2_AE3D_27D4_EB4F) ^ salt;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    ((z ^ (z >> 31)) % (P - 1)) + 1
}

pub(crate) struct Symbolic<'a> {
    eg: &'a EGraph,
    memo: FxHashMap<usize, Option<V>>,
    /// 自由点ごとの値(Wu の方法と線モードは代表元、塊モードは元の定義が自由点の実体の番号で引く)。
    free: FxHashMap<usize, V>,
    fixed_points: usize,
    pub nvars: usize,
    pub budget: Budget,
    pub fail: Option<String>,
    visiting: rustc_hash::FxHashSet<usize>,
    params: Params,
}

impl<'a> Symbolic<'a> {
    pub(crate) fn new(eg: &'a EGraph, max_terms: usize, max_mults: u64) -> Self {
        Symbolic { eg, memo: FxHashMap::default(), free: FxHashMap::default(), fixed_points: 0, nvars: 0,
            budget: Budget { max_terms, max_mults, mults: 0, peak_terms: 0 }, fail: None, visiting: Default::default(), params: Params::Variables }
    }

    /// 塊モード(次数のベクトルの1成分を測る)。memo は前の呼び出しの覚え(into_memo で取り出す)。
    pub(crate) fn on_block(eg: &'a EGraph, moving: Option<ClassId>, memo: SymMemo) -> Self {
        let mut s = Self::new(eg, usize::MAX, u64::MAX);
        s.params = Params::Block(moving);
        s.memo = memo.memo;
        s.free = memo.free;
        s
    }
    pub(crate) fn into_memo(self) -> SymMemo { SymMemo { memo: self.memo, free: self.free } }
    fn univariate(&self) -> bool { !matches!(self.params, Params::Variables) }

    /// 線モード: 全ての媒介変数を一般の直線 u = u0 + t·w の上に乗せる。値は t の多項式で、成分の公約式で割った次数が
    /// その実体の(全ての媒介変数についての)次数。証明には使わない(次数を測る・候補を選ぶ用)。
    pub(crate) fn on_line(eg: &'a EGraph, seed: u64) -> Self {
        let mut s = Self::new(eg, usize::MAX, u64::MAX);
        // 線モードでは自由点を (0,0)・(1,0) に固定しない(固定すると、その2点の長さが定数になって次数が変わる)。
        s.params = Params::Line(seed | 1);
        s
    }

    /// 自由点 id の k 番目の媒介変数。
    fn param(&mut self, id: ClassId, k: usize) -> Option<Poly> {
        let Params::Block(moving) = self.params else { return self.new_var() };
        self.nvars += 1;
        let u0 = generic_param(id.0, k, 0x5151);
        let mut terms = FxHashMap::default();
        terms.insert(0u128, u0);
        if moving == Some(id) { terms.insert(1u128, generic_param(id.0, k, 0xA7A7)); }
        let mut p = Poly { terms, maxdeg: [0; MAX_VARS] };
        p.refresh_degrees();
        Some(p)
    }

    fn new_var(&mut self) -> Option<Poly> {
        if let Params::Line(st) = &mut self.params {
            let mut next = || { *st ^= *st << 13; *st ^= *st >> 7; *st ^= *st << 17; *st % P };
            let (a, b) = (next(), next().max(1));
            self.nvars += 1;
            let mut terms = FxHashMap::default();
            if a != 0 { terms.insert(0u128, a); }
            terms.insert(1u128, b);
            let mut p = Poly { terms, maxdeg: [0; MAX_VARS] };
            p.refresh_degrees();
            return Some(p);
        }
        if self.nvars >= MAX_VARS { self.fail.get_or_insert_with(|| format!("変数が {} 個を超える", MAX_VARS)); return None; }
        self.nvars += 1;
        Some(Poly::var(self.nvars - 1))
    }

    fn give_up<T>(&mut self, why: String) -> Option<T> { self.fail.get_or_insert(why); None }

    fn free_point(&mut self, id: ClassId) -> Option<V> {
        let eg = self.eg;
        // 自由点は探索の前の時点の代表元で引く(探索の併合で代表元が変わっても値が変わらないように。途中の値を使い回すので)。
        let rep = eg.frozen_free_key(id);
        let key = if matches!(self.params, Params::Block(_)) { id.0 } else { rep };
        if let Some(v) = self.free.get(&key) { return Some(v.clone()); }
        let curves: Vec<ClassId> = eg.premise_incidences.as_ref().map(|ps| ps.iter().filter(|(p, _)| eg.frozen_free_key(*p) == rep).map(|(_, c)| *c).collect()).unwrap_or_default();
        let v = match curves.as_slice() {
            [] if self.fixed_points < 2 && matches!(self.params, Params::Variables) => {
                self.fixed_points += 1;
                vec![Poly::constant(if self.fixed_points == 1 { 0 } else { 1 }), Poly::constant(0), Poly::constant(1)]
            }
            [] => { let (x, y) = (self.param(id, 0)?, self.param(id, 1)?); vec![x, y, Poly::constant(1)] }
            [c] => {
                let cv = self.value(*c)?;
                let t = self.param(id, 0)?;
                match eg.entities[c.0].entity_type {
                    EntityType::Line => {
                        // 原点からの垂線の足 (−ac, −bc, a² + b²) から方向 (b, −a) に沿って。
                        let bg = &mut self.budget;
                        let (a, b, c) = (&cv[0], &cv[1], &cv[2]);
                        let s = a.mul(a, bg)?.add(&b.mul(b, bg)?);
                        vec![t.mul(b, bg)?.sub(&a.mul(c, bg)?), b.mul(c, bg)?.neg().sub(&t.mul(a, bg)?), s]
                    }
                    EntityType::Conic => {
                        let Some(k) = self.known_point_of(*c) else { return self.give_up("円の上の点で、円の既知の点が無い".into()) };
                        if eg.frozen_free_key(k) == rep { return self.give_up("円の既知の点が自分".into()); }
                        let kv = self.value(k)?;
                        let bg = &mut self.budget;
                        // K を通る傾き t の直線 (t, −1, t·kx/kz… は分母が出るので、直線の係数を (t·kz, −kz, ky − t·kx) とする)。
                        let l = vec![t.mul(&kv[2], bg)?, kv[2].neg(), kv[1].sub(&t.mul(&kv[0], bg)?)];
                        second_on_conic(&kv, &l, &cv, bg)?
                    }
                    _ => return self.give_up("点・直線・円でない曲線".into()),
                }
            }
            _ => return self.give_up(format!("前提の曲線が {} 本ある自由点", curves.len())),
        };
        self.free.insert(key, v.clone());
        Some(v)
    }

    fn known_point_of(&self, conic: ClassId) -> Option<ClassId> {
        match &self.eg.entities[conic.0].original_definition {
            Definition::Circumcircle(p1, _, _) => Some(*p1),
            Definition::CircleCenterPoint(_, p) => Some(*p),
            _ => None,
        }
    }

    /// 実体の値(元の定義から)。点・直線は同次座標、円は6係数、スカラーは (分子, 分母)。
    pub(crate) fn value(&mut self, id: ClassId) -> Option<V> {
        if let Some(v) = self.memo.get(&id.0) { return v.clone(); }
        if !self.visiting.insert(id.0) { return self.give_up("定義が循環".into()); }
        let mut v = self.compute(id);
        if let Some(v) = v.as_mut() {
            strip_monomial(v);
            if self.univariate() { reduce_line(v); }
            if std::env::var("GS_DEBUG_SYM").is_ok() {
                let deg: u32 = v.iter().flat_map(|p| p.terms.keys().map(|&m| exps(m).iter().map(|&e| e as u32).sum::<u32>())).max().unwrap_or(0);
                let terms: usize = v.iter().map(|p| p.terms.len()).sum();
                println!("  SYM {:<40} {:<28} deg={:<4} terms={}", self.eg.entities[id.0].name, self.eg.entities[id.0].original_definition.get_type_name(), deg, terms);
            }
        }
        self.visiting.remove(&id.0);
        self.memo.insert(id.0, v.clone());
        v
    }

    fn compute(&mut self, id: ClassId) -> Option<V> {
        let eg = self.eg;
        if id == eg.ang90 { return Some(vec![Poly::constant(1), Poly::constant(0)]); }
        if id == eg.ang0 { return Some(vec![Poly::constant(0), Poly::constant(1)]); }
        if id == eg.line_infinity { return Some(vec![Poly::constant(0), Poly::constant(0), Poly::constant(1)]); }
        let def = eg.entities[id.0].original_definition.clone();
        let z = Poly::default;
        Some(match def {
            Definition::FreePoint => return self.free_point(id),
            Definition::Midpoint(a, b) => {
                let (a, b) = (self.value(a)?, self.value(b)?);
                let bg = &mut self.budget;
                vec![a[0].mul(&b[2], bg)?.add(&b[0].mul(&a[2], bg)?), a[1].mul(&b[2], bg)?.add(&b[1].mul(&a[2], bg)?), a[2].mul(&b[2], bg)?.scale(2)]
            }
            Definition::LineThroughPoints(a, b) => { let (a, b) = (self.value(a)?, self.value(b)?); cross(&a, &b, &mut self.budget)? }
            Definition::Intersection(a, b) => { let (a, b) = (self.value(a)?, self.value(b)?); cross(&a, &b, &mut self.budget)? }
            Definition::PerpendicularLine(l, p) => {
                let (l, p) = (self.value(l)?, self.value(p)?);
                let bg = &mut self.budget;
                vec![l[1].mul(&p[2], bg)?, l[0].mul(&p[2], bg)?.neg(), l[1].mul(&p[0], bg)?.sub(&l[0].mul(&p[1], bg)?).neg()]
            }
            Definition::ParallelLine(l, p) => {
                let (l, p) = (self.value(l)?, self.value(p)?);
                let bg = &mut self.budget;
                vec![l[0].mul(&p[2], bg)?, l[1].mul(&p[2], bg)?, l[0].mul(&p[0], bg)?.add(&l[1].mul(&p[1], bg)?).neg()]
            }
            Definition::DirectionOf(l) => { let l = self.value(l)?; vec![l[1].clone(), l[0].neg(), z()] }
            Definition::PerpDirectionOf(d) => { let d = self.value(d)?; vec![d[1].neg(), d[0].clone(), z()] }
            Definition::Circumcircle(a, b, c) => {
                let pts = [self.value(a)?, self.value(b)?, self.value(c)?];
                let bg = &mut self.budget;
                // 行 (x² + y², xz, yz, z²) の 3×4 行列の余因子が (α, β, γ, δ): α(x² + y²) + βxz + γyz + δz² = 0。
                let mut rows: Vec<[Poly; 4]> = Vec::new();
                for p in &pts {
                    rows.push([p[0].mul(&p[0], bg)?.add(&p[1].mul(&p[1], bg)?), p[0].mul(&p[2], bg)?, p[1].mul(&p[2], bg)?, p[2].mul(&p[2], bg)?]);
                }
                let minor = |cols: [usize; 3], bg: &mut Budget| -> Option<Poly> {
                    let m = |i: usize, j: usize| &rows[i][cols[j]];
                    let t1 = m(0, 0).mul(&m(1, 1).mul(m(2, 2), bg)?.sub(&m(1, 2).mul(m(2, 1), bg)?), bg)?;
                    let t2 = m(0, 1).mul(&m(1, 0).mul(m(2, 2), bg)?.sub(&m(1, 2).mul(m(2, 0), bg)?), bg)?;
                    let t3 = m(0, 2).mul(&m(1, 0).mul(m(2, 1), bg)?.sub(&m(1, 1).mul(m(2, 0), bg)?), bg)?;
                    Some(t1.sub(&t2).add(&t3))
                };
                let al = minor([1, 2, 3], bg)?;
                let be = minor([0, 2, 3], bg)?.neg();
                let ga = minor([0, 1, 3], bg)?;
                let de = minor([0, 1, 2], bg)?.neg();
                vec![al.clone(), z(), al, be, ga, de]
            }
            Definition::CircleCenterPoint(o, p) => {
                let (o, p) = (self.value(o)?, self.value(p)?);
                let bg = &mut self.budget;
                let pz2 = p[2].mul(&p[2], bg)?;
                let oz2 = o[2].mul(&o[2], bg)?;
                let lead = pz2.mul(&oz2, bg)?;
                let dx = p[0].mul(&o[2], bg)?.sub(&o[0].mul(&p[2], bg)?);
                let dy = p[1].mul(&o[2], bg)?.sub(&o[1].mul(&p[2], bg)?);
                let r2 = dx.mul(&dx, bg)?.add(&dy.mul(&dy, bg)?);
                let oo = o[0].mul(&o[0], bg)?.add(&o[1].mul(&o[1], bg)?);
                vec![lead.clone(), z(), lead, pz2.mul(&o[2], bg)?.mul(&o[0], bg)?.scale(-2), pz2.mul(&o[2], bg)?.mul(&o[1], bg)?.scale(-2),
                     pz2.mul(&oo, bg)?.sub(&r2)]
            }
            Definition::TangentLine(c, p) => {
                let (q, p) = (self.value(c)?, self.value(p)?);
                let bg = &mut self.budget;
                let e = |i: usize| -> V { (0..3).map(|j| if i == j { Poly::constant(1) } else { Poly::default() }).collect() };
                vec![bilinear(&q, &e(0), &p, bg)?, bilinear(&q, &e(1), &p, bg)?, bilinear(&q, &e(2), &p, bg)?]
            }
            Definition::SecondIntersectionOfLineAndConic(k, l, c) => {
                let (k, l, c) = (self.value(k)?, self.value(l)?, self.value(c)?);
                second_on_conic(&k, &l, &c, &mut self.budget)?
            }
            Definition::RadicalAxis(c1, c2) => { let (c1, c2) = (self.value(c1)?, self.value(c2)?); radical_axis(&c1, &c2, &mut self.budget)? }
            Definition::SecondIntersectionOfCircles(k, c1, c2) => {
                let (k, c1, c2) = (self.value(k)?, self.value(c1)?, self.value(c2)?);
                let l = radical_axis(&c1, &c2, &mut self.budget)?;
                second_on_conic(&k, &l, &c1, &mut self.budget)?
            }
            Definition::HarmonicConjugateOf(a, b, c) => {
                // C = λA + μB のとき D = λA − μB。n = A×B として λ|n|² = (C×B)·n、μ|n|² = (A×C)·n。
                let (a, b, c) = (self.value(a)?, self.value(b)?, self.value(c)?);
                let bg = &mut self.budget;
                let n = cross(&a, &b, bg)?;
                let dot = |u: &V, v: &V, bg: &mut Budget| -> Option<Poly> {
                    Some(u[0].mul(&v[0], bg)?.add(&u[1].mul(&v[1], bg)?).add(&u[2].mul(&v[2], bg)?))
                };
                let lam = dot(&cross(&c, &b, bg)?, &n, bg)?;
                let mu = dot(&cross(&a, &c, bg)?, &n, bg)?;
                (0..3).map(|i| Some(lam.mul(&a[i], bg)?.sub(&mu.mul(&b[i], bg)?))).collect::<Option<V>>()?
            }
            Definition::AnglePair(d1, d2) => {
                let (d1, d2) = (self.value(d1)?, self.value(d2)?);
                let bg = &mut self.budget;
                vec![d1[0].mul(&d2[1], bg)?.sub(&d2[0].mul(&d1[1], bg)?), d1[0].mul(&d2[0], bg)?.add(&d1[1].mul(&d2[1], bg)?)]
            }
            Definition::LengthSq(a, b) => {
                let (a, b) = (self.value(a)?, self.value(b)?);
                let bg = &mut self.budget;
                let dx = a[0].mul(&b[2], bg)?.sub(&b[0].mul(&a[2], bg)?);
                let dy = a[1].mul(&b[2], bg)?.sub(&b[1].mul(&a[2], bg)?);
                vec![dx.mul(&dx, bg)?.add(&dy.mul(&dy, bg)?), a[2].mul(&a[2], bg)?.mul(&b[2].mul(&b[2], bg)?, bg)?]
            }
            Definition::Product(a, b) => {
                let (a, b) = (self.value(a)?, self.value(b)?);
                let bg = &mut self.budget;
                vec![a[0].mul(&b[0], bg)?, a[1].mul(&b[1], bg)?]
            }
            other => return self.give_up(format!("記号計算に無い作図 {}", other.get_type_name())),
        })
    }

    /// 2つの値が比例するか(全ての 2×2 小行列式が 0)。
    fn proportional(&mut self, a: &V, b: &V) -> Option<bool> {
        if a.len() != b.len() { return self.give_up("値の形が違う".into()); }
        for i in 0..a.len() {
            for j in (i + 1)..a.len() {
                let bg = &mut self.budget;
                if !a[i].mul(&b[j], bg)?.sub(&a[j].mul(&b[i], bg)?).is_zero() { return Some(false); }
            }
        }
        Some(true)
    }

    /// 目標が恒等式か。Some(true) なら法 P で恒等的に成り立つ、Some(false) なら成り立たない(多項式が 0 でない)、None は諦めた。
    pub(crate) fn prove(&mut self, kind: &str, args: &[ClassId]) -> Option<bool> {
        match (kind, args) {
            // 値が恒等的に 0 の作図(2点が一致する円など、退化したもの)は何とでも比例・接続してしまうので、示したことにしない。
            ("Identical", [a, b]) => {
                let (va, vb) = (self.value(*a)?, self.value(*b)?);
                if is_zero_vec(&va) || is_zero_vec(&vb) { return self.give_up("値が恒等的に 0 の作図(退化)".into()); }
                self.proportional(&va, &vb)
            }
            ("Connected", [p, c]) => {
                let (vp, vc) = (self.value(*p)?, self.value(*c)?);
                if is_zero_vec(&vp) || is_zero_vec(&vc) { return self.give_up("値が恒等的に 0 の作図(退化)".into()); }
                let bg = &mut self.budget;
                let r = if vc.len() == 3 {
                    vc[0].mul(&vp[0], bg)?.add(&vc[1].mul(&vp[1], bg)?).add(&vc[2].mul(&vp[2], bg)?)
                } else { bilinear(&vc, &vp, &vp, bg)? };
                Some(r.is_zero())
            }
            ("Concyclic", [a, b, c, rest @ ..]) if !rest.is_empty() => {
                // 最初の3点が一致すると円が決まらず、行列式が恒等的に 0 になるので示したことにしない。
                let (va, vb, vc) = (self.value(*a)?, self.value(*b)?, self.value(*c)?);
                for (x, y) in [(&va, &vb), (&va, &vc), (&vb, &vc)] {
                    if self.proportional(x, y)? { return self.give_up("共円の最初の3点が恒等的に一致する(退化)".into()); }
                }
                // 5点以上は、最初の3点と残りの1点ずつの4点がそれぞれ共円。
                let mut rows: Vec<Vec<Poly>> = Vec::new();
                for &x in [*a, *b, *c].iter().chain(rest.iter()) {
                    let p = self.value(x)?;
                    let bg = &mut self.budget;
                    rows.push(vec![p[0].mul(&p[0], bg)?.add(&p[1].mul(&p[1], bg)?), p[0].mul(&p[2], bg)?, p[1].mul(&p[2], bg)?, p[2].mul(&p[2], bg)?]);
                }
                for i in 3..rows.len() {
                    let m = vec![rows[0].clone(), rows[1].clone(), rows[2].clone(), rows[i].clone()];
                    if !det(&m, &mut self.budget)?.is_zero() { return Some(false); }
                }
                Some(true)
            }
            _ => self.give_up(format!("目標 {} ×{} は記号計算に無い", kind, args.len())),
        }
    }
}

/// 行列式(余因子展開。4×4 まで)。
fn det(m: &[Vec<Poly>], bg: &mut Budget) -> Option<Poly> {
    let n = m.len();
    if n == 1 { return Some(m[0][0].clone()); }
    let mut s = Poly::default();
    for j in 0..n {
        if m[0][j].is_zero() { continue; }
        let sub: Vec<Vec<Poly>> = m[1..].iter().map(|r| r.iter().enumerate().filter(|(k, _)| *k != j).map(|(_, x)| x.clone()).collect()).collect();
        let t = m[0][j].mul(&det(&sub, bg)?, bg)?;
        s = if j % 2 == 0 { s.add(&t) } else { s.sub(&t) };
    }
    Some(s)
}

impl EGraph {
    /// 自由点の、探索の前の時点の代表元(固めていなければ今の代表元)。
    pub(crate) fn frozen_free_key(&self, id: ClassId) -> usize {
        self.frozen_free_keys.as_ref().and_then(|m| m.get(&id.0).copied()).unwrap_or_else(|| self.get_rep(id).0)
    }

    /// 目標を記号計算(Wu の方法の有理的な作図の場合)で示す。(結果, 変数の数, 最大の項数, 掛け算の回数, 諦めた理由)。
    pub(crate) fn symbolic_prove(&self, kind: &str, args: &[ClassId], max_terms: usize, max_mults: u64) -> (Option<bool>, usize, usize, u64, Option<String>) {
        self.symbolic_prove_with(kind, args, max_terms, max_mults, &mut WuMemo::default())
    }

    /// symbolic_prove を、前の試みの途中の値(memo)の続きから計算する。終わったら値の出来た実体を memo に残す(上限で諦めた実体は
    /// 次に計算し直す)。
    pub(crate) fn symbolic_prove_with(&self, kind: &str, args: &[ClassId], max_terms: usize, max_mults: u64, memo: &mut WuMemo) -> (Option<bool>, usize, usize, u64, Option<String>) {
        self.with_symbolic(max_terms, max_mults, memo, |eg, s| match eg.check_premises(s) {
            Err(why) => (None, Some(why)),
            Ok(()) => eg.prove_fact(s, kind, args),
        })
    }

    /// 与えた前提が作図から恒等的に従うか(Some(true) なら、作図だけからの計算で示したことが元の問題でも成り立つ)。
    pub(crate) fn symbolic_premises_with(&self, max_terms: usize, max_mults: u64, memo: &mut WuMemo) -> (Option<bool>, u64, Option<String>) {
        let (r, _, _, mults, fail) = self.with_symbolic(max_terms, max_mults, memo, |eg, s| match eg.check_premises(s) {
            Ok(()) => (Some(true), None),
            Err(why) => (if s.fail.is_none() && why.starts_with("前提に作図から") { Some(false) } else { None }, Some(why)),
        });
        (r, mults, fail)
    }

    /// 前提を確かめずに、事実が作図から恒等的に従うかを見る(前提は呼び出し側が symbolic_premises_with で確かめておく)。
    pub(crate) fn symbolic_fact_with(&self, kind: &str, args: &[ClassId], max_terms: usize, max_mults: u64, memo: &mut WuMemo) -> (Option<bool>, u64, Option<String>) {
        let (r, _, _, mults, fail) = self.with_symbolic(max_terms, max_mults, memo, |eg, s| eg.prove_fact(s, kind, args));
        (r, mults, fail)
    }

    fn with_symbolic(&self, max_terms: usize, max_mults: u64, memo: &mut WuMemo,
                     f: impl FnOnce(&Self, &mut Symbolic) -> (Option<bool>, Option<String>)) -> (Option<bool>, usize, usize, u64, Option<String>) {
        let mut s = Symbolic::new(self, max_terms, max_mults);
        let m = std::mem::take(memo);
        (s.memo, s.free, s.fixed_points, s.nvars) = (m.memo, m.free, m.fixed_points, m.nvars);
        let (r, fail) = f(self, &mut s);
        let out = (r, s.nvars, s.budget.peak_terms, s.budget.mults, fail);
        s.memo.retain(|_, v| v.is_some());
        *memo = WuMemo { memo: s.memo, free: s.free, fixed_points: s.fixed_points, nvars: s.nvars };
        out
    }

    /// 与えた前提(等式・作図した点の接続)は、作図から恒等的に従うもの(読み込みが作図の定義を前提として合流させたもの、
    /// 鏡映の中点など)だけを認める。従わない前提があれば、作図だけからの計算では示せない。
    fn check_premises(&self, s: &mut Symbolic) -> Result<(), String> {
        let free = self.premise_incidences.clone().unwrap_or_default();
        let mut premises: Vec<(&str, Vec<ClassId>)> = self.proof_edges.values()
            .filter(|e| matches!(e.justification, super::Justification::Given)).map(|e| ("Identical", vec![e.from, e.to])).collect();
        for (&(a, b), j) in &self.incidence_provenance {
            if !matches!(j, super::Justification::Given) { continue; }
            let (p, c) = if self.entities[a.0].entity_type == EntityType::Point { (a, b) } else { (b, a) };
            if free.iter().any(|&(q, d)| self.get_rep(q) == self.get_rep(p) && self.get_rep(d) == self.get_rep(c)) { continue; }
            premises.push(("Connected", vec![p, c]));
        }
        for (k, a) in &premises {
            match s.prove(k, a) {
                Some(true) => {}
                Some(false) => return Err("前提に作図から従わない等式・接続がある".into()),
                None => return Err(s.fail.clone().unwrap_or_else(|| "前提の確認で計算の上限".into())),
            }
        }
        Ok(())
    }

    fn prove_fact(&self, s: &mut Symbolic, kind: &str, args: &[ClassId]) -> (Option<bool>, Option<String>) {
        let r = s.prove(kind, args);
        let fail = if r.is_none() && s.fail.is_none() { Some("計算の上限(項の数・掛け算の回数・次数)".to_string()) } else { s.fail.clone() };
        (r, fail)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn field_arithmetic() {
        assert_eq!(mulm(P - 1, P - 1), 1);
        assert_eq!(addm(P - 1, 2), 1);
        let mut b = Budget { max_terms: 1000, max_mults: 100000, mults: 0, peak_terms: 0 };
        let (x, y) = (Poly::var(0), Poly::var(1));
        // (x + y)(x − y) − (x² − y²) = 0
        let l = x.add(&y).mul(&x.sub(&y), &mut b).unwrap();
        let r = x.mul(&x, &mut b).unwrap().sub(&y.mul(&y, &mut b).unwrap());
        assert!(l.sub(&r).is_zero());
    }
}

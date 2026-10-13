//! 🌟 点の差の乗法的関係(単数群)の格子 ― 筋の良い AR の測定用(改善候補 b51)。
//!
//! 点 X の等方座標 z_X = x + iy・z̄_X = x − iy は配置空間の有理関数で、点の差 z_X − z_Y・z̄_X − z̄_Y と直線の方向 a ± ib の
//! 乗法的関係(積が定数)が、AR の扱う事実(有向角・比・共円・共線・相似・中点)。作図は有理的なので座標環は多項式環(一意分解)で、
//! 関係は互いに素な基底に分けた指数の行列の整数の核として全部求まる。ここでは全ての媒介変数を一般の直線の上に乗せた一変数の
//! 多項式(法 P、i を入れて F_{P²}。P ≡ 3 (mod 4) なので −1 は平方非剰余)で基底を作る。別々の既約因子は一般の直線の上でも
//! 互いに素なので、核は変わらない。数値の標本なので測定・候補選び用で、証明には使わない。

use rustc_hash::FxHashMap;

use super::fact_census::CensusFact;
use super::symbolic::{addm, dense, invm, mulm, negm, Symbolic, V, P};

/// 一般の直線の取り方(格子と補助作図の候補で同じ記号計算を使う)。
pub(crate) const UNIT_SEED: u64 = 0x2545_F491_4F6C_DD1D;
use super::{ClassId, EGraph};

type C = (u64, u64);
const ZERO: C = (0, 0);

fn cadd(a: C, b: C) -> C { (addm(a.0, b.0), addm(a.1, b.1)) }
fn csub(a: C, b: C) -> C { (addm(a.0, negm(b.0)), addm(a.1, negm(b.1))) }
fn cmul(a: C, b: C) -> C { (addm(mulm(a.0, b.0), negm(mulm(a.1, b.1))), addm(mulm(a.0, b.1), mulm(a.1, b.0))) }
fn cinv(a: C) -> C { let n = invm(addm(mulm(a.0, a.0), mulm(a.1, a.1))); (mulm(a.0, n), mulm(negm(a.1), n)) }

/// F_{P²} の一変数多項式(次数の低い順、最高次は 0 でない)。
type Pl = Vec<C>;

fn trim(mut v: Pl) -> Pl { while v.last() == Some(&ZERO) { v.pop(); } v }
fn monic(v: Pl) -> Pl {
    let Some(&l) = v.last() else { return v };
    let inv = cinv(l);
    v.into_iter().map(|c| cmul(c, inv)).collect()
}
fn pmul(a: &[C], b: &[C]) -> Pl {
    if a.is_empty() || b.is_empty() { return Vec::new(); }
    let mut r = vec![ZERO; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() { for (j, &y) in b.iter().enumerate() { r[i + j] = cadd(r[i + j], cmul(x, y)); } }
    trim(r)
}
fn psub(a: &[C], b: &[C]) -> Pl {
    let mut r = vec![ZERO; a.len().max(b.len())];
    for (i, &x) in a.iter().enumerate() { r[i] = x; }
    for (i, &y) in b.iter().enumerate() { r[i] = csub(r[i], y); }
    trim(r)
}
/// a を b で割った (商, 余り)。
fn divrem(a: &[C], b: &[C]) -> (Pl, Pl) {
    let lb = b.len();
    if a.len() < lb { return (Vec::new(), a.to_vec()); }
    let inv = cinv(b[lb - 1]);
    let mut r = a.to_vec();
    let mut q = vec![ZERO; a.len() + 1 - lb];
    while r.len() >= lb {
        let c = cmul(r[r.len() - 1], inv);
        let s = r.len() - lb;
        q[s] = c;
        for i in 0..lb { r[s + i] = csub(r[s + i], cmul(c, b[i])); }
        r.pop();
        r = trim(r);
    }
    (q, r)
}
fn gcd(a: &[C], b: &[C]) -> Pl {
    let (mut x, mut y) = (a.to_vec(), b.to_vec());
    while !y.is_empty() { let r = divrem(&x, &y).1; x = y; y = r; }
    monic(x)
}
fn real(v: &[u64]) -> Pl { trim(v.iter().map(|&c| (c, 0)).collect()) }

/// 原子(乗法的関係の記号)。
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Atom {
    /// z_X − z_Y(conj なら z̄)の分子 (z_X Z_Y − z_Y Z_X)。点の番号は小さい方が先(向きの違いは定数倍)。
    Pair(usize, usize, bool),
    /// 点の同次座標の Z(z_X = (x + iy)/Z の分母)。
    Den(usize),
    /// 直線 ax + by + c = 0 の a + ib(conj なら a − ib)。方向の2倍角は (a + ib)/(a − ib) の定数倍。
    Line(usize, bool),
}

/// 原子の整数係数の和(乗法的関係の候補: Π 原子^係数)。
pub(crate) type RelVec = Vec<(usize, i64)>;

/// 図の点・直線の原子と、互いに素な基底での指数。
pub(crate) struct UnitRelations {
    atom_ids: FxHashMap<Atom, usize>,
    atom_list: Vec<Atom>,
    polys: Vec<Pl>,
    /// 原子ごとの、基底での指数(作ってから)。
    expo: Vec<Vec<(usize, i64)>>,
    pub base_len: usize,
    /// 互いに素な基底(factor の後)。
    basis: Vec<Pl>,
    point_of: FxHashMap<usize, usize>,
    line_of: FxHashMap<usize, usize>,
    pts: Vec<[Pl; 3]>,
    lines: Vec<[Pl; 2]>,
    /// 既知の接続の事実から分かる、直線・円の上の点(点の番号)。
    on_line: FxHashMap<usize, Vec<usize>>,
    on_conic: FxHashMap<usize, Vec<usize>>,
}

impl UnitRelations {
    fn atom(&mut self, a: Atom) -> Option<usize> {
        if let Some(&i) = self.atom_ids.get(&a) { return Some(i); }
        let p = match a {
            Atom::Pair(i, j, conj) => self.pair_poly(i, j, conj),
            Atom::Den(i) => self.pts[i][2].clone(),
            Atom::Line(l, conj) => {
                let [a, b] = &self.lines[l];
                let n = a.len().max(b.len());
                trim((0..n).map(|k| { let x = a.get(k).copied().unwrap_or(ZERO).0; let y = b.get(k).copied().unwrap_or(ZERO).0; (x, if conj { negm(y) } else { y }) }).collect())
            }
        };
        if p.is_empty() { return None; }
        let i = self.polys.len();
        self.polys.push(p);
        self.atom_ids.insert(a, i);
        self.atom_list.push(a);
        Some(i)
    }
    fn pair_poly(&self, i: usize, j: usize, conj: bool) -> Pl {
        let ([xi, yi, zi], [xj, yj, zj]) = (&self.pts[i], &self.pts[j]);
        let s = |y: &Pl| if conj { y.iter().map(|&(u, w)| (negm(u), negm(w))).collect::<Pl>() } else { y.clone() };
        // x + iy を作る(x, y は実の多項式)。
        let zc = |x: &Pl, y: &Pl| -> Pl {
            let y = s(y);
            let n = x.len().max(y.len());
            trim((0..n).map(|k| { let a = x.get(k).copied().unwrap_or(ZERO); let b = y.get(k).copied().unwrap_or(ZERO); (a.0, b.0) }).collect())
        };
        psub(&pmul(&zc(xi, yi), zj), &pmul(&zc(xj, yj), zi))
    }
    fn pair(&mut self, x: usize, y: usize, conj: bool) -> Option<usize> {
        if x == y { return None; }
        self.atom(Atom::Pair(x.min(y), x.max(y), conj))
    }
    /// 2点の方向の2倍角 (z_X − z_Y)/(z̄_X − z̄_Y)。
    fn dir_pp(&mut self, x: usize, y: usize, k: i64, v: &mut RelVec) -> Option<()> {
        v.push((self.pair(x, y, false)?, k)); v.push((self.pair(x, y, true)?, -k)); Some(())
    }
    fn dir_line(&mut self, l: usize, k: i64, v: &mut RelVec) -> Option<()> {
        v.push((self.atom(Atom::Line(l, false))?, k)); v.push((self.atom(Atom::Line(l, true))?, -k)); Some(())
    }
    fn concyclic(&mut self, [a, b, c, d]: [usize; 4], v: &mut RelVec) -> Option<()> {
        // 複比 (a,b;c,d) とその共役の比が定数。
        for (x, y, k) in [(a, c, 1), (b, d, 1), (a, d, -1), (b, c, -1)] {
            v.push((self.pair(x, y, false)?, k)); v.push((self.pair(x, y, true)?, -k));
        }
        Some(())
    }
    fn len_sq(&mut self, x: usize, y: usize, k: i64, v: &mut RelVec) -> Option<()> {
        v.push((self.pair(x, y, false)?, k)); v.push((self.pair(x, y, true)?, k));
        v.push((self.atom(Atom::Den(x))?, -2 * k)); v.push((self.atom(Atom::Den(y))?, -2 * k));
        Some(())
    }

    /// 実体の無い点(補助作図の候補)を key で足す。
    pub(crate) fn add_point(&mut self, key: usize, v: &V) -> Option<()> {
        if v.len() != 3 { return None; }
        let z = real(&dense(&v[2]));
        if z.is_empty() { return None; }
        self.point_of.insert(key, self.pts.len());
        self.pts.push([real(&dense(&v[0])), real(&dense(&v[1])), z]);
        Some(())
    }
    pub(crate) fn point_ids(&self) -> Vec<ClassId> { let mut v: Vec<ClassId> = self.point_of.keys().map(|&k| ClassId(k)).collect(); v.sort_by_key(|c| c.0); v }
    pub(crate) fn line_ids(&self) -> Vec<ClassId> { let mut v: Vec<ClassId> = self.line_of.keys().map(|&k| ClassId(k)).collect(); v.sort_by_key(|c| c.0); v }

    /// 中点 m = (a + b)/2 の定義から出る関係: (z_m − z_a)/(z_m − z_b) と、その共役が定数。
    pub(crate) fn midpoint_vectors(&mut self, m: ClassId, a: ClassId, b: ClassId) -> Vec<RelVec> {
        let (Some(&m), Some(&a), Some(&b)) = (self.point_of.get(&m.0), self.point_of.get(&a.0), self.point_of.get(&b.0)) else { return Vec::new() };
        [false, true].iter().filter_map(|&c| Some(vec![(self.pair(m, a, c)?, 1), (self.pair(m, b, c)?, -1)])).collect()
    }
    /// 2点 a・b の方向と直線 l の方向の比が定数(平行・垂直)。
    pub(crate) fn dir_point_line(&mut self, a: ClassId, b: ClassId, l: ClassId) -> Option<RelVec> {
        let (a, b, l) = (*self.point_of.get(&a.0)?, *self.point_of.get(&b.0)?, *self.line_of.get(&l.0)?);
        let mut v = RelVec::new();
        self.dir_pp(a, b, 1, &mut v)?;
        self.dir_line(l, -1, &mut v)?;
        Some(v)
    }

    /// 事実を原子の和にする(乗法的関係の形で書けない事実・点の足りない接続は None)。
    pub(crate) fn fact_vector(&mut self, f: &CensusFact) -> Option<RelVec> {
        let (on_line, on_conic) = (std::mem::take(&mut self.on_line), std::mem::take(&mut self.on_conic));
        let r = self.fact_vector_in(f, &on_line, &on_conic);
        (self.on_line, self.on_conic) = (on_line, on_conic);
        r
    }

    fn fact_vector_in(&mut self, f: &CensusFact, on_line: &FxHashMap<usize, Vec<usize>>, on_conic: &FxHashMap<usize, Vec<usize>>) -> Option<RelVec> {
        let p = |me: &Self, x: ClassId| me.point_of.get(&x.0).copied();
        let l = |me: &Self, x: ClassId| me.line_of.get(&x.0).copied();
        let mut v = RelVec::new();
        match (f.kind, f.objs.as_slice()) {
            ("共線", [a, b, c]) => { let (a, b, c) = (p(self, *a)?, p(self, *b)?, p(self, *c)?); self.dir_pp(a, b, 1, &mut v)?; self.dir_pp(a, c, -1, &mut v)?; }
            ("共円", [a, b, c, d]) => { let q = [p(self, *a)?, p(self, *b)?, p(self, *c)?, p(self, *d)?]; self.concyclic(q, &mut v)?; }
            ("等長", [a, b, c, d]) => { let (a, b, c, d) = (p(self, *a)?, p(self, *b)?, p(self, *c)?, p(self, *d)?); self.len_sq(a, b, 1, &mut v)?; self.len_sq(c, d, -1, &mut v)?; }
            ("平行" | "垂直", [a, b]) => { let (a, b) = (l(self, *a)?, l(self, *b)?); self.dir_line(a, 1, &mut v)?; self.dir_line(b, -1, &mut v)?; }
            ("等角", [a, b, c, d]) => {
                let (a, b, c, d) = (l(self, *a)?, l(self, *b)?, l(self, *c)?, l(self, *d)?);
                self.dir_line(b, 1, &mut v)?; self.dir_line(a, -1, &mut v)?; self.dir_line(d, -1, &mut v)?; self.dir_line(c, 1, &mut v)?;
            }
            ("接続(直線)", [x, ln]) => {
                let (x, li) = (p(self, *x)?, l(self, *ln)?);
                let q = on_line.get(&ln.0)?.iter().copied().find(|&q| q != x)?;
                self.dir_pp(x, q, 1, &mut v)?; self.dir_line(li, -1, &mut v)?;
            }
            ("接続(円)", [x, c]) => {
                let x = p(self, *x)?;
                let qs: Vec<usize> = on_conic.get(&c.0)?.iter().copied().filter(|&q| q != x).take(3).collect();
                if qs.len() < 3 { return None; }
                self.concyclic([qs[0], qs[1], qs[2], x], &mut v)?;
            }
            _ => return None,
        }
        let mut m: FxHashMap<usize, i64> = FxHashMap::default();
        for (a, k) in v { *m.entry(a).or_default() += k; }
        let mut v: RelVec = m.into_iter().filter(|&(_, k)| k != 0).collect();
        v.sort_unstable();
        Some(v)
    }

    /// 原子を全て互いに素な基底に分け、原子ごとの指数を求める。
    fn factor(&mut self) {
        let mut base: Vec<Pl> = Vec::new();
        for f in &self.polys {
            let mut todo = vec![f.clone()];
            'next: while let Some(f) = todo.pop() {
                let f = monic(f);
                if f.len() <= 1 { continue; }
                for j in 0..base.len() {
                    let g = gcd(&f, &base[j]);
                    if g.len() <= 1 { continue; }
                    let b = base.swap_remove(j);
                    todo.push(divrem(&b, &g).0);
                    todo.push(divrem(&f, &g).0);
                    todo.push(g);
                    continue 'next;
                }
                base.push(f);
            }
        }
        self.base_len = base.len();
        self.expo = self.polys.iter().map(|f| {
            let mut f = f.clone();
            let mut e = Vec::new();
            for (j, b) in base.iter().enumerate() {
                if f.len() <= 1 { break; }
                let mut k = 0i64;
                while f.len() >= b.len() {
                    let (q, r) = divrem(&f, b);
                    if !r.is_empty() { break; }
                    f = q;
                    k += 1;
                }
                if k > 0 { e.push((j, k)); }
            }
            e
        }).collect();
        self.basis = base;
    }

    /// 点 x(factor の後に add_point で足した点)の原子(図の点との差とその共役、Z)を足したときの、乗法的関係の格子の階数の
    /// 増え(x を含む独立な関係の数)と、x の原子の因子のうち古い原子と共有するもの・全ての因子の数(重複を込めて)。
    /// 古い原子は点 pts・直線 lns(番号、同じ点を2度含まない)のもの。測る用。
    pub(crate) fn point_gain(&self, x: usize, pts: &[usize], lns: &[usize]) -> (usize, usize, usize) {
        let mut old: Vec<usize> = Vec::new();
        for (k, &i) in pts.iter().enumerate() {
            old.extend(self.atom_ids.get(&Atom::Den(i)));
            for &j in &pts[k + 1..] { for c in [false, true] { old.extend(self.atom_ids.get(&Atom::Pair(i.min(j), i.max(j), c))); } }
        }
        for &l in lns { for c in [false, true] { old.extend(self.atom_ids.get(&Atom::Line(l, c))); } }
        let mut new: Vec<Pl> = vec![self.pts[x][2].clone()];
        for &y in pts { for c in [false, true] { let p = self.pair_poly(x, y, c); if !p.is_empty() { new.push(p); } } }
        // 古い原子の基底を新しい原子で細かくする(割れなかった元の基底は番号を持ったまま)。
        let mut cols: Vec<usize> = old.iter().flat_map(|&a| self.expo[a].iter().map(|&(j, _)| j)).collect();
        cols.sort_unstable();
        cols.dedup();
        let mut base: Vec<(Pl, Option<usize>)> = cols.iter().map(|&j| (self.basis[j].clone(), Some(j))).collect();
        let mut split: Vec<usize> = Vec::new();
        for f in &new {
            let mut todo = vec![f.clone()];
            'next: while let Some(f) = todo.pop() {
                let f = monic(f);
                if f.len() <= 1 { continue; }
                for k in 0..base.len() {
                    let g = gcd(&f, &base[k].0);
                    if g.len() <= 1 { continue; }
                    if g == base[k].0 { todo.push(divrem(&f, &g).0); continue 'next; }
                    let (b, tag) = base.swap_remove(k);
                    split.extend(tag);
                    todo.push(divrem(&b, &g).0);
                    todo.push(divrem(&f, &g).0);
                    todo.push(g);
                    continue 'next;
                }
                base.push((f, None));
            }
        }
        let col = |k: usize| base[k].1.unwrap_or(self.basis.len() + k);
        let fac = |f: &Pl, only_new: bool| -> Vec<(usize, i64)> {
            let mut f = f.clone();
            let mut e = Vec::new();
            for (k, (b, tag)) in base.iter().enumerate() {
                if only_new && tag.is_some() { continue; }
                let mut n = 0i64;
                while f.len() >= b.len() && f.len() > 1 {
                    let (q, r) = divrem(&f, b);
                    if !r.is_empty() { break; }
                    f = q;
                    n += 1;
                }
                if n > 0 { e.push((col(k), n)); }
            }
            e
        };
        let pieces: FxHashMap<usize, Vec<(usize, i64)>> = split.iter().map(|&j| (j, fac(&self.basis[j], true))).collect();
        let mut old_cols: rustc_hash::FxHashSet<usize> = cols.iter().copied().collect();
        for v in pieces.values() { old_cols.extend(v.iter().map(|&(c, _)| c)); }
        let mut el = Eliminator::default();
        for &a in &old {
            let mut m: FxHashMap<usize, i64> = FxHashMap::default();
            for &(j, e) in &self.expo[a] {
                match pieces.get(&j) { Some(ps) => for &(c, k) in ps { *m.entry(c).or_default() += e * k; }, None => *m.entry(j).or_default() += e }
            }
            el.insert(&m.into_iter().collect::<Vec<_>>());
        }
        let (mut inc, mut shared, mut total) = (0, 0, 0);
        for f in &new {
            let v = fac(f, false);
            for &(c, k) in &v { total += k as usize; if old_cols.contains(&c) { shared += k as usize; } }
            if el.insert(&v) { inc += 1; }
        }
        (new.len() - inc, shared, total)
    }
    /// 点 key の原子(差とその共役、Z)の番号。
    pub(crate) fn point_atoms(&self, key: usize) -> rustc_hash::FxHashSet<usize> {
        let Some(&p) = self.point_of.get(&key) else { return Default::default() };
        self.atom_ids.iter().filter(|(a, _)| match **a { Atom::Pair(i, j, _) => i == p || j == p, Atom::Den(i) => i == p, Atom::Line(..) => false }).map(|(_, &i)| i).collect()
    }
    /// いまの点の数(この後に add_point で足す点の番号はこれ以上)。
    pub(crate) fn npoints(&self) -> usize { self.pts.len() }
    /// 原子 a が番号 first 以上の点(add_point で足した点)を含むか。
    pub(crate) fn touches_points_from(&self, a: usize, first: usize) -> bool {
        match self.atom_list[a] { Atom::Pair(i, j, _) => i >= first || j >= first, Atom::Den(i) => i >= first, Atom::Line(..) => false }
    }
    pub(crate) fn point_index(&self, key: usize) -> Option<usize> { self.point_of.get(&key).copied() }
    pub(crate) fn line_index(&self, key: usize) -> Option<usize> { self.line_of.get(&key).copied() }

    /// 関係の候補が乗法的関係として成り立つか(基底での指数の和が 0)。
    pub(crate) fn holds(&self, v: &RelVec) -> bool {
        let mut m: FxHashMap<usize, i64> = FxHashMap::default();
        for &(a, k) in v { for &(j, e) in &self.expo[a] { *m.entry(j).or_default() += k * e; } }
        m.values().all(|&x| x == 0)
    }

    /// 原子どうしの乗法的関係の格子の階数(原子の数 − 指数の行列の階数)。
    pub(crate) fn lattice_rank(&self) -> usize {
        let mut el = Eliminator::default();
        let r = self.expo.iter().filter(|e| el.insert(e)).count();
        self.polys.len() - r
    }
    pub(crate) fn atoms(&self) -> usize { self.polys.len() }
}

/// 事実(次数の低い順に並んだもの)のうち sel が選ぶものの関係の候補が張る階数を、次数ごとに累積で返す: (次数, 階数)。
pub(crate) fn cumulative_ranks(facts: &[CensusFact], vecs: &[Option<RelVec>], sel: &dyn Fn(usize) -> bool) -> Vec<(u32, usize)> {
    let mut el = Eliminator::default();
    let mut rank = 0;
    let mut out: Vec<(u32, usize)> = Vec::new();
    for (i, f) in facts.iter().enumerate() {
        if sel(i) && let Some(v) = &vecs[i] && el.insert(v) { rank += 1; }
        match out.last_mut() { Some(last) if last.0 == f.degree => last.1 = rank, _ => out.push((f.degree, rank)) }
    }
    out
}

/// 法 P の疎な掃き出し(整数係数のベクトルの階数を測る)。
#[derive(Default, Clone)]
pub(crate) struct Eliminator { pivots: FxHashMap<usize, Vec<(usize, u64)>> }

/// 整数係数のベクトルを法 P の行(列の順)にする。
fn modp(v: &[(usize, i64)]) -> Vec<(usize, u64)> {
    let mut row: Vec<(usize, u64)> = v.iter().map(|&(i, k)| (i, k.rem_euclid(P as i64) as u64)).filter(|&(_, k)| k != 0).collect();
    row.sort_unstable();
    row
}

/// row − x · piv(どちらも列の順)。
fn axpy(row: &[(usize, u64)], x: u64, piv: &[(usize, u64)]) -> Vec<(usize, u64)> {
    let mut out = Vec::with_capacity(row.len() + piv.len());
    let (mut i, mut j) = (0, 0);
    while i < row.len() || j < piv.len() {
        let take_row = j >= piv.len() || (i < row.len() && row[i].0 < piv[j].0);
        let take_piv = i >= row.len() || (j < piv.len() && piv[j].0 < row[i].0);
        if take_row { out.push(row[i]); i += 1; }
        else if take_piv { out.push((piv[j].0, negm(mulm(x, piv[j].1)))); j += 1; }
        else { let s = addm(row[i].1, negm(mulm(x, piv[j].1))); if s != 0 { out.push((row[i].0, s)); } i += 1; j += 1; }
    }
    out
}

impl Eliminator {
    fn reduce_m(&self, mut row: Vec<(usize, u64)>) -> Vec<(usize, u64)> {
        loop {
            let Some(&(c, x)) = row.first() else { return row };
            let Some(piv) = self.pivots.get(&c) else { return row };
            // piv の先頭は 1。
            row = axpy(&row, x, piv);
        }
    }

    /// ベクトルを足して、階数が増えたら true。
    pub(crate) fn insert(&mut self, v: &[(usize, i64)]) -> bool { self.insert_m(&modp(v)) }

    /// 法 P の行(列の順)を足して、階数が増えたら true。
    pub(crate) fn insert_m(&mut self, v: &[(usize, u64)]) -> bool {
        let row = self.reduce_m(v.to_vec());
        let Some(&(c, x)) = row.first() else { return false };
        let inv = invm(x);
        self.pivots.insert(c, row.iter().map(|&(i, k)| (i, mulm(k, inv))).collect());
        true
    }

    /// 足したベクトルの張る空間に入っているか(足さない)。
    pub(crate) fn depends(&self, v: &[(usize, i64)]) -> bool { self.reduce_m(modp(v)).is_empty() }
    pub(crate) fn depends_m(&self, v: &[(usize, u64)]) -> bool { self.reduce_m(v.to_vec()).is_empty() }

    /// 張る空間を法とした標準形(要の列の成分を全て消したもの)。線形なので、張る空間に別の空間を足したときの判定を、標準形どうしの
    /// 小さな掃き出しでできる。
    pub(crate) fn normal_form(&self, v: &[(usize, i64)]) -> Vec<(usize, u64)> {
        let mut row = modp(v);
        let mut k = 0;
        while k < row.len() {
            // 要の行の列は要の列より後ろなので、k より前は変わらない。
            match self.pivots.get(&row[k].0) { Some(piv) => row = axpy(&row, row[k].1, piv), None => k += 1 }
        }
        row
    }

    /// 要の列が min_col 以上の行(min_col より前の列の成分を持たない行)。
    pub(crate) fn rows_from(&self, min_col: usize) -> Vec<Vec<(usize, u64)>> {
        let mut cols: Vec<usize> = self.pivots.keys().copied().filter(|&c| c >= min_col).collect();
        cols.sort_unstable();
        cols.into_iter().map(|c| self.pivots[&c].clone()).collect()
    }
}

impl EGraph {
    /// 事実の一覧に出てくる点・直線の原子を作り、互いに素な基底に分ける。事実ごとの関係の候補(書けないものは None)も返す。
    pub(crate) fn unit_relations(&self, facts: &[CensusFact]) -> (UnitRelations, Vec<Option<RelVec>>) {
        let mut s = Symbolic::on_line(self, UNIT_SEED);
        let (mut ur, vecs) = self.unit_relations_with(&mut s, facts);
        // 図の点の全ての組の原子も入れる(格子の階数は全ての原子について測る)。
        for i in 0..ur.pts.len() {
            ur.atom(Atom::Den(i));
            for j in (i + 1)..ur.pts.len() { ur.pair(i, j, false); ur.pair(i, j, true); }
        }
        for l in 0..ur.lines.len() { ur.atom(Atom::Line(l, false)); ur.atom(Atom::Line(l, true)); }
        ur.factor();
        (ur, vecs)
    }

    /// 点・直線の一覧の全ての組の原子を作り、互いに素な基底に分ける(測る用)。
    pub(crate) fn unit_relations_of(&self, s: &mut Symbolic, objs: &[ClassId]) -> UnitRelations {
        let fake = CensusFact { kind: "", objs: objs.to_vec(), degree: 0, known: false };
        let (mut ur, _) = self.unit_relations_with(s, std::slice::from_ref(&fake));
        for i in 0..ur.pts.len() {
            ur.atom(Atom::Den(i));
            for j in (i + 1)..ur.pts.len() { ur.pair(i, j, false); ur.pair(i, j, true); }
        }
        for l in 0..ur.lines.len() { ur.atom(Atom::Line(l, false)); ur.atom(Atom::Line(l, true)); }
        ur.factor();
        ur
    }

    /// 事実の原子のベクトルだけ(基底に分けない)。s は一般の直線の上の記号計算(補助作図の候補と同じものを使う)。
    pub(crate) fn unit_relations_with(&self, s: &mut Symbolic, facts: &[CensusFact]) -> (UnitRelations, Vec<Option<RelVec>>) {
        let mut ur = UnitRelations { atom_ids: FxHashMap::default(), atom_list: Vec::new(), polys: Vec::new(), expo: Vec::new(), base_len: 0, basis: Vec::new(),
            point_of: FxHashMap::default(), line_of: FxHashMap::default(), pts: Vec::new(), lines: Vec::new(),
            on_line: FxHashMap::default(), on_conic: FxHashMap::default() };
        let ty = |x: ClassId| self.entities[x.0].entity_type;
        for f in facts {
            for &x in &f.objs {
                if ur.point_of.contains_key(&x.0) || ur.line_of.contains_key(&x.0) { continue; }
                let Some(v) = s.value(x) else { s.fail = None; continue };
                match ty(x) {
                    super::EntityType::Point if v.len() == 3 => {
                        let z = real(&dense(&v[2]));
                        if z.is_empty() { continue; }
                        ur.point_of.insert(x.0, ur.pts.len());
                        ur.pts.push([real(&dense(&v[0])), real(&dense(&v[1])), z]);
                    }
                    super::EntityType::Line if v.len() == 3 => {
                        ur.line_of.insert(x.0, ur.lines.len());
                        ur.lines.push([real(&dense(&v[0])), real(&dense(&v[1]))]);
                    }
                    _ => {}
                }
            }
        }
        // 既知の接続の事実から、直線・円の上の点(接続を「方向・共円の関係」に直すときの相手。値の比較で見つけただけの接続を
        // 使うと、示したい接続が自分自身から従うように見えてしまう)。
        let mut on_line: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
        let mut on_conic: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
        for f in facts {
            if !f.known { continue; }
            let (Some(&x), Some(&c)) = (f.objs.first(), f.objs.get(1)) else { continue };
            let Some(&pi) = ur.point_of.get(&x.0) else { continue };
            match f.kind { "接続(直線)" => on_line.entry(c.0).or_default().push(pi), "接続(円)" => on_conic.entry(c.0).or_default().push(pi), _ => {} }
        }
        (ur.on_line, ur.on_conic) = (on_line, on_conic);
        let vecs: Vec<Option<RelVec>> = facts.iter().map(|f| ur.fact_vector(f)).collect();
        (ur, vecs)
    }
}

/// 出どころつきの掃き出し(調べる用): ベクトルがどの事実の何倍の和かを法 P で求める。
#[derive(Default)]
pub(crate) struct ProvEliminator { pivots: FxHashMap<usize, ProvRow> }

/// 正規化した行と、その出どころ(事実ごとの係数)。
type ProvRow = (Vec<(usize, u64)>, FxHashMap<usize, u64>);

impl ProvEliminator {
    fn reduce(&self, v: &[(usize, i64)]) -> (Vec<(usize, u64)>, FxHashMap<usize, u64>) {
        let mut row: Vec<(usize, u64)> = v.iter().map(|&(i, k)| (i, k.rem_euclid(P as i64) as u64)).filter(|&(_, k)| k != 0).collect();
        row.sort_unstable();
        let mut src: FxHashMap<usize, u64> = FxHashMap::default();
        loop {
            let Some(&(c, x)) = row.first() else { return (row, src) };
            let Some((piv, psrc)) = self.pivots.get(&c) else { return (row, src) };
            let mut m: FxHashMap<usize, u64> = row.iter().copied().collect();
            for &(i, k) in piv { let e = m.entry(i).or_insert(0); *e = addm(*e, negm(mulm(x, k))); }
            row = m.into_iter().filter(|&(_, k)| k != 0).collect();
            row.sort_unstable();
            for (&i, &k) in psrc { let e = src.entry(i).or_insert(0); *e = addm(*e, mulm(x, k)); }
        }
    }
    /// 事実 idx のベクトルを足す。
    pub(crate) fn insert(&mut self, v: &[(usize, i64)], idx: usize) -> bool {
        let (row, src) = self.reduce(v);
        let Some(&(c, x)) = row.first() else { return false };
        let inv = invm(x);
        // row = v − Σ src·(元のベクトル) なので、正規化した行の出どころは (idx − src)/x。
        let mut s2: FxHashMap<usize, u64> = src.into_iter().map(|(i, k)| (i, mulm(negm(k), inv))).collect();
        *s2.entry(idx).or_insert(0) = addm(s2.get(&idx).copied().unwrap_or(0), inv);
        self.pivots.insert(c, (row.iter().map(|&(i, k)| (i, mulm(k, inv))).collect(), s2));
        true
    }
    /// v が張る空間に入っていれば、事実ごとの係数(法 P)。
    pub(crate) fn explain(&self, v: &[(usize, i64)]) -> Option<Vec<(usize, u64)>> {
        let (row, src) = self.reduce(v);
        if !row.is_empty() { return None; }
        let mut out: Vec<(usize, u64)> = src.into_iter().filter(|&(_, k)| k != 0).collect();
        out.sort_unstable();
        Some(out)
    }
}

/// 法 P の値を小さな分数 a/b に戻す(有理数の復元)。
pub(crate) fn rational(c: u64) -> (i64, i64) {
    let (mut r0, mut r1) = (P as i128, c as i128);
    let (mut t0, mut t1) = (0i128, 1i128);
    let bound = 1i128 << 30;
    while r1 >= bound {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (t0, t1) = (t1, t0 - q * t1);
    }
    let (a, b) = if t1 < 0 { (-r1, -t1) } else { (r1, t1) };
    (a as i64, b as i64)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 標準形は張る空間を法とした線形写像: 和の標準形は標準形の和、張る空間の元の標準形は 0。
    #[test]
    fn normal_form_is_linear_modulo_span() {
        let mut el = Eliminator::default();
        el.insert(&[(0, 1), (2, 1)]);
        el.insert(&[(1, 1), (2, -1), (3, 2)]);
        let (a, b): (RelVec, RelVec) = (vec![(0, 3), (3, 1)], vec![(1, 2), (2, 5)]);
        let sum: RelVec = vec![(0, 3), (1, 2), (2, 5), (3, 1)];
        let mut ab: FxHashMap<usize, u64> = FxHashMap::default();
        for (i, k) in el.normal_form(&a).into_iter().chain(el.normal_form(&b)) { let e = ab.entry(i).or_insert(0); *e = addm(*e, k); }
        let mut ab: Vec<(usize, u64)> = ab.into_iter().filter(|&(_, k)| k != 0).collect();
        ab.sort_unstable();
        assert_eq!(el.normal_form(&sum), ab);
        assert!(el.normal_form(&[(0, 2), (1, -1), (2, 3), (3, -2)]).is_empty());
        // 標準形に要の列は残らない。
        assert!(el.normal_form(&a).iter().all(|(c, _)| el.pivots.get(c).is_none()));
    }
}

//! 🌟 代数的な追跡(AR、`--ar`): 複比と有向角の等式を、形式的な対数の線形代数でまとめて閉じる。
//!
//! 同じ直線の上の2点 X, Y の「差」を形式的な記号 s(X,Y) とすると(s(Y,X) = −s(X,Y))、評価器の複比
//! (A,B;C,D) = τ_C/τ_D は s(A,C)·s(D,B) / (s(C,B)·s(A,D)) と書ける(基準点 R を取った行列式 [XYR] が実際の値)。
//! 有向角は虚円点との複比 (I,J;D1,D2)、線束の複比は方向の点の複比なので、どれも無限遠直線を含む直線の上の
//! 点の複比として同じ形に載る。形式的な対数を取ると、複比の積・商の関係は記号の整数係数の和になる。
//! 数値の対数は計算しない(離散対数は要らない)。
//!
//! 係数は ℤ で持つ: 有向角は mod π なので、2θ₁ = 2θ₂ から θ₁ = θ₂ は出ない(割り算をすると健全でない)。
//! 向きの入れ替え(−1)・直角(−1)・虚円点で出る ±i は、ねじれの座標 T(4倍すると0)で持つ ― ℤⁿ ⊕ ℤ/4。
//! 等式の集合を整数の格子(エルミート標準形)に積み、各同値類の記号の式を正準な剰余に還元して、剰余が同じ
//! 同値類どうしを併合する。証明の前提には、その差を消すのに使った等式(同値類の中の2つの定義の一致)を記録する。
//!
//! 各定義を記号の式に写したら、固定座標でその式の値(行列式の積)と定義の値が一致することを確かめ、一致した
//! ものだけを使う(向きの約束の取り違えや、共点でない4直線の線束の複比などを弾く)。値の定まらない記号
//! (重なった2点の差)を含む定義も使わない(非退化条件)。

use std::collections::BTreeMap;
use std::ops::Bound::{Excluded, Unbounded};

use rustc_hash::FxHashMap;

use super::BlackboardEngine;
use crate::mmp_core::{ClassId, Definition, EGraph, EntityType, Justification};
use crate::mmp_math::ModInt;

/// 行演算を仕事量に数えるときの割り算(ar_round のコメント参照)。
const AR_OPS_PER_WORK: u64 = 16;

/// ねじれの座標(4倍すると0)。列の中で最後に来るよう最大値にする。
const T: u32 = u32::MAX;

type SVec = BTreeMap<u32, i64>;

fn add_scaled(v: &mut SVec, r: &SVec, k: i64) -> Option<()> {
    if k == 0 { return Some(()); }
    for (&c, &x) in r {
        let e = v.entry(c).or_insert(0);
        *e = e.checked_add(x.checked_mul(k)?)?;
        if *e == 0 { v.remove(&c); }
    }
    Some(())
}

fn scaled(v: &SVec, k: i64) -> Option<SVec> {
    let mut out = SVec::new();
    for (&c, &x) in v { let y = x.checked_mul(k)?; if y != 0 { out.insert(c, y); } }
    Some(out)
}

fn union(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() || j < b.len() {
        let x = match (a.get(i), b.get(j)) {
            (Some(&x), Some(&y)) if x == y => { i += 1; j += 1; x }
            (Some(&x), Some(&y)) if x < y => { i += 1; x }
            (Some(_), Some(&y)) => { j += 1; y }
            (Some(&x), None) => { i += 1; x }
            (None, Some(&y)) => { j += 1; y }
            (None, None) => unreachable!(),
        };
        out.push(x);
    }
    out
}

/// 拡張ユークリッド: (g, x, y) で x·a + y·b = g > 0。
fn egcd(a: i64, b: i64) -> (i64, i64, i64) {
    let (mut r0, mut r1, mut s0, mut s1, mut t0, mut t1) = (a, b, 1i64, 0i64, 0i64, 1i64);
    while r1 != 0 {
        let q = r0.div_euclid(r1);
        (r0, r1) = (r1, r0 - q * r1);
        (s0, s1) = (s1, s0 - q * s1);
        (t0, t1) = (t1, t0 - q * t1);
    }
    if r0 < 0 { (-r0, -s0, -t0) } else { (r0, s0, t0) }
}

/// 整数の格子(行はエルミート標準形の階段、主成分は正)。各行は、どの等式から作ったか(出どころ)を持つ。
#[derive(Default)]
struct Lattice {
    rows: BTreeMap<u32, (SVec, Vec<u32>)>,
    /// 行の組み合わせの回数(仕事量に数える)。
    ops: u64,
}

impl Lattice {
    fn insert(&mut self, mut v: SVec, mut src: Vec<u32>) -> Option<()> {
        loop {
            let Some((&c, &b)) = v.iter().next() else { return Some(()) };
            let Some((row, rsrc)) = self.rows.get(&c).cloned() else {
                if b < 0 { v = scaled(&v, -1)?; }
                self.rows.insert(c, (v, src));
                return Some(());
            };
            self.ops += 1;
            let a = row[&c];
            if b % a == 0 {
                add_scaled(&mut v, &row, -(b / a))?;
                src = union(&src, &rsrc);
            } else {
                let (g, x, y) = egcd(a, b);
                let mut new_row = scaled(&row, x)?;
                add_scaled(&mut new_row, &v, y)?;
                let mut rest = scaled(&v, a / g)?;
                add_scaled(&mut rest, &row, -(b / g))?;
                let both = union(&src, &rsrc);
                self.rows.insert(c, (new_row, both.clone()));
                v = rest;
                src = both;
            }
        }
    }

    /// 正準な剰余(主成分の列を 0 ≤ v[c] < 主成分 に揃える)と、使った行の出どころ。
    fn reduce(&mut self, v: &SVec) -> Option<(SVec, Vec<u32>)> {
        let mut v = v.clone();
        let mut src: Vec<u32> = Vec::new();
        let mut from: Option<u32> = None;
        loop {
            let next = match from { None => v.iter().next(), Some(c) => v.range((Excluded(c), Unbounded)).next() }
                .map(|(&c, &x)| (c, x));
            let Some((c, x)) = next else { break };
            if let Some((row, rsrc)) = self.rows.get(&c) {
                let q = x.div_euclid(row[&c]);
                if q != 0 {
                    self.ops += 1;
                    add_scaled(&mut v, row, -q)?;
                    src = union(&src, rsrc);
                }
            }
            from = Some(c);
        }
        Some((v, src))
    }

    /// reduce と同じ剰余を、記号1つずつの剰余(cache に溜める)の和をもう一度簡約して求める。格子を変えない間に
    /// 同じ記号を含む式をたくさん簡約するとき用。出どころは返さない(記号ごとの出どころの和は大きすぎて証明が膨らむ)
    /// ので、使うと決めた式だけ reduce で出どころを取り直す。
    fn reduce_cached(&mut self, v: &SVec, cache: &mut FxHashMap<u32, SVec>) -> Option<SVec> {
        let mut acc = SVec::new();
        for (&c, &x) in v {
            if !cache.contains_key(&c) {
                let (r, _) = self.reduce(&SVec::from([(c, 1)]))?;
                cache.insert(c, r);
            }
            add_scaled(&mut acc, &cache[&c], x)?;
        }
        Some(self.reduce(&acc)?.0)
    }
}

/// 記号の番号の端(実体・等方線束の要素)が指す実体。
fn entity_of(x: usize) -> ClassId {
    if x >= ISO_I_BASE { ClassId(x - ISO_I_BASE) } else if x >= ISO_J_BASE { ClassId(x - ISO_J_BASE) } else { ClassId(x) }
}

/// 相似 σ(番号 id、opposite は裏返し)で (A,B) が (A2,B2) に移るという2つの等式:
/// s(JA2,JB2) − s(JA,JB) − log a = 0 と、I の線束での同じ式(裏返しは I と J を入れ替える)。
fn sim_relations(atoms: &mut Atoms, a: ClassId, b: ClassId, a2: ClassId, b2: ClassId, opposite: bool, id: usize) -> Vec<SVec> {
    let maps: [(u8, fn(ClassId) -> usize, fn(ClassId) -> usize); 2] = if opposite {
        [(SIM_J, iso_i, iso_j), (SIM_I, iso_j, iso_i)]
    } else {
        [(SIM_J, iso_j, iso_j), (SIM_I, iso_i, iso_i)]
    };
    let mut out = Vec::new();
    for (kind, src_iso, dst_iso) in maps {
        let mut v = SVec::new();
        let ok = atoms.add(&mut v, dst_iso(a2), dst_iso(b2), 1).and_then(|_| atoms.add(&mut v, src_iso(a), src_iso(b), -1))
            .and_then(|_| atoms.add_fresh(&mut v, (kind, id, 0, 0), -1));
        if ok.is_some() { out.push(v); }
    }
    out
}

/// 1回の追跡の状態: 記号の表・格子・等式の出どころと、既に入れた等式。
struct ArState {
    atoms: Atoms,
    lattice: Lattice,
    premises_of: Vec<Vec<(String, Vec<ClassId>)>>,
    /// 既に格子に入れた等式(式そのもの)。同じ等式を2度入れない。
    seen: rustc_hash::FxHashSet<Vec<(u32, i64)>>,
    /// 相似な三角形の組ごとの、相似の定数の記号の番号。
    sim_ids: FxHashMap<([usize; 3], [usize; 3], bool), usize>,
    /// 2つの実体が固定座標で区別できるか(記号 s(X,Y) が意味を持つか)の判定の使い回し。
    distinct: FxHashMap<(usize, usize), bool>,
}

impl ArState {
    fn new() -> Option<Self> {
        let mut st = ArState { atoms: Atoms::default(), lattice: Lattice::default(), premises_of: Vec::new(),
            seen: Default::default(), sim_ids: FxHashMap::default(), distinct: FxHashMap::default() };
        st.lattice.insert(SVec::from([(T, 4)]), Vec::new())?;
        Some(st)
    }

    /// 等式を(まだ入れていなければ)格子に入れる。extra は、この等式を出すのに使った既存の等式(出どころ)。
    /// 入れたら Some(true)、既にあれば Some(false)、係数があふれたら None。
    fn insert(&mut self, eg: &EGraph, rel: SVec, premises: Vec<(String, Vec<ClassId>)>, extra: &[u32]) -> Option<bool> {
        if rel.is_empty() { return Some(false); }
        // 2点の差の記号は、2点が実際に別の点でないと意味を持たない(長さ 0 の差の対数)。まだマージされていないだけで
        // 図の上では同じ点(例: centroid で別々に作った2つの重心)の記号を含む等式は、格子に矛盾(2 = −1 など)を持ち込む。
        for &c in rel.keys() {
            let Some(&(x, y)) = self.atoms.pair_of.get(&c) else { continue };
            if is_virtual(x) || is_virtual(y) { continue; }
            let (ex, ey) = (entity_of(x), entity_of(y));
            if ex == ey { continue; }
            let key = (ex.0.min(ey.0), ex.0.max(ey.0));
            let ok = *self.distinct.entry(key).or_insert_with(|| eg.fixed_equal(ex, ey) == Some(Some(false)));
            if !ok { return Some(false); }
        }
        let key: Vec<(u32, i64)> = rel.iter().map(|(&c, &x)| (c, x)).collect();
        if !self.seen.insert(key) { return Some(false); }
        let id = self.premises_of.len() as u32;
        self.premises_of.push(premises);
        self.lattice.insert(rel, union(&[id], extra))?;
        Some(true)
    }
}

/// 記号の番号。s(X,Y)(順序のない点の組ごと)と、等式を作るときに導入する新しい記号(円の点の記号など)。
#[derive(Default)]
struct Atoms {
    ids: FxHashMap<(usize, usize), u32>,
    /// ids の逆引き(記号の番号 → 点の組)。
    pair_of: FxHashMap<u32, (usize, usize)>,
    fresh: FxHashMap<(u8, usize, usize, usize), u32>,
    next: u32,
}

/// 新しい記号の種類。
const THETA: u8 = 0;       // 円 C の上の点 P の記号 θ_C(P)(弦 PX の方向の記号 = θ_C(P) + θ_C(X) + c_C)
const CIRCLE_C: u8 = 1;    // 円 C の定数 c_C
const PROJ_MU: u8 = 2;     // 中心 O から直線 L への射影の、点 X の倍率 μ_{O,L}(X)
const PROJ_K: u8 = 3;      // その定数 κ_{O,L}
const CONIC_S: u8 = 4;     // 二次曲線 C の媒介変数の差 s_C(X,Y)(向きのある組)
const STEINER_MU: u8 = 5;  // 二次曲線 C の頂点 P からの線束の、点 X の倍率
const STEINER_K: u8 = 6;   // その定数
const PARALLEL_K: u8 = 7;
const LOG_PRIME: u8 = 8;
const CHART_J: u8 = 9;     // 直線 m の上の点の差と、J の等方線束の差のずれ(m ごとの定数)
const CHART_I: u8 = 10;    // 同じく I の等方線束
const CHART_0: u8 = 11;    // 等方線束のずれの差と方向の角の記号のずれ(全体で1つ)
const SIM_J: u8 = 12;      // 相似ごとの定数(J の線束の上の拡大・回転、複素数 a の対数)
const SIM_I: u8 = 13;      // 同じく I の線束(共役 ā)   // 素数 p の形式的な対数 log p(有理数の比の定数。足し算の関係から来る比を積の世界に持ち込む)  // 方向 D に沿った直線 L1 から L2 への射影(アフィン)の拡大率 κ_{D,L1,L2}

/// 等方線束の要素(点 X を通る J 方向・I 方向の等方直線 JX・IX)の番号。実体の番号・仮の無限遠点と重ならない範囲に置く。
/// JX と JY は J で交わるので、その差の記号 s(JX,JY) は J の線束の上の差(複素座標の差 z_X − z_Y)。
const ISO_J_BASE: usize = 1 << 40;
const ISO_I_BASE: usize = 1 << 41;
fn iso_j(x: ClassId) -> usize { ISO_J_BASE + x.0 }
fn iso_i(x: ClassId) -> usize { ISO_I_BASE + x.0 }
fn is_entity(id: usize) -> bool { id < ISO_J_BASE }

/// 直線の無限遠点の仮の番号(方向の点がまだ図に無い直線用)。実体の番号とは重ならない大きい側に置く。
const VIRTUAL_BASE: usize = usize::MAX / 2;
fn virtual_infinity(line: ClassId) -> usize { usize::MAX - line.0 }
fn is_virtual(id: usize) -> bool { id >= VIRTUAL_BASE }

impl Atoms {
    /// s(X,Y) を v に sign 倍で足す。X > Y なら向きを入れ替えてねじれ 2(= −1)を足す。重なった2点なら None。
    fn add(&mut self, v: &mut SVec, x: usize, y: usize, sign: i64) -> Option<()> {
        if x == y { return None; }
        let (key, flipped) = if x < y { ((x, y), false) } else { ((y, x), true) };
        let id = match self.ids.get(&key) { Some(&id) => id, None => { let id = self.next; self.next += 1; self.ids.insert(key, id); self.pair_of.insert(id, key); id } };
        add_scaled(v, &SVec::from([(id, 1)]), sign)?;
        if flipped { add_scaled(v, &SVec::from([(T, 2)]), sign)?; }
        Some(())
    }

    /// 新しい記号を v に sign 倍で足す。
    fn add_fresh(&mut self, v: &mut SVec, key: (u8, usize, usize, usize), sign: i64) -> Option<()> {
        let id = match self.fresh.get(&key) { Some(&id) => id, None => { let id = self.next; self.next += 1; self.fresh.insert(key, id); id } };
        add_scaled(v, &SVec::from([(id, 1)]), sign)
    }

    /// 向きのある差の新しい記号(s_C(Y,X) = s_C(X,Y) + ねじれ 2)。
    fn add_fresh_diff(&mut self, v: &mut SVec, kind: u8, owner: usize, x: usize, y: usize, sign: i64) -> Option<()> {
        if x == y { return None; }
        let (a, b, flipped) = if x < y { (x, y, false) } else { (y, x, true) };
        self.add_fresh(v, (kind, owner, a, b), sign)?;
        if flipped { add_scaled(v, &SVec::from([(T, 2)]), sign)?; }
        Some(())
    }

    /// 方向 D の角の記号 β(D) = s(I,D) − s(D,J)(有向角 (I,J;D1,D2) = β(D1) − β(D2))。
    fn add_beta(&mut self, v: &mut SVec, i: usize, j: usize, d: usize, sign: i64) -> Option<()> {
        self.add(v, i, d, sign)?;
        self.add(v, d, j, -sign)
    }
}

impl BlackboardEngine {
    /// 方向の点(無限遠直線の上の点)の代表元。直線の方向がまだ図に無ければ None。
    fn ar_direction(&self, line: ClassId) -> Option<ClassId> {
        let eg = &self.prover.egraph;
        eg.memo.get(&eg.normalize_definition(&Definition::DirectionOf(eg.get_rep(line)))).map(|&d| eg.get_rep(d))
    }

    /// 定義が表す複比の4点 (A,B;C,D)(代表元)。
    fn ar_cross_ratio_points(&self, def: &Definition) -> Option<[usize; 4]> {
        let eg = &self.prover.egraph;
        let r = |x: ClassId| eg.get_rep(x).0;
        match *def {
            Definition::AnglePair(d1, d2) => Some([r(eg.circ_i), r(eg.circ_j), r(d1), r(d2)]),
            Definition::CrossRatio(a, b, c, d) => Some([r(a), r(b), r(c), r(d)]),
            Definition::CrossRatioOfLines(a, b, c, d) =>
                Some([self.ar_direction(a)?.0, self.ar_direction(b)?.0, self.ar_direction(c)?.0, self.ar_direction(d)?.0]),
            _ => None,
        }
    }

    /// 点(仮の無限遠点を含む)の固定座標での値。直線 (a,b,c) の無限遠点は (b,−a,0)。
    fn ar_point_value(&self, id: usize, k: usize) -> Option<Vec<ModInt>> {
        let eg = &self.prover.egraph;
        if !is_entity(id) && !is_virtual(id) { return None; }
        if is_virtual(id) {
            let l = eg.class_value(ClassId(usize::MAX - id), k)?;
            return (l.len() >= 3).then(|| vec![l[1], -l[0], ModInt::new(0)]);
        }
        eg.class_value(ClassId(id), k)
    }

    /// 記号の式 s(A,C)·s(D,B) / (s(C,B)·s(A,D)) の固定座標での値(基準点 R の行列式 [XYR])。どれかの差が 0 なら None。
    fn ar_formula_value(&self, pts: [usize; 4], k: usize) -> Option<ModInt> {
        let p: Vec<Vec<ModInt>> = pts.iter().map(|&x| self.ar_point_value(x, k)).collect::<Option<_>>()?;
        // 基準点は一般の位置の定数(どの直線にも乗らない)。
        let rr = [ModInt::new(314_159 + 17 * k as i64), ModInt::new(271_828 + 29 * k as i64), ModInt::new(1)];
        let det = |x: &[ModInt], y: &[ModInt]| x[0] * (y[1] * rr[2] - y[2] * rr[1]) - x[1] * (y[0] * rr[2] - y[2] * rr[0]) + x[2] * (y[0] * rr[1] - y[1] * rr[0]);
        let num = det(&p[0], &p[2]) * det(&p[3], &p[1]);
        let den = det(&p[2], &p[1]) * det(&p[0], &p[3]);
        (num.0 != 0 && den.0 != 0).then(|| num / den)
    }

    /// 定義の値が記号の式の値と一致するか(全標本)。
    fn ar_verify(&self, def: &Definition, pts: [usize; 4]) -> bool {
        let eg = &self.prover.egraph;
        (0..eg.fixed_samples()).all(|k| {
            let val = eg.fixed_def_value(def, k).and_then(|v| v.first().copied());
            matches!((val, self.ar_formula_value(pts, k)), (Some(v), Some(f)) if v.0 == f.0)
        })
    }

    /// 記号の式の値が定数 c か(全標本)。
    fn ar_verify_const(&self, pts: [usize; 4], c: ModInt) -> bool {
        (0..self.prover.egraph.fixed_samples()).all(|k| matches!(self.ar_formula_value(pts, k), Some(f) if f.0 == c.0))
    }

    /// 定義から従う「比」の等式(無限遠点との複比が −1): 中点 (A,B;M,∞) = −1、調和共役 (A,B;C,D) = −1。
    /// 返り値は (4点, 前提)。
    fn ar_ratio_facts(&self) -> Vec<([usize; 4], (String, Vec<ClassId>))> {
        let eg = &self.prover.egraph;
        let mut out = Vec::new();
        for i in 0..eg.entities.len() {
            let rep = ClassId(i);
            if eg.get_rep(rep) != rep || eg.entities[i].entity_type != EntityType::Point { continue; }
            let defs = eg.entities[i].components.first().map(|c| c.definitions.clone()).unwrap_or_default();
            for def in &defs {
                let ent = eg.memo.get(&eg.normalize_definition(def)).copied().unwrap_or(rep);
                match *def {
                    Definition::Midpoint(a, b) => {
                        let (a, b) = (eg.get_rep(a), eg.get_rep(b));
                        let Some(line) = eg.find_common_line(&[a, b, rep]) else { continue };
                        let inf = self.ar_direction(line).map(|d| d.0).unwrap_or_else(|| virtual_infinity(line));
                        out.push(([a.0, b.0, rep.0, inf], ("DefinedBy:Midpoint".to_string(), vec![a, b, ent])));
                    }
                    Definition::HarmonicConjugateOf(a, b, c) => {
                        let (a, b, c) = (eg.get_rep(a), eg.get_rep(b), eg.get_rep(c));
                        out.push(([a.0, b.0, c.0, rep.0], ("DefinedBy:HarmonicConjugateOf".to_string(), vec![a, b, c, ent])));
                    }
                    _ => {}
                }
            }
        }
        out
    }

    /// 1回の追跡: 等式を格子に積み、剰余が同じ同値類を併合する。併合した数を返す。
    fn ar_round(&mut self) -> usize {
        // 格子は毎回作り直す(来歴 #85: 呼び出しをまたいで積むと、古い代表元の記号の行が溜まって遅くなり、
        // 行の出どころが合併を重ねて太り、証明が数十倍に膨らんだ)。
        let Some(mut st) = ArState::new() else { return 0 };
        let merged = self.ar_round_with(&mut st);
        // 行演算1回(疎なベクトル数項の足し算)は dfs_match 1回よりずっと軽いので、16回で仕事量1と数える
        // (nine_point_full で行演算が 80万増えて壁時計は 0.3秒しか増えず、dfs_match 1回はおよそその18倍だった)。
        self.prover.egraph.spiral_prop_work += st.lattice.ops / AR_OPS_PER_WORK;
        self.ar_ops += st.lattice.ops;
        self.ar_rounds += 1;
        merged.unwrap_or(0)
    }

    fn ar_round_with(&mut self, st: &mut ArState) -> Option<usize> {
        let (t0, ops0) = (std::time::Instant::now(), st.lattice.ops);
        let eg = &self.prover.egraph;
        let mut atoms = std::mem::take(&mut st.atoms);
        // 同値類ごとの (記号の式, その式を持つ実体)。
        let mut classes: Vec<(ClassId, Vec<(SVec, ClassId)>)> = Vec::new();
        let (mut dbg_degen, mut dbg_unverified, mut dbg_ratio) = (0usize, 0usize, 0usize);
        let (ang90, ang0) = (eg.get_rep(eg.ang90), eg.get_rep(eg.ang0));
        for i in 0..eg.entities.len() {
            let rep = ClassId(i);
            if eg.get_rep(rep) != rep || eg.entities[i].entity_type != EntityType::Scalar { continue; }
            let mut vs: Vec<(SVec, ClassId)> = Vec::new();
            if rep == ang90 { vs.push((SVec::from([(T, 2)]), eg.ang90)); }
            if rep == ang0 { vs.push((SVec::new(), eg.ang0)); }
            let defs = eg.entities[i].components.first().map(|c| c.definitions.clone()).unwrap_or_default();
            for def in &defs {
                // 長さ: LengthSq(X,Y) = (z_X − z_Y)(z̄_X − z̄_Y) = s(JX,JY) + s(IX,IY)。積は和。
                if let Some(v) = self.ar_length_vector(def, &mut atoms) {
                    let ent = eg.memo.get(&eg.normalize_definition(def)).copied().unwrap_or(rep);
                    vs.push((v, ent));
                    continue;
                }
                let Some(pts) = self.ar_cross_ratio_points(def) else { continue };
                let mut v = SVec::new();
                let [a, b, c, d] = pts;
                let ok = atoms.add(&mut v, a, c, 1).and_then(|_| atoms.add(&mut v, d, b, 1))
                    .and_then(|_| atoms.add(&mut v, c, b, -1)).and_then(|_| atoms.add(&mut v, a, d, -1));
                if ok.is_none() { dbg_degen += 1; continue; }
                if !self.ar_verify(def, pts) { dbg_unverified += 1; continue; }
                let ent = eg.memo.get(&eg.normalize_definition(def)).copied().unwrap_or(rep);
                vs.push((v, ent));
            }
            if !vs.is_empty() { classes.push((rep, vs)); }
        }

        st.atoms = atoms;
        // 等式(同値類の中の2つの式の差)。ねじれの関係 4T = 0 は状態を作るときに入れてある。
        for (_, vs) in &classes {
            for (v, ent) in &vs[1..] {
                let mut rel = v.clone();
                if add_scaled(&mut rel, &vs[0].0, -1).is_none() { continue; }
                st.insert(&self.prover.egraph, rel, vec![("Identical".to_string(), vec![*ent, vs[0].1])], &[])?;
            }
        }
        // 定義から従う比の等式(無限遠点との複比が −1)。
        let minus_one = ModInt::new(-1);
        for (pts, premise) in self.ar_ratio_facts() {
            let [a, b, c, d] = pts;
            let mut rel = SVec::new();
            let ok = st.atoms.add(&mut rel, a, c, 1).and_then(|_| st.atoms.add(&mut rel, d, b, 1))
                .and_then(|_| st.atoms.add(&mut rel, c, b, -1)).and_then(|_| st.atoms.add(&mut rel, a, d, -1))
                .and_then(|_| add_scaled(&mut rel, &SVec::from([(T, 2)]), -1));
            if ok.is_none() || !self.ar_verify_const(pts, minus_one) { continue; }
            if st.insert(&self.prover.egraph, rel, vec![premise], &[])? { dbg_ratio += 1; }
        }

        // 定理の代わりに等式を作る(円・透視射影・二次曲線の射影対応)。
        let mut gen_count = 0usize;
        for (rel, premises) in self.ar_generated_relations(&mut st.atoms) {
            if st.insert(&self.prover.egraph, rel, premises, &[])? { gen_count += 1; }
        }
        let (t1, ops1) = (std::time::Instant::now(), st.lattice.ops);
        let sims = self.ar_similarity(st)?;
        self.ar_similar += sims as u64;
        let (t2, ops2) = (std::time::Instant::now(), st.lattice.ops);
        if std::env::var("GS_DEBUG_AR").is_ok() {
            println!("  AR_DEBUG generated={} similar_pairs={} insert {:?}/{} ops, similarity {:?}/{} ops", gen_count, sims,
                t1 - t0, ops1 - ops0, t2 - t1, ops2 - ops1);
            let mapped: usize = classes.iter().map(|(_, v)| v.len()).sum();
            println!("  AR_DEBUG classes={} mapped={} degen={} unverified={} ratio_facts={} relations={} rows={} atoms={}",
                classes.len(), mapped, dbg_degen, dbg_unverified, dbg_ratio, st.premises_of.len(), st.lattice.rows.len(), st.atoms.ids.len());
        }
        // 剰余が同じ同値類を探す。ここから先は格子を変えないので、記号ごとの剰余を使い回す。
        let mut rc: FxHashMap<u32, SVec> = FxHashMap::default();
        let mut by_key: FxHashMap<Vec<(u32, i64)>, usize> = FxHashMap::default();
        let mut merges: Vec<(ClassId, ClassId, Vec<u32>)> = Vec::new();
        for (idx, (rep, vs)) in classes.iter().enumerate() {
            let Some(r) = st.lattice.reduce_cached(&vs[0].0, &mut rc) else { continue };
            let key: Vec<(u32, i64)> = r.into_iter().collect();
            match by_key.get(&key) {
                None => { by_key.insert(key, idx); }
                Some(&first) => {
                    let mut diff = vs[0].0.clone();
                    if add_scaled(&mut diff, &classes[first].1[0].0, -1).is_none() { continue; }
                    let Some((_, src)) = st.lattice.reduce(&diff) else { continue };
                    merges.push((classes[first].0, *rep, src));
                }
            }
        }
        // 方向どうしの一致: (I,J;D1,D2) の式が 0 に還元されるなら D1 = D2(平行)。等式に出てくる方向だけを見る。
        let eg = &self.prover.egraph;
        let (ci, cj) = (eg.get_rep(eg.circ_i), eg.get_rep(eg.circ_j));
        let mut dirs: Vec<ClassId> = st.atoms.ids.keys()
            .flat_map(|&(x, y)| [x, y]).filter(|&x| is_entity(x)).map(ClassId)
            .filter(|&d| d != ci && d != cj && eg.get_rep(d) == d && eg.entities[d.0].entity_type == EntityType::Point
                && eg.is_connected(d, eg.line_infinity))
            .collect();
        dirs.sort_by_key(|d| d.0);
        dirs.dedup();
        let zero = st.lattice.reduce(&SVec::new()).map(|r| r.0);
        let mut dir_merges: Vec<(ClassId, ClassId, Vec<u32>)> = Vec::new();
        for i in 0..dirs.len() {
            for j in (i + 1)..dirs.len() {
                let (d1, d2) = (dirs[i], dirs[j]);
                let mut v = SVec::new();
                let ok = st.atoms.add(&mut v, ci.0, d1.0, 1).and_then(|_| st.atoms.add(&mut v, d2.0, cj.0, 1))
                    .and_then(|_| st.atoms.add(&mut v, d1.0, cj.0, -1)).and_then(|_| st.atoms.add(&mut v, ci.0, d2.0, -1));
                if ok.is_none() { continue; }
                if st.lattice.reduce_cached(&v, &mut rc).as_ref() != zero.as_ref() { continue; }
                let Some((_, src)) = st.lattice.reduce(&v) else { continue };
                dir_merges.push((d1, d2, src));
            }
        }
        let links = self.ar_detect_concyclic(&mut st.atoms, &mut st.lattice, &mut rc, zero.as_ref());
        let parallels = self.ar_detect_parallel(&mut st.atoms, &mut st.lattice, &mut rc, zero.as_ref());
        if std::env::var("GS_DEBUG_AR").is_ok() {
            println!("  AR_DEBUG detect {:?}/{} ops", t2.elapsed(), st.lattice.ops - ops2);
        }
        merges.extend(dir_merges);
        merges.extend(parallels);

        let mut merged = 0;
        for (a, b, src) in merges {
            let eg = &mut self.prover.egraph;
            if eg.get_rep(a) == eg.get_rep(b) { continue; }
            if eg.merge_checks && eg.fixed_equal(a, b) == Some(Some(false)) {
                self.ar_rejected += 1;
                continue;
            }
            let premises: Vec<(String, Vec<ClassId>)> = src.iter()
                .flat_map(|&i| st.premises_of[i as usize].clone()).collect();
            let (na, nb) = (eg.entities[eg.get_rep(a).0].name.clone(), eg.entities[eg.get_rep(b).0].name.clone());
            if std::env::var("GS_DEBUG_AR").is_ok() { println!("  AR_DEBUG merge src={} premises={}", src.len(), premises.len()); }
            let justification = Justification::Theorem { name: "代数的な追跡(複比・有向角の線形関係)".to_string(), premises };
            if eg.merge_entities_justified(a, b, justification) {
                println!("  🧮 [代数的な追跡] {} ≡ {}", na, nb);
                merged += 1;
            }
        }
        // 円周角の逆(検出): 点を円に接続する。
        for (z, c, src) in links {
            let eg = &mut self.prover.egraph;
            let (z, c) = (eg.get_rep(z), eg.get_rep(c));
            if eg.is_connected(z, c) { continue; }
            if eg.merge_checks && eg.numeric_incidence_check(z, c, 2) == Some(false) { self.ar_rejected += 1; continue; }
            let premises: Vec<(String, Vec<ClassId>)> = src.iter().flat_map(|&i| st.premises_of[i as usize].clone()).collect();
            let (nz, nc) = (eg.entities[z.0].name.clone(), eg.entities[c.0].name.clone());
            eg.link_logical_incidence_justified(z, c, Justification::Theorem { name: "代数的な追跡(円周角の逆)".to_string(), premises });
            println!("  🧮 [代数的な追跡] {} ∈ {}", nz, nc);
            merged += 1;
        }
        Some(merged)
    }

    /// 直線の方向の点(無ければ直線ごとの仮の無限遠点)。
    fn ar_dir_or_virtual(&self, line: ClassId) -> usize {
        self.ar_direction(line).map(|d| d.0).unwrap_or_else(|| virtual_infinity(line))
    }

    /// 有限の点の代表元のうち、曲線 c に乗っているもの(図の上でも乗っていて、互いに相異なるもの)。
    fn ar_points_on(&self, c: ClassId) -> Vec<ClassId> {
        let eg = &self.prover.egraph;
        let mut out: Vec<ClassId> = eg.entities[c.0].components.first().map(|comp| comp.subobjects.iter().map(|&s| eg.get_rep(s))
            .filter(|&s| eg.entities[s.0].entity_type == EntityType::Point && !eg.is_connected(s, eg.line_infinity)).collect()).unwrap_or_default();
        out.sort_by_key(|x| x.0);
        out.dedup();
        out.retain(|&p| eg.fixed_incidence(p, c, eg.entities[c.0].entity_type) == Some(Some(true)));
        let mut distinct: Vec<ClassId> = Vec::new();
        for p in out { if distinct.iter().all(|&q| eg.fixed_equal(p, q) == Some(Some(false))) { distinct.push(p); } }
        distinct
    }

    /// 直線の代表元のうち、点 a と b を両方通るもの。
    fn ar_lines_through(&self, a: ClassId, b: ClassId) -> Vec<ClassId> {
        let eg = &self.prover.egraph;
        let mut out: Vec<ClassId> = eg.entities[a.0].components.first().map(|comp| comp.subobjects.iter().map(|&s| eg.get_rep(s))
            .filter(|&s| eg.entities[s.0].entity_type == EntityType::Line && s != eg.get_rep(eg.line_infinity) && eg.is_connected(b, s)).collect()).unwrap_or_default();
        out.sort_by_key(|x| x.0);
        out.dedup();
        out
    }

    /// 円か(虚円点 I, J を通る二次曲線)。
    fn ar_is_circle(&self, c: ClassId) -> bool {
        let eg = &self.prover.egraph;
        eg.is_connected(c, eg.get_rep(eg.circ_i)) && eg.is_connected(c, eg.get_rep(eg.circ_j))
    }

    /// 定理の代わりに作る等式と、その前提。
    /// - 円: 弦 PX の方向の記号 β = θ_C(P) + θ_C(X) + c_C、接線 β = 2θ_C(P) + c_C(円周角の定理・接弦定理)。
    ///   単位円の複素座標で、弦 PX の方向の等角座標は −p·x、接線は −p² になる(2点の積に分かれる)ことによる。
    /// - 透視射影: 中心 O から直線 L への射影は一次分数変換なので、方向の差 = 点の差 + 各点の倍率 + 定数
    ///   (点→線束・線束→点の透視射影不変性)。
    /// - 円以外の二次曲線: 頂点 P からの線束も二次曲線の媒介変数の一次分数変換なので、同じ形(シュタイナーの定理)。
    fn ar_generated_relations(&self, atoms: &mut Atoms) -> Vec<(SVec, Vec<(String, Vec<ClassId>)>)> {
        let eg = &self.prover.egraph;
        let (ci, cj) = (eg.get_rep(eg.circ_i).0, eg.get_rep(eg.circ_j).0);
        let linf = eg.get_rep(eg.line_infinity);
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        let mut out = Vec::new();
        let conics: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&c| eg.get_rep(c) == c && eg.entities[c.0].entity_type == EntityType::Conic && eg.entities[c.0].is_active()).collect();
        let lines: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&l| eg.get_rep(l) == l && l != linf && eg.entities[l.0].entity_type == EntityType::Line && eg.entities[l.0].is_active()).collect();
        let tangent_of = |l: ClassId| -> Option<(ClassId, ClassId)> {
            eg.entities[l.0].components.first()?.definitions.iter().find_map(|d| match *d {
                Definition::TangentLine(c, p) => Some((eg.get_rep(c), eg.get_rep(p))), _ => None })
        };

        for &c in &conics {
            let pts = self.ar_points_on(c);
            if pts.len() < 2 { continue; }
            if self.ar_is_circle(c) {
                // 弦
                for i in 0..pts.len() {
                    for j in (i + 1)..pts.len() {
                        let (p, x) = (pts[i], pts[j]);
                        for l in self.ar_lines_through(p, x) {
                            let d = self.ar_dir_or_virtual(l);
                            let mut v = SVec::new();
                            let ok = atoms.add_beta(&mut v, ci, cj, d, 1)
                                .and_then(|_| atoms.add_fresh(&mut v, (THETA, c.0, p.0, 0), -1))
                                .and_then(|_| atoms.add_fresh(&mut v, (THETA, c.0, x.0, 0), -1))
                                .and_then(|_| atoms.add_fresh(&mut v, (CIRCLE_C, c.0, 0, 0), -1));
                            if ok.is_some() { out.push((v, vec![conn(p, c), conn(x, c), conn(p, l), conn(x, l)])); }
                        }
                    }
                }
                // 接線
                for &l in &lines {
                    let Some((tc, tp)) = tangent_of(l) else { continue };
                    if tc != c || !pts.contains(&tp) { continue; }
                    let d = self.ar_dir_or_virtual(l);
                    let mut v = SVec::new();
                    let ok = atoms.add_beta(&mut v, ci, cj, d, 1)
                        .and_then(|_| atoms.add_fresh(&mut v, (THETA, c.0, tp.0, 0), -2))
                        .and_then(|_| atoms.add_fresh(&mut v, (CIRCLE_C, c.0, 0, 0), -1));
                    if ok.is_some() { out.push((v, vec![conn(tp, c), ("DefinedBy:TangentLine".to_string(), vec![c, tp, l])])); }
                }
            } else if pts.len() >= 4 {
                // 二次曲線の頂点 P からの線束(接線は X = P の方向)。
                for &p in &pts {
                    let mut rays: Vec<(ClassId, usize, Vec<(String, Vec<ClassId>)>)> = Vec::new();
                    for &x in &pts {
                        if x == p { continue; }
                        if let Some(l) = self.ar_lines_through(p, x).first().copied() {
                            rays.push((x, self.ar_dir_or_virtual(l), vec![conn(p, c), conn(x, c), conn(p, l), conn(x, l)]));
                        }
                    }
                    for &l in &lines {
                        if let Some((tc, tp)) = tangent_of(l) && tc == c && tp == p {
                            rays.push((p, self.ar_dir_or_virtual(l), vec![conn(p, c), ("DefinedBy:TangentLine".to_string(), vec![c, p, l])]));
                        }
                    }
                    if rays.len() < 4 { continue; }
                    for a in 0..rays.len() {
                        for b in (a + 1)..rays.len() {
                            let (x, dx, px) = &rays[a];
                            let (y, dy, py) = &rays[b];
                            let mut v = SVec::new();
                            let ok = atoms.add(&mut v, *dx, *dy, 1)
                                .and_then(|_| atoms.add_fresh_diff(&mut v, CONIC_S, c.0, x.0, y.0, -1))
                                .and_then(|_| atoms.add_fresh(&mut v, (STEINER_MU, c.0, p.0, x.0), -1))
                                .and_then(|_| atoms.add_fresh(&mut v, (STEINER_MU, c.0, p.0, y.0), -1))
                                .and_then(|_| atoms.add_fresh(&mut v, (STEINER_K, c.0, p.0, 0), -1));
                            if ok.is_some() { out.push((v, [px.clone(), py.clone()].concat())); }
                        }
                    }
                }
            }
        }

        // 透視射影: 中心 O を通る直線と直線 L の交点 X ごとに、方向 OX と L の上の X を対応させる。
        let points: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&o| eg.get_rep(o) == o && eg.entities[o.0].entity_type == EntityType::Point && eg.entities[o.0].is_active()
                && !eg.is_connected(o, linf)).collect();
        for &o in &points {
            let through_o: Vec<ClassId> = eg.entities[o.0].components.first().map(|comp| comp.subobjects.iter().map(|&s| eg.get_rep(s))
                .filter(|&s| s != linf && eg.entities[s.0].entity_type == EntityType::Line).collect()).unwrap_or_default();
            if through_o.len() < 3 { continue; }
            for &l in &lines {
                if eg.is_connected(o, l) || eg.fixed_incidence(o, l, EntityType::Line) != Some(Some(false)) { continue; }
                let mut rays: Vec<(ClassId, usize, ClassId)> = Vec::new();
                for &m in &through_o {
                    // m と L の交点のうち図にある有限の点。
                    let Some(x) = self.ar_points_on(l).into_iter().find(|&x| x != o && eg.is_connected(x, m)) else { continue };
                    if rays.iter().any(|r| r.0 == x) { continue; }
                    rays.push((x, self.ar_dir_or_virtual(m), m));
                }
                if rays.len() < 3 { continue; }
                for a in 0..rays.len() {
                    for b in (a + 1)..rays.len() {
                        let (x, dx, mx) = rays[a];
                        let (y, dy, my) = rays[b];
                        let mut v = SVec::new();
                        let ok = atoms.add(&mut v, dx, dy, 1)
                            .and_then(|_| atoms.add(&mut v, x.0, y.0, -1))
                            .and_then(|_| atoms.add_fresh(&mut v, (PROJ_MU, o.0, l.0, x.0), -1))
                            .and_then(|_| atoms.add_fresh(&mut v, (PROJ_MU, o.0, l.0, y.0), -1))
                            .and_then(|_| atoms.add_fresh(&mut v, (PROJ_K, o.0, l.0, 0), -1));
                        if ok.is_some() {
                            out.push((v, vec![conn(o, mx), conn(x, mx), conn(x, l), conn(o, my), conn(y, my), conn(y, l)]));
                        }
                    }
                }
            }
        }

        // 等方線束と直線のつながり: J から直線 m への射影は m の無限遠点を無限遠直線に移すので、J の線束の差と m の上の差の
        // ずれは m ごとの定数(s(JX,JY) = s(X,Y) + κ_J(m))。I も同じ。ずれの差は m の方向の角の記号と全体の定数だけずれる
        // (z の差と z̄ の差の比が方向の等角座標)。
        for &m in &lines {
            let pts = self.ar_points_on(m);
            if pts.len() < 2 { continue; }
            for a in 0..pts.len() {
                for b in (a + 1)..pts.len() {
                    let (x, y) = (pts[a], pts[b]);
                    for (kind, iso) in [(CHART_J, iso_j as fn(ClassId) -> usize), (CHART_I, iso_i as fn(ClassId) -> usize)] {
                        let mut v = SVec::new();
                        let ok = atoms.add(&mut v, iso(x), iso(y), 1).and_then(|_| atoms.add(&mut v, x.0, y.0, -1))
                            .and_then(|_| atoms.add_fresh(&mut v, (kind, m.0, 0, 0), -1));
                        if ok.is_some() { out.push((v, vec![conn(x, m), conn(y, m)])); }
                    }
                }
            }
            let d = self.ar_dir_or_virtual(m);
            let mut v = SVec::new();
            let ok = atoms.add_fresh(&mut v, (CHART_J, m.0, 0, 0), 1).and_then(|_| atoms.add_fresh(&mut v, (CHART_I, m.0, 0, 0), -1))
                .and_then(|_| atoms.add_beta(&mut v, ci, cj, d, -1)).and_then(|_| atoms.add_fresh(&mut v, (CHART_0, 0, 0, 0), -1));
            if ok.is_some() { out.push((v, vec![conn(pts[0], m), conn(pts[1], m)])); }
        }

        // アフィンの等式: 同じ直線の上では、無限遠点までの差 s(X,∞_L) が一定(z=1 の座標で [X ∞ R] が X によらない)。
        // これで無限遠点との複比が本物の比になる(中点 (A,B;M,∞) = −1 から AM = MB)。座標の取り方によらない量
        // (複比・方向)の併合にしか使わないので健全。
        let mut on_line: FxHashMap<usize, Vec<ClassId>> = FxHashMap::default();
        for &l in &lines {
            let pts = self.ar_points_on(l);
            if pts.len() >= 2 {
                let inf = self.ar_dir_or_virtual(l);
                for &x in &pts[1..] {
                    let mut v = SVec::new();
                    let ok = atoms.add(&mut v, x.0, inf, 1).and_then(|_| atoms.add(&mut v, pts[0].0, inf, -1));
                    if ok.is_some() { out.push((v, vec![conn(pts[0], l), conn(x, l)])); }
                }
            }
            on_line.insert(l.0, pts);
        }

        // 中点の比(足し算の関係 A − B = 2(M − B) から来る、定数 2 の比): s(A,B) = s(A,M) + log 2、s(B,A) = s(B,M) + log 2。
        // 無限遠点との複比 −1 は「AM = MB」しか言わず、「BA = 2·BM」は足し算からしか出ないので、ここで定義から入れる。
        for i in 0..eg.entities.len() {
            let m = ClassId(i);
            if eg.get_rep(m) != m || eg.entities[i].entity_type != EntityType::Point { continue; }
            let defs = eg.entities[i].components.first().map(|c| c.definitions.clone()).unwrap_or_default();
            for def in &defs {
                let Definition::Midpoint(a, b) = *def else { continue };
                let (a, b) = (eg.get_rep(a), eg.get_rep(b));
                if a == b || a == m || b == m { continue; }
                let ent = eg.memo.get(&eg.normalize_definition(def)).copied().unwrap_or(m);
                let premise = vec![("DefinedBy:Midpoint".to_string(), vec![a, b, ent])];
                for (x, y) in [(a, b), (b, a)] {
                    let mut v = SVec::new();
                    let ok = atoms.add(&mut v, x.0, y.0, 1).and_then(|_| atoms.add(&mut v, x.0, m.0, -1))
                        .and_then(|_| atoms.add_fresh(&mut v, (LOG_PRIME, 2, 0, 0), -1));
                    if ok.is_some() { out.push((v, premise.clone())); }
                }
            }
        }

        // 平行 ⇒ 比: 方向 D の平行線の族に沿った L1 から L2 への射影はアフィンなので、対応する2点の差の比は一定
        // (s_{L2}(X2,Y2) − s_{L1}(X1,Y1) = κ)。2直線の交点は自分自身に対応する。
        for (d, fam, l1, l2, corr) in self.ar_parallel_correspondences(&lines, &on_line) {
            for a in 0..corr.len() {
                for b in (a + 1)..corr.len() {
                    let ((x1, x2, pa), (y1, y2, pb)) = (&corr[a], &corr[b]);
                    let mut v = SVec::new();
                    let ok = atoms.add(&mut v, x2.0, y2.0, 1)
                        .and_then(|_| atoms.add(&mut v, x1.0, y1.0, -1))
                        .and_then(|_| atoms.add_fresh(&mut v, (PARALLEL_K, d, l1.0, l2.0), -1));
                    if ok.is_some() { out.push((v, [pa.clone(), pb.clone(), fam.clone()].concat())); }
                }
            }
        }
        out
    }

    /// 方向 D の平行線の族が2直線 L1 < L2 を切る点の対応 (X1 ∈ L1, X2 ∈ L2)。2直線が交わる点は自分自身に対応する。
    /// 返り値は (D, 族全体の前提(今は空), L1, L2, [(X1, X2, 前提)])。対応が2つ以上あるものだけ。
    #[allow(clippy::type_complexity)]
    fn ar_parallel_correspondences(&self, lines: &[ClassId], on_line: &FxHashMap<usize, Vec<ClassId>>)
        -> Vec<(usize, Vec<(String, Vec<ClassId>)>, ClassId, ClassId, Vec<(ClassId, ClassId, Vec<(String, Vec<ClassId>)>)>)> {
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        let mut families: FxHashMap<usize, Vec<ClassId>> = FxHashMap::default();
        for &m in lines {
            if let Some(d) = self.ar_direction(m) { families.entry(d.0).or_default().push(m); }
        }
        let mut out = Vec::new();
        let mut dirs: Vec<usize> = families.keys().copied().collect();
        dirs.sort();
        for d in dirs {
            let fam = &families[&d];
            if fam.is_empty() { continue; }
            for i in 0..lines.len() {
                for j in (i + 1)..lines.len() {
                    let (l1, l2) = (lines[i], lines[j]);
                    if fam.contains(&l1) || fam.contains(&l2) { continue; }
                    let (p1, p2) = (&on_line[&l1.0], &on_line[&l2.0]);
                    let mut corr: Vec<(ClassId, ClassId, Vec<(String, Vec<ClassId>)>)> = Vec::new();
                    // 2直線の交点
                    if let Some(&a) = p1.iter().find(|a| p2.contains(a)) { corr.push((a, a, vec![conn(a, l1), conn(a, l2)])); }
                    for &m in fam {
                        let on_m = &on_line[&m.0];
                        let x1 = p1.iter().find(|x| on_m.contains(x));
                        let x2 = p2.iter().find(|x| on_m.contains(x));
                        if let (Some(&x1), Some(&x2)) = (x1, x2) {
                            if x1 == x2 || corr.iter().any(|c| c.0 == x1 || c.1 == x2) { continue; }
                            corr.push((x1, x2, vec![conn(x1, l1), conn(x1, m), conn(x2, l2), conn(x2, m),
                                ("DefinedBy:DirectionOf".to_string(), vec![m, ClassId(d)])]));
                        }
                    }
                    if corr.len() >= 2 { out.push((d, Vec::new(), l1, l2, corr)); }
                }
            }
        }
        out
    }

    /// 比 ⇒ 平行(検出)。2直線 L1, L2 を切る横断線 m_i(L1 と X1_i、L2 と X2_i で交わる)について:
    /// - L1, L2 が点 A で交わるなら、AX2_i / AX1_i の比が2本で一致すれば m_i ∥ m_j(中点連結定理はこの特別な場合)。
    /// - 既に平行な m_i ∥ m_j があり、第3の m_k で X1_i X1_k / X1_i X1_j と X2_i X2_k / X2_i X2_j が一致すれば m_k ∥ m_i。
    /// 返り値は併合する方向の組と、使った等式。
    fn ar_detect_parallel(&self, atoms: &mut Atoms, lattice: &mut Lattice, rc: &mut FxHashMap<u32, SVec>, zero: Option<&SVec>) -> Vec<(ClassId, ClassId, Vec<u32>)> {
        let eg = &self.prover.egraph;
        let linf = eg.get_rep(eg.line_infinity);
        let mut out = Vec::new();
        let Some(zero) = zero else { return out };
        let lines: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&l| eg.get_rep(l) == l && l != linf && eg.entities[l.0].entity_type == EntityType::Line && eg.entities[l.0].is_active()).collect();
        let on_line: FxHashMap<usize, Vec<ClassId>> = lines.iter().map(|&l| (l.0, self.ar_points_on(l))).collect();
        for i in 0..lines.len() {
            for j in (i + 1)..lines.len() {
                let (l1, l2) = (lines[i], lines[j]);
                let (p1, p2) = (&on_line[&l1.0], &on_line[&l2.0]);
                if p1.len() < 2 || p2.len() < 2 { continue; }
                let shared = p1.iter().find(|a| p2.contains(a)).copied();
                // 横断線: L1, L2 以外の直線で、L1 と L2 のそれぞれと図にある点で交わるもの(交点は共有点以外)。
                let mut trans: Vec<(ClassId, ClassId, ClassId, ClassId)> = Vec::new(); // (m, X1, X2, dir)
                for &m in &lines {
                    if m == l1 || m == l2 { continue; }
                    let on_m = &on_line[&m.0];
                    let x1 = p1.iter().find(|x| on_m.contains(x) && Some(**x) != shared);
                    let x2 = p2.iter().find(|x| on_m.contains(x) && Some(**x) != shared);
                    let (Some(&x1), Some(&x2)) = (x1, x2) else { continue };
                    if x1 == x2 { continue; }
                    let Some(d) = self.ar_direction(m) else { continue };
                    trans.push((m, x1, x2, d));
                }
                if trans.len() < 2 { continue; }
                for a in 0..trans.len() {
                    for b in (a + 1)..trans.len() {
                        let (ma, xa1, xa2, da) = trans[a];
                        let (mb, xb1, xb2, db) = trans[b];
                        if da == db || ma == mb { continue; }
                        let mut v = SVec::new();
                        let ok = if let Some(o) = shared {
                            // s(A,Xa2) − s(A,Xa1) − s(A,Xb2) + s(A,Xb1) ≡ 0
                            atoms.add(&mut v, o.0, xa2.0, 1).and_then(|_| atoms.add(&mut v, o.0, xa1.0, -1))
                                .and_then(|_| atoms.add(&mut v, o.0, xb2.0, -1)).and_then(|_| atoms.add(&mut v, o.0, xb1.0, 1))
                        } else {
                            // 既に平行な横断線 m_c ∥ m_a を基準に、m_b が同じ比で切るか。
                            let Some(&(_, xc1, xc2, _)) = trans.iter().find(|t| t.3 == da && t.0 != ma) else { continue };
                            atoms.add(&mut v, xc2.0, xa2.0, 1).and_then(|_| atoms.add(&mut v, xc1.0, xa1.0, -1))
                                .and_then(|_| atoms.add(&mut v, xc2.0, xb2.0, -1)).and_then(|_| atoms.add(&mut v, xc1.0, xb1.0, 1))
                        };
                        if ok.is_none() { continue; }
                        if lattice.reduce_cached(&v, rc).as_ref() != Some(zero) { continue; }
                        let Some((_, src)) = lattice.reduce(&v) else { continue };
                        out.push((da, db, src));
                    }
                }
            }
        }
        out
    }

    /// 長さの記号の式: LengthSq(X,Y) = s(JX,JY) + s(IX,IY)、Product(a,b) は a と b の(LengthSq の)式の和。
    fn ar_length_vector(&self, def: &Definition, atoms: &mut Atoms) -> Option<SVec> {
        let eg = &self.prover.egraph;
        let len = |d: &Definition, atoms: &mut Atoms| -> Option<SVec> {
            let Definition::LengthSq(x, y) = *d else { return None };
            let (x, y) = (eg.get_rep(x), eg.get_rep(y));
            if x == y || eg.is_connected(x, eg.line_infinity) || eg.is_connected(y, eg.line_infinity) { return None; }
            let mut v = SVec::new();
            atoms.add(&mut v, iso_j(x), iso_j(y), 1)?;
            atoms.add(&mut v, iso_i(x), iso_i(y), 1)?;
            Some(v)
        };
        match def {
            Definition::LengthSq(..) => len(def, atoms),
            Definition::Product(a, b) => {
                let first_len = |c: ClassId| eg.entities[eg.get_rep(c).0].components.first()
                    .and_then(|comp| comp.definitions.iter().find(|d| matches!(d, Definition::LengthSq(..))).cloned());
                let (da, db) = (first_len(*a)?, first_len(*b)?);
                let mut v = len(&da, atoms)?;
                add_scaled(&mut v, &len(&db, atoms)?, 1)?;
                Some(v)
            }
            _ => None,
        }
    }

    /// 相似の検出(AA)と結論。3辺が図にある三角形の、2つの頂点の有向角の記号の正準な剰余を鍵にして、同じ鍵の三角形どうしを
    /// 同じ向きの相似、符号を変えた鍵と一致するものを裏返しの相似とする。
    /// 同じ向きの相似は I と J を動かさない射影変換なので、J の線束の上では拡大・回転(複素数 a 倍)になる:
    /// 対応する各辺 (X,Y) について s(JX′,JY′) = s(JX,JY) + log a、I の線束で s(IX′,IY′) = s(IX,IY) + log ā。
    /// 裏返しは I と J を入れ替える。仮定の角から結論を出すのは線形でない(三角形が閉じる条件が足し算)ので、ここで検出して等式を足す。
    /// 返り値は足した相似の組の数。
    fn ar_similarity(&self, st: &mut ArState) -> Option<usize> {
        const MAX_TRIANGLES: usize = 3000;
        const MAX_PAIRS: usize = 400;
        let eg = &self.prover.egraph;
        let (ci, cj) = (eg.get_rep(eg.circ_i).0, eg.get_rep(eg.circ_j).0);
        let linf = eg.get_rep(eg.line_infinity);
        let points: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&o| eg.get_rep(o) == o && eg.entities[o.0].entity_type == EntityType::Point && eg.entities[o.0].is_active()
                && !eg.is_connected(o, linf)).collect();
        // 辺: 2点を通る直線が図にある組。
        let mut edge: FxHashMap<(usize, usize), ClassId> = FxHashMap::default();
        let mut nbr: FxHashMap<usize, Vec<ClassId>> = FxHashMap::default();
        for i in 0..points.len() {
            for j in (i + 1)..points.len() {
                let (a, b) = (points[i], points[j]);
                if let Some(&l) = self.ar_lines_through(a, b).first() {
                    edge.insert((a.0, b.0), l);
                    nbr.entry(a.0).or_default().push(b);
                    nbr.entry(b.0).or_default().push(a);
                }
            }
        }
        let line_of = |a: ClassId, b: ClassId| edge.get(&(a.0.min(b.0), a.0.max(b.0))).copied();
        let mut tris: Vec<[ClassId; 3]> = Vec::new();
        'outer: for &a in &points {
            let Some(na) = nbr.get(&a.0) else { continue };
            for &b in na {
                if b.0 <= a.0 { continue; }
                for &c in na {
                    if c.0 <= b.0 || line_of(b, c).is_none() { continue; }
                    let (lab, lbc, lca) = (line_of(a, b).unwrap(), line_of(b, c).unwrap(), line_of(c, a).unwrap());
                    if lab == lbc || lbc == lca || lca == lab { continue; }
                    if eg.fixed_collinear(&[a, b, c]) != Some(Some(false)) { continue; }
                    tris.push([a, b, c]);
                    if tris.len() >= MAX_TRIANGLES { break 'outer; }
                }
            }
        }
        // 順序つきの三角形 (P,Q,R) の鍵 = (P での角, Q での角) の剰余。角は2方向だけで決まるので、方向の β の剰余と
        // 角の剰余(と符号を変えた剰余)を方向の組ごとに1度だけ求める(剰余は線形なので、剰余の差をもう一度簡約すればよい)。
        // 出どころは、相似の組として使うと決めたものだけ、角の式を直接簡約して取り直す。
        let mut beta_cache: FxHashMap<usize, Option<SVec>> = FxHashMap::default();
        let mut angle_cache: FxHashMap<(usize, usize), Option<(SVec, SVec)>> = FxHashMap::default();
        let mut angle = |st: &mut ArState, p: ClassId, q: ClassId, r: ClassId| -> Option<(SVec, SVec)> {
            let (dpq, dpr) = (self.ar_dir_or_virtual(line_of(p, q)?), self.ar_dir_or_virtual(line_of(p, r)?));
            if let Some(a) = angle_cache.get(&(dpq, dpr)) { return a.clone(); }
            let mut beta = |st: &mut ArState, d: usize| -> Option<SVec> {
                if let Some(b) = beta_cache.get(&d) { return b.clone(); }
                let mut v = SVec::new();
                let b = st.atoms.add_beta(&mut v, ci, cj, d, 1).and_then(|_| st.lattice.reduce(&v)).map(|r| r.0);
                beta_cache.insert(d, b.clone());
                b
            };
            let a = (|| {
                let mut v = beta(st, dpq)?;
                add_scaled(&mut v, &beta(st, dpr)?, -1)?;
                let (k, _) = st.lattice.reduce(&v)?;
                let (m, _) = st.lattice.reduce(&scaled(&k, -1)?)?;
                Some((k, m))
            })();
            angle_cache.insert((dpq, dpr), a.clone());
            a
        };
        // 三角形 (P,Q,R) の P と Q の角の式を直接簡約したときの出どころ。
        let exact_src = |st: &mut ArState, t: &[ClassId; 3]| -> Option<Vec<u32>> {
            let mut src = Vec::new();
            for (p, q, r) in [(t[0], t[1], t[2]), (t[1], t[2], t[0])] {
                let mut v = SVec::new();
                st.atoms.add_beta(&mut v, ci, cj, self.ar_dir_or_virtual(line_of(p, q)?), 1)?;
                st.atoms.add_beta(&mut v, ci, cj, self.ar_dir_or_virtual(line_of(p, r)?), -1)?;
                src = union(&src, &st.lattice.reduce(&v)?.1);
            }
            Some(src)
        };
        type Key = (Vec<(u32, i64)>, Vec<(u32, i64)>);
        let mut by_key: FxHashMap<Key, Vec<[ClassId; 3]>> = FxHashMap::default();
        let mut entries: Vec<([ClassId; 3], Key, Key)> = Vec::new();
        for t in &tris {
            for [p, q, r] in [[t[0], t[1], t[2]], [t[0], t[2], t[1]], [t[1], t[0], t[2]], [t[1], t[2], t[0]], [t[2], t[0], t[1]], [t[2], t[1], t[0]]] {
                let (Some((kp, mp)), Some((kq, mq))) = (angle(st, p, q, r), angle(st, q, r, p)) else { continue };
                let key: Key = (kp.into_iter().collect(), kq.into_iter().collect());
                let mirror: Key = (mp.into_iter().collect(), mq.into_iter().collect());
                by_key.entry(key.clone()).or_default().push([p, q, r]);
                entries.push(([p, q, r], key, mirror));
            }
        }
        let sorted_set = |t: &[ClassId; 3]| { let mut v = t.map(|x| x.0); v.sort(); v };
        let mut done: rustc_hash::FxHashSet<([usize; 3], [usize; 3], bool)> = rustc_hash::FxHashSet::default();
        let mut pairs = 0usize;
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        // 見つけた相似の組 (t, u, 裏返しか, 番号)。後で対応する点を探す。
        let mut found: Vec<([ClassId; 3], [ClassId; 3], bool, usize)> = Vec::new();
        'scan: for (t, key, mirror) in &entries {
            for (opposite, k) in [(false, key), (true, mirror)] {
                let Some(others) = by_key.get(k) else { continue };
                for u in others {
                    let (sa, sb) = (sorted_set(t), sorted_set(u));
                    if sa == sb || sa > sb || !done.insert((sa, sb, opposite)) { continue; }
                    if pairs >= MAX_PAIRS { break 'scan; }
                    let next = st.sim_ids.len();
                    let id = *st.sim_ids.entry((sa, sb, opposite)).or_insert(next);
                    let mut prem: Vec<(String, Vec<ClassId>)> = Vec::new();
                    for (x, y) in [(0, 1), (0, 2), (1, 2)] {
                        for tr in [t, u] {
                            if let Some(l) = line_of(tr[x], tr[y]) { prem.push(conn(tr[x], l)); prem.push(conn(tr[y], l)); }
                        }
                    }
                    let (Some(ts), Some(us)) = (exact_src(st, t), exact_src(st, u)) else { continue };
                    let key_src = union(&ts, &us);
                    let mut added = false;
                    for (x, y) in [(0, 1), (0, 2), (1, 2)] {
                        for v in sim_relations(&mut st.atoms, t[x], t[y], u[x], u[y], opposite, id) {
                            if st.insert(&self.prover.egraph, v, prem.clone(), &key_src)? { added = true; }
                        }
                    }
                    if added { pairs += 1; }
                    if std::env::var("GS_DEBUG_AR").is_ok() {
                        let nm = |c: ClassId| eg.entities[c.0].name.clone();
                        println!("  AR_DEBUG sim [{} {} {}] ~ [{} {} {}] opp={}", nm(t[0]), nm(t[1]), nm(t[2]), nm(u[0]), nm(u[1]), nm(u[2]), opposite);
                    }
                    found.push((*t, *u, opposite, id));
                }
            }
        }
        self.ar_sim_correspondences(st, &found, &line_of, &points)?;
        Some(pairs)
    }

    /// 相似で対応する点: 相似 σ: t → u の辺 XY の上の点 P と、対応する辺 X'Y' の上の点 P' について、
    /// σ(X) = X' からの2つの等式(s(JX',JP') − s(JX,JP) = log a と I の線束の同じ式)が格子で言えるなら P' = σ(P)
    /// (同じ直線の上では、これは内分比 XP/XY = X'P'/X'Y' が言えることと同じ)。
    /// 対応が分かった点は、三角形の頂点と既に分かった対応点の全てとの組で σ の等式を足す。返り値は見つけた対応の数。
    fn ar_sim_correspondences(&self, st: &mut ArState, found: &[([ClassId; 3], [ClassId; 3], bool, usize)],
        line_of: &dyn Fn(ClassId, ClassId) -> Option<ClassId>, points: &[ClassId]) -> Option<usize> {
        const MAX_CANDIDATES: usize = 20000;
        let is_point: rustc_hash::FxHashSet<usize> = points.iter().map(|p| p.0).collect();
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        let eg = &self.prover.egraph;
        let zero = st.lattice.reduce(&SVec::new())?.0;
        let mut tried = 0usize;
        let mut count = 0usize;
        for &(t, u, opposite, id) in found {
            // 対応の分かった点の組 (P, P', その前提, 使った等式)。三角形の頂点から始める。
            let mut pts: Vec<(ClassId, ClassId)> = (0..3).map(|i| (t[i], u[i])).collect();
            for (x, y) in [(0, 1), (0, 2), (1, 2)] {
                let (Some(l), Some(l2)) = (line_of(t[x], t[y]), line_of(u[x], u[y])) else { continue };
                let on_l: Vec<ClassId> = self.ar_points_on(l).into_iter().filter(|p| is_point.contains(&p.0) && !t.contains(p)).collect();
                let on_l2: Vec<ClassId> = self.ar_points_on(l2).into_iter().filter(|p| is_point.contains(&p.0) && !u.contains(p)).collect();
                for &p in &on_l {
                    for &p2 in &on_l2 {
                        if pts.iter().any(|&(a, b)| a == p || b == p2) { continue; }
                        tried += 1;
                        if tried > MAX_CANDIDATES { return Some(count); }
                        let rels = sim_relations(&mut st.atoms, t[x], p, u[x], p2, opposite, id);
                        if rels.len() < 2 { continue; }
                        let mut src = Vec::new();
                        let mut ok = true;
                        for v in &rels {
                            match st.lattice.reduce(v) {
                                Some((r, s)) if r == zero => src = union(&src, &s),
                                _ => { ok = false; break; }
                            }
                        }
                        if !ok { continue; }
                        let prem = vec![conn(p, l), conn(p2, l2)];
                        for &(a, a2) in &pts {
                            // 図の上で同じ点の組(相似の中心とまだマージされていない点など)の等式は、記号が打ち消し合って
                            // 「log a = 0」のような偽の等式になる(centroid で 2 = −1 が出た)。
                            if a == t[x] || eg.fixed_equal(a, p) != Some(Some(false)) || eg.fixed_equal(a2, p2) != Some(Some(false)) { continue; }
                            for v in sim_relations(&mut st.atoms, a, p, a2, p2, opposite, id) {
                                st.insert(&self.prover.egraph, v, prem.clone(), &src)?;
                            }
                        }
                        if std::env::var("GS_DEBUG_AR").is_ok() {
                            let nm = |c: ClassId| self.prover.egraph.entities[c.0].name.clone();
                            println!("  AR_DEBUG corr [{} {} {}] -> [{} {} {}] opp={} : {} -> {}", nm(t[0]), nm(t[1]), nm(t[2]), nm(u[0]), nm(u[1]), nm(u[2]), opposite, nm(p), nm(p2));
                        }
                        pts.push((p, p2));
                        count += 1;
                        break;
                    }
                }
            }
        }
        Some(count)
    }

    /// 円周角の逆(検出): 円 C の外の点 Z から、C の上の2点 A, B への直線の方向の記号の差 β(ZA) − β(ZB) が
    /// θ_C(A) − θ_C(B) に還元されるなら、Z は C の上にある。返り値は (Z, C, 使った等式)。
    fn ar_detect_concyclic(&self, atoms: &mut Atoms, lattice: &mut Lattice, rc: &mut FxHashMap<u32, SVec>, zero: Option<&SVec>) -> Vec<(ClassId, ClassId, Vec<u32>)> {
        let eg = &self.prover.egraph;
        let (ci, cj) = (eg.get_rep(eg.circ_i).0, eg.get_rep(eg.circ_j).0);
        let linf = eg.get_rep(eg.line_infinity);
        let mut out = Vec::new();
        let Some(zero) = zero else { return out };
        let conics: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&c| eg.get_rep(c) == c && eg.entities[c.0].entity_type == EntityType::Conic && eg.entities[c.0].is_active()).collect();
        let points: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&o| eg.get_rep(o) == o && eg.entities[o.0].entity_type == EntityType::Point && eg.entities[o.0].is_active()
                && !eg.is_connected(o, linf)).collect();
        for &c in &conics {
            if !self.ar_is_circle(c) { continue; }
            let on_c = self.ar_points_on(c);
            if on_c.len() < 3 { continue; }
            // 円の点の記号が格子に出ている(弦の等式がある)点だけを使う。
            let with_theta: Vec<ClassId> = on_c.into_iter().filter(|p| atoms.fresh.contains_key(&(THETA, c.0, p.0, 0))).collect();
            for &z in &points {
                if eg.is_connected(z, c) || with_theta.contains(&z) { continue; }
                let rays: Vec<(ClassId, ClassId)> = with_theta.iter().filter_map(|&a| self.ar_lines_through(z, a).first().map(|&l| (a, l))).collect();
                if rays.len() < 2 { continue; }
                'pairs: for i in 0..rays.len() {
                    for j in (i + 1)..rays.len() {
                        let ((a, la), (b, lb)) = (rays[i], rays[j]);
                        if la == lb { continue; }
                        let mut v = SVec::new();
                        let ok = atoms.add_beta(&mut v, ci, cj, self.ar_dir_or_virtual(la), 1)
                            .and_then(|_| atoms.add_beta(&mut v, ci, cj, self.ar_dir_or_virtual(lb), -1))
                            .and_then(|_| atoms.add_fresh(&mut v, (THETA, c.0, a.0, 0), -1))
                            .and_then(|_| atoms.add_fresh(&mut v, (THETA, c.0, b.0, 0), 1));
                        if ok.is_none() { continue; }
                        if lattice.reduce_cached(&v, rc).as_ref() != Some(zero) { continue; }
                        let Some((_, src)) = lattice.reduce(&v) else { continue };
                        out.push((z, c, src));
                        break 'pairs;
                    }
                }
            }
        }
        out
    }

    /// 手が止まったときに呼ぶ。併合が無くなるまで(最大数回)追跡し、何か併合したら定理を全部試し直させる。
    pub fn run_ar(&mut self) -> bool {
        if !self.prover.egraph.fixed_active() { return false; }
        let mut total = 0;
        for _ in 0..4 {
            let n = self.ar_round();
            if n == 0 { break; }
            total += n;
            self.prover.egraph.apply_congruence_closure();
        }
        self.ar_merged += total as u64;
        if total > 0 { self.schedule_full_sweep(); }
        total > 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sv(xs: &[(u32, i64)]) -> SVec { xs.iter().copied().collect() }
    fn same(l: &mut Lattice, a: &SVec, b: &SVec) -> bool { l.reduce(a).unwrap().0 == l.reduce(b).unwrap().0 }

    /// x − y = 0 を積めば x と y は同じ剰余になる。
    #[test]
    fn a_relation_makes_both_sides_equal() {
        let mut l = Lattice::default();
        l.insert(sv(&[(0, 1), (1, -1)]), vec![0]).unwrap();
        assert!(same(&mut l, &sv(&[(0, 1)]), &sv(&[(1, 1)])));
        assert!(!same(&mut l, &sv(&[(0, 1)]), &sv(&[(2, 1)])));
    }

    /// ℤ の上なので 2x = 2y から x = y は出ない(有向角 mod π で 2θ₁ = 2θ₂ ⇏ θ₁ = θ₂)。
    #[test]
    fn no_division_by_two() {
        let mut l = Lattice::default();
        l.insert(sv(&[(0, 2), (1, -2)]), vec![0]).unwrap();
        assert!(!same(&mut l, &sv(&[(0, 1)]), &sv(&[(1, 1)])));
        assert!(same(&mut l, &sv(&[(0, 2)]), &sv(&[(1, 2)])));
    }

    /// ねじれ: 4T = 0 と x = y + 2T(x = −y)から、2x = 2y と x ≠ y が出る。
    #[test]
    fn torsion_mod_four() {
        let mut l = Lattice::default();
        l.insert(sv(&[(T, 4)]), vec![]).unwrap();
        l.insert(sv(&[(0, 1), (1, -1), (T, -2)]), vec![0]).unwrap();
        assert!(same(&mut l, &sv(&[(0, 1)]), &sv(&[(1, 1), (T, 2)])));
        assert!(same(&mut l, &sv(&[(0, 2)]), &sv(&[(1, 2)])));
        assert!(!same(&mut l, &sv(&[(0, 1)]), &sv(&[(1, 1)])));
        assert!(same(&mut l, &sv(&[(T, 6)]), &sv(&[(T, 2)])));
    }

    /// 主成分が割り切れない行どうしは拡張ユークリッドで置き換える(格子は変わらない)。
    #[test]
    fn gcd_combination_keeps_the_lattice() {
        let mut l = Lattice::default();
        // 2x − 3y と 3x − 5y が張る格子は、行列式が −1 なので x と y を両方含む(x = y = 0)。
        l.insert(sv(&[(0, 2), (1, -3)]), vec![0]).unwrap();
        l.insert(sv(&[(0, 3), (1, -5)]), vec![1]).unwrap();
        assert!(same(&mut l, &sv(&[(0, 1)]), &SVec::new()));
        assert!(same(&mut l, &sv(&[(1, 1)]), &SVec::new()));
        let (_, src) = l.reduce(&sv(&[(0, 1)])).unwrap();
        assert_eq!(src, vec![0, 1]);
    }

    /// 記号ごとの剰余を足して簡約し直しても、まとめて簡約したのと同じ剰余になる(ねじれ・割り切れない主成分を含めて)。
    #[test]
    fn cached_reduction_matches_direct() {
        let mut l = Lattice::default();
        l.insert(sv(&[(T, 4)]), vec![]).unwrap();
        l.insert(sv(&[(0, 3), (2, -1), (T, 1)]), vec![0]).unwrap();
        l.insert(sv(&[(1, 2), (3, 5)]), vec![1]).unwrap();
        l.insert(sv(&[(2, 4), (3, -2), (T, 2)]), vec![2]).unwrap();
        let mut cache = FxHashMap::default();
        for v in [sv(&[(0, 5), (1, -3), (3, 7)]), sv(&[(0, -2), (2, 9), (T, 3)]), sv(&[(1, 4), (2, -4), (3, 2)]), SVec::new()] {
            assert_eq!(l.reduce(&v).unwrap().0, l.reduce_cached(&v, &mut cache).unwrap());
        }
    }
}

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
use crate::mmp_core::{ClassId, Definition, EntityType, Justification};
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
}

/// 記号の番号。s(X,Y)(順序のない点の組ごと)と、等式を作るときに導入する新しい記号(円の点の記号など)。
#[derive(Default)]
struct Atoms {
    ids: FxHashMap<(usize, usize), u32>,
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

/// 直線の無限遠点の仮の番号(方向の点がまだ図に無い直線用)。実体の番号とは重ならない大きい側に置く。
const VIRTUAL_BASE: usize = usize::MAX / 2;
fn virtual_infinity(line: ClassId) -> usize { usize::MAX - line.0 }
fn is_virtual(id: usize) -> bool { id >= VIRTUAL_BASE }

impl Atoms {
    /// s(X,Y) を v に sign 倍で足す。X > Y なら向きを入れ替えてねじれ 2(= −1)を足す。重なった2点なら None。
    fn add(&mut self, v: &mut SVec, x: usize, y: usize, sign: i64) -> Option<()> {
        if x == y { return None; }
        let (key, flipped) = if x < y { ((x, y), false) } else { ((y, x), true) };
        let id = match self.ids.get(&key) { Some(&id) => id, None => { let id = self.next; self.next += 1; self.ids.insert(key, id); id } };
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
        let eg = &self.prover.egraph;
        let mut atoms = Atoms::default();
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

        // 等式(同値類の中の2つの式の差)と、ねじれの関係 4T = 0。
        let mut lattice = Lattice::default();
        let mut premises_of: Vec<Vec<(String, Vec<ClassId>)>> = Vec::new();
        if lattice.insert(SVec::from([(T, 4)]), Vec::new()).is_none() { return 0; }
        for (_, vs) in &classes {
            for (v, ent) in &vs[1..] {
                let mut rel = v.clone();
                if add_scaled(&mut rel, &vs[0].0, -1).is_none() { continue; }
                let id = premises_of.len() as u32;
                premises_of.push(vec![("Identical".to_string(), vec![*ent, vs[0].1])]);
                if lattice.insert(rel, vec![id]).is_none() { return 0; }
            }
        }
        // 定義から従う比の等式(無限遠点との複比が −1)。
        let minus_one = ModInt::new(-1);
        for (pts, premise) in self.ar_ratio_facts() {
            let [a, b, c, d] = pts;
            let mut rel = SVec::new();
            let ok = atoms.add(&mut rel, a, c, 1).and_then(|_| atoms.add(&mut rel, d, b, 1))
                .and_then(|_| atoms.add(&mut rel, c, b, -1)).and_then(|_| atoms.add(&mut rel, a, d, -1))
                .and_then(|_| add_scaled(&mut rel, &SVec::from([(T, 2)]), -1));
            if ok.is_none() || !self.ar_verify_const(pts, minus_one) { continue; }
            let id = premises_of.len() as u32;
            premises_of.push(vec![premise]);
            dbg_ratio += 1;
            if lattice.insert(rel, vec![id]).is_none() { return 0; }
        }

        // 定理の代わりに等式を作る(円・透視射影・二次曲線の射影対応)。
        let mut gen_count = 0usize;
        for (rel, premises) in self.ar_generated_relations(&mut atoms) {
            let id = premises_of.len() as u32;
            premises_of.push(premises);
            gen_count += 1;
            if lattice.insert(rel, vec![id]).is_none() { return 0; }
        }
        if std::env::var("GS_DEBUG_AR").is_ok() {
            println!("  AR_DEBUG generated={}", gen_count);
            let mapped: usize = classes.iter().map(|(_, v)| v.len()).sum();
            println!("  AR_DEBUG classes={} mapped={} degen={} unverified={} ratio_facts={} relations={} rows={} atoms={}",
                classes.len(), mapped, dbg_degen, dbg_unverified, dbg_ratio, premises_of.len(), lattice.rows.len(), atoms.ids.len());
        }
        // 剰余が同じ同値類を探す。
        let mut by_key: FxHashMap<Vec<(u32, i64)>, usize> = FxHashMap::default();
        let mut merges: Vec<(ClassId, ClassId, Vec<u32>)> = Vec::new();
        for (idx, (rep, vs)) in classes.iter().enumerate() {
            let Some((r, _)) = lattice.reduce(&vs[0].0) else { continue };
            let key: Vec<(u32, i64)> = r.into_iter().collect();
            match by_key.get(&key) {
                None => { by_key.insert(key, idx); }
                Some(&first) => {
                    let mut diff = vs[0].0.clone();
                    if add_scaled(&mut diff, &classes[first].1[0].0, -1).is_none() { continue; }
                    let Some((_, src)) = lattice.reduce(&diff) else { continue };
                    merges.push((classes[first].0, *rep, src));
                }
            }
        }
        // 方向どうしの一致: (I,J;D1,D2) の式が 0 に還元されるなら D1 = D2(平行)。等式に出てくる方向だけを見る。
        let eg = &self.prover.egraph;
        let (ci, cj) = (eg.get_rep(eg.circ_i), eg.get_rep(eg.circ_j));
        let mut dirs: Vec<ClassId> = atoms.ids.keys()
            .flat_map(|&(x, y)| [x, y]).filter(|&x| !is_virtual(x)).map(ClassId)
            .filter(|&d| d != ci && d != cj && eg.get_rep(d) == d && eg.entities[d.0].entity_type == EntityType::Point
                && eg.is_connected(d, eg.line_infinity))
            .collect();
        dirs.sort_by_key(|d| d.0);
        dirs.dedup();
        let zero = lattice.reduce(&SVec::new()).map(|r| r.0);
        let mut dir_merges: Vec<(ClassId, ClassId, Vec<u32>)> = Vec::new();
        for i in 0..dirs.len() {
            for j in (i + 1)..dirs.len() {
                let (d1, d2) = (dirs[i], dirs[j]);
                let mut v = SVec::new();
                let ok = atoms.add(&mut v, ci.0, d1.0, 1).and_then(|_| atoms.add(&mut v, d2.0, cj.0, 1))
                    .and_then(|_| atoms.add(&mut v, d1.0, cj.0, -1)).and_then(|_| atoms.add(&mut v, ci.0, d2.0, -1));
                if ok.is_none() { continue; }
                let Some((r, src)) = lattice.reduce(&v) else { continue };
                if Some(&r) == zero.as_ref() { dir_merges.push((d1, d2, src)); }
            }
        }
        let links = self.ar_detect_concyclic(&mut atoms, &mut lattice, zero.as_ref());
        // 行演算1回(疎なベクトル数項の足し算)は dfs_match 1回よりずっと軽いので、16回で仕事量1と数える
        // (nine_point_full で行演算が 80万増えて壁時計は 0.3秒しか増えず、dfs_match 1回はおよそその18倍だった)。
        self.prover.egraph.spiral_prop_work += lattice.ops / AR_OPS_PER_WORK;
        self.ar_ops += lattice.ops;
        self.ar_rounds += 1;
        merges.extend(dir_merges);

        let mut merged = 0;
        for (a, b, src) in merges {
            let eg = &mut self.prover.egraph;
            if eg.get_rep(a) == eg.get_rep(b) { continue; }
            if eg.merge_checks && eg.fixed_equal(a, b) == Some(Some(false)) {
                self.ar_rejected += 1;
                continue;
            }
            let premises: Vec<(String, Vec<ClassId>)> = src.iter()
                .flat_map(|&i| premises_of[i as usize].clone()).collect();
            let (na, nb) = (eg.entities[eg.get_rep(a).0].name.clone(), eg.entities[eg.get_rep(b).0].name.clone());
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
            let premises: Vec<(String, Vec<ClassId>)> = src.iter().flat_map(|&i| premises_of[i as usize].clone()).collect();
            let (nz, nc) = (eg.entities[z.0].name.clone(), eg.entities[c.0].name.clone());
            eg.link_logical_incidence_justified(z, c, Justification::Theorem { name: "代数的な追跡(円周角の逆)".to_string(), premises });
            println!("  🧮 [代数的な追跡] {} ∈ {}", nz, nc);
            merged += 1;
        }
        merged
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
        out
    }

    /// 円周角の逆(検出): 円 C の外の点 Z から、C の上の2点 A, B への直線の方向の記号の差 β(ZA) − β(ZB) が
    /// θ_C(A) − θ_C(B) に還元されるなら、Z は C の上にある。返り値は (Z, C, 使った等式)。
    fn ar_detect_concyclic(&self, atoms: &mut Atoms, lattice: &mut Lattice, zero: Option<&SVec>) -> Vec<(ClassId, ClassId, Vec<u32>)> {
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
                        let Some((r, src)) = lattice.reduce(&v) else { continue };
                        if &r == zero { out.push((z, c, src)); break 'pairs; }
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
}

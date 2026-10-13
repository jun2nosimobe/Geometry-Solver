//! 🌟 補助作図の候補を次数の順に選ぶ(#108、改善候補 b51 の (c))。
//!
//! 候補は図の点・直線・円から作る中点・2直線の交点・垂線の足・直線と円のもう一方の交点。自然な次数(natural_degree.rs)の低い順に
//! 見て、その点が加わって新しく成り立つ事実(共線・共円・直線や円の上・等長・平行や垂直。一般の直線の上の3か所で値を比べて選ぶ。
//! 候補選び用で、証明には使わない)のうち、目標の次数より低いものと定義する図形の上だけで閉じるもの、候補の定義から出る関係を、
//! 図の目標より低い次数の事実と既知の事実に足したとき、目標の関係(units.rs の原子のベクトル)がその張る空間に入る候補だけを残す。
//! そうなれば証明は「目標より低い次数の補題 + AR の線形結合」になる。同じ次数の中では目標からの距離(作図・接続のつながりの段数)の
//! 近い順、親が事実によく出てくる順に並べる。1つで足りなければ、2つの組を、それぞれが土台に足せる関係(補助点の原子を消して残る
//! 図の原子どうしの関係)を合わせた空間で見る。点の差の和は補助点の差になる((z_A − z_B) + (z_C − z_D) = 2(z_M − z_N))ので、足し引きしてから
//! 分解するのはここで中点などを足すことに当たる。

use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};

use super::fact_census::{Census, CensusFact};
use super::symbolic::{addm, circle_reduced, invm, join_reduced, length_sq, line_direction, line_eval, mulm, negm, Symbolic, V};
use super::units::{Eliminator, RelVec, UnitRelations, UNIT_SEED};
use super::{ClassId, Definition, EGraph, EntityType};

/// 補助作図の候補の作り方。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AuxKind {
    Midpoint(ClassId, ClassId),
    Intersection(ClassId, ClassId),
    /// 点から直線への垂線の足 (点, 直線)。
    Foot(ClassId, ClassId),
    /// 直線と円のもう一方の交点 (分かっている交点, 直線, 円)。
    Second(ClassId, ClassId, ClassId),
}

impl AuxKind {
    pub(crate) fn parents(&self) -> Vec<ClassId> {
        match *self {
            AuxKind::Midpoint(a, b) | AuxKind::Intersection(a, b) | AuxKind::Foot(a, b) => vec![a, b],
            AuxKind::Second(p, l, c) => vec![p, l, c],
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct AuxCandidate {
    /// 足す補助点(1つか2つ)。
    pub kinds: Vec<AuxKind>,
    /// 補助点の次数の最大。
    pub degree: u32,
    /// 補助点ごとに土台に足した新しい事実の本数の和。
    pub gain: usize,
    /// 目標の実体からの、作図・接続のつながりの段数。
    pub goal_dist: u32,
    /// 親が図の事実に出てくる回数。
    pub usage: usize,
}

const TS: [u64; 3] = [0x1234_5678_9ABC, 0x0FED_CBA9_8765, 0x7777_3333_1111];
/// 2つの補助点の組を測る数の上限。
const AUX_PAIR_EVAL: usize = 5000;
fn sub(a: u64, b: u64) -> u64 { addm(a, negm(b)) }
type Aff = [(u64, u64); 3];

fn affine(v: &V) -> Option<Aff> {
    if v.len() != 3 { return None; }
    let mut out = [(0, 0); 3];
    for (k, &t) in TS.iter().enumerate() {
        let x = line_eval(v, t);
        if x[2] == 0 { return None; }
        let iz = invm(x[2]);
        out[k] = (mulm(x[0], iz), mulm(x[1], iz));
    }
    Some(out)
}
fn collinear(a: &Aff, b: &Aff, c: &Aff) -> bool {
    (0..3).all(|k| { let (a, b, c) = (a[k], b[k], c[k]); sub(mulm(sub(b.0, a.0), sub(c.1, a.1)), mulm(sub(b.1, a.1), sub(c.0, a.0))) == 0 })
}
fn concyclic(p: [&Aff; 4]) -> bool {
    (0..3).all(|k| {
        let r = |q: (u64, u64)| { let (dx, dy) = (sub(q.0, p[0][k].0), sub(q.1, p[0][k].1)); [addm(mulm(dx, dx), mulm(dy, dy)), dx, dy] };
        let m = [r(p[1][k]), r(p[2][k]), r(p[3][k])];
        let t1 = mulm(m[0][0], sub(mulm(m[1][1], m[2][2]), mulm(m[1][2], m[2][1])));
        let t2 = mulm(m[0][1], sub(mulm(m[1][0], m[2][2]), mulm(m[1][2], m[2][0])));
        let t3 = mulm(m[0][2], sub(mulm(m[1][0], m[2][1]), mulm(m[1][1], m[2][0])));
        addm(sub(t1, t2), t3) == 0
    })
}
fn len_key(a: &Aff, b: &Aff) -> [u64; 3] {
    [0, 1, 2].map(|k| { let (dx, dy) = (sub(a[k].0, b[k].0), sub(a[k].1, b[k].1)); addm(mulm(dx, dx), mulm(dy, dy)) })
}
fn same(a: &Aff, b: &Aff) -> bool { a == b }

impl EGraph {
    /// 補助作図の候補(次数が max_degree 以下)のうち、目標を「目標より低い次数の事実と既知の事実」の張る空間に入れるものを、
    /// 次数の低い順に返す(測るのは次数の低い順に max_eval 個まで)。1つで入れるものが無ければ、2つの組で入れるものを返す。
    pub(crate) fn aux_candidates(&self, census: &Census, target: &(String, Vec<ClassId>), max_degree: u32, max_eval: usize) -> Vec<AuxCandidate> {
        let mut s = Symbolic::on_line(self, UNIT_SEED);
        // 目標の点・直線も原子に入れる(図の事実に出てこない目標の点がある)。目標の事実は低い次数の空間には入れない。
        let goal_facts = self.goal_unit_facts(target);
        let mut all: Vec<CensusFact> = census.facts.iter().map(|f| CensusFact { kind: f.kind, objs: f.objs.clone(), degree: f.degree, known: f.known }).collect();
        all.extend(goal_facts.iter().map(|f| CensusFact { kind: f.kind, objs: f.objs.clone(), degree: 0, known: false }));
        let (mut ur, mut vecs) = self.unit_relations_with(&mut s, &all);
        vecs.truncate(census.facts.len());
        // 目標より低い次数の図の事実と、既知の事実(次数によらない。「D は直線 DE の上」のような定義から従う事実は目標と同じ
        // くらい高い次数のことがあり、これを除くと目標はまず張れない)の張る空間。
        let goal_degree = census.goal_degree.unwrap_or(u32::MAX);
        let mut base = Eliminator::default();
        for (f, v) in census.facts.iter().zip(&vecs) { if (f.degree < goal_degree || f.known) && let Some(v) = v { base.insert(v); } }
        let fact = |kind: &'static str, objs: Vec<ClassId>| CensusFact { kind, objs, degree: 0, known: false };
        // 目標の関係(書けない目標・既に低い次数の事実から従う目標には補助作図は要らない)。
        let dbg = std::env::var("GS_DEBUG_AUX").is_ok();
        if goal_facts.is_empty() { return Vec::new(); }
        let Some(goal_vecs) = goal_facts.iter().map(|f| ur.fact_vector(f)).collect::<Option<Vec<RelVec>>>() else { return Vec::new() };
        if dbg { println!("AUX_DEBUG goal_facts={} goal_degree={} goal_in_base={}", goal_facts.len(), goal_degree, goal_vecs.iter().all(|g| base.depends(g))); }
        if goal_vecs.iter().all(|g| base.depends(g)) { return Vec::new(); }

        // 図の点・直線・円の標本。
        let mut conic_ids: Vec<ClassId> = census.facts.iter().filter(|f| f.kind == "接続(円)").map(|f| f.objs[1]).collect();
        conic_ids.sort_by_key(|c| c.0);
        conic_ids.dedup();
        let fig = Sampled::new(&mut s, &ur.point_ids(), &ur.line_ids(), &conic_ids);
        let (pts, lines, conics) = (&fig.pts, &fig.lines, &fig.conics);
        let known_on = known_incidences(census);

        // 候補(同じ点は次数の低い作り方だけ)。
        let mut kinds: Vec<AuxKind> = Vec::new();
        for i in 0..pts.len() { for j in (i + 1)..pts.len() { kinds.push(AuxKind::Midpoint(pts[i].0, pts[j].0)); } }
        for i in 0..lines.len() { for j in (i + 1)..lines.len() { kinds.push(AuxKind::Intersection(lines[i].0, lines[j].0)); } }
        for p in pts { for l in lines { if !on_line(&p.1, &l.1) { kinds.push(AuxKind::Foot(p.0, l.0)); } } }
        for p in pts { for l in lines { if on_line(&p.1, &l.1) { for c in conics { if on_conic(&p.1, &c.1) { kinds.push(AuxKind::Second(p.0, l.0, c.0)); } } } } }
        let value = |s: &mut Symbolic, k: AuxKind| -> Option<V> {
            match k {
                AuxKind::Midpoint(a, b) => s.value_of(Definition::Midpoint(a, b)),
                AuxKind::Intersection(a, b) => s.value_of(Definition::Intersection(a, b)),
                AuxKind::Foot(p, l) => s.foot_value(p, l),
                AuxKind::Second(p, l, c) => s.value_of(Definition::SecondIntersectionOfLineAndConic(p, l, c)),
            }
        };
        let mut cands: Vec<(AuxKind, u32, V, Aff)> = Vec::new();
        for k in kinds {
            let Some(v) = value(&mut s, k) else { s.fail = None; continue };
            let Some(a) = affine(&v) else { continue };
            if pts.iter().any(|p| same(&p.1, &a)) { continue; }
            let Some(md) = self.multidegree_with(&|bs| value(bs, k)) else { continue };
            let d: u32 = md.iter().sum();
            if d > max_degree { continue; }
            cands.push((k, d, v, a));
        }
        cands.sort_by_key(|c| c.1);
        let mut seen: Vec<Aff> = Vec::new();
        cands.retain(|c| { if seen.iter().any(|a| same(a, &c.3)) { false } else { seen.push(c.3); true } });

        // 目標からの距離と、事実への出現回数。
        let mut adj: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
        let mut edge = |a: usize, b: usize| { adj.entry(a).or_default().push(b); adj.entry(b).or_default().push(a); };
        for (i, e) in self.entities.iter().enumerate() { for p in e.original_definition.get_parents() { edge(i, p.0); } }
        let mut usage: FxHashMap<usize, usize> = FxHashMap::default();
        for f in &census.facts {
            for o in &f.objs { *usage.entry(o.0).or_default() += 1; }
            if f.kind.starts_with("接続") { edge(f.objs[0].0, f.objs[1].0); }
        }
        let mut dist: FxHashMap<usize, u32> = FxHashMap::default();
        let mut queue: VecDeque<usize> = target.1.iter().map(|x| x.0).collect();
        for &x in &queue { dist.insert(x, 0); }
        while let Some(x) = queue.pop_front() {
            let d = dist[&x];
            for &y in adj.get(&x).map(|v| v.as_slice()).unwrap_or(&[]) {
                if let std::collections::hash_map::Entry::Vacant(e) = dist.entry(y) { e.insert(d + 1); queue.push_back(y); }
            }
        }

        // 候補ごとに、その事実(定義・定義する図形の上だけで閉じるもの・目標より低い次数のもの)を土台を法とした標準形に直す。
        // 補助点の原子の列を先にしてあるので、図の原子だけの行が、その補助点で土台に足せる関係。目標の標準形がその張る空間に
        // 入れば補助点1つで足りる。
        const OFF: usize = 1 << 40;
        let goal_nf: Vec<Vec<(usize, u64)>> = goal_vecs.iter().map(|g| base.normal_form(g).into_iter().map(|(i, k)| (i + OFF, k)).collect()).collect();
        let first_new = ur.npoints();
        let nf = |ur: &UnitRelations, r: &RelVec| -> Vec<(usize, u64)> {
            let mut w: Vec<(usize, u64)> = base.normal_form(r).into_iter().map(|(i, k)| (if ur.touches_points_from(i, first_new) { i } else { i + OFF }, k)).collect();
            w.sort_unstable();
            w
        };
        let nd = |f: &dyn Fn(&mut Symbolic) -> Option<V>| -> Option<u32> { self.multidegree_with(f).map(|v| v.iter().sum()) };
        let cand = |kinds: Vec<AuxKind>, degree: u32, gain: usize| {
            let ps: Vec<ClassId> = kinds.iter().flat_map(|k| k.parents()).collect();
            let goal_dist = 1 + ps.iter().map(|p| dist.get(&p.0).copied().unwrap_or(u32::MAX - 1)).min().unwrap_or(u32::MAX - 1);
            let usage = ps.iter().map(|p| usage.get(&p.0).copied().unwrap_or(0)).sum();
            AuxCandidate { kinds, degree, gain, goal_dist, usage }
        };
        let mut out = Vec::new();
        // (候補, 次数, 実体の代わりの番号, 標本, 足した事実の行, 足した事実の本数)
        type Eval = (AuxKind, u32, usize, Aff, Vec<Vec<(usize, u64)>>, usize);
        let mut evals: Vec<Eval> = Vec::new();
        for (n, (k, d, v, a)) in cands.into_iter().enumerate() {
            if n >= max_eval { break; }
            let key = usize::MAX - n;
            let m = ClassId(key);
            if ur.add_point(key, &v).is_none() { continue; }
            // 定義から出る関係。
            let defs: Vec<RelVec> = match k {
                AuxKind::Midpoint(x, y) => ur.midpoint_vectors(m, x, y),
                AuxKind::Intersection(l1, l2) => [l1, l2].iter().filter_map(|&l| ur.fact_vector(&fact("接続(直線)", vec![m, l]))).collect(),
                AuxKind::Foot(p, l) => [ur.fact_vector(&fact("接続(直線)", vec![m, l])), ur.dir_point_line(p, m, l)].into_iter().flatten().collect(),
                AuxKind::Second(_, l, c) => [ur.fact_vector(&fact("接続(直線)", vec![m, l])), ur.fact_vector(&fact("接続(円)", vec![m, c]))].into_iter().flatten().collect(),
            };
            let mut ex = Eliminator::default();
            for r in &defs { ex.insert_m(&nf(&ur, r)); }
            // 新しく成り立つ事実のうち、定義する図形の上だけで閉じるもの(作れば既知)と、目標より低い次数のもの。
            let dset = known_defining(self, &known_on, &k.parents(), matches!(k, AuxKind::Midpoint(..)), &|x| x);
            let mut used = 0;
            for f in fig.new_facts(m, &a) {
                let Some(r) = ur.fact_vector(&f) else { continue };
                let w = nf(&ur, &r);
                if ex.depends_m(&w) { continue; }
                let o = f.objs.clone();
                let deg = if o.iter().all(|x| *x == m || dset.contains(&x.0)) { Some(0) } else { match f.kind {
                    "共線" => nd(&|bs| Some(join_reduced(&value(bs, k)?, &bs.value(o[1])?))),
                    "共円" => nd(&|bs| Some(circle_reduced(&bs.value(o[0])?, &bs.value(o[1])?, &bs.value(o[2])?))),
                    "接続(直線)" | "接続(円)" => self.natural_degree(o[1]).map(|d| d as u32),
                    _ if o[2] == m => nd(&|bs| Some(length_sq(&value(bs, k)?, &bs.value(o[1])?))),
                    _ => nd(&|bs| Some(length_sq(&bs.value(o[2])?, &bs.value(o[3])?))),
                } };
                if deg.is_some_and(|d| d < goal_degree) && ex.insert_m(&w) { used += 1; }
            }
            // 図の点と結ぶ方向が図の直線と平行・垂直(共通の方向の次数)。
            for (y, l) in fig.dir_facts(&a) {
                let Some(r) = ur.dir_point_line(y, m, l) else { continue };
                let w = nf(&ur, &r);
                if ex.depends_m(&w) { continue; }
                let deg = if dset.contains(&y.0) && dset.contains(&l.0) { Some(0) } else { nd(&|bs| Some(line_direction(&bs.value(l)?))) };
                if deg.is_some_and(|d| d < goal_degree) && ex.insert_m(&w) { used += 1; }
            }
            let single = goal_nf.iter().all(|g| ex.depends_m(g));
            if dbg && n < 12 { println!("AUX_DEBUG cand {:?} deg={} used={} rel={} goal_in={}", k, d, used, ex.rows_from(OFF).len(), single); }
            if single { out.push(cand(vec![k], d, used)); }
            evals.push((k, d, key, a, ex.rows_from(0), used));
        }
        // 1つで足りなければ2つの組: 2つの事実の行に、2点の間の事実(目標より低い次数のもの)を足した空間に目標が入るか。次数の
        // 大きい方・小さい方の低い順に AUX_PAIR_EVAL 組まで。
        if out.is_empty() {
            let mut pairs: Vec<(usize, usize)> = (0..evals.len()).flat_map(|i| ((i + 1)..evals.len()).map(move |j| (i, j))).collect();
            pairs.sort_by_key(|&(i, j)| (evals[i].1.max(evals[j].1), evals[i].1.min(evals[j].1)));
            let mut tried = 0;
            for (i, j) in pairs.into_iter().take(AUX_PAIR_EVAL) {
                let (x, y) = (&evals[i], &evals[j]);
                let mut e = Eliminator::default();
                for r in x.4.iter().chain(&y.4) { e.insert_m(r); }
                let mut used = x.5 + y.5;
                let (mx, my) = (ClassId(x.2), ClassId(y.2));
                if !goal_nf.iter().all(|g| e.depends_m(g)) {
                    let (facts, dirs) = fig.joint_facts(mx, &x.3, my, &y.3);
                    if facts.is_empty() && dirs.is_empty() { continue; }
                    tried += 1;
                    let (kx, ky) = (x.0, y.0);
                    for f in facts {
                        let Some(r) = ur.fact_vector(&f) else { continue };
                        let w = nf(&ur, &r);
                        if e.depends_m(&w) { continue; }
                        let o = f.objs.clone();
                        let deg = match (f.kind, o.as_slice()) {
                            ("共線", _) => nd(&|bs| Some(join_reduced(&value(bs, kx)?, &value(bs, ky)?))),
                            ("共円", [p, q, ..]) => { let (p, q) = (*p, *q); nd(&|bs| Some(circle_reduced(&bs.value(p)?, &bs.value(q)?, &value(bs, kx)?))) }
                            (_, [_, p, _, q]) if p == q => { let p = *p; nd(&|bs| Some(length_sq(&value(bs, kx)?, &bs.value(p)?))) }
                            (_, [_, _, p, q]) => { let (p, q) = (*p, *q); nd(&|bs| Some(length_sq(&bs.value(p)?, &bs.value(q)?))) }
                            _ => None,
                        };
                        if deg.is_some_and(|d| d < goal_degree) && e.insert_m(&w) { used += 1; }
                    }
                    for l in dirs {
                        let Some(r) = ur.dir_point_line(mx, my, l) else { continue };
                        let w = nf(&ur, &r);
                        if e.depends_m(&w) { continue; }
                        if nd(&|bs| Some(line_direction(&bs.value(l)?))).is_some_and(|d| d < goal_degree) && e.insert_m(&w) { used += 1; }
                    }
                    if !goal_nf.iter().all(|g| e.depends_m(g)) { continue; }
                }
                out.push(cand(vec![x.0, y.0], x.1.max(y.1), used));
            }
            if dbg {
                // 目標の残り(土台を法とした標準形)が触れる原子と、それに触れる関係を足せる候補の数。
                let supp: FxHashSet<usize> = goal_nf.iter().flatten().map(|&(c, _)| c).collect();
                let touching = evals.iter().filter(|e| e.4.iter().any(|r| r[0].0 >= OFF && r.iter().any(|(c, _)| supp.contains(c)))).count();
                let with_rel = evals.iter().filter(|e| e.4.iter().any(|r| r[0].0 >= OFF)).count();
                println!("AUX_DEBUG pairs: {} candidates, {} pairs with joint facts, {} hits; goal residual atoms {}, candidates with relations {}, touching the residual {}",
                    evals.len(), tried, out.len(), supp.len(), with_rel, touching);
            }
        }
        out.sort_by_key(|c| (c.kinds.len(), c.degree, c.goal_dist, c.gain, std::cmp::Reverse(c.usage)));
        out
    }

    /// 目標を、乗法的関係の形の図の事実(fact_census の種類)に直す。直せない目標(点どうしの一致など)は空。
    pub(crate) fn goal_unit_facts(&self, (kind, args): &(String, Vec<ClassId>)) -> Vec<CensusFact> {
        let fact = |kind: &'static str, objs: Vec<ClassId>| CensusFact { kind, objs, degree: 0, known: false };
        let r = |x: ClassId| self.get_rep(x);
        let line_of_dir = |d: ClassId| match self.entities[d.0].original_definition { Definition::DirectionOf(l) => Some(r(l)), _ => None };
        let angle = |x: ClassId| match self.entities[x.0].original_definition {
            Definition::AnglePair(d1, d2) => Some((line_of_dir(d1)?, line_of_dir(d2)?)),
            _ => None,
        };
        match (kind.as_str(), args.as_slice()) {
            ("Concyclic", [a, b, c, rest @ ..]) => rest.iter().map(|&d| fact("共円", vec![r(*a), r(*b), r(*c), r(d)])).collect(),
            ("Connected", [x, y]) => {
                let (p, c) = self.point_and_curve(*x, *y);
                match self.entities[r(c).0].entity_type {
                    EntityType::Line => vec![fact("接続(直線)", vec![r(p), r(c)])],
                    EntityType::Conic => vec![fact("接続(円)", vec![r(p), r(c)])],
                    _ => Vec::new(),
                }
            }
            ("Identical", [a, b]) => {
                let is_const = |x: ClassId| r(x) == r(self.ang90) || r(x) == r(self.ang0);
                let len = |x: ClassId| match self.entities[x.0].original_definition { Definition::LengthSq(p, q) => Some((r(p), r(q))), _ => None };
                if is_const(*a) || is_const(*b) {
                    let x = if is_const(*a) { *b } else { *a };
                    angle(x).map(|(l1, l2)| vec![fact(if r(*a) == r(self.ang0) || r(*b) == r(self.ang0) { "平行" } else { "垂直" }, vec![l1, l2])]).unwrap_or_default()
                } else if let (Some(l1), Some(l2)) = (line_of_dir(*a), line_of_dir(*b)) {
                    vec![fact("平行", vec![l1, l2])]
                } else if let (Some((l1, l2)), Some((l3, l4))) = (angle(*a), angle(*b)) {
                    vec![fact("等角", vec![l1, l2, l3, l4])]
                } else if let (Some((p, q)), Some((u, w))) = (len(*a), len(*b)) {
                    vec![fact("等長", vec![p, q, u, w])]
                } else { Vec::new() }
            }
            _ => Vec::new(),
        }
    }
}

/// 補助作図の測定に使う、探索の前の図(EGraph::aux_figure)。
pub(crate) struct AuxFigure { census: Census, goal_facts: Vec<CensusFact>, keep: FxHashSet<usize> }

type Tri = [[u64; 3]; 3];
fn tri(v: &V) -> Option<Tri> {
    if v.len() != 3 { return None; }
    let e = TS.map(|t| line_eval(v, t));
    Some([[e[0][0], e[0][1], e[0][2]], [e[1][0], e[1][1], e[1][2]], [e[2][0], e[2][1], e[2][2]]])
}
fn on_line(p: &Aff, l: &Tri) -> bool { (0..3).all(|k| addm(addm(mulm(l[k][0], p[k].0), mulm(l[k][1], p[k].1)), l[k][2]) == 0) }
fn on_conic(p: &Aff, q: &[Vec<u64>; 3]) -> bool {
    (0..3).all(|k| {
        let (x, y) = p[k];
        let a = &q[k];
        [mulm(a[0], mulm(x, x)), mulm(a[1], mulm(x, y)), mulm(a[2], mulm(y, y)), mulm(a[3], x), mulm(a[4], y), a[5]].iter().fold(0, |s, &t| addm(s, t)) == 0
    })
}
fn same_line(a: &Tri, b: &Tri) -> bool { (0..3).all(|k| (0..3).all(|i| (0..3).all(|j| mulm(a[k][i], b[k][j]) == mulm(a[k][j], b[k][i])))) }

/// 既知の接続の事実: 曲線(直線・円)ごとの、その上にあると分かっている点。
fn known_incidences(census: &Census) -> FxHashMap<usize, Vec<usize>> {
    let mut on: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
    for f in &census.facts { if f.known && f.kind.starts_with("接続") { on.entry(f.objs[1].0).or_default().push(f.objs[0].0); } }
    on
}

/// 補助点を定義する図形の実体: 親と、親の直線・円の上にあると既知の点(読み込んだ・示した接続と、直線・円の定義の点)、中点なら
/// 親の2点を通ると既知の直線とその上の点。値の比較で見つけただけの接続は使わない(示したい接続を定義に数えてしまう)。
/// r は親を図の事実の実体に直す。
fn known_defining(eg: &EGraph, known_on: &FxHashMap<usize, Vec<usize>>, parents: &[ClassId], mid: bool, r: &dyn Fn(ClassId) -> ClassId) -> FxHashSet<usize> {
    let mut out: FxHashSet<usize> = FxHashSet::default();
    for &q in parents {
        let q0 = r(q);
        out.insert(q0.0);
        if eg.entities[q.0].entity_type == EntityType::Point { continue; }
        out.extend(known_on.get(&q0.0).into_iter().flatten().copied());
        match eg.entities[q.0].original_definition {
            Definition::LineThroughPoints(a, b) => { out.insert(r(a).0); out.insert(r(b).0); }
            Definition::PerpendicularLine(_, a) | Definition::ParallelLine(_, a) => { out.insert(r(a).0); }
            Definition::Circumcircle(a, b, c) => { out.extend([r(a).0, r(b).0, r(c).0]); }
            _ => {}
        }
    }
    if mid && let [a, b] = parents {
        let (a, b) = (r(*a).0, r(*b).0);
        for (l, ps) in known_on { if ps.contains(&a) && ps.contains(&b) { out.insert(*l); out.extend(ps.iter().copied()); } }
    }
    out
}

/// 図の点・直線・円の標本(候補が加わって新しく成り立つ事実を値の比較で見つける。調べる用で、証明には使わない)。
struct Sampled {
    pts: Vec<(ClassId, Aff)>,
    lines: Vec<(ClassId, Tri)>,
    conics: Vec<(ClassId, [Vec<u64>; 3])>,
    seg_len: FxHashMap<[u64; 3], Vec<(usize, usize)>>,
    noncol: FxHashSet<(usize, usize, usize)>,
}

impl Sampled {
    fn new(s: &mut Symbolic, points: &[ClassId], lines: &[ClassId], conics: &[ClassId]) -> Self {
        let mut pts: Vec<(ClassId, Aff)> = Vec::new();
        for &id in points {
            let Some(a) = s.value(id).and_then(|v| affine(&v)) else { s.fail = None; continue };
            if !pts.iter().any(|p| same(&p.1, &a)) { pts.push((id, a)); }
        }
        let lines: Vec<(ClassId, Tri)> = lines.iter().filter_map(|&id| Some((id, tri(&s.value(id)?)?))).collect();
        let conics: Vec<(ClassId, [Vec<u64>; 3])> = conics.iter().filter_map(|&id| {
            let v = s.value(id)?;
            if v.len() != 6 { return None; }
            Some((id, TS.map(|t| line_eval(&v, t))))
        }).collect();
        s.fail = None;
        let mut seg_len: FxHashMap<[u64; 3], Vec<(usize, usize)>> = FxHashMap::default();
        for i in 0..pts.len() { for j in (i + 1)..pts.len() { seg_len.entry(len_key(&pts[i].1, &pts[j].1)).or_default().push((i, j)); } }
        let mut noncol = FxHashSet::default();
        if pts.len() <= 60 {
            for i in 0..pts.len() { for j in (i + 1)..pts.len() { for k in (j + 1)..pts.len() {
                if !collinear(&pts[i].1, &pts[j].1, &pts[k].1) { noncol.insert((i, j, k)); }
            } } }
        }
        Sampled { pts, lines, conics, seg_len, noncol }
    }

    /// 点 m(標本 a)が加わって新しく成り立つ事実: 共線・共円・直線や円の上・等長。
    fn new_facts(&self, m: ClassId, a: &Aff) -> Vec<CensusFact> {
        let fact = |kind: &'static str, objs: Vec<ClassId>| CensusFact { kind, objs, degree: 0, known: false };
        let pts = &self.pts;
        let mut news: Vec<CensusFact> = Vec::new();
        for i in 0..pts.len() { for j in (i + 1)..pts.len() { if collinear(a, &pts[i].1, &pts[j].1) { news.push(fact("共線", vec![m, pts[i].0, pts[j].0])); } } }
        for &(i, j, l) in &self.noncol {
            if concyclic([&pts[i].1, &pts[j].1, &pts[l].1, a]) { news.push(fact("共円", vec![pts[i].0, pts[j].0, pts[l].0, m])); }
        }
        for l in &self.lines { if on_line(a, &l.1) { news.push(fact("接続(直線)", vec![m, l.0])); } }
        for c in &self.conics { if on_conic(a, &c.1) { news.push(fact("接続(円)", vec![m, c.0])); } }
        let mlen: Vec<[u64; 3]> = pts.iter().map(|p| len_key(a, &p.1)).collect();
        for i in 0..pts.len() {
            for &(x, y) in self.seg_len.get(&mlen[i]).map(|v| v.as_slice()).unwrap_or(&[]) { news.push(fact("等長", vec![m, pts[i].0, pts[x].0, pts[y].0])); }
            for j in (i + 1)..pts.len() { if mlen[i] == mlen[j] { news.push(fact("等長", vec![m, pts[i].0, m, pts[j].0])); } }
        }
        news
    }

    /// 2点 m1・m2(標本 a1・a2)の間で成り立つ事実: 図の点との共線、図の2点との共円、図の線分との等長、図の点から等距離
    /// (CensusFact)と、m1m2 と平行・垂直な図の直線。
    fn joint_facts(&self, m1: ClassId, a1: &Aff, m2: ClassId, a2: &Aff) -> (Vec<CensusFact>, Vec<ClassId>) {
        let fact = |kind: &'static str, objs: Vec<ClassId>| CensusFact { kind, objs, degree: 0, known: false };
        let pts = &self.pts;
        let mut out = Vec::new();
        for p in pts { if collinear(a1, a2, &p.1) { out.push(fact("共線", vec![m1, m2, p.0])); } }
        if pts.len() <= 40 {
            for i in 0..pts.len() {
                if collinear(&pts[i].1, a1, a2) { continue; }
                for j in (i + 1)..pts.len() {
                    if collinear(&pts[i].1, &pts[j].1, a1) || collinear(&pts[i].1, &pts[j].1, a2) || collinear(&pts[j].1, a1, a2) { continue; }
                    if concyclic([&pts[i].1, &pts[j].1, a1, a2]) { out.push(fact("共円", vec![pts[i].0, pts[j].0, m1, m2])); }
                }
            }
        }
        let l12 = len_key(a1, a2);
        for &(x, y) in self.seg_len.get(&l12).map(|v| v.as_slice()).unwrap_or(&[]) { out.push(fact("等長", vec![m1, m2, pts[x].0, pts[y].0])); }
        for p in pts { if len_key(a1, &p.1) == len_key(a2, &p.1) { out.push(fact("等長", vec![m1, p.0, m2, p.0])); } }
        let d: Vec<(u64, u64)> = (0..3).map(|k| (sub(a1[k].0, a2[k].0), sub(a1[k].1, a2[k].1))).collect();
        let dirs = self.lines.iter().filter(|l| {
            let par = (0..3).all(|k| addm(mulm(d[k].0, l.1[k][0]), mulm(d[k].1, l.1[k][1])) == 0);
            let perp = (0..3).all(|k| sub(mulm(d[k].0, l.1[k][1]), mulm(d[k].1, l.1[k][0])) == 0);
            par || perp
        }).map(|l| l.0).collect();
        (out, dirs)
    }

    /// 点(標本 a)と図の点 Y を結ぶ方向が図の直線 l と平行・垂直になる (Y, l)。
    fn dir_facts(&self, a: &Aff) -> Vec<(ClassId, ClassId)> {
        let mut out = Vec::new();
        for p in &self.pts {
            let d: Vec<(u64, u64)> = (0..3).map(|k| (sub(a[k].0, p.1[k].0), sub(a[k].1, p.1[k].1))).collect();
            if d.iter().all(|&(x, y)| x == 0 && y == 0) { continue; }
            for l in &self.lines {
                let par = (0..3).all(|k| addm(mulm(d[k].0, l.1[k][0]), mulm(d[k].1, l.1[k][1])) == 0);
                let perp = (0..3).all(|k| sub(mulm(d[k].0, l.1[k][1]), mulm(d[k].1, l.1[k][0])) == 0);
                if par || perp { out.push((p.0, l.0)); }
            }
        }
        out
    }
}

impl EGraph {
    /// 補助作図の測定の前準備(探索の前に呼ぶ): 問題文の実体の類だけの図の事実、目標の関係、問題文の実体の類(代表元の番号)。
    pub(crate) fn aux_figure(&self, target: Option<&(String, Vec<ClassId>)>) -> AuxFigure {
        let keep: FxHashSet<usize> = (0..self.entities.len()).filter(|&i| self.entities[i].origin == super::EntityOrigin::Given).map(|i| self.get_rep(ClassId(i)).0).collect();
        AuxFigure { census: self.fact_census_in(target, 90, Some(&keep)), goal_facts: target.map(|t| self.goal_unit_facts(t)).unwrap_or_default(), keep }
    }

    /// 🔎 補助点の候補(問題文の図から作る中点・交点・垂線の足・2つ目の交点)と証明に使った補助点 used を測り、used の順位を出す
    /// (GS_AUX_RICH、調べる用。来歴 #110)。(1) 因子の共有: 候補を含む乗法的関係の数から、定義する図形の上だけで閉じる分を
    /// 引いたもの。(2) 事実の増え: 候補の事実を図の事実に足し、候補の原子を消して残る図の原子どうしの新しい関係の数(全て・
    /// 低い次数の空間)。(3) 目標が低い次数の空間に入るか(aux_candidates と同じ判定)。
    pub(crate) fn report_aux_richness(&self, problem: &str, used: &[ClassId], fig0: &AuxFigure) {
        let AuxFigure { census, goal_facts, keep } = fig0;
        let given = |ty: EntityType| -> Vec<ClassId> {
            (0..self.entities.len()).filter(|&i| self.entities[i].origin == super::EntityOrigin::Given && self.entities[i].entity_type == ty).map(ClassId).collect()
        };
        // 探索の前の代表元(問題文の実体は読み込んだ時点で自分が代表元のことが多い)。
        let r0 = |x: ClassId| if keep.contains(&x.0) { x } else { self.get_rep(x) };
        let mut s = Symbolic::on_line(self, UNIT_SEED);
        // (1) 問題文の点・直線の全ての組の原子の格子。
        let objs: Vec<ClassId> = given(EntityType::Point).into_iter().chain(given(EntityType::Line)).collect();
        let mut ur = self.unit_relations_of(&mut s, &objs);
        let pids: Vec<ClassId> = ur.point_ids();
        let mut pts: Vec<(usize, Aff)> = Vec::new();
        for &id in &pids {
            let (Some(v), Some(i)) = (s.value(id), ur.point_index(id.0)) else { continue };
            if let Some(a) = affine(&v) && !pts.iter().any(|p| same(&p.1, &a)) { pts.push((i, a)); }
        }
        let lines: Vec<(ClassId, usize, Tri)> = ur.line_ids().into_iter().filter_map(|id| Some((id, ur.line_index(id.0)?, tri(&s.value(id)?)?))).collect();
        let conics: Vec<(ClassId, [Vec<u64>; 3])> = given(EntityType::Conic).into_iter().filter_map(|id| {
            let v = s.value(id)?;
            if v.len() != 6 { return None; }
            Some((id, TS.map(|t| line_eval(&v, t))))
        }).collect();
        s.fail = None;
        let pt_of = |a: &Aff| pts.iter().find(|p| same(&p.1, a)).map(|p| p.0);
        // 定義する図形: 親の点と、親の直線・円の上の点、親の直線(問題文の直線なら)。
        let defining = |s: &mut Symbolic, parents: &[ClassId], mid: bool| -> (Vec<usize>, Vec<usize>) {
            let (mut dp, mut dl): (Vec<usize>, Vec<usize>) = (Vec::new(), Vec::new());
            let mut paffs: Vec<Aff> = Vec::new();
            for &q in parents {
                let Some(v) = s.value(q) else { s.fail = None; continue };
                match self.entities[q.0].entity_type {
                    EntityType::Point => if let Some(a) = affine(&v) { dp.extend(pt_of(&a)); paffs.push(a); },
                    EntityType::Line => {
                        let Some(l) = tri(&v) else { continue };
                        dp.extend(pts.iter().filter(|p| on_line(&p.1, &l)).map(|p| p.0));
                        dl.extend(lines.iter().filter(|m| same_line(&m.2, &l)).map(|m| m.1));
                    }
                    EntityType::Conic if v.len() == 6 => {
                        let c = TS.map(|t| line_eval(&v, t));
                        dp.extend(pts.iter().filter(|p| on_conic(&p.1, &c)).map(|p| p.0));
                    }
                    _ => {}
                }
            }
            if mid && paffs.len() == 2 {
                dp.extend(pts.iter().filter(|p| collinear(&paffs[0], &paffs[1], &p.1)).map(|p| p.0));
                dl.extend(lines.iter().filter(|m| on_line(&paffs[0], &m.2) && on_line(&paffs[1], &m.2)).map(|m| m.1));
            }
            dp.sort_unstable(); dp.dedup(); dl.sort_unstable(); dl.dedup();
            (dp, dl)
        };
        let degree = |v: &V| v.iter().map(|c| super::symbolic::dense(c).len()).max().unwrap_or(1).saturating_sub(1);
        let all_p: Vec<usize> = pts.iter().map(|p| p.0).collect();
        let mut all_l: Vec<usize> = Vec::new();
        for (k, m) in lines.iter().enumerate() { if !lines[..k].iter().any(|n| same_line(&n.2, &m.2)) { all_l.push(m.1); } }

        // (2) 問題文の実体の類だけの図の事実(探索の前に数えたもの)と、その張る空間(全て・目標より低い次数)。
        let mut all: Vec<CensusFact> = census.facts.iter().map(|f| CensusFact { kind: f.kind, objs: f.objs.clone(), degree: f.degree, known: f.known }).collect();
        all.extend(goal_facts.iter().map(|f| CensusFact { kind: f.kind, objs: f.objs.clone(), degree: 0, known: false }));
        let mut keep_ids: Vec<usize> = keep.iter().copied().collect();
        keep_ids.sort_unstable();
        all.push(CensusFact { kind: "", objs: keep_ids.into_iter().map(ClassId).collect(), degree: 0, known: false });
        let (mut ur2, mut vecs) = self.unit_relations_with(&mut s, &all);
        vecs.truncate(census.facts.len());
        let goal_degree = census.goal_degree.unwrap_or(u32::MAX);
        let (mut f_all, mut f_low) = (Eliminator::default(), Eliminator::default());
        // 低い次数の空間には、既知の事実(読み込んだ時点で e-graph が知っているもの)を次数によらず入れる。
        for (f, v) in census.facts.iter().zip(&vecs) { if let Some(v) = v { f_all.insert(v); if f.degree < goal_degree || f.known { f_low.insert(v); } } }
        let goal_vecs: Option<Vec<RelVec>> = if goal_facts.is_empty() { None } else { goal_facts.iter().map(|f| ur2.fact_vector(f)).collect() };
        let mut conic_ids: Vec<ClassId> = census.facts.iter().filter(|f| f.kind == "接続(円)").map(|f| f.objs[1]).collect();
        conic_ids.sort_by_key(|c| c.0);
        conic_ids.dedup();
        let fig = Sampled::new(&mut s, &ur2.point_ids(), &ur2.line_ids(), &conic_ids);
        let dbg = std::env::var("GS_AUX_RICH_DBG").is_ok();
        // 事実の増え: (図の事実への増え, 低い次数の図の事実への増え, 目標が入るか(補助点の事実は全て), 目標が入るか(補助点の
        // 事実は目標より低い次数のものだけ))。val は補助点の値の作り方(次数を測る用)。
        let known_on = known_incidences(census);
        let fig_defining = |parents: &[ClassId], mid: bool| known_defining(self, &known_on, parents, mid, &r0);
        let gain2 = |ur2: &mut UnitRelations, key: usize, v: &V, a: &Aff, def: &Definition, foot: bool, val: &dyn Fn(&mut Symbolic) -> Option<V>, dset: &FxHashSet<usize>| -> Option<(usize, usize, bool, bool)> {
            ur2.add_point(key, v)?;
            let m = ClassId(key);
            let nm = |x: &ClassId| if x.0 == key { "X".to_string() } else { self.entities[x.0].name.clone() };
            // (説明, ベクトル, 次数の測り方: None なら定義、Some(Ok(事実))、Some(Err(直線)) なら直線の方向)。
            type XFact = (String, RelVec, Option<Result<CensusFact, ClassId>>);
            let mut xs: Vec<XFact> = fig.new_facts(m, a).into_iter().filter_map(|f| Some((format!("{}{:?}", f.kind, f.objs.iter().map(nm).collect::<Vec<_>>()), ur2.fact_vector(&f)?, Some(Ok(f))))).collect();
            for (y, l) in fig.dir_facts(a) { xs.extend(ur2.dir_point_line(y, m, l).map(|v| (format!("方向[X,{}]~{}", nm(&y), nm(&l)), v, Some(Err(l))))); }
            match *def {
                Definition::Midpoint(p, q) => xs.extend(ur2.midpoint_vectors(m, r0(p), r0(q)).into_iter().map(|v| ("中点の定義".to_string(), v, None))),
                Definition::Intersection(p, l) if foot => xs.extend(ur2.dir_point_line(r0(p), m, r0(l)).map(|v| ("足の定義".to_string(), v, None))),
                _ => {}
            }
            let xa = ur2.point_atoms(key);
            let (mut e_all, mut e_low, mut e_proj) = (f_all.clone(), f_low.clone(), Eliminator::default());
            let (mut n_all, mut n_low, mut n_proj) = (0usize, 0usize, 0usize);
            for (_, v, _) in &xs {
                if e_all.insert(v) { n_all += 1; }
                if e_low.insert(v) { n_low += 1; }
                let pv: RelVec = v.iter().filter(|(a, _)| xa.contains(a)).copied().collect();
                if e_proj.insert(&pv) { n_proj += 1; }
            }
            let gh = goal_vecs.as_ref().is_some_and(|g| g.iter().all(|v| e_low.depends(v)));
            // 補助点の事実を目標より低い次数のものに限る(目標の図の上にある点は、目標と同じことを言う事実を持つ)。
            let mut low: Vec<usize> = Vec::new();
            if gh {
                let nd = |f: &dyn Fn(&mut Symbolic) -> Option<V>| -> Option<u32> { self.multidegree_with(f).map(|v| v.iter().sum()) };
                let mut e2 = f_low.clone();
                for (k, (_, v, how)) in xs.iter().enumerate() {
                    if e2.depends(v) { continue; }
                    // 定義する図形の上だけで閉じる事実は、補助点を作れば既知(次数によらない)。
                    let closed = match how {
                        None => true,
                        Some(Err(l)) => dset.contains(&l.0),
                        Some(Ok(f)) => f.objs.iter().all(|o| o.0 == key || dset.contains(&o.0)),
                    };
                    let deg = if closed { Some(0) } else { match how {
                        None => Some(0),
                        Some(Err(l)) => { let l = *l; nd(&|bs| Some(line_direction(&bs.value(l)?))) }
                        Some(Ok(f)) => {
                            let o = f.objs.clone();
                            match f.kind {
                                "共線" => nd(&|bs| Some(join_reduced(&val(bs)?, &bs.value(o[1])?))),
                                "共円" => nd(&|bs| Some(circle_reduced(&bs.value(o[0])?, &bs.value(o[1])?, &bs.value(o[2])?))),
                                "接続(直線)" | "接続(円)" => self.natural_degree(o[1]).map(|d| d as u32),
                                _ if o[2] == m => nd(&|bs| Some(length_sq(&val(bs)?, &bs.value(o[1])?))),
                                _ => nd(&|bs| Some(length_sq(&bs.value(o[2])?, &bs.value(o[3])?))),
                            }
                        }
                    } };
                    if deg.is_some_and(|d| d < goal_degree) { e2.insert(v); low.push(k); }
                }
                if !goal_vecs.as_ref().is_some_and(|g| g.iter().all(|v| e2.depends(v))) { low.clear(); }
            }
            let gh_low = !low.is_empty();
            if gh && !gh_low && dbg {
                let nd = |f: &dyn Fn(&mut Symbolic) -> Option<V>| -> Option<u32> { self.multidegree_with(f).map(|v| v.iter().sum()) };
                let mut pe = super::units::ProvEliminator::default();
                for (i, (f, v)) in census.facts.iter().zip(&vecs).enumerate() { if f.degree < goal_degree && let Some(v) = v { pe.insert(v, i); } }
                for (k, x) in xs.iter().enumerate() { pe.insert(&x.1, 1_000_000 + k); }
                println!("AUXDBG any goal_degree={}", goal_degree);
                for g in goal_vecs.iter().flatten() {
                    for (i, c) in pe.explain(g).unwrap_or_default() {
                        let (n, d) = super::units::rational(c);
                        if i >= 1_000_000 {
                            let deg = match &xs[i - 1_000_000].2 {
                                None => Some(0),
                                Some(Err(l)) => { let l = *l; nd(&|bs| Some(line_direction(&bs.value(l)?))) }
                                Some(Ok(f)) => { let o = f.objs.clone(); match f.kind {
                                    "共線" => nd(&|bs| Some(join_reduced(&val(bs)?, &bs.value(o[1])?))),
                                    "共円" => nd(&|bs| Some(circle_reduced(&bs.value(o[0])?, &bs.value(o[1])?, &bs.value(o[2])?))),
                                    "接続(直線)" | "接続(円)" => self.natural_degree(o[1]).map(|d| d as u32),
                                    _ if o[2] == m => nd(&|bs| Some(length_sq(&val(bs)?, &bs.value(o[1])?))),
                                    _ => nd(&|bs| Some(length_sq(&bs.value(o[2])?, &bs.value(o[3])?))),
                                } }
                            };
                            println!("AUXDBG   {}/{} X: {} deg={:?}", n, d, xs[i - 1_000_000].0, deg);
                        } else { let f = &census.facts[i]; println!("AUXDBG   {}/{} {} {:?} deg={}", n, d, f.kind, f.objs.iter().map(nm).collect::<Vec<_>>(), f.degree); }
                    }
                }
            }
            if gh_low && dbg {
                let mut pe = super::units::ProvEliminator::default();
                for (i, (f, v)) in census.facts.iter().zip(&vecs).enumerate() { if f.degree < goal_degree && let Some(v) = v { pe.insert(v, i); } }
                for &k in &low { pe.insert(&xs[k].1, 1_000_000 + k); }
                for g in goal_vecs.iter().flatten() {
                    println!("AUXDBG goal {:?}", g);
                    for (i, c) in pe.explain(g).unwrap_or_default() {
                        let (n, d) = super::units::rational(c);
                        if i >= 1_000_000 { println!("AUXDBG   {}/{} X: {}", n, d, xs[i - 1_000_000].0); }
                        else { let f = &census.facts[i]; println!("AUXDBG   {}/{} {} {:?} deg={}", n, d, f.kind, f.objs.iter().map(nm).collect::<Vec<_>>(), f.degree); }
                    }
                }
            }
            Some((n_all.saturating_sub(n_proj), n_low.saturating_sub(n_proj), gh, gh_low))
        };

        // 候補。
        let mut defs: Vec<(&'static str, Definition)> = Vec::new();
        for i in 0..pids.len() { for j in (i + 1)..pids.len() { defs.push(("中点", Definition::Midpoint(pids[i], pids[j]))); } }
        for i in 0..lines.len() { for j in (i + 1)..lines.len() { defs.push(("交点", Definition::Intersection(lines[i].0, lines[j].0))); } }
        let paff: Vec<(ClassId, Aff)> = pids.iter().filter_map(|&p| Some((p, affine(&s.value(p)?)?))).collect();
        s.fail = None;
        for &(l, _, lt) in &lines {
            for (c, ct) in &conics {
                for (p, a) in &paff { if on_line(a, &lt) && on_conic(a, ct) { defs.push(("直線と円の2つ目の交点", Definition::SecondIntersectionOfLineAndConic(*p, l, *c))); } }
            }
            // 垂線の足は Intersection(点, 直線) の形で持ち、値は foot_value で作る。
            for (p, a) in &paff { if !on_line(a, &lt) { defs.push(("垂線の足", Definition::Intersection(*p, l))); } }
        }
        for i in 0..conics.len() { for j in (i + 1)..conics.len() {
            for (p, a) in &paff { if on_conic(a, &conics[i].1) && on_conic(a, &conics[j].1) { defs.push(("円と円の2つ目の交点", Definition::SecondIntersectionOfCircles(*p, conics[i].0, conics[j].0))); } }
        } }
        let mut cands: Vec<(&'static str, V, Aff, Definition)> = Vec::new();
        for (name, d) in defs {
            let v = if name == "垂線の足" { let [p, l] = d.get_parents()[..] else { continue }; s.foot_value(p, l) } else { s.value_of(d.clone()) };
            let Some(v) = v else { s.fail = None; continue };
            let Some(a) = affine(&v) else { continue };
            if pts.iter().any(|p| same(&p.1, &a)) || cands.iter().any(|c| same(&c.2, &a)) { continue; }
            cands.push((name, v, a, d));
        }
        let max_eval: usize = std::env::var("GS_AUX_RICH_MAX").ok().and_then(|x| x.parse().ok()).unwrap_or(300);
        let mut order: Vec<usize> = (0..cands.len()).collect();
        order.sort_by_key(|&i| degree(&cands[i].1));
        // (1) は点が多いと重い(候補ごとに点の数の3乗ほど)ので、点が 30 を超えたら測らない(0 とする)。
        let heavy = pts.len() > 30;
        let score = |ur: &mut UnitRelations, s: &mut Symbolic, key: usize, v: &V, def: &Definition| -> Option<usize> {
            if heavy { return Some(0); }
            ur.add_point(key, v)?;
            let x = ur.point_index(key)?;
            let parents = def.get_parents();
            let (dp, dl) = defining(s, &parents, matches!(def, Definition::Midpoint(..)));
            let (full, _, _) = ur.point_gain(x, &all_p, &all_l);
            let (sub, _, _) = ur.point_gain(x, &dp, &dl);
            Some(full.saturating_sub(sub))
        };
        // (種類, 次数, 因子の共有, 事実の増え, 低い次数の事実の増え, 目標が入るか)
        type Row = (&'static str, usize, usize, usize, usize, bool, bool);
        let mut scored: Vec<Row> = Vec::new();
        let mut cand_vals: Vec<Aff> = Vec::new();
        for (n, &i) in order.iter().take(max_eval).enumerate() {
            let (name, v, a, d) = &cands[i];
            let foot = *name == "垂線の足";
            let val = |bs: &mut Symbolic| -> Option<V> { if foot { let [p, l] = d.get_parents()[..] else { return None }; bs.foot_value(p, l) } else { bs.value_of(d.clone()) } };
            let dset = fig_defining(&d.get_parents(), matches!(d, Definition::Midpoint(..)));
            let (Some(nt), Some((pg, pgl, gh, ghl))) = (score(&mut ur, &mut s, usize::MAX - n, v, d), gain2(&mut ur2, usize::MAX - n, v, a, d, foot, &val, &dset)) else { continue };
            scored.push((name, degree(v), nt, pg, pgl, gh, ghl));
            cand_vals.push(*a);
            if gh && std::env::var("GS_AUX_RICH_TOP").is_ok() {
                println!("AUXGH\t{}\t{}\t{}\t{}\t{}", problem, name, degree(v), d.get_parents().iter().map(|p| self.entities[p.0].name.clone()).collect::<Vec<_>>().join(","), ghl);
            }
        }
        let nc = scored.len();
        let goal_low = goal_vecs.as_ref().map(|g| g.iter().all(|v| f_low.depends(v)));
        println!("AUXDIST\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:?}\t{}", problem, cands.len(), nc,
            scored.iter().filter(|c| c.2 > 0).count(), scored.iter().map(|c| c.2).max().unwrap_or(0),
            scored.iter().filter(|c| c.3 > 0).count(), scored.iter().map(|c| c.3).max().unwrap_or(0),
            scored.iter().filter(|c| c.4 > 0).count(), scored.iter().filter(|c| c.5).count(), goal_low, scored.iter().filter(|c| c.6).count());
        let frac = |f: &dyn Fn(&Row) -> std::cmp::Ordering| -> f64 {
            if nc == 0 { return f64::NAN; }
            let better = scored.iter().filter(|c| f(c) == std::cmp::Ordering::Less).count() as f64;
            let ties = scored.iter().filter(|c| f(c) == std::cmp::Ordering::Equal).count() as f64;
            (better + 0.5 * ties) / nc as f64
        };
        // 目標を低い次数の空間に入れる候補の、他の測り方での順位(0 に近いほど上位)。
        if goal_low == Some(false) {
            for &(name, d, nt, pg, pgl, _, ghl) in &scored {
                if !ghl { continue; }
                println!("AUXHIT\t{}\t{}\t{}\t{}\t{}\t{}\t{:.3}\t{:.3}\t{:.3}\t{:.3}\t{}", problem, name, d, nt, pg, pgl,
                    frac(&|c| nt.cmp(&c.2)), frac(&|c| pg.cmp(&c.3)), frac(&|c| pgl.cmp(&c.4)), frac(&|c| c.1.cmp(&d)), nc);
            }
        }
        for (u, &x) in used.iter().enumerate() {
            let skip = |why: &str| println!("AUXSKIP\t{}\t{}\t{}", problem, self.entities[x.0].original_name, why);
            let Some(v) = s.value(x) else { s.fail = None; skip("値を作れない"); continue };
            let Some(a) = affine(&v) else { skip("無限遠"); continue };
            if pts.iter().any(|p| same(&p.1, &a)) { skip("問題文の点と同じ"); continue; }
            let def = self.entities[x.0].original_definition.clone();
            let key = usize::MAX / 2 - u;
            let val = |bs: &mut Symbolic| bs.value(x);
            let dset = fig_defining(&def.get_parents(), matches!(def, Definition::Midpoint(..)));
            let (Some(nt), Some((pg, pgl, gh, ghl))) = (score(&mut ur, &mut s, key, &v, &def), gain2(&mut ur2, key, &v, &a, &def, false, &val, &dset)) else { continue };
            let d = degree(&v);
            // 候補 c が used より良い(多い・次数が低い)なら Less。0 に近いほど used が上位。
            let (p_nt, p_pg, p_pgl, p_deg) = (frac(&|c| nt.cmp(&c.2)), frac(&|c| pg.cmp(&c.3)), frac(&|c| pgl.cmp(&c.4)), frac(&|c| c.1.cmp(&d)));
            let in_c = cand_vals.iter().any(|c| same(c, &a));
            println!("AUXRANK\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.3}\t{:.3}\t{:.3}\t{:.3}\t{}\t{}\t{}", problem, self.entities[x.0].original_name, def.get_type_name(), d, nt, pg, pgl, gh, p_nt, p_pg, p_pgl, p_deg, nc, in_c, ghl);
        }
    }
}

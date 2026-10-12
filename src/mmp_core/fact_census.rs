//! 🌟 図の中で成り立つ事実(「定理」)を次数の順に並べて数える(`geom_solver facts`)。
//!
//! 問題を多項式の恒等式とみなす: 作図した点・直線・円・比のスカラーは配置空間 C からの有理写像で、事実は「2つの作図が同じ写像に
//! なる」という恒等式。事実の次数は、その共通の写像の次数(natural_degree.rs: 次数のベクトルの成分の和、各自由点の超平面類の和に
//! ついての次数)。共線 → 3点を通る直線、共円 → 4点を通る円、平行・垂直 → 直線の方向、等長 → 長さの2乗、等角 → 有向角、
//! 接続 → 点が乗る曲線、同じ点・同じ直線 → その点・直線。関わる実体の次数の和ではなく、恒等式の両辺が表す1つの写像の次数。
//! 事実の候補は、全ての媒介変数を一般の直線の上に乗せた3か所で値を比べて選ぶ(測定用。証明には使わない)。「既知」は、
//! その時点の e-graph が既に知っている事実(読み込んだ直後なら定義から従うもの、探索の後ならそれまでに示したもの。
//! 代数的な追跡の格子にだけある等式は数えない)。`--fact-census`(solve)は探索の前に一覧を作り、探索の後に判定し直す。

use rustc_hash::{FxHashMap, FxHashSet};

use super::symbolic::{addm, angle_of_directions, circle_reduced, invm, join_reduced, length_sq, line_degree, line_direction, line_eval, mulm, negm, Symbolic, V};
use super::{ClassId, Definition, EGraph, EntityType};

pub(crate) struct CensusFact {
    pub kind: &'static str,
    pub objs: Vec<ClassId>,
    pub degree: u32,
    pub known: bool,
}

pub(crate) struct Census {
    pub facts: Vec<CensusFact>,
    pub goal_degree: Option<u32>,
    /// 目標が一般の直線の上で恒等的に成り立つか(測定の確かめ)。
    pub goal_true: Option<bool>,
    pub points: usize,
    pub lines: usize,
    pub conics: usize,
    /// 値を作れなかった実体の数。
    pub failed: usize,
    pub params: usize,
    pub max_degree: u32,
    pub skipped: Vec<String>,
}

fn sub(a: u64, b: u64) -> u64 { addm(a, negm(b)) }

/// 点 (実体, 次数, 値, 3か所の (x, y))・直線 (実体, 次数, 値, 3か所の係数)・円 (実体, 次数, 3か所の係数)。
type PointVal = (ClassId, u32, V, [(u64, u64); 3]);
type LineVal = (ClassId, u32, V, [[u64; 3]; 3]);
type ConicVal = (ClassId, u32, [[u64; 6]; 3]);

impl EGraph {
    pub(crate) fn fact_census(&self, target: Option<&(String, Vec<ClassId>)>, max_points: usize) -> Census {
        // 写像 f の次数(次数のベクトルの成分の和)。
        let nd = |f: &dyn Fn(&mut Symbolic) -> Option<V>| -> Option<u32> { self.multidegree_with(f).map(|v| v.iter().sum()) };
        let mut s = Symbolic::on_line(self, 0x9E37_79B9_7F4A_7C15);
        let ts: [u64; 3] = [0x1234_5678_9ABC_u64 % super::symbolic::P, 0x0FED_CBA9_8765_u64 % super::symbolic::P, 0x7777_3333_1111_u64 % super::symbolic::P];
        let (linf, ci, cj) = (self.get_rep(self.line_infinity), self.get_rep(self.circ_i), self.get_rep(self.circ_j));
        let mut c = Census { facts: Vec::new(), goal_degree: None, goal_true: None, points: 0, lines: 0, conics: 0, failed: 0, params: 0, max_degree: 0, skipped: Vec::new() };
        // 実体の値。
        let mut pts: Vec<PointVal> = Vec::new();
        let mut lns: Vec<LineVal> = Vec::new();
        let mut cns: Vec<ConicVal> = Vec::new();
        for i in 0..self.entities.len() {
            let id = ClassId(i);
            if self.get_rep(id) != id || !self.entities[i].is_active() || id == linf || id == ci || id == cj { continue; }
            let ty = self.entities[i].entity_type;
            if !matches!(ty, EntityType::Point | EntityType::Line | EntityType::Conic) { continue; }
            let Some(v) = s.value(id) else { c.failed += 1; s.fail = None; continue };
            let d = self.natural_degree(id).map_or_else(|| line_degree(&v), |x| x as u32);
            let vals: Vec<Vec<u64>> = ts.iter().map(|&t| line_eval(&v, t)).collect();
            match ty {
                EntityType::Point => {
                    if vals.iter().any(|x| x.len() < 3 || x[2] == 0) { continue; }
                    let aff: Vec<(u64, u64)> = vals.iter().map(|x| { let iz = invm(x[2]); (mulm(x[0], iz), mulm(x[1], iz)) }).collect();
                    pts.push((id, d, v, [aff[0], aff[1], aff[2]]));
                }
                EntityType::Line => {
                    if vals.iter().any(|x| x.len() < 3 || (x[0] == 0 && x[1] == 0)) { continue; }
                    lns.push((id, d, v, [[vals[0][0], vals[0][1], vals[0][2]], [vals[1][0], vals[1][1], vals[1][2]], [vals[2][0], vals[2][1], vals[2][2]]]));
                }
                _ => {
                    if vals.iter().any(|x| x.len() < 6) { continue; }
                    let arr = |x: &Vec<u64>| [x[0], x[1], x[2], x[3], x[4], x[5]];
                    cns.push((id, d, [arr(&vals[0]), arr(&vals[1]), arr(&vals[2])]));
                }
            }
            c.max_degree = c.max_degree.max(d);
        }
        c.params = self.degree_blocks().len();
        (c.points, c.lines, c.conics) = (pts.len(), lns.len(), cns.len());
        // 接続(点が直線・円に乗る)。
        for p in &pts {
            for l in &lns {
                if (0..3).all(|k| { let (x, y) = p.3[k]; let a = l.3[k]; addm(addm(mulm(a[0], x), mulm(a[1], y)), a[2]) == 0 }) {
                    c.facts.push(CensusFact { kind: "接続(直線)", objs: vec![p.0, l.0], degree: l.1, known: false });
                }
            }
            for q in &cns {
                if (0..3).all(|k| { let (x, y) = p.3[k]; let a = q.2[k];
                    let v = [mulm(a[0], mulm(x, x)), mulm(a[1], mulm(x, y)), mulm(a[2], mulm(y, y)), mulm(a[3], x), mulm(a[4], y), a[5]];
                    v.iter().fold(0, |s, &t| addm(s, t)) == 0 }) {
                    c.facts.push(CensusFact { kind: "接続(円)", objs: vec![p.0, q.0], degree: q.1, known: false });
                }
            }
        }
        // 同じ点(別の実体なのに同じ位置)。
        let same = |a: &(u64, u64), b: &(u64, u64)| a.0 == b.0 && a.1 == b.1;
        let mut distinct: Vec<usize> = Vec::new();
        for i in 0..pts.len() {
            match distinct.iter().find(|&&j| (0..3).all(|k| same(&pts[i].3[k], &pts[j].3[k]))) {
                Some(&j) => c.facts.push(CensusFact { kind: "同じ点", objs: vec![pts[j].0, pts[i].0], degree: pts[j].1, known: false }),
                None => distinct.push(i),
            }
        }
        let ndistinct = distinct.len();
        let dp: Vec<usize> = distinct.into_iter().take(max_points).collect();
        if dp.len() < ndistinct { c.skipped.push(format!("点を {} 個に絞った", dp.len())); }
        // 共線。
        let col = |a: (u64, u64), b: (u64, u64), q: (u64, u64)| sub(mulm(sub(b.0, a.0), sub(q.1, a.1)), mulm(sub(b.1, a.1), sub(q.0, a.0))) == 0;
        let mut collinear: FxHashSet<(usize, usize, usize)> = FxHashSet::default();
        let mut joins: FxHashMap<(usize, usize), u32> = FxHashMap::default();
        for x in 0..dp.len() {
            for y in (x + 1)..dp.len() {
                for z in (y + 1)..dp.len() {
                    let (a, b, q) = (&pts[dp[x]], &pts[dp[y]], &pts[dp[z]]);
                    if !(0..3).all(|k| col(a.3[k], b.3[k], q.3[k])) { continue; }
                    collinear.insert((x, y, z));
                    let (ia, ib) = (a.0, b.0);
                    let degree = *joins.entry((x, y)).or_insert_with(|| nd(&|s| Some(join_reduced(&s.value(ia)?, &s.value(ib)?))).unwrap_or(0));
                    c.facts.push(CensusFact { kind: "共線", objs: vec![a.0, b.0, q.0], degree, known: false });
                }
            }
        }
        // 共円(3点が一直線のものは除く)。
        let det3 = |m: [[u64; 3]; 3]| -> u64 {
            let t1 = mulm(m[0][0], sub(mulm(m[1][1], m[2][2]), mulm(m[1][2], m[2][1])));
            let t2 = mulm(m[0][1], sub(mulm(m[1][0], m[2][2]), mulm(m[1][2], m[2][0])));
            let t3 = mulm(m[0][2], sub(mulm(m[1][0], m[2][1]), mulm(m[1][1], m[2][0])));
            addm(sub(t1, t2), t3)
        };
        let cyc = |p: [(u64, u64); 4]| -> bool {
            let r = |q: (u64, u64)| { let (dx, dy) = (sub(q.0, p[0].0), sub(q.1, p[0].1)); [addm(mulm(dx, dx), mulm(dy, dy)), dx, dy] };
            det3([r(p[1]), r(p[2]), r(p[3])]) == 0
        };
        let mut circles: FxHashMap<(usize, usize, usize), u32> = FxHashMap::default();
        if dp.len() <= 90 {
            for a in 0..dp.len() {
                for b in (a + 1)..dp.len() {
                    for x in (b + 1)..dp.len() {
                        if collinear.contains(&(a, b, x)) { continue; }
                        for y in (x + 1)..dp.len() {
                            if collinear.contains(&(a, b, y)) || collinear.contains(&(a, x, y)) || collinear.contains(&(b, x, y)) { continue; }
                            let q = [&pts[dp[a]], &pts[dp[b]], &pts[dp[x]], &pts[dp[y]]];
                            if !(0..3).all(|k| cyc([q[0].3[k], q[1].3[k], q[2].3[k], q[3].3[k]])) { continue; }
                            let (ia, ib, ic) = (q[0].0, q[1].0, q[2].0);
                            let degree = *circles.entry((a, b, x)).or_insert_with(|| nd(&|s| Some(circle_reduced(&s.value(ia)?, &s.value(ib)?, &s.value(ic)?))).unwrap_or(0));
                            c.facts.push(CensusFact { kind: "共円", objs: q.iter().map(|p| p.0).collect(), degree, known: false });
                        }
                    }
                }
            }
        } else { c.skipped.push("点が多いので共円は数えない".into()); }
        // 平行・垂直(共通の方向の次数)。
        let dirs: Vec<u32> = lns.iter().map(|l| { let id = l.0; nd(&|s| Some(line_direction(&s.value(id)?))).unwrap_or(0) }).collect();
        for i in 0..lns.len() {
            for j in (i + 1)..lns.len() {
                let (a, b) = (&lns[i].3, &lns[j].3);
                let same_line = (0..3).all(|k| { let (u, v) = (a[k], b[k]);
                    sub(mulm(u[0], v[1]), mulm(u[1], v[0])) == 0 && sub(mulm(u[0], v[2]), mulm(u[2], v[0])) == 0 && sub(mulm(u[1], v[2]), mulm(u[2], v[1])) == 0 });
                if same_line {
                    c.facts.push(CensusFact { kind: "同じ直線", objs: vec![lns[i].0, lns[j].0], degree: lns[i].1, known: false });
                    continue;
                }
                let deg = dirs[i];
                if (0..3).all(|k| sub(mulm(a[k][0], b[k][1]), mulm(a[k][1], b[k][0])) == 0) {
                    c.facts.push(CensusFact { kind: "平行", objs: vec![lns[i].0, lns[j].0], degree: deg, known: false });
                } else if (0..3).all(|k| addm(mulm(a[k][0], b[k][0]), mulm(a[k][1], b[k][1])) == 0) {
                    c.facts.push(CensusFact { kind: "垂直", objs: vec![lns[i].0, lns[j].0], degree: deg, known: false });
                }
            }
        }
        // 等長(長さの2乗が等しい線分の組)。
        let mut by_len: FxHashMap<[u64; 3], Vec<(usize, usize)>> = FxHashMap::default();
        for x in 0..dp.len() {
            for y in (x + 1)..dp.len() {
                let key = [0, 1, 2].map(|k| { let (a, b) = (pts[dp[x]].3[k], pts[dp[y]].3[k]); let (dx, dy) = (sub(a.0, b.0), sub(a.1, b.1)); addm(mulm(dx, dx), mulm(dy, dy)) });
                by_len.entry(key).or_default().push((dp[x], dp[y]));
            }
        }
        let mut len_deg: FxHashMap<(usize, usize), u32> = FxHashMap::default();
        for group in by_len.values().filter(|g| g.len() >= 2) {
            for &seg in group {
                let (ia, ib) = (pts[seg.0].0, pts[seg.1].0);
                len_deg.entry(seg).or_insert_with(|| nd(&|s| Some(length_sq(&s.value(ia)?, &s.value(ib)?))).unwrap_or(0));
            }
            for u in 0..group.len() {
                for w in (u + 1)..group.len() {
                    let (s1, s2) = (group[u], group[w]);
                    c.facts.push(CensusFact { kind: "等長", objs: vec![pts[s1.0].0, pts[s1.1].0, pts[s2.0].0, pts[s2.1].0], degree: len_deg[&s1], known: false });
                }
            }
        }
        // 等角(方向の類の組の有向角が等しい。直角と、同じ方向の類の組は除く)。
        let mut classes: Vec<usize> = Vec::new();
        for i in 0..lns.len() {
            match classes.iter().position(|&j| (0..3).all(|k| sub(mulm(lns[i].3[k][0], lns[j].3[k][1]), mulm(lns[i].3[k][1], lns[j].3[k][0])) == 0)) {
                Some(pos) => { if dirs[i] < dirs[classes[pos]] { classes[pos] = i; } }
                None => classes.push(i),
            }
        }
        let mut by_angle: FxHashMap<[u64; 3], Vec<(usize, usize)>> = FxHashMap::default();
        for &i in &classes {
            for &j in &classes {
                if i == j { continue; }
                let mut key = [0u64; 3];
                let mut right = false;
                for (k, slot) in key.iter_mut().enumerate() {
                    let (a, b) = (lns[i].3[k], lns[j].3[k]);
                    let cr = sub(mulm(a[0], b[1]), mulm(a[1], b[0]));
                    let dt = addm(mulm(a[0], b[0]), mulm(a[1], b[1]));
                    if dt == 0 { right = true; break; }
                    *slot = mulm(cr, invm(dt));
                }
                if !right { by_angle.entry(key).or_default().push((i, j)); }
            }
        }
        let mut ang_deg: FxHashMap<(usize, usize), u32> = FxHashMap::default();
        for group in by_angle.values().filter(|g| g.len() >= 2) {
            for &(i, j) in group {
                let (li, lj) = (lns[i].0, lns[j].0);
                ang_deg.entry((i, j)).or_insert_with(|| nd(&|s| Some(angle_of_directions(&line_direction(&s.value(li)?), &line_direction(&s.value(lj)?)))).unwrap_or(0));
            }
            for u in 0..group.len() {
                for w in (u + 1)..group.len() {
                    let ((i, j), (k, l)) = (group[u], group[w]);
                    // (D1,D2) = (D3,D4) と (D2,D1) = (D4,D3) は同じ事実なので、片方だけ数える。
                    if (i, j) > (j, i) && (k, l) > (l, k) { continue; }
                    c.facts.push(CensusFact { kind: "等角", objs: vec![lns[i].0, lns[j].0, lns[k].0, lns[l].0], degree: ang_deg[&(i, j)], known: false });
                }
            }
        }
        // 目標の次数(共通の写像の次数)と、一般の直線の上で成り立つか。
        if let Some(t) = target {
            c.goal_degree = self.goal_degree(t);
            c.goal_true = s.prove(&t.0, &t.1);
        }
        let known: Vec<bool> = c.facts.iter().map(|f| self.census_known(f)).collect();
        for (f, k) in c.facts.iter_mut().zip(known) { f.known = k; }
        c.facts.sort_by_key(|f| (f.degree, f.kind));
        c
    }

    /// 目標の次数(共通の写像の次数): 共円 → 最初の3点を通る円、接続 → 曲線、等しい → その実体。直角・平行(有向角が定数)は
    /// 方向の次数。
    pub(crate) fn goal_degree(&self, (kind, args): &(String, Vec<ClassId>)) -> Option<u32> {
        let nd = |f: &dyn Fn(&mut Symbolic) -> Option<V>| -> Option<u32> { self.multidegree_with(f).map(|v| v.iter().sum()) };
        let (ang90, ang0) = (self.get_rep(self.ang90), self.get_rep(self.ang0));
        let direction = |x: ClassId| -> Option<u32> { nd(&|s| { let v = s.value(x)?; Some(if v.len() == 3 && v[2].is_zero() { v } else { line_direction(&v) }) }) };
        match (kind.as_str(), args.as_slice()) {
            ("Concyclic", [a, b, c, ..]) => { let (a, b, c) = (*a, *b, *c); nd(&|s| Some(circle_reduced(&s.value(a)?, &s.value(b)?, &s.value(c)?))) }
            ("Connected", [x, y]) => self.natural_degree(self.point_and_curve(*x, *y).1).map(|d| d as u32),
            ("Identical", [a, b]) => {
                let is_const = |x: ClassId| self.get_rep(x) == ang90 || self.get_rep(x) == ang0;
                let x = if is_const(*a) { *b } else { *a };
                match self.entities[x.0].original_definition {
                    Definition::AnglePair(d1, _) if is_const(*a) || is_const(*b) => direction(d1),
                    _ => self.natural_degree(x).map(|d| d as u32),
                }
            }
            _ => None,
        }
    }

    /// 角・長さの事実の実体(直線の方向と有向角、長さの2乗)を作る。探索の後に代数的な追跡を回して、格子から従う事実も
    /// 数えるため(--fact-census。証明を出した後に呼ぶ)。
    pub(crate) fn census_materialize(&mut self, f: &CensusFact) {
        let make = |eg: &mut EGraph, def: Definition| { let ty = def.default_entity_type(); eg.create_entity(format!("census_{}", eg.entities.len()), def, ty) };
        let angle = |eg: &mut EGraph, a: ClassId, b: ClassId| {
            let (da, db) = (make(eg, Definition::DirectionOf(eg.get_rep(a))), make(eg, Definition::DirectionOf(eg.get_rep(b))));
            make(eg, Definition::AnglePair(da, db));
        };
        match (f.kind, f.objs.as_slice()) {
            ("平行" | "垂直", [a, b]) => angle(self, *a, *b),
            ("等角", [a, b, c, d]) => { angle(self, *a, *b); angle(self, *c, *d); }
            ("等長", [a, b, c, d]) => {
                let (a, b, c, d) = (self.get_rep(*a), self.get_rep(*b), self.get_rep(*c), self.get_rep(*d));
                make(self, Definition::LengthSq(a, b));
                make(self, Definition::LengthSq(c, d));
            }
            _ => {}
        }
    }

    /// 事実を、いまの e-graph が既に知っているか(実体はその時点の代表元で見るので、探索の前に作った一覧を探索の後に判定し直せる)。
    pub(crate) fn census_known(&self, f: &CensusFact) -> bool {
        let r = |x: ClassId| self.get_rep(x);
        let memo_rep = |def: Definition| self.memo.get(&self.normalize_definition(&def)).map(|&x| self.get_rep(x));
        let dir = |l: ClassId| memo_rep(Definition::DirectionOf(r(l)));
        let ang = |p: ClassId, q: ClassId| match (dir(p), dir(q)) { (Some(x), Some(y)) => memo_rep(Definition::AnglePair(x, y)), _ => None };
        // 最初の点を通る ty の曲線のうち、残りの点も全て通るものがあるか。
        let on_common = |ty: EntityType, ps: &[ClassId]| -> bool {
            self.entities[r(ps[0]).0].components.iter().flat_map(|c| c.subobjects.iter()).map(|&x| r(x))
                .filter(|&x| self.entities[x.0].entity_type == ty)
                .any(|x| ps[1..].iter().all(|&q| self.is_connected(q, x)))
        };
        match (f.kind, f.objs.as_slice()) {
            ("接続(直線)" | "接続(円)", [p, c]) => self.is_connected(*p, *c),
            ("同じ点" | "同じ直線", [a, b]) => r(*a) == r(*b),
            ("共線", ps) => on_common(EntityType::Line, ps),
            ("共円", ps) => on_common(EntityType::Conic, ps),
            ("平行", [a, b]) => (dir(*a).is_some() && dir(*a) == dir(*b)) || ang(*a, *b) == Some(r(self.ang0)),
            ("垂直", [a, b]) => ang(*a, *b) == Some(r(self.ang90)) || match (dir(*a), dir(*b)) {
                (Some(x), Some(y)) => memo_rep(Definition::PerpDirectionOf(x)) == Some(y) || memo_rep(Definition::PerpDirectionOf(y)) == Some(x),
                _ => false,
            },
            ("等長", [a, b, c, d]) => {
                let (x, y) = (memo_rep(Definition::LengthSq(r(*a), r(*b))), memo_rep(Definition::LengthSq(r(*c), r(*d))));
                x.is_some() && x == y
            }
            ("等角", [a, b, c, d]) => {
                let (x, y) = (ang(*a, *b), ang(*c, *d));
                x.is_some() && x == y
            }
            _ => false,
        }
    }
}

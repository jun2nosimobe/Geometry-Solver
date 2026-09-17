//! 🌟 padic.rs の算術(PInt、Z/P^4Z)の上に、EGraph の Definition を辿る評価器(discover_viz.rs::RealEvaluator と同じ構造)を
//! 実装し、自由点のペアを退化させては全図形ペアの一致を走査するドライバを用意する。
//! 手順:
//! 1. 2つの自由点A,Bを選び、A = B + P*δ(δは乱数)という座標を与える。他の自由点は一般的な乱数座標にする。
//! 2. 依存関係にある全ての図形を mod P^4 で評価する。
//! 3. 各図形の同次座標を共通する P の最大べきで割ってから mod P を取り、退化の極限での「先頭項」を読む。
//! 4. 先頭項が射影的に一致する2つの図形の組を「この退化のもとで関連がある」候補として集める。
//! 5. 退化なしの一般の乱数でも一致する組(常に真の一致)は、この技法固有の発見ではないので除く。

use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};
use crate::mmp_core::coords::{self, Geometry, Placed, Placement};
use crate::padic::{
    cross3,
    self, affine_point, intersection, line_through_points, midpoint, parallel_line,
    perpendicular_line, projectively_equal_mod_p, DivOutcome, PInt, Triple,
};
use rand::rngs::StdRng;
use rand::SeedableRng;
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Clone, Copy, Debug)]
pub enum DegenShape {
    Point(Triple),
    Line(Triple),
    /// known: この円周上にあると分かっている点(Circumcircle(a,b,c)ならa)。
    /// 円周上の点を平方根なしに厳密サンプリングするために使う
    /// (既知点Qから任意方向dへ引いた直線の"もう一方の交点"は、Qが既に根で
    /// あることを使うと1次方程式で解ける)。
    Circle { center: Triple, r_sq: PInt, known: Triple },
    /// 🌟 スカラー量(長さの二乗・その積・複比)を num/den の比のまま持つ。
    ///
    /// p進の環では割り算が常にできる(=分母が単元である)とは限らないので、
    /// 商にしてしまうと分母が退化した瞬間に評価不能になる。比のまま持って
    /// num1*den2 == num2*den1 で比べれば、無限遠が絡む複比もそのまま扱える。
    Scalar { num: PInt, den: PInt },
}

/// アフィン座標(x,y)を得るため、同次座標をzで割る。zの方が退化して
/// いれば(=無限遠へ発散、または判定不能)Noneを返す。
fn affine_xy(t: &Triple) -> Option<(PInt, PInt)> {
    match (t[0].checked_div(&t[2]), t[1].checked_div(&t[2])) {
        (DivOutcome::Finite(x), DivOutcome::Finite(y)) => Some((x, y)),
        _ => None,
    }
}

fn squared_distance(p: &Triple, q: &Triple) -> Option<PInt> {
    let (px, py) = affine_xy(p)?;
    let (qx, qy) = affine_xy(q)?;
    let dx = px.sub(&qx);
    let dy = py.sub(&qy);
    Some(dx.mul(&dx).add(&dy.mul(&dy)))
}

/// 円(中心center)上の既知点knownから方向(dx,dy)へ引いた直線が、その円と
/// もう一度交わる点。knownが既に根であることを使うと
/// t = -2 d·(known-center) / |d|² と1次で解けるので平方根が要らない
/// ――これが「一方の交点が既知なら円との第2交点は有理的に作図できる」の
/// 実体で、sample_on_circle(方向を乱数で取る)と
/// SecondIntersectionOfLineAndConic(方向を与えられた直線から取る)の
/// 両方がこの1つの式を共有する。
fn second_on_circle(center: &Triple, known: &Triple, dx: PInt, dy: PInt) -> Option<Triple> {
    let (qx, qy) = affine_xy(known)?;
    let (cx, cy) = affine_xy(center)?;
    let ux = qx.sub(&cx);
    let uy = qy.sub(&cy);
    let num = dx.mul(&ux).add(&dy.mul(&uy));
    let two_num = num.add(&num);
    let den = dx.mul(&dx).add(&dy.mul(&dy));
    let t = match two_num.checked_div(&den) { DivOutcome::Finite(v) => v.neg(), _ => return None };
    Some(affine_point(qx.add(&t.mul(&dx)), qy.add(&t.mul(&dy))))
}

/// 2つの同次3元ベクトル(点でも直線でもよい)が射影的に同一か。外積が完全に消えることと同値。
/// 共線・共点を行列式で判定するときは、3つのうち2つが同一でも行列式が0になるので、どのペアについてもこれで退化を弾く。
fn projectively_same(a: &Triple, b: &Triple) -> bool {
    cross3(a, b).iter().all(|x| x.valuation().is_none())
}

/// 2円の根軸(方冪が等しい点の軌跡)。円i: x²+y²-2x_i x-2y_i y+(x_i²+y_i²-r_i²)=0
/// の差を取るだけで二次の項が消えて1次式が残る。
/// mmp_calculators::calc_radical_axis の PInt 版。
fn radical_axis(c1: (&Triple, PInt), c2: (&Triple, PInt)) -> Option<Triple> {
    let (x1, y1) = affine_xy(c1.0)?;
    let (x2, y2) = affine_xy(c2.0)?;
    let two = PInt::from_i64_mod_p(2);
    let a = two.mul(&x2.sub(&x1));
    let b = two.mul(&y2.sub(&y1));
    let pow1 = x1.mul(&x1).add(&y1.mul(&y1)).sub(&c1.1);
    let pow2 = x2.mul(&x2).add(&y2.mul(&y2)).sub(&c2.1);
    Some([a, b, pow1.sub(&pow2)])
}

/// mmp_calculators::calc_harmonic_conjugateと同じ式(除算不要)をPInt化
/// したもの。a,b,cは既に共線(retrieved as points on some line)である
/// という前提。
fn harmonic_conjugate(a: &Triple, b: &Triple, c: &Triple) -> Triple {
    let is_apparently_zero = |t: &Triple| t.iter().all(|x| x.valuation().is_none());
    let try_pair = |i: usize, j: usize| -> [PInt; 2] {
        let row1 = [a[i], b[i], c[i].neg()];
        let row2 = [a[j], b[j], c[j].neg()];
        let cross = row1[1].mul(&row2[2]).sub(&row1[2].mul(&row2[1]));
        let cross2 = row1[2].mul(&row2[0]).sub(&row1[0].mul(&row2[2]));
        [cross, cross2]
    };
    let mut pq = try_pair(0, 1);
    if pq.iter().all(|x| x.valuation().is_none()) { pq = try_pair(1, 2); }
    if pq.iter().all(|x| x.valuation().is_none()) { pq = try_pair(0, 2); }
    let (p, q) = (pq[0], pq[1]);
    let d = [
        p.mul(&a[0]).sub(&q.mul(&b[0])),
        p.mul(&a[1]).sub(&q.mul(&b[1])),
        p.mul(&a[2]).sub(&q.mul(&b[2])),
    ];
    let _ = is_apparently_zero;
    d
}

/// p進の座標での評価。自由点の置き方と同値類の評価は mmp_core::coords と共通。
pub struct DegenEvaluator<'a> {
    egraph: &'a EGraph,
    coords: DegenCoords,
    cache: FxHashMap<usize, DegenShape>,
}

/// 置いた自由点の座標(代表元 -> アフィン座標)と、置くための乱数。
struct DegenCoords {
    free_coords: FxHashMap<ClassId, (PInt, PInt)>,
    rng: StdRng,
}

impl<'a> DegenEvaluator<'a> {
    /// merge_pairが指定されていれば、その2つの自由点(egraph.get_rep後)を
    /// A = B + P*δという退化した座標で結ぶ。指定が無ければ全ての自由点を
    /// 完全に一般的な乱数座標にする(discover.rsの一般乱数一致検出との
    /// 対照実験、「この一致は退化固有か」を確かめるベースラインに使う)。
    ///
    /// 残りの自由点は最初にまとめて置く。前提(「Dは辺BC上」など)を持つ点はその曲線の上に置き、前提を満たせ
    /// なかった点(直線と円の両方に乗る点など、平方根が要る組み合わせ)は置かずに残す ― 仮定を破った配置を作るより、
    /// その点に依存する図形を評価不能にする方が安全(崩壊検出が誤って発火する)。
    pub fn new(egraph: &'a EGraph, seed: u64, merge_pair: Option<(ClassId, ClassId)>) -> Self {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut free_coords = FxHashMap::default();
        if let Some((a_id, b_id)) = merge_pair {
            let a_rep = egraph.get_rep(a_id);
            let b_rep = egraph.get_rep(b_id);
            if a_rep != b_rep {
                let bx = PInt::random_unit(&mut rng);
                let by = PInt::random_unit(&mut rng);
                let dx = PInt::random_any(&mut rng);
                let dy = PInt::random_any(&mut rng);
                free_coords.insert(b_rep, (bx, by));
                free_coords.insert(a_rep, (bx.add(&dx.scaled_by_p()), by.add(&dy.scaled_by_p())));
            }
        }
        let mut coords = DegenCoords { free_coords, rng };
        if let Placed::Violated(points) = egraph.place_free_points(&egraph.all_free_points(), &mut coords, true) {
            for fp in points { coords.unplace(egraph, fp); }
        }
        Self { egraph, coords, cache: FxHashMap::default() }
    }

    pub fn eval(&mut self, id: ClassId) -> Option<DegenShape> {
        coords::evaluate(self.egraph, &self.coords, id, &mut self.cache, &mut std::collections::HashSet::new())
    }
}

impl DegenCoords {
    fn set(&mut self, egraph: &EGraph, point: ClassId, t: &Triple) -> bool {
        let Some(xy) = affine_xy(t) else { return false };
        self.free_coords.insert(egraph.get_rep(point), xy);
        true
    }
}

impl Geometry for DegenCoords {
    type Shape = DegenShape;

    fn free(&self, egraph: &EGraph, rep: ClassId, _def: &Definition) -> Option<DegenShape> {
        if egraph.entities[rep.0].entity_type != EntityType::Point { return None; } // Line_infinity等
        let &(x, y) = self.free_coords.get(&rep)?;
        Some(DegenShape::Point(affine_point(x, y)))
    }

    fn construct(&self, _egraph: &EGraph, def: &Definition, get: &mut dyn FnMut(ClassId) -> Option<DegenShape>) -> Option<DegenShape> {
        let point_of = |id: ClassId, get: &mut dyn FnMut(ClassId) -> Option<DegenShape>| match get(id)? { DegenShape::Point(t) => Some(t), _ => None };
        let line_of = |id: ClassId, get: &mut dyn FnMut(ClassId) -> Option<DegenShape>| match get(id)? { DegenShape::Line(t) => Some(t), _ => None };
        let circle_of = |id: ClassId, get: &mut dyn FnMut(ClassId) -> Option<DegenShape>| match get(id)? {
            DegenShape::Circle { center, r_sq, .. } => Some((center, r_sq)), _ => None };
        let scalar_of = |id: ClassId, get: &mut dyn FnMut(ClassId) -> Option<DegenShape>| match get(id)? {
            DegenShape::Scalar { num, den } => Some((num, den)), _ => None };
        match def {
            Definition::Intersection(l1, l2) => {
                let a = line_of(*l1, get)?;
                let b = line_of(*l2, get)?;
                Some(DegenShape::Point(intersection(&a, &b)))
            }
            Definition::LineThroughPoints(p1, p2) => {
                let a = point_of(*p1, get)?;
                let b = point_of(*p2, get)?;
                Some(DegenShape::Line(line_through_points(&a, &b)))
            }
            Definition::Midpoint(p1, p2) => {
                let a = point_of(*p1, get)?;
                let b = point_of(*p2, get)?;
                Some(DegenShape::Point(midpoint(&a, &b)))
            }
            // 🌟 スカラー量。これが評価できないと、長さや複比についての
            // 主張を検出器にも証明の目標にも載せられない。
            Definition::LengthSq(p1, p2) => {
                let a = point_of(*p1, get)?;
                let b = point_of(*p2, get)?;
                Some(DegenShape::Scalar { num: squared_distance(&a, &b)?, den: PInt::one() })
            }
            Definition::Product(s1, s2) => {
                let (n1, d1) = scalar_of(*s1, get)?;
                let (n2, d2) = scalar_of(*s2, get)?;
                Some(DegenShape::Scalar { num: n1.mul(&n2), den: d1.mul(&d2) })
            }
            Definition::CrossRatio(a, b, c, d) => {
                let (pa, pb) = (point_of(*a, get)?, point_of(*b, get)?);
                let (pc, pd) = (point_of(*c, get)?, point_of(*d, get)?);
                let (num, den) = cross_ratio_pair(&pa, &pb, &pc, &pd)?;
                Some(DegenShape::Scalar { num, den })
            }
            Definition::CrossRatioOfLines(a, b, c, d) => {
                // 直線の同次係数(a,b,c)を双対平面の"点"とみなせば、点の複比と同じ計算になる。
                let (la, lb) = (line_of(*a, get)?, line_of(*b, get)?);
                let (lc, ld) = (line_of(*c, get)?, line_of(*d, get)?);
                let (num, den) = cross_ratio_pair(&la, &lb, &lc, &ld)?;
                Some(DegenShape::Scalar { num, den })
            }
            Definition::PerpendicularLine(l, p) => {
                let ll = line_of(*l, get)?;
                let pp = point_of(*p, get)?;
                Some(DegenShape::Line(perpendicular_line(&ll, &pp)))
            }
            Definition::ParallelLine(l, p) => {
                let ll = line_of(*l, get)?;
                let pp = point_of(*p, get)?;
                Some(DegenShape::Line(parallel_line(&ll, &pp)))
            }
            Definition::Circumcircle(a, b, c) => {
                let pa = point_of(*a, get)?;
                let pb = point_of(*b, get)?;
                let pc = point_of(*c, get)?;
                let mid_ab = midpoint(&pa, &pb);
                let mid_ac = midpoint(&pa, &pc);
                let l_ab = line_through_points(&pa, &pb);
                let l_ac = line_through_points(&pa, &pc);
                let pb_ab = perpendicular_line(&l_ab, &mid_ab);
                let pb_ac = perpendicular_line(&l_ac, &mid_ac);
                let center = intersection(&pb_ab, &pb_ac);
                let r_sq = squared_distance(&center, &pa)?;
                Some(DegenShape::Circle { center, r_sq, known: pa })
            }
            Definition::TangentLine(circ, p) => {
                // pは既に円上にある接点(このプロジェクト全体の規約)。接線は半径(中心→p)に垂直でpを通る直線。
                let (center, _r_sq) = circle_of(*circ, get)?;
                let pp = point_of(*p, get)?;
                let radial_line = line_through_points(&center, &pp);
                Some(DegenShape::Line(perpendicular_line(&radial_line, &pp)))
            }
            Definition::HarmonicConjugateOf(a, b, c) => {
                let pa = point_of(*a, get)?;
                let pb = point_of(*b, get)?;
                let pc = point_of(*c, get)?;
                Some(DegenShape::Point(harmonic_conjugate(&pa, &pb, &pc)))
            }
            // 🌟 円と直線の第2交点(一方の交点pが既知)。直線[a,b,c]の方向は(b,-a)なので、second_on_circleの1次の式で解ける。
            Definition::SecondIntersectionOfLineAndConic(p, l, c) => {
                let pp = point_of(*p, get)?;
                let ll = line_of(*l, get)?;
                let (center, _r_sq) = circle_of(*c, get)?;
                second_on_circle(&center, &pp, ll[1], ll[0].neg()).map(DegenShape::Point)
            }
            // 🌟 2円の根軸。
            Definition::RadicalAxis(c1, c2) => {
                let (o1, r1) = circle_of(*c1, get)?;
                let (o2, r2) = circle_of(*c2, get)?;
                radical_axis((&o1, r1), (&o2, r2)).map(DegenShape::Line)
            }
            // 🌟 2円の第2交点。2交点はどちらも根軸上にあるので、根軸と円c1の第2交点として求まる(平方根不要)。
            Definition::SecondIntersectionOfCircles(p, c1, c2) => {
                let pp = point_of(*p, get)?;
                let (o1, r1) = circle_of(*c1, get)?;
                let (o2, r2) = circle_of(*c2, get)?;
                let axis = radical_axis((&o1, r1), (&o2, r2))?;
                second_on_circle(&o1, &pp, axis[1], axis[0].neg()).map(DegenShape::Point)
            }
            // 方向・有向角・一般の二次曲線は未対応(点・直線・円・スカラーが対象)。
            _ => None,
        }
    }
}

impl Placement for DegenCoords {
    fn is_placed(&self, egraph: &EGraph, point: ClassId) -> bool {
        self.free_coords.contains_key(&egraph.get_rep(point))
    }

    fn place_randomly(&mut self, egraph: &EGraph, point: ClassId) {
        let c = (PInt::random_unit(&mut self.rng), PInt::random_unit(&mut self.rng));
        self.free_coords.insert(egraph.get_rep(point), c);
    }

    fn unplace(&mut self, egraph: &EGraph, point: ClassId) {
        self.free_coords.remove(&egraph.get_rep(point));
    }

    fn place_on_two_lines(&mut self, egraph: &EGraph, point: ClassId, l1: &DegenShape, l2: &DegenShape) -> bool {
        let (DegenShape::Line(a), DegenShape::Line(b)) = (l1, l2) else { return false };
        self.set(egraph, point, &intersection(a, b))
    }

    /// 直線l上の点を1つ無作為に取る。lと2本の補助直線とのクロス積でl上の相異なる2点を作り、その射影的な線形結合を
    /// 返す(除算不要)。
    fn place_on_line(&mut self, egraph: &EGraph, point: ClassId, line: &DegenShape) -> bool {
        let DegenShape::Line(l) = line else { return false };
        let aux1: Triple = [PInt::one(), PInt::zero(), PInt::zero()];
        let aux2: Triple = [PInt::zero(), PInt::one(), PInt::zero()];
        let p1 = cross3(l, &aux1);
        let p2 = cross3(l, &aux2);
        let ok = |t: &Triple| !t.iter().all(|x| x.valuation().is_none());
        if !ok(&p1) || !ok(&p2) { return false; }
        let s = PInt::random_unit(&mut self.rng);
        let t = PInt::random_unit(&mut self.rng);
        let on = [
            p1[0].mul(&s).add(&p2[0].mul(&t)),
            p1[1].mul(&s).add(&p2[1].mul(&t)),
            p1[2].mul(&s).add(&p2[2].mul(&t)),
        ];
        self.set(egraph, point, &on)
    }

    fn conic_usable(&self, conic: &DegenShape) -> bool {
        matches!(conic, DegenShape::Circle { .. })
    }

    /// 円周上の点を1つ無作為に取る。円周上の既知点から任意方向へ引いた直線ともう一度交わる点は1次で解ける
    /// (second_on_circle)。既知点は円の値に入っているものを使う。
    fn place_on_conic(&mut self, egraph: &EGraph, point: ClassId, conic: &DegenShape, _known: &DegenShape) -> bool {
        let DegenShape::Circle { center, known, .. } = conic else { return false };
        let dx = PInt::random_unit(&mut self.rng);
        let dy = PInt::random_unit(&mut self.rng);
        match second_on_circle(center, known, dx, dy) {
            Some(t) => self.set(egraph, point, &t),
            None => false,
        }
    }

    fn lies_on(&self, point: &DegenShape, curve: &DegenShape, _curve_type: EntityType) -> bool {
        let DegenShape::Point(p) = point else { return false };
        match curve {
            DegenShape::Line(l) => l[0].mul(&p[0]).add(&l[1].mul(&p[1])).add(&l[2].mul(&p[2])).valuation().is_none(),
            DegenShape::Circle { center, r_sq, .. } => squared_distance(center, p).is_some_and(|d| d.sub(r_sq).valuation().is_none()),
            _ => false,
        }
    }
}

/// 図形の「先頭項」(付値, mod Pでの同次座標3つ組)。Circleはcenterの
/// 先頭項をそのまま使う(半径r_sqの比較はまだ行わない)。
fn leading_order_of(shape: &DegenShape) -> Option<(EntityType, usize, [i64; 3])> {
    match shape {
        DegenShape::Point(t) => padic::leading_order(t).map(|(v, l)| (EntityType::Point, v, l)),
        DegenShape::Line(t) => padic::leading_order(t).map(|(v, l)| (EntityType::Line, v, l)),
        DegenShape::Circle { center, .. } => padic::leading_order(center).map(|(v, l)| (EntityType::Conic, v, l)),
        // num/den を [num, den, 0] という同次座標とみなせば、射影的に等しい
        // = num1*den2 == num2*den1 で、そのまま既存の比較に載る。
        DegenShape::Scalar { num, den } =>
            padic::leading_order(&[*num, *den, PInt::zero()]).map(|(v, l)| (EntityType::Scalar, v, l)),
    }
}

/// 共線な4点(あるいは共点な4直線)の複比を num/den の形で返す。
///
/// 同次座標のまま2x2行列式で組み立てるので、割り算も平方根も要らず、
/// 無限遠点(z=0)が混ざっていてもそのまま扱える――これは重要で、
/// 「線分の比 AX:XB」は「A,B,X とその直線の無限遠点の複比」に他ならないため、
/// 比についての古典的な主張(メネラウス・チェバ)をこの語彙で表せる。
fn cross_ratio_pair(a: &Triple, b: &Triple, c: &Triple, d: &Triple) -> Option<(PInt, PInt)> {
    // 3つの座標から2つを選んで2x2行列式を作る。直線の向きによっては
    // ある組み合わせが全部0になるので、意味のある組が出るまで順に試す。
    for (i, k) in [(0usize, 2usize), (1usize, 2usize), (0usize, 1usize)] {
        let det = |p: &Triple, q: &Triple| p[i].mul(&q[k]).sub(&p[k].mul(&q[i]));
        let num = det(a, c).mul(&det(b, d));
        let den = det(a, d).mul(&det(b, c));
        if num.valuation().is_some() || den.valuation().is_some() {
            return Some((num, den));
        }
    }
    None
}

/// 2つのスカラー(比の形)が射影的に等しいか。
fn scalars_equal(x: (PInt, PInt), y: (PInt, PInt)) -> bool {
    let (n1, d1) = x;
    let (n2, d2) = y;
    // 0/0 は比較する意味が無い。
    if n1.valuation().is_none() && d1.valuation().is_none() { return false; }
    if n2.valuation().is_none() && d2.valuation().is_none() { return false; }
    n1.mul(&d2) == n2.mul(&d1)
}

// ============================================================
// 🌟 スカラーの検出器
// 接続幾何(一致・共線・共点・共円・接続)の検出器だけでは、長さや複比の主張は発見できない。量は長さそのものではなく
// 長さの二乗と複比で測る。前者は平方根が要らず有限体上の多項式になり、後者は無限遠点を4点目に取ることで比の情報を
// 射影的に運べる(cross_ratio_pair 参照)。
// ============================================================

/// 2つの線分の長さの二乗が、独立な乱数すべてで等しい組を探す。
///
/// 返すのは [A, B, C, D] で「|AB|² = |CD|²」の意味。同じ2点の組や、
/// 4点が2点しか使っていないものは除く。
/// 🌟 2つの線分の長さの二乗が、e-graph上で既に同じ同値類に
/// 入っているか(= 発見するまでもなく既知か)。
///
/// LengthSq は遼延生成なので、まだ実体が無い場合は「既知ではない」とする
/// (検出器は読み取り専用なので、ここで新しく作りはしない)。
fn lengths_already_known_equal(egraph: &EGraph, a: ClassId, b: ClassId, c: ClassId, d: ClassId) -> bool {
    let l1 = egraph.normalize_definition(&crate::mmp_core::Definition::LengthSq(a, b));
    let l2 = egraph.normalize_definition(&crate::mmp_core::Definition::LengthSq(c, d));
    match (egraph.memo.get(&l1), egraph.memo.get(&l2)) {
        (Some(&x), Some(&y)) => egraph.get_rep(x) == egraph.get_rep(y),
        _ => false,
    }
}

pub fn find_generic_equal_lengths(egraph: &EGraph, seeds: &[u64], max_points: usize)
    -> Vec<[ClassId; 4]>
{
    if seeds.is_empty() { return Vec::new(); }
    let ids = hot_reps_of_type(egraph, EntityType::Point, max_points, true);
    if ids.len() < 3 { return Vec::new(); }

    // 点の組を固定の順序で並べておく(どのseedでも同じ添字を指すように)。
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    for i in 0..ids.len() {
        for j in (i + 1)..ids.len() { pairs.push((i, j)); }
    }

    let mut candidates: Option<std::collections::HashSet<(usize, usize)>> = None;
    for &seed in seeds {
        let mut ev = DegenEvaluator::new(egraph, seed, None);
        let coords: Vec<Option<Triple>> = ids.iter()
            .map(|&id| match ev.eval(id) { Some(DegenShape::Point(t)) => Some(t), _ => None })
            .collect();
        // 長さの二乗でバケツ分けすると、総当たり(組の組)を避けられる。
        let mut buckets: FxHashMap<PInt, Vec<usize>> = FxHashMap::default();
        for (k, &(i, j)) in pairs.iter().enumerate() {
            let (a, b) = match (&coords[i], &coords[j]) { (Some(a), Some(b)) => (a, b), _ => continue };
            let d = match squared_distance(a, b) { Some(d) => d, None => continue };
            // 長さ0(同じ点)は比べる意味が無い。
            if d.valuation().is_none() { continue; }
            buckets.entry(d).or_default().push(k);
        }
        // 🌟 平行で長さも等しい2線分は、端点を共有していない限り
        // 「片方をずらしたもの」=平行四辺形の言い換えにしかならない。
        // 自由作図は中点や平行線を大量に作るのでこれが山ほど出てしまい、
        // 他の種類の発見を押し流す。数値の向きで判定して落とす。
        let parallel = |k1: usize, k2: usize| -> bool {
            let ((i1, j1), (i2, j2)) = (pairs[k1], pairs[k2]);
            if i1 == i2 || i1 == j2 || j1 == i2 || j1 == j2 { return false; }  // 端点を共有
            let get = |i: usize, j: usize| -> Option<(PInt, PInt)> {
                let (a, b) = (coords[i].as_ref()?, coords[j].as_ref()?);
                let (ax, ay) = affine_xy(a)?;
                let (bx, by) = affine_xy(b)?;
                Some((bx.sub(&ax), by.sub(&ay)))
            };
            match (get(i1, j1), get(i2, j2)) {
                (Some((dx1, dy1)), Some((dx2, dy2))) =>
                    dx1.mul(&dy2).sub(&dy1.mul(&dx2)).valuation().is_none(),
                _ => false,
            }
        };
        let mut here: std::collections::HashSet<(usize, usize)> = std::collections::HashSet::new();
        for (_, group) in buckets {
            // 同じ長さの組が多すぎるのは退化(全部同じ点に潰れている等)の兆候。
            if group.len() > 12 { continue; }
            for x in 0..group.len() {
                for y in (x + 1)..group.len() {
                    if parallel(group[x], group[y]) { continue; }
                    here.insert((group[x], group[y]));
                }
            }
        }
        candidates = Some(match candidates {
            None => here,
            Some(prev) => prev.intersection(&here).copied().collect(),
        });
        if candidates.as_ref().map_or(true, |c| c.is_empty()) { return Vec::new(); }
    }

    let mut out: Vec<[ClassId; 4]> = Vec::new();
    for (k1, k2) in candidates.unwrap_or_default() {
        let (i1, j1) = pairs[k1];
        let (i2, j2) = pairs[k2];
        // 使っている点が2つしかない(= 同じ線分)ものは除く。
        let mut used = vec![i1, j1, i2, j2];
        used.sort_unstable();
        used.dedup();
        if used.len() < 3 { continue; }
        // 両方の LengthSq が既に同じ同値類にいるなら既知なので報告しない(共線・共円の検出器と同じく「構造的にまだ知られて
        // いない」ものだけを出す。落とさないと中点のたびに AM = MB を発見し直す)。
        if lengths_already_known_equal(egraph, ids[i1], ids[j1], ids[i2], ids[j2]) { continue; }
        out.push([ids[i1], ids[j1], ids[i2], ids[j2]]);
    }
    out.sort_by_key(|q| (q[0].0, q[1].0, q[2].0, q[3].0));
    out
}

/// 複比が等しい2つの4点組を探す。
///
/// 複比が意味を持つのは4点が共線のときだけなので、候補は「構造的に同じ
/// 直線に乗っていると分かっている点」から作る。同じ直線上の4点組どうしの
/// 一致は複比の定義から自明なことが多いので、異なる直線に乗る組どうしだけを
/// 報告する(これが射影変換で移り合う配置=透視・射影の主張になる)。
pub fn find_generic_equal_cross_ratios(egraph: &EGraph, seeds: &[u64], max_lines: usize)
    -> Vec<[ClassId; 8]>
{
    if seeds.is_empty() { return Vec::new(); }
    let lines = hot_reps_of_type(egraph, EntityType::Line, max_lines, false);

    // 各直線について、その上の点を熱の順に少数だけ取り、4点組を作る。
    let mut quads: Vec<(ClassId, [ClassId; 4])> = Vec::new();
    for &l in &lines {
        if egraph.get_rep(l) == egraph.line_infinity { continue; }
        let mut pts: Vec<ClassId> = egraph.entities[egraph.get_rep(l).0].components.first()
            .map(|c| c.subobjects.clone()).unwrap_or_default()
            .into_iter()
            .map(|p| egraph.get_rep(p))
            .filter(|&p| egraph.entities[p.0].entity_type == EntityType::Point)
            .filter(|&p| !egraph.is_connected(p, egraph.line_infinity))
            .collect();
        pts.sort_unstable_by_key(|id| id.0);
        pts.dedup();
        if pts.len() < 4 { continue; }
        // 組み合わせ爆発を避けるため、熱の高い上位6点までに絞る。
        pts.sort_by(|&a, &b| egraph.entities[b.0].heat_with_degree()
            .partial_cmp(&egraph.entities[a.0].heat_with_degree()).unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| a.0.cmp(&b.0)));
        pts.truncate(6);
        pts.sort_unstable_by_key(|id| id.0);
        for a in 0..pts.len() { for b in (a+1)..pts.len() {
            for c in (b+1)..pts.len() { for d in (c+1)..pts.len() {
                quads.push((l, [pts[a], pts[b], pts[c], pts[d]]));
            }}
        }}
    }
    if quads.len() < 2 { return Vec::new(); }

    let mut candidates: Option<std::collections::HashSet<(usize, usize)>> = None;
    for &seed in seeds {
        let mut ev = DegenEvaluator::new(egraph, seed, None);
        let values: Vec<Option<(PInt, PInt)>> = quads.iter().map(|(_, q)| {
            let pts: Option<Vec<Triple>> = q.iter().map(|&id| match ev.eval(id) {
                Some(DegenShape::Point(t)) => Some(t), _ => None }).collect();
            let pts = pts?;
            cross_ratio_pair(&pts[0], &pts[1], &pts[2], &pts[3])
        }).collect();
        let mut here: std::collections::HashSet<(usize, usize)> = std::collections::HashSet::new();
        for x in 0..quads.len() {
            let vx = match values[x] { Some(v) => v, None => continue };
            for y in (x + 1)..quads.len() {
                if quads[x].0 == quads[y].0 { continue; }   // 同じ直線どうしは自明
                let vy = match values[y] { Some(v) => v, None => continue };
                if scalars_equal(vx, vy) { here.insert((x, y)); }
            }
        }
        candidates = Some(match candidates {
            None => here,
            Some(prev) => prev.intersection(&here).copied().collect(),
        });
        if candidates.as_ref().map_or(true, |c| c.is_empty()) { return Vec::new(); }
    }

    let mut out: Vec<[ClassId; 8]> = Vec::new();
    for (x, y) in candidates.unwrap_or_default() {
        let (a, b) = (quads[x].1, quads[y].1);
        // 2つの4点組が3点以上を共有しているなら、複比の一致はほぼ言い換え。
        let mut shared = 0;
        for p in a.iter() { if b.contains(p) { shared += 1; } }
        if shared >= 3 { continue; }
        out.push([a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]]);
    }
    out.sort_by_key(|q| (q[0].0, q[1].0, q[2].0, q[3].0, q[4].0));
    out
}

/// 与えられたmerge_pair(Noneなら退化させない一般乱数)のもとで、egraph内の
/// 全エンティティを評価し、射影的に一致する(ClassId, ClassId)の組を集める
/// (a.0 < b.0で正規化、名前解決やヒートボーナスへの反映は呼び出し側の仕事)。
pub fn find_coincidences(egraph: &EGraph, seed: u64, merge_pair: Option<(ClassId, ClassId)>) -> Vec<(ClassId, ClassId)> {
    let mut ev = DegenEvaluator::new(egraph, seed, merge_pair);
    let n = egraph.entities.len();
    let mut leading: Vec<Option<(EntityType, usize, [i64; 3])>> = Vec::with_capacity(n);
    for i in 0..n {
        let id = ClassId(i);
        if egraph.get_rep(id) != id { leading.push(None); continue; } // 代表元だけ評価すれば十分
        let shape = ev.eval(id);
        leading.push(shape.as_ref().and_then(leading_order_of));
    }
    let mut result = Vec::new();
    for i in 0..n {
        let (ty_i, _vi, li) = match &leading[i] { Some(x) => x, None => continue };
        for j in (i + 1)..n {
            let (ty_j, _vj, lj) = match &leading[j] { Some(x) => x, None => continue };
            if ty_i != ty_j { continue; }
            if projectively_equal_mod_p(*li, *lj) {
                result.push((ClassId(i), ClassId(j)));
            }
        }
    }
    result
}

/// find_coincidencesの結果から、一般乱数(退化なし)でも成り立つ「常に真」
/// の一致(discover.rsが既に別の仕組みで見つけられるもの)を除いた、
/// この退化に固有の一致だけを返す。
pub fn find_degeneration_specific_coincidences(
    egraph: &EGraph,
    seed: u64,
    merge_pair: (ClassId, ClassId),
) -> Vec<(ClassId, ClassId)> {
    let baseline: std::collections::HashSet<(ClassId, ClassId)> =
        find_coincidences(egraph, seed ^ 0xA5A5_A5A5_A5A5_A5A5u64, None).into_iter().collect();
    find_coincidences(egraph, seed, Some(merge_pair))
        .into_iter()
        .filter(|pair| !baseline.contains(pair))
        .collect()
}

// ============================================================
// 🌟 退化のもとで直接観測された関連(「Xを退化させたらYと一致した」)を、推移閉包を取らずに隣接グラフとして持つ。
// bump_heat_bonus が同じグループの実体にボーナスを伝播するのに使う。異なる退化パターンで見つかった関係は互いに
// 両立しない別々の極限の話なので、union-find で推移的に合併すると全実体が1つのグループに潰れ、熱の差が消える。
// ============================================================

#[derive(Clone, Debug, Default)]
pub struct DegenerationRelations {
    edges: FxHashMap<usize, Vec<usize>>,
}

impl DegenerationRelations {
    pub fn new() -> Self { Self { edges: FxHashMap::default() } }

    /// aとbが(何らかの退化のもとで)直接一致することが観測された、という
    /// 事実を記録する。推移閉包は取らない(a-b, b-cが記録されていても
    /// aとcが自動的に関連づくことはない――上のドキュメント参照)。
    pub fn add_observed_relation(&mut self, a: ClassId, b: ClassId) {
        if a == b { return; }
        self.edges.entry(a.0).or_default().push(b.0);
        self.edges.entry(b.0).or_default().push(a.0);
    }

    /// aと直接関連が観測された他の実体(1ホップのみ)。関連が一度も
    /// 観測されていないエンティティに対してはO(1)で空を返す。
    pub fn members_of(&self, a: ClassId) -> Vec<ClassId> {
        self.edges.get(&a.0).map(|v| v.iter().copied().map(ClassId).collect()).unwrap_or_default()
    }

    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool { self.edges.is_empty() }
}

/// 与えられたegraphの全自由点ペアについて退化固有の一致を走査し、
/// 複数回の独立な乱数drawで再現した組だけをDegenerationRelationsへ記録する
/// (推移閉包は取らない、直接観測された辺のみ)。discover_degenerate.rs::
/// runと同じロジックだが、CLI表示ではなくEGraphに直接取り込むための版。
pub fn compute_degeneration_groups(egraph: &EGraph, seed: u64, min_hits: u32) -> DegenerationRelations {
    let trials = min_hits.max(2);
    // 全実体を見て、FreePoint として作られたものの代表元を集める(マージが進むと自由点は代表元でなくなるのが普通なので、
    // 「代表元かつ original_definition が FreePoint」では拾えない)。
    let mut free_points = Vec::new();
    let mut seen: std::collections::HashSet<ClassId> = std::collections::HashSet::new();
    for i in 0..egraph.entities.len() {
        let e = &egraph.entities[i];
        if e.entity_type != EntityType::Point { continue; }
        if !matches!(e.original_definition, Definition::FreePoint) { continue; }
        let rep = egraph.get_rep(ClassId(i));
        if seen.insert(rep) { free_points.push(rep); }
    }
    let mut relations = DegenerationRelations::new();
    for i in 0..free_points.len() {
        for j in (i + 1)..free_points.len() {
            let mut counts: FxHashMap<(ClassId, ClassId), u32> = FxHashMap::default();
            for t in 0..trials {
                let hits = find_degeneration_specific_coincidences(
                    egraph, seed.wrapping_add(t as u64 * 7919), (free_points[i], free_points[j]));
                for pair in hits { *counts.entry(pair).or_insert(0) += 1; }
            }
            for ((x, y), c) in counts {
                if c >= min_hits { relations.add_observed_relation(x, y); }
            }
        }
    }
    relations
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::padic::PInt as TPInt;

    fn pi(v: i64) -> TPInt { TPInt::from_i64_mod_p(v) }

    /// 🌟 det4(4x4行列式の余因子展開)の符号と大きさを、手計算できる
    /// 行列で検証する。共円判定の土台なので、符号を1つ間違えるだけで
    /// 「偽の発見」を静かに量産してしまう。
    #[test]
    fn det4_matches_hand_computed_values() {
        let diag = [
            [pi(1), pi(0), pi(0), pi(0)],
            [pi(0), pi(2), pi(0), pi(0)],
            [pi(0), pi(0), pi(3), pi(0)],
            [pi(0), pi(0), pi(0), pi(4)],
        ];
        assert_eq!(det4(&diag), pi(24), "対角行列の行列式は積(24)であるべき");

        // 1行目と2行目を入れ替えた単位行列 -> 行列式は -1
        let swap = [
            [pi(0), pi(1), pi(0), pi(0)],
            [pi(1), pi(0), pi(0), pi(0)],
            [pi(0), pi(0), pi(1), pi(0)],
            [pi(0), pi(0), pi(0), pi(1)],
        ];
        assert_eq!(det4(&swap), pi(-1), "1回の行入替で符号が反転するべき");

        // 同じ行が2つあれば行列式は0
        let dup = [
            [pi(3), pi(1), pi(4), pi(1)],
            [pi(5), pi(9), pi(2), pi(6)],
            [pi(3), pi(1), pi(4), pi(1)],
            [pi(2), pi(7), pi(1), pi(8)],
        ];
        assert_eq!(det4(&dup), pi(0), "重複行があれば行列式は0であるべき");
    }

    /// 🌟 共円判定そのものの検証。円の有理パラメータ表示
    /// (cx + r(1-t²)/(1+t²), cy + 2rt/(1+t²)) を使って厳密に円上の4点を作り、
    /// 判定式が0になること・円から外した5点目では0にならないことを確認する。
    #[test]
    fn concyclic_determinant_vanishes_exactly_on_a_circle() {
        let (cx, cy, r) = (pi(11), pi(7), pi(5));
        let on_circle = |t: i64| -> [TPInt; 4] {
            let t = pi(t);
            let one = TPInt::one();
            let denom = one.add(&t.mul(&t));           // 1+t²
            let inv = denom.unit_inverse();
            let x = cx.add(&r.mul(&one.sub(&t.mul(&t))).mul(&inv));
            let y = cy.add(&r.mul(&pi(2)).mul(&t).mul(&inv));
            let z = TPInt::one();
            [x.mul(&x).add(&y.mul(&y)), x.mul(&z), y.mul(&z), z.mul(&z)]
        };
        let rows = [on_circle(1), on_circle(2), on_circle(3), on_circle(4)];
        assert_eq!(det4(&rows), pi(0), "厳密に同一円周上の4点では判定式が消えるべき");

        // 5点目を円から外す(半径をずらす)と消えないはず。
        let off = {
            let x = cx.add(&r.add(&TPInt::one()));  // 中心から r+1 離れた点
            let y = cy;
            let z = TPInt::one();
            [x.mul(&x).add(&y.mul(&y)), x.mul(&z), y.mul(&z), z.mul(&z)]
        };
        let rows_off = [on_circle(1), on_circle(2), on_circle(3), off];
        assert_ne!(det4(&rows_off), pi(0), "円から外れた点を混ぜれば判定式は0でないべき");
    }

    use crate::mmp_core::EGraph;

    /// 🌟 三角形A,B,C+外心O+垂心Hという配置で、B,Cを退化させたときに
    /// 何らかの新しい一致が実際に検出できることを確認する(具体的に何が
    /// 見つかるかは乱数drawに依存するので、ここでは「パイプライン全体が
    /// クラッシュせず、Point/Line/Circleを一通り評価できる」ことと
    /// 「一般乱数のベースラインより退化後の一致数が減らない」ことだけを
    /// 確認する最小限のスモークテスト)。
    #[test]
    fn find_coincidences_runs_end_to_end_on_a_real_configuration() {
        let mut egraph = EGraph::new();
        let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
        let bc = egraph.create_entity("BC".into(), Definition::new_line(b, c), EntityType::Line);
        let ca = egraph.create_entity("CA".into(), Definition::new_line(c, a), EntityType::Line);
        let alt_a = egraph.create_entity("Alt_A".into(), Definition::PerpendicularLine(bc, a), EntityType::Line);
        let alt_b = egraph.create_entity("Alt_B".into(), Definition::PerpendicularLine(ca, b), EntityType::Line);
        let _h = egraph.create_entity("H".into(), Definition::Intersection(alt_a, alt_b), EntityType::Point);
        let _o = crate::problems::geo_helpers::circumcenter(&mut egraph, a, b, c, "O");
        let _circ = egraph.create_entity("Circ".into(), Definition::Circumcircle(a, b, c), EntityType::Conic);

        let generic = find_coincidences(&egraph, 1, None);
        // 一般乱数では偶然の一致はまず起きないはず(自明な自己反射以外)。
        assert!(generic.is_empty(), "一般乱数で偶然の一致が出た(乱数drawが悪いか、実装にバグがある可能性): {:?}", generic);

        let specific = find_degeneration_specific_coincidences(&egraph, 2, (b, c));
        // 退化特有の一致は必ずしも何か見つかるとは限らないが(この配置と
        // 退化パターン次第)、少なくともクラッシュせず実行できることを
        // 確認する。
        println!("B≡C退化で見つかった一致: {} 件", specific.len());
        for (x, y) in &specific {
            println!("  {} ≡ {}", egraph.entities[x.0].name, egraph.entities[y.0].name);
        }
    }

    /// 🌟 接続検出器(find_generic_point_on_curve)が実際に働くことの検証。
    /// 垂心H = Alt_A ∩ Alt_B は、3本目の高さAlt_C(=ABへのCからの垂線)の
    /// 上にもある。Alt_CはPerpendicularLineなので「2点で定義された直線」
    /// ではなく、共線性検出では表現できない ―― まさにこの検出器の担当。
    #[test]
    fn point_on_curve_detector_finds_the_third_altitude() {
        let mut egraph = EGraph::new();
        let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
        let bc = egraph.create_entity("BC".into(), Definition::new_line(b, c), EntityType::Line);
        let ca = egraph.create_entity("CA".into(), Definition::new_line(c, a), EntityType::Line);
        let ab = egraph.create_entity("AB".into(), Definition::new_line(a, b), EntityType::Line);
        let alt_a = egraph.create_entity("Alt_A".into(), Definition::PerpendicularLine(bc, a), EntityType::Line);
        let alt_b = egraph.create_entity("Alt_B".into(), Definition::PerpendicularLine(ca, b), EntityType::Line);
        let alt_c = egraph.create_entity("Alt_C".into(), Definition::PerpendicularLine(ab, c), EntityType::Line);
        let h = egraph.create_entity("H".into(), Definition::Intersection(alt_a, alt_b), EntityType::Point);
        let (h, alt_c) = (egraph.get_rep(h), egraph.get_rep(alt_c));

        let seeds = [0xC0FFEE_u64, 0xBEEF77, 0x1234ABCD];
        let found = find_generic_point_on_curve(&egraph, &seeds, 40, 40);
        assert!(found.iter().any(|&(p, l)| p == h && l == alt_c),
            "垂心が3本目の高さの上にあることを検出できるべき: {:?}", found);
    }

    /// 🌟 円関連の作図(根軸・2円の第2交点・円と直線の第2交点)がp進評価器
    /// 側でも正しく計算できることの検証。検出パイプライン(find_coincidences)
    /// はこちらの評価器を使うので、mmp_core側だけ正しくてもここが間違って
    /// いると発見報告が丸ごと嘘になる。
    ///
    /// 共通点A,Bを持つ2円について、
    ///   根軸 ≡ 直線AB、  2円の第2交点(既知=A) ≡ B
    /// が任意の(一般の)座標で成り立つはずなので、一般乱数の一致検出に
    /// この2件がそのまま現れることを確認する。
    #[test]
    fn circle_constructions_are_consistent_under_padic_evaluation() {
        let mut egraph = EGraph::new();
        let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
        let d = egraph.create_entity("D".into(), Definition::FreePoint, EntityType::Point);
        let circ1 = egraph.create_entity("Circ1".into(), Definition::Circumcircle(a, b, c), EntityType::Conic);
        let circ2 = egraph.create_entity("Circ2".into(), Definition::Circumcircle(a, b, d), EntityType::Conic);
        let axis = egraph.create_entity("Axis".into(), Definition::RadicalAxis(circ1, circ2), EntityType::Line);
        let second = egraph.create_entity("Second".into(),
            Definition::SecondIntersectionOfCircles(a, circ1, circ2), EntityType::Point);
        let line_ab = egraph.create_entity("LineAB".into(), Definition::new_line(a, b), EntityType::Line);

        let (axis, second, line_ab, b) = (egraph.get_rep(axis), egraph.get_rep(second), egraph.get_rep(line_ab), egraph.get_rep(b));
        let found = find_coincidences(&egraph, 0xC17C1E ^ 0x5EED, None);
        let has = |x: ClassId, y: ClassId| found.iter().any(|&(p, q)| (p == x && q == y) || (p == y && q == x));
        assert!(has(axis, line_ab), "2点A,Bを共有する2円の根軸は直線ABと一致するべき: {:?}", found);
        assert!(has(second, b), "Aを既知の交点とした2円の第2交点はBと一致するべき: {:?}", found);
    }
}

// ============================================================
// 🌟 総当たりの一致検出。e-graph 上の全ての実体を独立な乱数座標で評価し、同じ型の全ペアを比べる。独立な乱数で
// 一致する偶然の確率は約1/998244353なので、複数の seed で再現すれば実在する関係とみなせる。「独立に作った2つの図形が
// 一致した」(共点性・共線性・円の一致など)という本命の発見は、作図が0/0に退化したときにしか発火しない
// log_conjecture_candidate では拾えない。
// ============================================================

/// 複数の独立な乱数drawの全てで射影的に一致した、まだ記号的には統合されて
/// いない同型の実体ペアを返す(退化(全成分ゼロ)は除外済み)。
pub fn find_generic_coincidences(egraph: &EGraph, seeds: &[u64]) -> Vec<(ClassId, ClassId)> {
    if seeds.is_empty() { return Vec::new(); }
    let mut counts: FxHashMap<(ClassId, ClassId), u32> = FxHashMap::default();
    for &s in seeds {
        for pair in find_coincidences(egraph, s, None) {
            *counts.entry(pair).or_insert(0) += 1;
        }
    }
    let need = seeds.len() as u32;
    let mut out: Vec<(ClassId, ClassId)> = counts.into_iter()
        .filter(|&(_, c)| c == need)
        .map(|(p, _)| p)
        .filter(|&(a, b)| egraph.get_rep(a) != egraph.get_rep(b))
        .collect();
    out.sort_by_key(|&(a, b)| (a.0, b.0));
    out
}

/// 3点が(複数の独立な乱数drawで)共線であることを検出する。共点性
/// (3直線が1点で交わる)は上のfind_generic_coincidencesが
/// Intersection同士の一致として自然に拾うが、共線性は「その3点を通る
/// 直線」が実体として作られていないと拾えないため、点の三つ組を直接
/// 判定する専用の検査を用意する(オイラー線のような古典的な発見は
/// まさにこの形をしている)。
///
/// 候補が組み合わせ爆発しないよう、対象は「熱量(heat_with_degree)が
/// 高い上位max_points個の有限点」に絞る。
pub fn find_generic_collinear_triples(egraph: &EGraph, seeds: &[u64], max_points: usize) -> Vec<(ClassId, ClassId, ClassId)> {
    if seeds.is_empty() { return Vec::new(); }
    // 有限点(無限遠点=方向は共線判定の対象にしない)を集める。
    let ids = hot_reps_of_type(egraph, EntityType::Point, max_points, true);

    let mut counts: FxHashMap<(ClassId, ClassId, ClassId), u32> = FxHashMap::default();
    for &s in seeds {
        let mut ev = DegenEvaluator::new(egraph, s, None);
        let coords: Vec<Option<Triple>> = ids.iter()
            .map(|&id| match ev.eval(id) { Some(DegenShape::Point(t)) => Some(t), _ => None })
            .collect();
        if crate::cli::sweep_debug() {
            let ok = coords.iter().filter(|c| c.is_some()).count();
            let bad: Vec<String> = ids.iter().zip(coords.iter()).filter(|(_, c)| c.is_none())
                .map(|(&id, _)| egraph.entities[id.0].name.chars().take(24).collect()).collect();
            eprintln!("  [sweep-debug] 共線判定: 評価成功{}/{} 失敗: {:?}", ok, ids.len(), bad);
        }
        for i in 0..ids.len() {
            let Some(pi) = coords[i] else { continue };
            for j in (i + 1)..ids.len() {
                let Some(pj) = coords[j] else { continue };
                // 退化(2点が一致)は除外する。
                let line_ij = cross3(&pi, &pj);
                if line_ij.iter().all(|x| x.valuation().is_none()) { continue; }
                for k in (j + 1)..ids.len() {
                    let Some(pk) = coords[k] else { continue };
                    // 3つ目が先の2点のどちらかと同一なら、共線は自明に成り立つ
                    // だけで内容が無い(projectively_sameのドキュメント参照)。
                    if projectively_same(&pk, &pi) || projectively_same(&pk, &pj) { continue; }
                    // 3点が共線 <=> 行列式(=同次座標の三重積)が0。
                    let dot = line_ij[0].mul(&pk[0]).add(&line_ij[1].mul(&pk[1])).add(&line_ij[2].mul(&pk[2]));
                    if dot.valuation().is_none() {
                        *counts.entry((ids[i], ids[j], ids[k])).or_insert(0) += 1;
                    }
                }
            }
        }
    }
    let need = seeds.len() as u32;
    let mut out: Vec<(ClassId, ClassId, ClassId)> = counts.into_iter()
        .filter(|&(_, c)| c == need)
        .map(|(t, _)| t)
        .collect();
    out.sort_by_key(|&(a, b, c)| (a.0, b.0, c.0));
    out
}

/// 検査対象の max_items 個の実体(ty で指定した型)を集める共通処理。
/// 問題・定理由来の本物の実体(base_importance>=1.0)を常に優先し、余った枠だけを MCTS 由来の実体で熱量順に埋める
/// (純粋な熱量順だと、MCTS の足場が熱ボーナスで上位を占め、外心・垂心のような古典的な点が押し出される)。
fn hot_reps_of_type(egraph: &EGraph, ty: EntityType, max_items: usize, finite_points_only: bool) -> Vec<ClassId> {
    let mut v: Vec<(ClassId, bool, f64)> = (0..egraph.entities.len())
        .map(ClassId)
        .filter(|&id| egraph.get_rep(id) == id
            && egraph.entities[id.0].entity_type == ty
            && egraph.entities[id.0].is_active()
            && id != egraph.line_infinity
            && !(finite_points_only && egraph.is_connected(id, egraph.line_infinity)))
        .map(|id| (id, egraph.entities[id.0].base_importance >= 1.0, egraph.entities[id.0].heat_with_degree()))
        .collect();
    // 本物の実体(true)が先、その中では熱量の降順。
    v.sort_by(|a, b| b.1.cmp(&a.1).then(b.2.partial_cmp(&a.2).unwrap_or(std::cmp::Ordering::Equal)));
    v.truncate(max_items);
    let out: Vec<ClassId> = v.into_iter().map(|(id, _, _)| id).collect();
    if crate::cli::sweep_debug() {
        let names: Vec<String> = out.iter().map(|&id| egraph.entities[id.0].name.chars().take(28).collect()).collect();
        eprintln!("  [sweep-debug] {:?} 候補{}件: {:?}", ty, names.len(), names);
    }
    out
}

/// 3直線が1点で交わる(共点)ことの検出。3点の共線性と完全に双対で、
/// 同次座標の三重積(=3x3行列式)が消えるかどうかで判定できる
/// (「3本の高さは1点で交わる」のような古典的な結論がまさにこの形)。
/// 交点が実体として作られていなくても検出できるのが利点。
pub fn find_generic_concurrent_lines(egraph: &EGraph, seeds: &[u64], max_lines: usize) -> Vec<(ClassId, ClassId, ClassId)> {
    if seeds.is_empty() { return Vec::new(); }
    let ids = hot_reps_of_type(egraph, EntityType::Line, max_lines, false);
    let mut counts: FxHashMap<(ClassId, ClassId, ClassId), u32> = FxHashMap::default();
    for &s in seeds {
        let mut ev = DegenEvaluator::new(egraph, s, None);
        let coords: Vec<Option<Triple>> = ids.iter()
            .map(|&id| match ev.eval(id) { Some(DegenShape::Line(t)) => Some(t), _ => None })
            .collect();

        for i in 0..ids.len() {
            let Some(li) = coords[i] else { continue };
            for j in (i + 1)..ids.len() {
                let Some(lj) = coords[j] else { continue };
                let meet = cross3(&li, &lj);
                // 2直線が数値的に同一(交点が定義不能)なら共点性を問う意味がない。
                if meet.iter().all(|x| x.valuation().is_none()) { continue; }
                // 交点が無限遠(z=0)、つまり3直線が平行なだけの場合も行列式は0になるので、有限の共有点だけを共点として扱う。
                if meet[2].valuation().is_none() { continue; }
                for k in (j + 1)..ids.len() {
                    let Some(lk) = coords[k] else { continue };
                    // 3本目が先の2本のどちらかと同一の直線なら、共点は自明。
                    // (i,jが同一のケースはmeetが消えることで既に弾かれているが、
                    // kが重複するケースはここまで素通りしていた。)
                    if projectively_same(&lk, &li) || projectively_same(&lk, &lj) { continue; }
                    let dot = meet[0].mul(&lk[0]).add(&meet[1].mul(&lk[1])).add(&meet[2].mul(&lk[2]));
                    if dot.valuation().is_none() {
                        *counts.entry((ids[i], ids[j], ids[k])).or_insert(0) += 1;
                    }
                }
            }
        }
    }
    let need = seeds.len() as u32;
    let mut out: Vec<_> = counts.into_iter().filter(|&(_, c)| c == need).map(|(t, _)| t).collect();
    out.sort_by_key(|&(a, b, c)| (a.0, b.0, c.0));
    out
}

/// 🌟 「点Pが直線L上にある」「点Pが円C上にある」という接続そのものを総当たりで探す検出器。共線性検出(3点の形)では
/// 垂線・接線・根軸のような2点で定義されていない直線への接続を言えず、共円性検出(名前の無い円に4点)では「外接円の
/// 上に由来の全く違う点が乗る」(垂心のBCに関する対称点など)を自然な形で言えない。
/// 構造的に既知の接続(is_connected)は除く。LineThroughPoints で定義された直線は共線性検出が報告するので扱わない。
pub fn find_generic_point_on_curve(egraph: &EGraph, seeds: &[u64], max_points: usize, max_curves: usize)
    -> Vec<(ClassId, ClassId)>
{
    if seeds.is_empty() { return Vec::new(); }
    let pts = hot_reps_of_type(egraph, EntityType::Point, max_points, true);
    let mut curves = hot_reps_of_type(egraph, EntityType::Line, max_curves, false);
    curves.retain(|&l| !matches!(egraph.entities[l.0].original_definition, Definition::LineThroughPoints(_, _)));
    curves.extend(hot_reps_of_type(egraph, EntityType::Conic, max_curves, false));

    let mut counts: FxHashMap<(ClassId, ClassId), u32> = FxHashMap::default();
    for &s in seeds {
        let mut ev = DegenEvaluator::new(egraph, s, None);
        let pcoords: Vec<Option<Triple>> = pts.iter()
            .map(|&id| match ev.eval(id) { Some(DegenShape::Point(t)) => Some(t), _ => None }).collect();
        let ccoords: Vec<Option<DegenShape>> = curves.iter().map(|&id| ev.eval(id)).collect();
        for (ci, &c) in curves.iter().enumerate() {
            let Some(shape) = &ccoords[ci] else { continue };
            for (pi, &p) in pts.iter().enumerate() {
                if egraph.is_connected(p, c) { continue; }
                let Some(pt) = pcoords[pi] else { continue };
                // 無限遠点(z=0)はどの平行な直線にも乗るので、接続の中身が平行性の言い換えになる。構造的に L∞ に接続されていない
                // 無限遠点も残るので、数値の z 成分で落とす。
                if pt[2].valuation().is_none() { continue; }
                let on = match shape {
                    DegenShape::Line(l) => {
                        // 直線が退化(全成分0)していれば判定に意味が無い。
                        if l.iter().all(|x| x.valuation().is_none()) { continue; }
                        l[0].mul(&pt[0]).add(&l[1].mul(&pt[1])).add(&l[2].mul(&pt[2])).valuation().is_none()
                    }
                    DegenShape::Circle { center, r_sq, .. } => {
                        match squared_distance(center, &pt) {
                            Some(d) => d.sub(r_sq).valuation().is_none(),
                            None => continue,
                        }
                    }
                    // 点とスカラーは「その上に乗る」対象ではない。
                    DegenShape::Point(_) | DegenShape::Scalar { .. } => continue,
                };
                if !on { continue; }
                // P が既に乗っていると分かっている曲線のどれかと L が数値的に同一なら報告しない(中身は2つの図形の一致で、
                // 新しい接続ではない。一致は別枠で検出される)。
                let explained_by_coincidence = curves.iter().enumerate().any(|(oi, &other)| {
                    if other == c || !egraph.is_connected(p, other) { return false; }
                    match (&ccoords[oi], shape) {
                        (Some(DegenShape::Line(a)), DegenShape::Line(b)) => projectively_same(a, b),
                        (Some(DegenShape::Circle { center: o1, r_sq: r1, .. }),
                         DegenShape::Circle { center: o2, r_sq: r2, .. }) => {
                            projectively_same(o1, o2) && r1.sub(r2).valuation().is_none()
                        }
                        _ => false,
                    }
                });
                if explained_by_coincidence { continue; }
                *counts.entry((p, c)).or_insert(0) += 1;
            }
        }
    }
    let need = seeds.len() as u32;
    let mut out: Vec<(ClassId, ClassId)> = counts.into_iter().filter(|&(_, c)| c == need).map(|(k, _)| k).collect();
    out.sort_by_key(|&(a, b)| (a.0, b.0));
    out
}

/// 🌟 3つの円が1点を共有するか(ミケル点・根心型の結論)の検出。共円性検出は「名前の無い円に4点が乗る」形なので、
/// 「名前のある3つの円が1点で会う」形は別に要る。
/// 判定は根心で行う: 2つの根軸の交点R(3円のどれに対しても方冪が等しい点)での方冪が0なら、Rは3円すべての上にある。
/// 既に構造的に共有点が分かっている三つ組は除く。
pub fn find_generic_concurrent_circles(egraph: &EGraph, seeds: &[u64], max_circles: usize)
    -> Vec<(ClassId, ClassId, ClassId)>
{
    if seeds.is_empty() { return Vec::new(); }
    let ids = hot_reps_of_type(egraph, EntityType::Conic, max_circles, false);
    let mut counts: FxHashMap<(ClassId, ClassId, ClassId), u32> = FxHashMap::default();
    for &s in seeds {
        let mut ev = DegenEvaluator::new(egraph, s, None);
        let circles: Vec<Option<(Triple, PInt)>> = ids.iter()
            .map(|&id| match ev.eval(id) {
                Some(DegenShape::Circle { center, r_sq, .. }) => Some((center, r_sq)),
                _ => None,
            }).collect();
        for i in 0..ids.len() {
            let Some((o1, r1)) = circles[i] else { continue };
            for j in (i + 1)..ids.len() {
                let Some((o2, r2)) = circles[j] else { continue };
                let Some(ax12) = radical_axis((&o1, r1), (&o2, r2)) else { continue };
                if ax12.iter().all(|x| x.valuation().is_none()) { continue; }
                for k in (j + 1)..ids.len() {
                    let Some((o3, r3)) = circles[k] else { continue };
                    let Some(ax13) = radical_axis((&o1, r1), (&o3, r3)) else { continue };
                    let center = cross3(&ax12, &ax13);
                    // 根軸が平行(=3円の中心が共線)なら根心は無限遠、共点ではない。
                    if center[2].valuation().is_none() { continue; }
                    let Some(d) = squared_distance(&o1, &center) else { continue };
                    if d.sub(&r1).valuation().is_none() {
                        *counts.entry((ids[i], ids[j], ids[k])).or_insert(0) += 1;
                    }
                }
            }
        }
    }
    let need = seeds.len() as u32;
    let mut out: Vec<_> = counts.into_iter().filter(|&(_, c)| c == need).map(|(t, _)| t).collect();
    out.sort_by_key(|&(a, b, c)| (a.0, b.0, c.0));
    out
}

/// 🌟 系統的作図のための「退化した組み合わせ」のふるい。系統的作図は定理適用の前に走るので、数値的には同じ点なのに
/// 記号的には別の同値類、という組が普通にある(別々に作った同じ垂心など)。そこから「実質2点しか指定していない円」を
/// 作ると円が定まらず、その根軸や接線を通じて誤ったマージが連鎖して e-graph が潰れる。構造的な共線判定では
/// まだ証明されていない退化を捕まえられないので、数値側でふるう。
pub struct NumericSieve {
    coincident: FxHashSet<(ClassId, ClassId)>,
    collinear: FxHashSet<(ClassId, ClassId, ClassId)>,
    unevaluable: FxHashSet<ClassId>,
}

impl NumericSieve {
    fn key2(a: ClassId, b: ClassId) -> (ClassId, ClassId) { if a.0 <= b.0 { (a, b) } else { (b, a) } }
    fn key3(a: ClassId, b: ClassId, c: ClassId) -> (ClassId, ClassId, ClassId) {
        let mut v = [a, b, c]; v.sort_unstable_by_key(|x| x.0); (v[0], v[1], v[2])
    }
    /// 2点が数値的に同一(またはどちらかが評価不能)か。
    pub fn same_point(&self, a: ClassId, b: ClassId) -> bool {
        a == b || self.unevaluable.contains(&a) || self.unevaluable.contains(&b)
            || self.coincident.contains(&Self::key2(a, b))
    }
    /// 3点が円を定めない(=一致する2点があるか、共線)か。
    pub fn degenerate_triple(&self, a: ClassId, b: ClassId, c: ClassId) -> bool {
        self.same_point(a, b) || self.same_point(b, c) || self.same_point(a, c)
            || self.collinear.contains(&Self::key3(a, b, c))
    }
}

/// idsに挙げた点を1つの乱数座標で評価し、一致するペアと共線な三つ組を集める。
pub fn numeric_sieve(egraph: &EGraph, seed: u64, ids: &[ClassId]) -> NumericSieve {
    let mut ev = DegenEvaluator::new(egraph, seed, None);
    let coords: Vec<Option<Triple>> = ids.iter()
        .map(|&id| match ev.eval(id) { Some(DegenShape::Point(t)) => Some(t), _ => None }).collect();
    let mut out = NumericSieve {
        coincident: FxHashSet::default(), collinear: FxHashSet::default(), unevaluable: FxHashSet::default(),
    };
    for (i, &id) in ids.iter().enumerate() {
        if coords[i].is_none() { out.unevaluable.insert(id); }
    }
    for i in 0..ids.len() {
        let Some(pi) = coords[i] else { continue };
        for j in (i + 1)..ids.len() {
            let Some(pj) = coords[j] else { continue };
            let line = cross3(&pi, &pj);
            if line.iter().all(|x| x.valuation().is_none()) {
                out.coincident.insert(NumericSieve::key2(ids[i], ids[j]));
                continue;
            }
            for k in (j + 1)..ids.len() {
                let Some(pk) = coords[k] else { continue };
                let dot = line[0].mul(&pk[0]).add(&line[1].mul(&pk[1])).add(&line[2].mul(&pk[2]));
                if dot.valuation().is_none() {
                    out.collinear.insert(NumericSieve::key3(ids[i], ids[j], ids[k]));
                }
            }
        }
    }
    out
}

/// 4x4行列式(余因子展開、除算不要なのでPIntのままで計算できる)。
fn det4(m: &[[PInt; 4]; 4]) -> PInt {
    // 下2行の2x2小行列式(Laplace展開、いわゆるプリュッカー座標)を先に作る。
    let minor = |r1: usize, r2: usize, c1: usize, c2: usize| -> PInt {
        m[r1][c1].mul(&m[r2][c2]).sub(&m[r1][c2].mul(&m[r2][c1]))
    };
    let cols = [(0usize, 1usize), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];
    // det = Σ ± (上2行の小行列式) * (下2行の補となる小行列式)
    let mut acc = PInt::zero();
    for (idx, &(c1, c2)) in cols.iter().enumerate() {
        let top = minor(0, 1, c1, c2);
        let rest: Vec<usize> = (0..4).filter(|c| *c != c1 && *c != c2).collect();
        let bot = minor(2, 3, rest[0], rest[1]);
        let term = top.mul(&bot);
        // 符号: (c1,c2)の組の並び (01,23)+ (02,13)- (03,12)+ (12,03)+ (13,02)- (23,01)+
        let plus = matches!(idx, 0 | 2 | 3 | 5);
        acc = if plus { acc.add(&term) } else { acc.sub(&term) };
    }
    acc
}

/// 4点が同一円周上にある(共円)ことの検出。同次座標(x,y,z)に対する
/// 古典的な行列式 |x²+y², xz, yz, z²| = 0 で判定する。九点円のような
/// 「複数の由来が異なる点が実は1つの円に乗る」という発見はこの形をしている。
pub fn find_generic_concyclic_quadruples(egraph: &EGraph, seeds: &[u64], max_points: usize) -> Vec<[ClassId; 4]> {
    if seeds.is_empty() { return Vec::new(); }
    // 🌟 4点の総当たりは O(n⁴) で他の検出器(O(n³))より1桁重く、図が大きいとここだけで何分もかかる。
    // 共円は熱量上位の点に絞っても十分拾えるので、この検出器だけ独自の上限を掛ける。
    const CONCYCLIC_CAP: usize = 46;
    let ids = hot_reps_of_type(egraph, EntityType::Point, max_points.min(CONCYCLIC_CAP), true);
    let mut counts: FxHashMap<[ClassId; 4], u32> = FxHashMap::default();
    for &s in seeds {
        let mut ev = DegenEvaluator::new(egraph, s, None);
        let pts_xyz: Vec<Triple> = ids.iter().map(|&id| match ev.eval(id) {
            Some(DegenShape::Point(t)) => t,
            _ => [PInt::zero(); 3],
        }).collect();
        let rows: Vec<Option<[PInt; 4]>> = ids.iter().map(|&id| {
            match ev.eval(id) {
                Some(DegenShape::Point(t)) => {
                    let (x, y, z) = (t[0], t[1], t[2]);
                    // z=0(無限遠点)はhot_reps_of_typeで除外済みだが念のため。
                    if z.valuation().is_none() { return None; }
                    Some([x.mul(&x).add(&y.mul(&y)), x.mul(&z), y.mul(&z), z.mul(&z)])
                }
                _ => None,
            }
        }).collect();
        for i in 0..ids.len() {
            let Some(ri) = rows[i] else { continue };
            for j in (i + 1)..ids.len() {
                let Some(rj) = rows[j] else { continue };
                for k in (j + 1)..ids.len() {
                    let Some(rk) = rows[k] else { continue };
                    for l in (k + 1)..ids.len() {
                        let Some(rl) = rows[l] else { continue };
                        let d = det4(&[ri, rj, rk, rl]);
                        if d.valuation().is_none() {
                            // 直線は退化した円なので、共線な4点組は除外する
                            // (verify_propertyのFIXコメント参照)。
                            let (pi2, pj2, pk2) = (pts_xyz[i], pts_xyz[j], pts_xyz[k]);
                            let line_ij2 = cross3(&pi2, &pj2);
                            // 2点が数値的に同一だと行列に同じ行が並び、
                            // 4点目に関係なく行列式が0になる(verify_propertyの
                            // FIXコメント参照)。共線・重複はどちらも除外する。
                            let pl2 = pts_xyz[l];
                            let quad = [pi2, pj2, pk2, pl2];
                            let mut degenerate = line_ij2.iter().all(|x| x.valuation().is_none());
                            for a in 0..4 { for b in (a + 1)..4 {
                                if cross3(&quad[a], &quad[b]).iter().all(|x| x.valuation().is_none()) { degenerate = true; }
                            }}
                            let collinear_ijk = !line_ij2.iter().all(|x| x.valuation().is_none())
                                && line_ij2[0].mul(&pk2[0]).add(&line_ij2[1].mul(&pk2[1])).add(&line_ij2[2].mul(&pk2[2])).valuation().is_none();
                            if degenerate || collinear_ijk { continue; }
                            *counts.entry([ids[i], ids[j], ids[k], ids[l]]).or_insert(0) += 1;
                        }
                    }
                }
            }
        }
    }
    let need = seeds.len() as u32;
    let mut out: Vec<_> = counts.into_iter().filter(|&(_, c)| c == need).map(|(t, _)| t).collect();
    out.sort_by_key(|q| (q[0].0, q[1].0, q[2].0, q[3].0));
    out
}


/// 与えられた集合が実際に(全てのseedで)共線/共点/共円かを検証する。
/// 報告をクラスタで大きくまとめる際、その集合全体で本当に主張が成り立って
/// いるかを確かめるために使う(部分集合ごとの検出結果を素朴に併合すると、
/// 平行な族の混入などで偽の大集合が出来てしまうため)。
// 🌟 同じ図について何度も呼ぶ場面では verify_property_cached
// (precompute_shapes で評価器を使い回す版)に置き換え済み。
// 1回だけ確かめたいときのために素朴な版も残してある。
#[allow(dead_code)]
pub fn verify_property(egraph: &EGraph, seeds: &[u64], ids: &[ClassId], kind: PropertyKind) -> bool {
    let tables = precompute_shapes(egraph, seeds, ids);
    verify_property_cached(&tables, ids, kind)
}

/// 🌟 verify_property を何千回も呼ぶ側(maximal_verified_sets)のための前計算。同じ e-graph・同じ seed なら評価結果は
/// 不変なので、候補に出てくる実体の座標を seed ごとに1度だけ計算しておく(呼ぶたびに根から評価し直すと、実体が
/// 数百個の図で探索が何分も止まる)。
pub fn precompute_shapes(egraph: &EGraph, seeds: &[u64], ids: &[ClassId])
    -> Vec<FxHashMap<ClassId, Option<DegenShape>>>
{
    seeds.iter().map(|&s| {
        let mut ev = DegenEvaluator::new(egraph, s, None);
        ids.iter().map(|&id| (id, ev.eval(id))).collect()
    }).collect()
}

/// precompute_shapesの結果を使う版。tablesに載っていない実体があれば
/// 検証失敗として扱う(呼び出し側が前計算に入れ忘れた場合の安全側)。
pub fn verify_property_cached(
    tables: &[FxHashMap<ClassId, Option<DegenShape>>],
    ids: &[ClassId],
    kind: PropertyKind,
) -> bool {
    if ids.len() < kind.min_size() { return false; }
    if tables.is_empty() { return false; }
    for table in tables {
        let shapes: Vec<Option<DegenShape>> = ids.iter()
            .map(|id| table.get(id).cloned().unwrap_or(None)).collect();
        if shapes.iter().any(|x| x.is_none()) { return false; }
        match kind {
            PropertyKind::Collinear | PropertyKind::Concurrent => {
                // 共線(点)も共点(直線)も「同次座標の三重積が全て0」で判定できる(双対)。
                let vecs: Vec<Triple> = shapes.iter().map(|sh| match sh {
                    Some(DegenShape::Point(t)) | Some(DegenShape::Line(t)) => *t,
                    _ => [PInt::zero(); 3],
                }).collect();
                // 集合内に重複(同じ点/同じ直線)があると主張が意味を成さない
                // ――そちらは「2つの図形が一致した」として別枠で検出される。
                for i in 0..vecs.len() {
                    for j in (i + 1)..vecs.len() {
                        if cross3(&vecs[i], &vecs[j]).iter().all(|x| x.valuation().is_none()) { return false; }
                    }
                }
                let base = cross3(&vecs[0], &vecs[1]);
                if base.iter().all(|x| x.valuation().is_none()) { return false; }
                if kind == PropertyKind::Concurrent && base[2].valuation().is_none() { return false; }
                for v in &vecs[2..] {
                    let dot = base[0].mul(&v[0]).add(&base[1].mul(&v[1])).add(&base[2].mul(&v[2]));
                    if dot.valuation().is_some() { return false; }
                }
            }
            PropertyKind::Concyclic => {
                let pts: Vec<Triple> = shapes.iter().map(|sh| match sh {
                    Some(DegenShape::Point(t)) => *t,
                    _ => [PInt::zero(); 3],
                }).collect();
                // 判定式 |x²+y², xz, yz, z²| = 0 は4点が同一直線上でも成り立つ(直線は退化した円)。また基準の3点が退化していると
                // (同じ点を含む・共線)、4点目が何であれ行列式は恒等的に0になる。基準には「互いに相異なりかつ共線でない3点」を
                // 明示的に選び、無ければ検証失敗とする。
                let same_point = |a: &Triple, b: &Triple| cross3(a, b).iter().all(|x| x.valuation().is_none());
                let mut base: Option<(usize, usize, usize)> = None;
                'base: for i in 0..pts.len() {
                    for j in (i + 1)..pts.len() {
                        if same_point(&pts[i], &pts[j]) { continue; }
                        let l = cross3(&pts[i], &pts[j]);
                        for k in (j + 1)..pts.len() {
                            if same_point(&pts[i], &pts[k]) || same_point(&pts[j], &pts[k]) { continue; }
                            let dot = l[0].mul(&pts[k][0]).add(&l[1].mul(&pts[k][1])).add(&l[2].mul(&pts[k][2]));
                            if dot.valuation().is_some() { base = Some((i, j, k)); break 'base; }
                        }
                    }
                }
                let Some((bi, bj, bk)) = base else { return false };
                // 集合内に重複した点があれば、その組は「共円」の主張として
                // 意味を成さない(円上の相異なる点の集まりを報告したい)。
                for i in 0..pts.len() {
                    for j in (i + 1)..pts.len() {
                        if same_point(&pts[i], &pts[j]) { return false; }
                    }
                }

                let rows: Vec<[PInt; 4]> = pts.iter().map(|t| {
                    let (x, y, z) = (t[0], t[1], t[2]);
                    [x.mul(&x).add(&y.mul(&y)), x.mul(&z), y.mul(&z), z.mul(&z)]
                }).collect();
                for i in 0..rows.len() {
                    if i == bi || i == bj || i == bk { continue; }
                    if det4(&[rows[bi], rows[bj], rows[bk], rows[i]]).valuation().is_some() { return false; }
                }
            }
        }
    }
    true
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PropertyKind { Collinear, Concurrent, Concyclic }

impl PropertyKind {
    fn min_size(self) -> usize {
        match self { PropertyKind::Concyclic => 4, _ => 3 }
    }
}

/// 🌟 崩壊検出(本質版): e-graphが「点Pは直線L上にある」と構造的に主張して
/// いる全ての接続について、数値評価でも本当にP∈Lになっているかを確かめる。
///
/// 自由探索は稀に誤ったマージを連鎖させ、e-graphを実際の幾何と矛盾した
/// 状態へ潰してしまう。その状態で数値評価をすると、構造上の主張と数値が
/// 食い違い、「15点が同一円周上」のような(実際には多くが同一直線上に
/// あって円には2点しか乗れないはずの)無意味な報告が出る。自由点が一般の
/// 位置にあるかを見るだけでは、土台の三角形が無事なまま中間の実体だけが
/// 壊れているケースを取り逃がすため、接続関係そのものを検証する。
///
/// 矛盾が1件でも見つかれば、その(点, 直線)を返す。
pub fn find_incidence_inconsistency(egraph: &EGraph, seed: u64) -> Option<(ClassId, ClassId)> {
    let mut ev = DegenEvaluator::new(egraph, seed, None);
    let lines: Vec<ClassId> = (0..egraph.entities.len()).map(ClassId)
        .filter(|&id| egraph.get_rep(id) == id
            && egraph.entities[id.0].entity_type == EntityType::Line
            && id != egraph.line_infinity)
        .collect();
    for l in lines {
        let Some(DegenShape::Line(lv)) = ev.eval(l) else { continue };
        if lv.iter().all(|x| x.valuation().is_none()) { continue; }
        let pts: Vec<ClassId> = egraph.entities[l.0].components.first()
            .map(|c| c.subobjects.iter().map(|&s| egraph.get_rep(s))
                .filter(|&s| egraph.entities[s.0].entity_type == EntityType::Point)
                .collect())
            .unwrap_or_default();
        for p in pts {
            let Some(DegenShape::Point(pv)) = ev.eval(p) else { continue };
            if pv.iter().all(|x| x.valuation().is_none()) { continue; }
            let dot = lv[0].mul(&pv[0]).add(&lv[1].mul(&pv[1])).add(&lv[2].mul(&pv[2]));
            if dot.valuation().is_some() {
                if crate::cli::sweep_debug() {
                    let defs = egraph.entities[l.0].components.first()
                        .map(|c| c.definitions.iter().map(|d| egraph.format_definition(d)).collect::<Vec<_>>())
                        .unwrap_or_default();
                    eprintln!("  [incidence-debug] 点{} が 直線{} 上に無い。直線の同値類が持つ定義: {:?}",
                        egraph.entities[p.0].name.chars().take(40).collect::<String>(),
                        egraph.entities[l.0].name.chars().take(40).collect::<String>(),
                        defs.iter().map(|d| d.chars().take(50).collect::<String>()).collect::<Vec<_>>());
                    let pdefs = egraph.entities[p.0].components.first()
                        .map(|c| c.definitions.iter().map(|d| egraph.format_definition(d)).collect::<Vec<_>>())
                        .unwrap_or_default();
                    eprintln!("  [incidence-debug] 点の同値類が持つ定義: {:?}",
                        pdefs.iter().map(|d| d.chars().take(50).collect::<String>()).collect::<Vec<_>>());
                    let cons: Vec<String> = egraph.find_extraneous_incidences(p).iter()
                        .map(|&cc| egraph.entities[cc.0].name.chars().take(40).collect::<String>()).collect();
                    eprintln!("  [incidence-debug] 点が制約として使う曲線: {:?}", cons);
                    // 直線の各定義の親(点)について、その点が本当にこの直線上に
                    // 乗っているか・どんな制約で決まったかを出す。
                    let parents: Vec<ClassId> = egraph.entities[l.0].components.first()
                        .map(|c| c.definitions.iter().flat_map(|d| d.get_parents()).map(|q| egraph.get_rep(q)).collect())
                        .unwrap_or_default();
                    for q in parents {
                        if egraph.entities[q.0].entity_type != EntityType::Point { continue; }
                        let qc: Vec<String> = egraph.find_extraneous_incidences(q).iter()
                            .map(|&cc| egraph.entities[cc.0].name.chars().take(30).collect::<String>()).collect();
                        let on = match ev.eval(q) {
                            Some(DegenShape::Point(qv)) => {
                                let d2 = lv[0].mul(&qv[0]).add(&lv[1].mul(&qv[1])).add(&lv[2].mul(&qv[2]));
                                if d2.valuation().is_none() { "乗っている" } else { "乗っていない" }
                            }
                            _ => "評価不能",
                        };
                        eprintln!("      親点 {:<22} は直線に{} / 制約={:?} / 定義={:?}",
                            egraph.entities[q.0].name.chars().take(22).collect::<String>(), on, qc,
                            egraph.entities[q.0].components.first()
                                .map(|c| c.definitions.iter().map(|d| egraph.format_definition(d).chars().take(40).collect::<String>()).collect::<Vec<_>>())
                                .unwrap_or_default());
                    }
                }
                return Some((p, l));
            }
        }
    }
    None
}

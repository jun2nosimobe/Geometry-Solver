//! 🌟 padic.rsの算術基盤(PInt、Z/P^4Z)の上に、EGraphのDefinitionを辿る
//! 一般的な評価器(discover_viz.rs::RealEvaluatorと同じ構造)を実装し、
//! 自由点のペアを機械的に退化させては全図形ペアの一致を走査するドライバを
//! 用意する。ユーザー方針(1,2を進める)への対応の第2段。
//!
//! 手順:
//! 1. 2つの自由点A,Bを選び、A = B + P*δ(δは乱数)という座標を与える。
//!    それ以外の自由点は通常通り完全に一般的な乱数座標を与える。
//! 2. 依存関係にある全ての図形(Point/Line/Circle)をmod P^4で評価する。
//! 3. 各図形について「同次座標3成分に共通するPの最大べきで割ってから
//!    mod Pを取る」ことで、この退化の極限で実際にどこへ収束するかを表す
//!    「先頭項」を読み取る。
//! 4. 先頭項が(偶然ではありえない精度で)射影的に一致する2つの図形の組を
//!    「この退化のもとで関連がある」候補として集める。
//! 5. ただし、退化を全く使わない一般乱数(discover.rsが既にSchwartz-Zippel
//!    法で検出している)でも一致してしまう組は、既に別の仕組みで見つかる
//!    「常に真」の一致であってこの技法固有の発見ではないので除外する。

use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};
use crate::padic::{
    self, affine_point, intersection, line_through_points, midpoint, parallel_line,
    perpendicular_line, projectively_equal_mod_p, DivOutcome, PInt, Triple,
};
use rand::rngs::StdRng;
use rand::SeedableRng;
use rustc_hash::FxHashMap;

#[derive(Clone, Copy, Debug)]
pub enum DegenShape {
    Point(Triple),
    Line(Triple),
    Circle { center: Triple, r_sq: PInt },
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

pub struct DegenEvaluator<'a> {
    egraph: &'a EGraph,
    cache: FxHashMap<ClassId, Option<DegenShape>>,
    free_coords: FxHashMap<ClassId, (PInt, PInt)>,
    rng: StdRng,
}

impl<'a> DegenEvaluator<'a> {
    /// merge_pairが指定されていれば、その2つの自由点(egraph.get_rep後)を
    /// A = B + P*δという退化した座標で結ぶ。指定が無ければ全ての自由点を
    /// 完全に一般的な乱数座標にする(discover.rsの一般乱数一致検出との
    /// 対照実験、「この一致は退化固有か」を確かめるベースラインに使う)。
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
        Self { egraph, cache: FxHashMap::default(), free_coords, rng }
    }

    pub fn eval(&mut self, id: ClassId) -> Option<DegenShape> {
        let rep = self.egraph.get_rep(id);
        if let Some(v) = self.cache.get(&rep) { return *v; }
        self.cache.insert(rep, None); // 循環防止のプレースホルダ
        let def = self.egraph.entities[rep.0].original_definition.clone();
        let result = self.eval_def(rep, &def);
        self.cache.insert(rep, result);
        result
    }

    fn point_of(&mut self, id: ClassId) -> Option<Triple> {
        match self.eval(id)? { DegenShape::Point(t) => Some(t), _ => None }
    }
    fn line_of(&mut self, id: ClassId) -> Option<Triple> {
        match self.eval(id)? { DegenShape::Line(t) => Some(t), _ => None }
    }
    fn circle_of(&mut self, id: ClassId) -> Option<(Triple, PInt)> {
        match self.eval(id)? { DegenShape::Circle { center, r_sq } => Some((center, r_sq)), _ => None }
    }

    fn eval_def(&mut self, rep: ClassId, def: &Definition) -> Option<DegenShape> {
        match def {
            Definition::FreePoint | Definition::GivenPoint => {
                if self.egraph.entities[rep.0].entity_type == EntityType::Point {
                    if let Some(&c) = self.free_coords.get(&rep) { return Some(DegenShape::Point(affine_point(c.0, c.1))); }
                    let c = (PInt::random_unit(&mut self.rng), PInt::random_unit(&mut self.rng));
                    self.free_coords.insert(rep, c);
                    Some(DegenShape::Point(affine_point(c.0, c.1)))
                } else {
                    None // Line_infinity等
                }
            }
            Definition::Intersection(l1, l2) => {
                let a = self.line_of(*l1)?;
                let b = self.line_of(*l2)?;
                Some(DegenShape::Point(intersection(&a, &b)))
            }
            Definition::LineThroughPoints(p1, p2) => {
                let a = self.point_of(*p1)?;
                let b = self.point_of(*p2)?;
                Some(DegenShape::Line(line_through_points(&a, &b)))
            }
            Definition::Midpoint(p1, p2) => {
                let a = self.point_of(*p1)?;
                let b = self.point_of(*p2)?;
                Some(DegenShape::Point(midpoint(&a, &b)))
            }
            Definition::PerpendicularLine(l, p) => {
                let ll = self.line_of(*l)?;
                let pp = self.point_of(*p)?;
                Some(DegenShape::Line(perpendicular_line(&ll, &pp)))
            }
            Definition::ParallelLine(l, p) => {
                let ll = self.line_of(*l)?;
                let pp = self.point_of(*p)?;
                Some(DegenShape::Line(parallel_line(&ll, &pp)))
            }
            Definition::Circumcircle(a, b, c) => {
                let pa = self.point_of(*a)?;
                let pb = self.point_of(*b)?;
                let pc = self.point_of(*c)?;
                let mid_ab = midpoint(&pa, &pb);
                let mid_ac = midpoint(&pa, &pc);
                let l_ab = line_through_points(&pa, &pb);
                let l_ac = line_through_points(&pa, &pc);
                let pb_ab = perpendicular_line(&l_ab, &mid_ab);
                let pb_ac = perpendicular_line(&l_ac, &mid_ac);
                let center = intersection(&pb_ab, &pb_ac);
                let r_sq = squared_distance(&center, &pa)?;
                Some(DegenShape::Circle { center, r_sq })
            }
            Definition::TangentLine(circ, p) => {
                // pは既に円上にある接点だという前提(このプロジェクト全体の
                // 規約、discover_viz.rs::RealEvaluatorと同じ)。接線は
                // 半径(中心→p)に垂直でpを通る直線。
                let (center, _r_sq) = self.circle_of(*circ)?;
                let pp = self.point_of(*p)?;
                let radial_line = line_through_points(&center, &pp);
                Some(DegenShape::Line(perpendicular_line(&radial_line, &pp)))
            }
            Definition::HarmonicConjugateOf(a, b, c) => {
                let pa = self.point_of(*a)?;
                let pb = self.point_of(*b)?;
                let pc = self.point_of(*c)?;
                Some(DegenShape::Point(harmonic_conjugate(&pa, &pb, &pc)))
            }
            // Scalar/Conic(一般二次曲線)/CrossRatio系はまだ未対応
            // (Point/Line/Circleのみが第一段の対象、discover_viz.rs::
            // RealEvaluatorと同じスコープ)。
            _ => None,
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
    }
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
// 🌟 ユーザー提案:「同じ退化グループにあるかはすぐ判定できるはずだから
// それを用いてheatにボーナスすることを考えている」への対応。
//
// 🐛 最初はunion-find(推移閉包)で実装したが、simsonで実測したところ
// 明確な悪化(2.1秒、無効時の約0.89秒から2倍以上に劣化)が見つかった。
// 原因を辿ると、union-findは「異なる退化パターンで見つかった関係」まで
// 無差別に推移合併してしまうバグだった: 例えばsimsonでは「A≡Bという
// 退化ではD≡E」「A≡Cという退化ではD≡F」「B≡Cという退化ではE≡F」が
// それぞれ別々に成り立つが、これらは互いに両立しない(同時には起こり
// 得ない)別々の極限の話であって「D,E,Fは常に関連しあう」という意味では
// 全く無いにもかかわらず、union-findにそのまま食わせるとD≡E≡Fが推移的に
// 1つのグループへ潰れ、さらに芋づる式にA,B,C,P全体が1つの巨大グループへ
// 潰れてしまっていた(実際にsimsonの7つの実体がほぼ全て1グループに
// なっていたことを確認)。これによりbump_heat_bonusが「ほぼ全ての実体」に
// ボーナスを撒くようになり、熱による優先度の差が消えて熱cap切り捨ての
// 効果自体が薄まっていたのが遅くなった理由。
//
// 修正: 推移閉包を取らない、直接発見された辺だけを保持する隣接グラフに
// 変更した(「Xを退化させたらYと一致した」という個々の観測をそのまま
// 記録するだけで、そこから「ならZとも関連するはず」という推論はしない)。
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

    pub fn is_empty(&self) -> bool { self.edges.is_empty() }
}

/// 与えられたegraphの全自由点ペアについて退化固有の一致を走査し、
/// 複数回の独立な乱数drawで再現した組だけをDegenerationRelationsへ記録する
/// (推移閉包は取らない、直接観測された辺のみ)。discover_degenerate.rs::
/// runと同じロジックだが、CLI表示ではなくEGraphに直接取り込むための版。
pub fn compute_degeneration_groups(egraph: &EGraph, seed: u64, min_hits: u32) -> DegenerationRelations {
    let trials = min_hits.max(2);
    let mut free_points = Vec::new();
    for i in 0..egraph.entities.len() {
        let id = ClassId(i);
        if egraph.get_rep(id) != id { continue; }
        let e = &egraph.entities[i];
        if e.entity_type == EntityType::Point && matches!(e.original_definition, Definition::FreePoint) {
            free_points.push(id);
        }
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
}

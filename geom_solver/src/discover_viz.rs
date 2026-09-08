//! 🌟 ユーザー要望:「報告が読めない問題に対処するために、図形を描画して
//! 確認できるようにしたい」への対応(discover.rsの報告がPrettyNamerで
//! 読める名前になった後も、テキストの構成手順から実際の図を思い浮かべる
//! のは依然として大変、という指摘)。discover.rsが発見した予想(a≡b)に
//! ついて、その依存関係の閉包を実数座標(f64)で評価し直し、SVGとして
//! 描画する。
//!
//! 既存の証明エンジン(mmp_core/eval.rs)は健全性のため有限体(ModInt、
//! mod 998244353)上の厳密演算だけを使い、実数座標を一切保持しない
//! (証明の正しさに実数座標は不要で、むしろ浮動小数点誤差を持ち込む
//! リスクにしかならない)。図示のためだけに、この設計とは完全に独立した
//! 「実数版の再評価器」をここに新設する――旧Python版のvisualizer.py
//! (RealtimeVisualizer.broadcast_state)が自由変数にランダムな実数を
//! 割り当ててcalculate()する方式を参考にした(ModIntへのモンキーパッチは
//! Rust版には存在しない有限体/実数混在の都合なので移植不要)。
//!
//! 対象はPoint/Line/Circleの3種類だけで良い: このプロジェクトの
//! Definition列挙型(mmp_core/mod.rs::get_parents)を確認したところ、
//! Angle/Scalar/Direction/Conic/CrossRatio系の値を入力に取るPoint/Line/
//! Circle構成は1つも無い――つまり描画に必要な実体は、必ずPoint/Line/
//! Circle型の祖先だけを辿れば揃う。

use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};
use rustc_hash::FxHashMap;

#[derive(Clone, Copy, Debug)]
pub enum RealShape {
    Point(f64, f64),
    /// 点pを通り方向dへ伸びる直線。dは正規化しない(長さは描画時の
    /// クリッピングにしか影響しないため、ゼロ除算さえ避ければ良い)。
    Line { p: (f64, f64), d: (f64, f64) },
    Circle { c: (f64, f64), r: f64 },
}

const EPS: f64 = 1e-7;

fn sub(a: (f64, f64), b: (f64, f64)) -> (f64, f64) { (a.0 - b.0, a.1 - b.1) }
fn add(a: (f64, f64), b: (f64, f64)) -> (f64, f64) { (a.0 + b.0, a.1 + b.1) }
fn scale(a: (f64, f64), k: f64) -> (f64, f64) { (a.0 * k, a.1 * k) }
fn dot(a: (f64, f64), b: (f64, f64)) -> f64 { a.0 * b.0 + a.1 * b.1 }
fn cross(a: (f64, f64), b: (f64, f64)) -> f64 { a.0 * b.1 - a.1 * b.0 }
fn norm(a: (f64, f64)) -> f64 { (a.0 * a.0 + a.1 * a.1).sqrt() }
fn dist(a: (f64, f64), b: (f64, f64)) -> f64 { norm(sub(a, b)) }

fn intersect_lines(p1: (f64, f64), d1: (f64, f64), p2: (f64, f64), d2: (f64, f64)) -> Option<(f64, f64)> {
    let denom = cross(d1, d2);
    if denom.abs() < EPS { return None; } // 平行(この乱数draw下では退化)
    let t = cross(sub(p2, p1), d2) / denom;
    Some(add(p1, scale(d1, t)))
}

/// 標準的な外心の公式。3点が(ほぼ)共線なら計算不能としてNoneを返す。
fn circumcircle_real(a: (f64, f64), b: (f64, f64), c: (f64, f64)) -> Option<((f64, f64), f64)> {
    let d = 2.0 * (a.0 * (b.1 - c.1) + b.0 * (c.1 - a.1) + c.0 * (a.1 - b.1));
    if d.abs() < EPS { return None; }
    let a2 = a.0 * a.0 + a.1 * a.1;
    let b2 = b.0 * b.0 + b.1 * b.1;
    let c2 = c.0 * c.0 + c.1 * c.1;
    let ux = (a2 * (b.1 - c.1) + b2 * (c.1 - a.1) + c2 * (a.1 - b.1)) / d;
    let uy = (a2 * (c.0 - b.0) + b2 * (a.0 - c.0) + c2 * (b.0 - a.0)) / d;
    Some(((ux, uy), dist((ux, uy), a)))
}

/// 調和共役点の公式。直線AB上でa=0, b=1とパラメータ化し、cの位置tcから
/// 古典的な公式 d = tc / (2*tc - 1) でdの位置tdを求める
/// (交比(A,B;C,D)=-1の定義から導出、cross-ratio = [(C-A)/(C-B)] / [(D-A)/(D-B)])。
fn harmonic_conjugate_real(a: (f64, f64), b: (f64, f64), c: (f64, f64)) -> Option<(f64, f64)> {
    let dir = sub(b, a);
    let len2 = dot(dir, dir);
    if len2 < EPS { return None; }
    let tc = dot(sub(c, a), dir) / len2;
    let denom = 2.0 * tc - 1.0;
    if denom.abs() < EPS { return None; } // cが中点(dは無限遠、この乱数drawでは描画不能)
    let td = tc / denom;
    Some(add(a, scale(dir, td)))
}

/// 🌟 discover.rsのdescribe_constructionと対になる、実数版の再評価器。
/// キャッシュはClassId単位(get_rep後)で、自由点には初回評価時に
/// ランダムな座標を割り当てて記憶する(以後は同じ座標を使い回す)。
pub struct RealEvaluator<'a> {
    egraph: &'a EGraph,
    cache: FxHashMap<ClassId, Option<RealShape>>,
    free_coords: FxHashMap<ClassId, (f64, f64)>,
    rng_state: u64,
}

impl<'a> RealEvaluator<'a> {
    pub fn new(egraph: &'a EGraph, seed: u64) -> Self {
        Self { egraph, cache: FxHashMap::default(), free_coords: FxHashMap::default(), rng_state: seed.max(1) }
    }

    // 🌟 依存を増やさないための最小限のxorshift64。座標の見た目に暗号学的な
    // 質は不要で、「同じseedなら同じ配置を再現できる」ことの方が重要
    // (失敗時に別のseedへ振り直して再試行する仕組みと組み合わせて使う)。
    fn next_unit(&mut self) -> f64 {
        let mut x = self.rng_state;
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        self.rng_state = x;
        (x >> 11) as f64 / (1u64 << 53) as f64
    }

    fn random_coord(&mut self) -> (f64, f64) {
        // -1.5..1.5、0近辺(退化しやすい)は避ける
        // (旧visualizer.pyのstatic_t_dict生成ロジックを踏襲)。
        let mut mk = || -> f64 {
            let v = self.next_unit() * 3.0 - 1.5;
            if v.abs() < 0.3 { if v >= 0.0 { 0.4 } else { -0.4 } } else { v }
        };
        (mk(), mk())
    }

    pub fn eval(&mut self, id: ClassId) -> Option<RealShape> {
        let rep = self.egraph.get_rep(id);
        if let Some(v) = self.cache.get(&rep) { return *v; }
        // 循環防止のプレースホルダ。discover.rs::has_degenerate_ancestorが
        // 事前に閉路を除外しているはずだが、防御的にNoneで埋めておく。
        self.cache.insert(rep, None);
        let def = self.egraph.entities[rep.0].original_definition.clone();
        let result = self.eval_def(rep, &def);
        self.cache.insert(rep, result);
        result
    }

    fn line_of(&mut self, id: ClassId) -> Option<((f64, f64), (f64, f64))> {
        match self.eval(id)? { RealShape::Line { p, d } => Some((p, d)), _ => None }
    }
    fn point_of(&mut self, id: ClassId) -> Option<(f64, f64)> {
        match self.eval(id)? { RealShape::Point(x, y) => Some((x, y)), _ => None }
    }
    fn circle_of(&mut self, id: ClassId) -> Option<((f64, f64), f64)> {
        match self.eval(id)? { RealShape::Circle { c, r } => Some((c, r)), _ => None }
    }

    fn eval_def(&mut self, rep: ClassId, def: &Definition) -> Option<RealShape> {
        match def {
            Definition::FreePoint | Definition::GivenPoint => {
                if self.egraph.entities[rep.0].entity_type == EntityType::Point {
                    if let Some(&c) = self.free_coords.get(&rep) { return Some(RealShape::Point(c.0, c.1)); }
                    let c = self.random_coord();
                    self.free_coords.insert(rep, c);
                    Some(RealShape::Point(c.0, c.1))
                } else {
                    None // Line_infinity等(非Point定数)は描画非対応
                }
            }
            Definition::Intersection(l1, l2) => {
                let (p1, d1) = self.line_of(*l1)?;
                let (p2, d2) = self.line_of(*l2)?;
                intersect_lines(p1, d1, p2, d2).map(|(x, y)| RealShape::Point(x, y))
            }
            Definition::LineThroughPoints(a, b) => {
                let (pa, pb) = (self.point_of(*a)?, self.point_of(*b)?);
                if dist(pa, pb) < EPS { return None; }
                Some(RealShape::Line { p: pa, d: sub(pb, pa) })
            }
            Definition::Midpoint(a, b) => {
                let (pa, pb) = (self.point_of(*a)?, self.point_of(*b)?);
                Some(RealShape::Point((pa.0 + pb.0) / 2.0, (pa.1 + pb.1) / 2.0))
            }
            Definition::Circumcircle(a, b, c) => {
                let (pa, pb, pc) = (self.point_of(*a)?, self.point_of(*b)?, self.point_of(*c)?);
                circumcircle_real(pa, pb, pc).map(|(c, r)| RealShape::Circle { c, r })
            }
            Definition::PerpendicularLine(l, p) => {
                let (_, d) = self.line_of(*l)?;
                let pt = self.point_of(*p)?;
                Some(RealShape::Line { p: pt, d: (-d.1, d.0) })
            }
            Definition::ParallelLine(l, p) => {
                let (_, d) = self.line_of(*l)?;
                let pt = self.point_of(*p)?;
                Some(RealShape::Line { p: pt, d })
            }
            Definition::TangentLine(circ, p) => {
                // 🌟 このプロジェクトのTangentLine(circle, p)は「pは既に円上に
                // ある接点」という前提(円外の点からの2接線の選択曖昧性を
                // 持たない)で使われている――半径方向に垂直な直線として描く。
                let (center, _r) = self.circle_of(*circ)?;
                let pt = self.point_of(*p)?;
                let radial = sub(pt, center);
                if norm(radial) < EPS { return None; }
                Some(RealShape::Line { p: pt, d: (-radial.1, radial.0) })
            }
            Definition::HarmonicConjugateOf(a, b, c) => {
                let (pa, pb, pc) = (self.point_of(*a)?, self.point_of(*b)?, self.point_of(*c)?);
                harmonic_conjugate_real(pa, pb, pc).map(|(x, y)| RealShape::Point(x, y))
            }
            // Angle/Scalar/Conic/CrossRatio系、およびDirectionOf/PerpDirectionOf
            // (EntityType::Direction撤廃後は単なるPoint型だが、無限遠点は
            // アフィン平面のSVGには描画しようがないので変わらずNoneでよい)
            // は描画不要と確認済み。
            _ => None,
        }
    }
}

/// 🌟 discover.rsから呼ぶエントリポイント。orderで与えた実体(親が先の
/// 依存関係順、describe_constructionが返すものと同じ)を実数座標で評価し、
/// labelsで示された表示名を添えたSVGを組み立てる。a, bは強調表示する
/// (発見された予想の当事者)。乱数の初期配置がたまたま退化(平行線・
/// 共線3点等)した場合は、seedを変えて最大max_attempts回まで再試行する。
/// 全て失敗すればNone(呼び出し側はテキスト報告のみへフォールバックする)。
pub fn render_svg(
    egraph: &EGraph,
    order: &[ClassId],
    labels: &FxHashMap<ClassId, String>,
    a: ClassId,
    b: ClassId,
    max_attempts: u32,
) -> Option<String> {
    for attempt in 0..max_attempts {
        let seed = 0x9E3779B97F4A7C15u64.wrapping_mul(attempt as u64 + 1).wrapping_add(12345);
        let mut ev = RealEvaluator::new(egraph, seed);
        let shapes: Vec<(ClassId, Option<RealShape>)> = order.iter().map(|&id| (id, ev.eval(id))).collect();
        // a, bの両方が(この乱数drawで)描画可能でなければやり直す。
        if ev.eval(a).is_none() || ev.eval(b).is_none() { continue; }
        if let Some(svg) = build_svg(egraph, &shapes, labels, a, b) {
            return Some(svg);
        }
    }
    None
}

fn build_svg(
    egraph: &EGraph,
    shapes: &[(ClassId, Option<RealShape>)],
    labels: &FxHashMap<ClassId, String>,
    a: ClassId,
    b: ClassId,
) -> Option<String> {
    let (a_rep, b_rep) = (egraph.get_rep(a), egraph.get_rep(b));

    // 1. バウンディングボックスを、評価に成功した点・円の範囲から求める。
    let mut min_x = f64::INFINITY; let mut max_x = f64::NEG_INFINITY;
    let mut min_y = f64::INFINITY; let mut max_y = f64::NEG_INFINITY;
    let mut expand = |x: f64, y: f64| {
        if x < min_x { min_x = x; } if x > max_x { max_x = x; }
        if y < min_y { min_y = y; } if y > max_y { max_y = y; }
    };
    for (_, shape) in shapes {
        match shape {
            Some(RealShape::Point(x, y)) => expand(*x, *y),
            Some(RealShape::Circle { c, r }) => { expand(c.0 - r, c.1 - r); expand(c.0 + r, c.1 + r); }
            _ => {}
        }
    }
    if !min_x.is_finite() { return None; } // 描画対象が1つも無い
    let pad = ((max_x - min_x).max(max_y - min_y) * 0.15).max(0.5);
    min_x -= pad; max_x += pad; min_y -= pad; max_y += pad;
    let w = (max_x - min_x).max(1e-3);
    let h = (max_y - min_y).max(1e-3);
    let diag = (w * w + h * h).sqrt();

    // 2. SVG本体を組み立てる(y軸はSVGでは下向きが正なので、[min_y,max_y]の
    // 範囲内で上下反転してから使う)。
    let flip_y = |y: f64| min_y + max_y - y;
    let to_svg = |p: (f64, f64)| (p.0, flip_y(p.1));

    let mut body = String::new();
    // 2a. 直線(円・点より先に描いて背面に置く)。
    for (id, shape) in shapes {
        if let Some(RealShape::Line { p, d }) = shape {
            let dn = norm(*d);
            if dn < EPS { continue; }
            let ext = diag * 2.0;
            let p1 = add(*p, scale(*d, ext / dn));
            let p2 = sub(*p, scale(*d, ext / dn));
            let (x1, y1) = to_svg(p1);
            let (x2, y2) = to_svg(p2);
            let is_target = egraph.get_rep(*id) == a_rep || egraph.get_rep(*id) == b_rep;
            let (color, width) = if is_target { ("#e0575b", 2.4) } else { ("#8a94a6", 1.1) };
            body.push_str(&format!(
                "<line x1=\"{:.4}\" y1=\"{:.4}\" x2=\"{:.4}\" y2=\"{:.4}\" stroke=\"{}\" stroke-width=\"{}\" />\n",
                x1, y1, x2, y2, color, width
            ));
        }
    }
    // 2b. 円。
    for (id, shape) in shapes {
        if let Some(RealShape::Circle { c, r }) = shape {
            let (cx, cy) = to_svg(*c);
            let is_target = egraph.get_rep(*id) == a_rep || egraph.get_rep(*id) == b_rep;
            let color = if is_target { "#e0575b" } else { "#5b8def" };
            let width = if is_target { 2.4 } else { 1.3 };
            body.push_str(&format!(
                "<circle cx=\"{:.4}\" cy=\"{:.4}\" r=\"{:.4}\" fill=\"none\" stroke=\"{}\" stroke-width=\"{}\" />\n",
                cx, cy, r, color, width
            ));
        }
    }
    // 2c. 点(ラベル付き、最後に描いて最前面に置く)。
    let font_size = (diag * 0.028).max(0.05);
    let dot_r = (diag * 0.009).max(0.02);
    for (id, shape) in shapes {
        if let Some(RealShape::Point(x, y)) = shape {
            let (sx, sy) = to_svg((*x, *y));
            let is_target = egraph.get_rep(*id) == a_rep || egraph.get_rep(*id) == b_rep;
            let color = if is_target { "#e0575b" } else { "#1f2733" };
            let label = labels.get(&egraph.get_rep(*id)).cloned().unwrap_or_else(|| egraph.entities[egraph.get_rep(*id).0].name.clone());
            body.push_str(&format!(
                "<circle cx=\"{:.4}\" cy=\"{:.4}\" r=\"{:.4}\" fill=\"{}\" />\n<text x=\"{:.4}\" y=\"{:.4}\" font-size=\"{:.4}\" fill=\"{}\">{}</text>\n",
                sx, sy, dot_r, color, sx + dot_r * 1.6, sy - dot_r * 1.6, font_size, color, xml_escape(&label)
            ));
        }
    }

    let label_a = labels.get(&a_rep).cloned().unwrap_or_else(|| egraph.entities[a_rep.0].name.clone());
    let label_b = labels.get(&b_rep).cloned().unwrap_or_else(|| egraph.entities[b_rep.0].name.clone());
    Some(format!(
        "<figure style=\"margin:0;\">\n<svg viewBox=\"0 0 {w:.4} {h:.4}\" width=\"420\" height=\"420\" xmlns=\"http://www.w3.org/2000/svg\" style=\"background:#fbfaf7;border:1px solid #d8d3c8;border-radius:6px;\">\n<g transform=\"translate({tx:.4},{ty:.4})\">\n{body}</g>\n</svg>\n<figcaption style=\"font:12px monospace;color:#555;margin-top:4px;\">赤色 = {label_a} ≡ {label_b}</figcaption>\n</figure>\n",
        w = w, h = h, tx = -min_x, ty = -min_y, body = body, label_a = xml_escape(&label_a), label_b = xml_escape(&label_b)
    ))
}

fn xml_escape(s: &str) -> String {
    s.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mmp_core::EGraph;

    /// 🌟 実数座標評価器の正しさを、乱数MCTSの当たり外れに頼らず検証する。
    /// 三角形A,B,C + 外接円 + 中点 + 交点という典型的な構成を手で組み、
    /// (1) 外接円の中心が実際にA,B,Cから等距離であること、
    /// (2) 直線AB,ACの交点が実際にAと一致すること、
    /// を数値的に確認する。
    #[test]
    fn real_evaluator_produces_geometrically_consistent_shapes() {
        let mut egraph = EGraph::new();
        let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
        let ab = egraph.create_entity("AB".into(), Definition::new_line(a, b), EntityType::Line);
        let ac = egraph.create_entity("AC".into(), Definition::new_line(a, c), EntityType::Line);
        let m = egraph.create_entity("M".into(), Definition::Midpoint(b, c), EntityType::Point);
        let o = egraph.create_entity("O".into(), Definition::Circumcircle(a, b, c), EntityType::Circle);
        let inter = egraph.create_entity("Inter".into(), Definition::Intersection(ab, ac), EntityType::Point);

        let mut ev = RealEvaluator::new(&egraph, 42);
        let (pa, pb, pc) = (ev.point_of(a).unwrap(), ev.point_of(b).unwrap(), ev.point_of(c).unwrap());
        let (center, r) = ev.circle_of(o).unwrap();
        assert!((dist(center, pa) - r).abs() < 1e-6, "外接円の中心はAから半径分だけ離れているべき");
        assert!((dist(center, pb) - r).abs() < 1e-6, "外接円の中心はBから半径分だけ離れているべき");
        assert!((dist(center, pc) - r).abs() < 1e-6, "外接円の中心はCから半径分だけ離れているべき");

        let pm = ev.point_of(m).unwrap();
        assert!((pm.0 - (pb.0 + pc.0) / 2.0).abs() < 1e-9 && (pm.1 - (pb.1 + pc.1) / 2.0).abs() < 1e-9);

        let p_inter = ev.point_of(inter).unwrap();
        assert!(dist(p_inter, pa) < 1e-6, "AB∩ACはAそのものと一致するべき");
    }

    /// 🌟 調和共役の公式を、既知の解析解(0, 1, 2 → 2/3)で検証する
    /// (交比(0,1;2,d)=-1の標準的な結果)。
    #[test]
    fn harmonic_conjugate_matches_known_value() {
        let a = (0.0, 0.0);
        let b = (1.0, 0.0);
        let c = (2.0, 0.0);
        let d = harmonic_conjugate_real(a, b, c).unwrap();
        assert!((d.0 - 2.0 / 3.0).abs() < 1e-9, "既知の解析解2/3と一致するべき (実際: {:?})", d);
    }

    /// 🌟 render_svgが実際にwell-formedなSVGを生成し、a, bを含む全ての実体が
    /// 描画されること(座標が有限であること)を確認する。
    #[test]
    fn render_svg_end_to_end() {
        let mut egraph = EGraph::new();
        let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
        let ab = egraph.create_entity("AB".into(), Definition::new_line(a, b), EntityType::Line);
        let ac = egraph.create_entity("AC".into(), Definition::new_line(a, c), EntityType::Line);
        let o = egraph.create_entity("O".into(), Definition::Circumcircle(a, b, c), EntityType::Circle);
        let mut labels = FxHashMap::default();
        for (id, name) in [(a, "A"), (b, "B"), (c, "C"), (ab, "AB"), (ac, "AC"), (o, "O")] {
            labels.insert(id, name.to_string());
        }
        let order = vec![a, b, c, ab, ac, o];
        let svg = render_svg(&egraph, &order, &labels, a, b, 10).expect("非退化な配置なので描画できるべき");
        assert!(svg.contains("<svg"), "SVGタグを含むべき");
        assert!(svg.contains("<circle"), "円(O)と点の両方がcircle要素で表現されるべき");
        assert!(!svg.contains("NaN") && !svg.contains("inf"), "座標に非数・無限大が含まれてはならない");
    }
}

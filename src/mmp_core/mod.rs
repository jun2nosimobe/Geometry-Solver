use std::collections::{HashMap, HashSet};
use std::cell::Cell;
use crate::mmp_math::ModInt;

// mmp_core は図形の表現(e-graph)。型定義と基本操作(生成・union-find・接続)はこのファイルに置き、
// 残りは関心事ごとに分ける:
//   congruence        - 合同閉包 (merge_entities, propagate_*, apply_congruence_closure)
//   eval              - 数値評価と健全性チェック (evaluate_node, numeric_plausibility_check)
//   proof / raw_proof - 証明の復元と出力
//   construction      - 調和共役点など、複数の実体を作る補助構成
//   query             - is_connected など読み取り専用の問い合わせ
mod congruence;
mod eval;
mod proof;
mod construction;
mod query;
mod raw_proof;
pub use raw_proof::{RawProof, DeepProof};
#[cfg(test)]
mod tests;

// 1. 強力な型付きID (Newtype Pattern)
// オブジェクトの直接参照（ポインタ）を廃止し、すべてこのIDで管理する
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClassId(pub usize);

// 2. 図形の種類
// 方向・円・有向角には専用の型を持たせない。「特殊な場合」は型タグではなく、基準となる実体への接続で表す:
//   方向   = 無限遠直線 line_infinity 上の Point
//   円     = 円周点 circ_i, circ_j を通る Conic
//   有向角 = 無限遠直線上の4点の複比 (I,J;D1,D2) である Scalar
// 型をまとめるときは、候補プールが混ざらないかと、キャッシュの無効化が粗くならないか
// (angle_generation 参照)の両方を点検する。
// 経緯: docs/notes/mmp_core.md「Direction / Circle / Angle 型の撤廃」
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EntityType {
    Point, Line, Scalar,
    // 🌟 5点を通る一般二次曲線(Definition::ConicThrough5Points)。円も
    // (I,Jを通るという特殊な場合として)この型に含まれる。
    Conic,
}

// 3. 作図定義 (Algebraic Data Types)
// 文字列による判定を排除。コンパイラが引数の数や型を保証する。
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Definition {
    GivenPoint,
    FreePoint,
    Intersection(ClassId, ClassId),
    LineThroughPoints(ClassId, ClassId), // 順不同
    PerpendicularLine(ClassId, ClassId), // (Line, Point)
    Circumcircle(ClassId, ClassId, ClassId), // 順不同
    DirectionOf(ClassId),
    // 🌟 与えられた方向に垂直な方向。無限遠直線上の対合(involution)として
    // 垂直性を表す。perp(perp(D))=D という対合性を apply_trivial_relations で
    // 構造的に保証しておくことで、「同じ直線への垂線は全て平行」のような事実が
    // 専用の角度チェイス定理を経由せず、通常の合同閉包(f(a)=f(b) if a=b)だけで
    // 自動的に導かれるようになる。
    PerpDirectionOf(ClassId),
    AnglePair(ClassId, ClassId),
    Midpoint(ClassId, ClassId),
    LengthSq(ClassId, ClassId),
    TangentLine(ClassId, ClassId),
    ParallelLine(ClassId, ClassId),
    // 🌟 調和共役点: 直線上の3点A,B,Cに対する「A,Bを固定点とする対合」による
    // Cの像D。円錐曲線を一切使わず、完全四辺形(直線と交点だけ)で作図できる
    // 古典的な射影的構成。(A,B)の順序は不問(normalize_definitionでソート)。
    // この対合性(H(A,B,H(A,B,C))=C)や交叉比の対称性(H(A,B,C)=D ⟹ H(C,D,A)=B)を
    // apply_trivial_relationsで構造的に登録しておくことで、PerpDirectionOfと
    // 同じ要領で「通常の合同閉包(f(a)=f(b) if a=b)だけで自動的に従う事実」を
    // 専用定理なしに手に入れられる。
    HarmonicConjugateOf(ClassId, ClassId, ClassId),
    // 🌟 複比(A,B;C,D) (Scalar): 直線上の4点の射影不変量。4引数の置換のうち、
    // 値を厳密に保つのは4元クライン群V4={(A,B,C,D),(B,A,D,C),(C,D,A,B),
    // (D,C,B,A)}のみ(normalize_definitionでこの4通りの中からClassId辞書順
    // 最小を選ぶ)。残り20通りの置換は6種の異なる値(k,1/k,1-k,1/(1-k),
    // k/(k-1),(k-1)/k)を生むため、それぞれ別エンティティになり得るが、
    // 他のDefinitionと同様にmemoによる遅延生成なので、実際に定理/問題文が
    // 参照した組み合わせしか作られない(組み合わせ爆発はしない)。
    CrossRatio(ClassId, ClassId, ClassId, ClassId),
    // 🌟 共点な4直線がなす線束の複比 (Scalar)。直線の同次係数 (a,b,c) を双対平面の点とみなせば、
    // 点の複比と同じ calc_cross_ratio で計算できる。透視射影不変性を「点の複比 → 線束の複比 →
    // 別の直線上の点の複比」という2つの小さな定理(theorems.rs)に分けるための中継点。
    CrossRatioOfLines(ClassId, ClassId, ClassId, ClassId),
    // 🌟 固定された同次座標を持つ定数。円周点 I=(1,i,0), J=(1,-i,0) のような定点に使う
    // (法 998244353 は p≡1 (mod 4) なので i が体の中にある)。GivenPoint は常に (0,0,1) に
    // 評価されるので、任意の定数には使えない。
    ConstantHomogeneous(ModInt, ModInt, ModInt),
    // 🌟 5点を通る一般二次曲線(Ax²+Bxy+Cy²+Dxz+Eyz+Fz²=0、射影空間として
    // 5自由度)。Circumcircle(3点から円を復元)の一般化で、5点は完全に
    // 順不同(normalize_definitionでソート)。ユーザー提案「二次曲線の導入」
    // への最小限の対応として、この定義・数値評価・生成元5点の構造的な
    // 接続(Connected)判定までを実装し、接線・直線との交点計算は含まない。
    ConicThrough5Points(ClassId, ClassId, ClassId, ClassId, ClassId),
    // 🌟 2つのScalar値の積(順不同)。方冪の定理(PA・PB=PC・PD)のように
    // 「2辺の長さの積」を1つのScalarとして比較したい場合に使う。
    // LengthSq等と同じ「値,1,1」の3要素形式で評価される。
    Product(ClassId, ClassId),
    // 🌟 (known_point, line, conic): line と conic の交点のうち known_point ではない方。known_point は
    // 両方に乗っている前提なので、引数は順不同ではない。計算は
    // mmp_calculators::calc_second_intersection_of_line_and_conic。
    SecondIntersectionOfLineAndConic(ClassId, ClassId, ClassId),
    // 🌟 2円の根軸(方冪が等しい点の軌跡)。順不同。2円が交わらなくても定義される。
    // 計算は mmp_calculators::calc_radical_axis。
    RadicalAxis(ClassId, ClassId),
    // 🌟 同上。一方の交点が既知のときの「2円のもう一方の交点」。
    // (known_point, c1, c2) で、c1とc2は順不同。SecondIntersectionOfLineAnd
    // Conicの円×円版で、実装上も根軸を経由して同じ計算に帰着する。
    // 円と円の交点は一般には平方根を要する(=この有限体の中で作図できると
    // は限らない)が、「一方の交点が既に分かっている」という条件を付ければ
    // 有理的に作図できる ―― これはオリンピック幾何で「2円の第2交点」が
    // 常にこの形(共通点が1つ与えられている)で現れることと一致する。
    SecondIntersectionOfCircles(ClassId, ClassId, ClassId),
}

impl Definition {
    pub fn new_line(mut a: ClassId, mut b: ClassId) -> Self {
        if a.0 > b.0 { std::mem::swap(&mut a, &mut b); }
        Definition::LineThroughPoints(a, b)
    }

    /// 定理から参照できる作図の種類。定数・自由点・内部専用の定義は None。
    pub fn kind(&self) -> Option<DefKind> {
        use DefKind as K;
        Some(match self {
            Definition::Intersection(..) => K::Intersection,
            Definition::LineThroughPoints(..) => K::LineThroughPoints,
            Definition::PerpendicularLine(..) => K::PerpendicularLine,
            Definition::Circumcircle(..) => K::Circumcircle,
            Definition::DirectionOf(..) => K::DirectionOf,
            Definition::AnglePair(..) => K::AnglePair,
            Definition::Midpoint(..) => K::Midpoint,
            Definition::LengthSq(..) => K::LengthSq,
            Definition::TangentLine(..) => K::TangentLine,
            Definition::ParallelLine(..) => K::ParallelLine,
            Definition::CrossRatio(..) => K::CrossRatio,
            Definition::CrossRatioOfLines(..) => K::CrossRatioOfLines,
            Definition::ConicThrough5Points(..) => K::ConicThrough5Points,
            Definition::Product(..) => K::Product,
            Definition::SecondIntersectionOfLineAndConic(..) => K::SecondIntersectionOfLineAndConic,
            Definition::RadicalAxis(..) => K::RadicalAxis,
            Definition::SecondIntersectionOfCircles(..) => K::SecondIntersectionOfCircles,
            Definition::GivenPoint | Definition::FreePoint | Definition::PerpDirectionOf(_)
            | Definition::HarmonicConjugateOf(..) | Definition::ConstantHomogeneous(..) => return None,
        })
    }

    pub fn get_type_name(&self) -> &'static str {
        match self {
            Definition::Midpoint(_,_) => "Midpoint",
            Definition::DirectionOf(_) => "DirectionOf",
            Definition::PerpDirectionOf(_) => "PerpDirectionOf",
            Definition::LineThroughPoints(_,_) => "LineThroughPoints",
            Definition::Intersection(_,_) => "Intersection",
            Definition::AnglePair(_,_) => "AnglePair",
            Definition::GivenPoint => "GivenPoint",
            Definition::FreePoint => "FreePoint",
            Definition::Circumcircle(_,_,_) => "Circumcircle",
            Definition::PerpendicularLine(_,_) => "PerpendicularLine",
            Definition::LengthSq(_,_) => "LengthSq",
            Definition::TangentLine(_,_) => "TangentLine",
            Definition::ParallelLine(_,_) => "ParallelLine",
            Definition::HarmonicConjugateOf(_,_,_) => "HarmonicConjugateOf",
            Definition::CrossRatio(_,_,_,_) => "CrossRatio",
            Definition::CrossRatioOfLines(_,_,_,_) => "CrossRatioOfLines",
            Definition::ConstantHomogeneous(_,_,_) => "ConstantHomogeneous",
            Definition::ConicThrough5Points(_,_,_,_,_) => "ConicThrough5Points",
            Definition::Product(_,_) => "Product",
            Definition::SecondIntersectionOfLineAndConic(_,_,_) => "SecondIntersectionOfLineAndConic",
            Definition::RadicalAxis(_,_) => "RadicalAxis",
            Definition::SecondIntersectionOfCircles(_,_,_) => "SecondIntersectionOfCircles",
        }
    }

    pub fn get_parents(&self) -> Vec<ClassId> {
        match self {
            Definition::Midpoint(a, b) => vec![*a, *b],
            Definition::DirectionOf(a) => vec![*a],
            Definition::PerpDirectionOf(a) => vec![*a],
            Definition::LineThroughPoints(a, b) => vec![*a, *b],
            Definition::Intersection(a, b) => vec![*a, *b],
            Definition::AnglePair(a, b) => vec![*a, *b],
            Definition::PerpendicularLine(a, b) => vec![*a, *b],
            Definition::Circumcircle(a, b, c) => vec![*a, *b, *c],
            Definition::LengthSq(a, b) => vec![*a, *b],
            Definition::TangentLine(c, p) => vec![*c, *p],
            Definition::ParallelLine(l, p) => vec![*l, *p],
            Definition::HarmonicConjugateOf(a, b, c) => vec![*a, *b, *c],
            Definition::CrossRatio(a, b, c, d) => vec![*a, *b, *c, *d],
            Definition::CrossRatioOfLines(a, b, c, d) => vec![*a, *b, *c, *d],
            Definition::ConicThrough5Points(a, b, c, d, e) => vec![*a, *b, *c, *d, *e],
            Definition::Product(a, b) => vec![*a, *b],
            Definition::SecondIntersectionOfLineAndConic(p, l, c) => vec![*p, *l, *c],
            Definition::RadicalAxis(c1, c2) => vec![*c1, *c2],
            Definition::SecondIntersectionOfCircles(p, c1, c2) => vec![*p, *c1, *c2],
            _ => vec![],
        }
    }

    /// 🌟 MCTS/ActionGeneratorのために、この定義が生み出すエンティティの
    /// 型を機械的に返す。execute_constructions内のtarget_type判定とは
    /// 独立(あちらは定理テンプレート側が明示するのでこれを使わない)が、
    /// 「作図アクション候補としてどんな型の図形ができるか」を1箇所にまとめて
    /// おくことで、action_space.rs / mcts.rs 側の重複判定を避ける。
    pub fn default_entity_type(&self) -> EntityType {
        match self {
            Definition::LineThroughPoints(_, _) => EntityType::Line,
            Definition::PerpendicularLine(_, _) => EntityType::Line,
            Definition::ParallelLine(_, _) => EntityType::Line,
            Definition::TangentLine(_, _) => EntityType::Line,
            Definition::Intersection(_, _) => EntityType::Point,
            Definition::Midpoint(_, _) => EntityType::Point,
            Definition::HarmonicConjugateOf(_, _, _) => EntityType::Point,
            Definition::Circumcircle(_, _, _) => EntityType::Conic,
            Definition::DirectionOf(_) => EntityType::Point,
            Definition::PerpDirectionOf(_) => EntityType::Point,
            Definition::AnglePair(_, _) => EntityType::Scalar,
            Definition::LengthSq(_, _) => EntityType::Scalar,
            Definition::CrossRatio(_, _, _, _) => EntityType::Scalar,
            Definition::CrossRatioOfLines(_, _, _, _) => EntityType::Scalar,
            Definition::GivenPoint | Definition::FreePoint => EntityType::Point,
            // 🌟 円周点I,Jのように「同次座標を持つ定数」は、デフォルトでは
            // Point(GivenPoint/FreePointと同じ)として扱っておく。circ_i/circ_j
            // も(EntityType::Direction撤廃により)実際にPointとして作られ、
            // L∞上にあるという事実はlink_logical_incidence(EGraph::new参照)で
            // 別途表現するので、ここは特別扱い不要でそのままフォールバックとして使える。
            Definition::ConstantHomogeneous(_, _, _) => EntityType::Point,
            Definition::ConicThrough5Points(_, _, _, _, _) => EntityType::Conic,
            Definition::Product(_, _) => EntityType::Scalar,
            Definition::SecondIntersectionOfLineAndConic(_, _, _) => EntityType::Point,
            Definition::RadicalAxis(_, _) => EntityType::Line,
            Definition::SecondIntersectionOfCircles(_, _, _) => EntityType::Point,
        }
    }
}

/// 定理のパターン・作図テンプレートが名指しする作図の種類。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefKind {
    Intersection,
    LineThroughPoints,
    PerpendicularLine,
    Circumcircle,
    DirectionOf,
    AnglePair,
    Midpoint,
    LengthSq,
    TangentLine,
    ParallelLine,
    CrossRatio,
    CrossRatioOfLines,
    ConicThrough5Points,
    Product,
    SecondIntersectionOfLineAndConic,
    RadicalAxis,
    SecondIntersectionOfCircles,
}

/// 親の並べ方の自由度。DefinedBy のマッチで、1つの定義から親変数への割り当てを何通り試すかを決める。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParentSymmetry {
    /// 親の順序に意味がある。
    Ordered,
    /// 親を任意に並べ替えてよい(2点・3点のみ全順列を試す)。
    Unordered,
    /// 複比: 値を保つクライン4群 V4 の4通りだけ。
    KleinFour,
}

impl DefKind {
    pub fn name(self) -> &'static str {
        match self {
            DefKind::Intersection => "Intersection",
            DefKind::LineThroughPoints => "LineThroughPoints",
            DefKind::PerpendicularLine => "PerpendicularLine",
            DefKind::Circumcircle => "Circumcircle",
            DefKind::DirectionOf => "DirectionOf",
            DefKind::AnglePair => "AnglePair",
            DefKind::Midpoint => "Midpoint",
            DefKind::LengthSq => "LengthSq",
            DefKind::TangentLine => "TangentLine",
            DefKind::ParallelLine => "ParallelLine",
            DefKind::CrossRatio => "CrossRatio",
            DefKind::CrossRatioOfLines => "CrossRatioOfLines",
            DefKind::ConicThrough5Points => "ConicThrough5Points",
            DefKind::Product => "Product",
            DefKind::SecondIntersectionOfLineAndConic => "SecondIntersectionOfLineAndConic",
            DefKind::RadicalAxis => "RadicalAxis",
            DefKind::SecondIntersectionOfCircles => "SecondIntersectionOfCircles",
        }
    }

    /// 作図名の接頭辞(DirectionOf だけ短く Dir)。
    pub fn label(self) -> &'static str {
        if self == DefKind::DirectionOf { "Dir" } else { self.name() }
    }

    pub fn arity(self) -> usize {
        match self {
            DefKind::DirectionOf => 1,
            DefKind::Circumcircle | DefKind::SecondIntersectionOfLineAndConic
            | DefKind::SecondIntersectionOfCircles => 3,
            DefKind::CrossRatio | DefKind::CrossRatioOfLines => 4,
            DefKind::ConicThrough5Points => 5,
            _ => 2,
        }
    }

    pub fn parent_symmetry(self) -> ParentSymmetry {
        match self {
            DefKind::Midpoint | DefKind::LineThroughPoints | DefKind::Intersection
            | DefKind::LengthSq | DefKind::Circumcircle => ParentSymmetry::Unordered,
            DefKind::CrossRatio | DefKind::CrossRatioOfLines => ParentSymmetry::KleinFour,
            _ => ParentSymmetry::Ordered,
        }
    }

    /// 正規化前の定義を組み立てる。親の数が合わなければ None。
    /// 呼び出し側は EGraph::build_definition を使うこと(memo のキーは正規化済み)。
    fn raw(self, p: &[ClassId]) -> Option<Definition> {
        if p.len() != self.arity() { return None; }
        Some(match self {
            DefKind::Intersection => Definition::Intersection(p[0], p[1]),
            DefKind::LineThroughPoints => Definition::LineThroughPoints(p[0], p[1]),
            DefKind::PerpendicularLine => Definition::PerpendicularLine(p[0], p[1]),
            DefKind::Circumcircle => Definition::Circumcircle(p[0], p[1], p[2]),
            DefKind::DirectionOf => Definition::DirectionOf(p[0]),
            DefKind::AnglePair => Definition::AnglePair(p[0], p[1]),
            DefKind::Midpoint => Definition::Midpoint(p[0], p[1]),
            DefKind::LengthSq => Definition::LengthSq(p[0], p[1]),
            DefKind::TangentLine => Definition::TangentLine(p[0], p[1]),
            DefKind::ParallelLine => Definition::ParallelLine(p[0], p[1]),
            DefKind::CrossRatio => Definition::CrossRatio(p[0], p[1], p[2], p[3]),
            DefKind::CrossRatioOfLines => Definition::CrossRatioOfLines(p[0], p[1], p[2], p[3]),
            DefKind::ConicThrough5Points => Definition::ConicThrough5Points(p[0], p[1], p[2], p[3], p[4]),
            DefKind::Product => Definition::Product(p[0], p[1]),
            DefKind::SecondIntersectionOfLineAndConic => Definition::SecondIntersectionOfLineAndConic(p[0], p[1], p[2]),
            DefKind::RadicalAxis => Definition::RadicalAxis(p[0], p[1]),
            DefKind::SecondIntersectionOfCircles => Definition::SecondIntersectionOfCircles(p[0], p[1], p[2]),
        })
    }
}

// 4. E-Graph (環境とUnion-Findの統合)
#[derive(Clone)]
pub struct EGraph {
    pub entities: Vec<GeoEntity>,
    parents: Vec<Cell<usize>>,
    pub memo: HashMap<Definition, ClassId>,
    pub ang90: ClassId,
    pub ang0: ClassId,
    // 🌟 無限遠直線: 全ての「方向(Direction)」エンティティをこの直線上の点として
    // 構造的にリンクしておくための定数ノード。これにより「2直線が平行」は
    // 「無限遠直線上の同じ点(=同じ方向)を共有している」という、通常の点の
    // 共有と全く同じ形の関係として扱えるようになり、propagate_line_uniqueness /
    // propagate_point_uniqueness の局所伝播をそのまま使い回せる。
    // 定理(有向角の加法性・交替律・円周角の定理など)は Definition::DirectionOf
    // を通じて方向をそのまま参照し続けるので、この追加はパターンには一切影響しない。
    pub line_infinity: ClassId,
    // 🌟 円周点 I, J。有向角 AnglePair(D1,D2) は無限遠直線上の4点の複比 (I,J;D1,D2) として
    // 評価する(eval.rs)。この複比は加法性・交替律をそのまま満たすので、角度の定理は値の計算式に
    // 依存しない。円は I,J を通る Conic として表す。
    pub circ_i: ClassId,
    pub circ_j: ClassId,
    pub worklist: Vec<ClassId>, // 🌟 NEW: マージが発生して再評価が必要なIDキュー

    // 🌟 証明復元(explain)のための「証明の森」。
    // 通常のunion-find(parents)は経路圧縮するため、最終的な代表元は分かっても
    // 「なぜ」その2つが同じになったのかという履歴は失われる。そこで union が
    // 実際に起きるたびに、吸収された側(root2)から生き残った側(root1)への
    // 有向辺として、その理由(Justification)を別に記録しておく。
    // キーは「吸収された側」の(union-find上の)生スロット番号なので、
    // 一度書き込まれたら二度と上書きされない(その番号が再びrootになることはない)。
    // ある2つのエンティティが同値であることを説明したい時は、両方から
    // この森を根に向かって辿り、共通の根で合流させれば良い(explain_identical)。
    pub proof_edges: rustc_hash::FxHashMap<usize, ProofEdge>,
    // 🌟 「点PはこのCircleに乗っている」のような接続関係(incidence)がいつ・なぜ
    // 成り立ったかの記録。Concyclicの目標(共円であることの証明)を復元する時に使う。
    // キーは(小さい方のClassId, 大きい方のClassId)。
    pub incidence_provenance: rustc_hash::FxHashMap<(ClassId, ClassId), Justification>,
    // 🌟 数値評価(eval.rs)が偶然の一致(log_conjecture_candidate)を検出した
    // ときに蓄積する「証明されていないが数値的根拠のある予想」。通常の証明
    // 状態(parents/memo/subobjects)とは完全に独立しており、証明の健全性には
    // 一切影響しない。BlackboardEngine::process_pending_conjecturesが読み出し、
    // 使い捨てのクローン上での価値推定を経てheat_bonusへのフィードバックだけに
    // 使う(現実のegraphへ直接マージされることは無い)。
    // Cell/RefCellを使うのは、numeric_plausibility_check系の呼び出し連鎖
    // (evaluate_node等)が&selfのみで完結する設計を崩したくないため
    // (mmp_tester.rs等、既存の全ての呼び出し元は&EGraphしか渡さない)。
    // キーは正規化された(小さい方の代表元インデックス, 大きい方の代表元インデックス)。
    pub conjectures: std::cell::RefCell<rustc_hash::FxHashMap<(usize, usize), ConjectureEntry>>,
    // 🌟 union-find の併合が実際に起きるたびに増えるカウンタ。rejected_conic_pairs が
    // 「却下してから一度もマージが起きていないか」を判定するのに使う。
    pub merge_generation: u64,
    // 🌟 propagate_conic_uniqueness で数値チェックが却下したペア。キーは代表元インデックスの
    // (小, 大)、値は却下したときの merge_generation。その後マージが起きていなければ再チェックしても
    // 結果は同じなので飛ばす(円は同じ点集合の上に重複が積み上がりやすく、同じ却下の繰り返しが
    // 時間の大半を食うことがある)。
    pub rejected_conic_pairs: rustc_hash::FxHashMap<(usize, usize), u64>,
    /// 数値検証・次数測定に使う乱数の状態(EGraph::random_modint)。シード固定なので、
    /// 同じ問題は毎回同じ座標で検算する。
    rng_state: Cell<u64>,
    // 🌟 EntityType ごとの生成済み ClassId の一覧。create_entity で追記するだけでマージでは消さないので、
    // 使う側は get_rep で代表元に直す(iter_reps_of_type)。定理マッチングが特定の型の実体を探すときに
    // 全件を走査しないための索引。
    pub type_index: rustc_hash::FxHashMap<EntityType, Vec<ClassId>>,
    // 🌟 EntityType ごとの「その型のマッチング候補(実体・接続・memo)が最後に変わった世代」。
    // 失敗キャッシュ(logic_core の failed_paths)や型ごとのキャッシュの無効化判定に使う。
    // 不変条件: components / subobjects / uses / memo を書き換えるのは create_entity /
    // merge_entities / link_logical_incidence / insert_memo の4つのゲートウェイだけで、それぞれが
    // note_type_changed を呼ぶ。書き込み経路を足すときは必ずゲートウェイを通す(通知漏れは
    // エラーにならず、探索の取りこぼしとして静かに効く)。
    pub type_generation: rustc_hash::FxHashMap<EntityType, u64>,
    /// 🌟 EntityTypeごとの実体数のキャッシュ。(数えた世代, 個数)を持ち、
    /// type_generation が動いていなければ数え直さない。
    pub(crate) type_counts: std::cell::RefCell<rustc_hash::FxHashMap<EntityType, (u64, usize)>>,
    /// 🌟 Scalar のうち有向角(AnglePair)が絡む変化だけで増える世代(angle_generation)と、それ以外の
    /// Scalar の変化だけで増える世代(plain_scalar_generation)。角度の自己束縛候補のキャッシュ
    /// (logic_core::cost の identical_self_bind_angle_cache)を、長さや積が作られるたびに捨てないよう、
    /// type_generation[Scalar] とは別に持つ。更新するのは create_entity / merge_entities / insert_memo
    /// (接続の追加は Scalar の代表元集合を変えないので対象外)。
    pub angle_generation: u64,
    pub plain_scalar_generation: u64,
    // 🌟 退化のもとで関連が観測された実体の組(padic_eval.rs)。Some のときだけ bump_heat_bonus が
    // 同じ組の他の実体にもボーナスを伝播する。既定は None で、何も計算しない。
    pub degeneration_groups: Option<crate::padic_eval::DegenerationRelations>,
    // 🌟 bump_heat_bonus が退化グループの他の実体に伝播するボーナスの割合(0.5 = 元の半分)。
    // --degen-heat-factor=X で変えられる。
    pub degeneration_heat_factor: f64,
    /// 🌟 いま作られる図形に刻む出どころ。既定は Given (問題文) で、オンデマンド
    /// 作図などの呼び出し側が set_origin で一時的に差し替える。
    pub current_origin: EntityOrigin,
    /// apply_trivial_relations の入れ子の深さ。0 より大きい間に作られた図形は
    /// 「付随して生えたもの」として印を付ける。
    pub trivial_depth: u32,
}

/// 🌟 1つの予想候補(数値的な偶然の一致)の記録。
#[derive(Debug, Clone)]
pub struct ConjectureEntry {
    /// この一致が何を示唆しているか(例: "2点が同一点である")
    pub hypothesis: String,
    /// 独立した乱数試行で何回観測されたか(1回でも約10億分の1の偶然でしか
    /// 起こらないほぼ確実な兆候だが、多いほど確信度の目安になる)
    pub occurrences: u32,
    /// process_pending_conjecturesで既に価値評価(estimate_conjecture_value)
    /// 済みかどうか。同じ予想を何度も再評価しないための重複排除フラグ。
    pub tested: bool,
}

/// 🌟 estimate_conjecture_valueの結果。
#[derive(Debug, Clone, Copy)]
pub struct ConjectureValue {
    /// 予想を仮定して合同閉包だけを走らせた時に、追加でいくつの同値類が
    /// 統合された(=マージが起きた)か。
    pub additional_merges: usize,
    /// その仮定だけで(定理マッチングなしに)証明目標に到達したか。
    pub target_reached: bool,
}

/// 🌟 なぜこの等式(またはこの接続関係)が成り立つのかの理由。
/// 証明復元(generate_proof)がこれを人間可読な文字列に変換する。
#[derive(Debug, Clone)]
pub enum Justification {
    /// 問題の初期条件・作図の前提として直接与えられた
    Given,
    /// 定理の結論として導かれた。premisesはこの定理が実際に使った前提事実
    /// (パターン中のFact節をbindで解決したもの)だけを保持し、
    /// そのマッチで偶然一緒に束縛されていただけの無関係な図形は含まない
    /// (Python版がbind.values()を丸ごと前提として記録し、無関係な図形まで
    /// 証明ツリーに混入していた問題への対処)。
    Theorem {
        name: String,
        premises: Vec<(String, Vec<ClassId>)>,
    },
    /// 通常の合同閉包: 同じ定義(Definition)が正規化した結果一致した
    /// (f(a)=f(b) if a=b)。
    Congruence { definition: String },
    /// 「直線の一致条件」局所伝播: 2直線が十分な数の点/方向を共有していた
    LineUniqueness { shared_points: Vec<ClassId> },
    /// 「2直線の交点の一意性」局所伝播
    PointUniqueness { via_lines: (ClassId, ClassId) },
    /// 🌟 「円の一致条件」局所伝播: 2つのCircumcircle等が3点以上を共有していた
    /// (直線は2点、円は3点で一意に決まるという違いだけで、propagate_line_uniqueness
    /// と全く同じ発想)。HAGeo-409ベンチマークの調査で、同じ4点が乗っている
    /// はずのCircumcircle(A,B,C)とCircumcircle(A,B,D)が別実体のまま統合されず、
    /// エンティティ数の肥大化と証明の断絶を引き起こしていたことが分かったため追加。
    ConicUniqueness { shared_points: Vec<ClassId> },
    /// apply_trivial_relations由来の構造的な結合(垂線→Ang90、
    /// PerpDirectionOf/HarmonicConjugateOfの対合性など、定義から機械的に従うもの)
    Trivial { reason: String },
}

#[derive(Debug, Clone)]
pub struct ProofEdge {
    pub from: ClassId,
    pub to: ClassId,
    pub justification: Justification,
}

impl EGraph {
    pub fn new() -> Self {
        let mut egraph = Self {
            entities: Vec::new(),
            parents: Vec::new(),
            memo: HashMap::new(),
            ang90: ClassId(0), // ダミー初期化
            ang0: ClassId(0),
            line_infinity: ClassId(0),
            circ_i: ClassId(0),
            circ_j: ClassId(0),
            worklist: Vec::new(),
            proof_edges: rustc_hash::FxHashMap::default(),
            incidence_provenance: rustc_hash::FxHashMap::default(),
            conjectures: std::cell::RefCell::new(rustc_hash::FxHashMap::default()),
            merge_generation: 0,
            rejected_conic_pairs: rustc_hash::FxHashMap::default(),
            rng_state: Cell::new(0x5EED_6E0_5017_E5),
            type_index: rustc_hash::FxHashMap::default(),
            type_generation: rustc_hash::FxHashMap::default(),
            type_counts: std::cell::RefCell::new(rustc_hash::FxHashMap::default()),
            angle_generation: 0,
            plain_scalar_generation: 0,
            degeneration_groups: None,
            degeneration_heat_factor: 0.5,
            current_origin: EntityOrigin::Given,
            trivial_depth: 0,
        };
        // 🌟 定数ノードの生成 (GivenPointをプレースホルダとして利用)
        egraph.ang90 = egraph.create_entity("Ang90".to_string(), Definition::GivenPoint, EntityType::Scalar);
        egraph.ang0 = egraph.create_entity("Ang0".to_string(), Definition::GivenPoint, EntityType::Scalar);
        egraph.line_infinity = egraph.create_entity("Line_infinity".to_string(), Definition::GivenPoint, EntityType::Line);
        // 🌟 円周点 I=(1,i,0), J=(1,-i,0) (i=√-1)。このプロジェクトの法
        // 998244353 は p≡1(mod4) なので体内に平方根が存在し、原始根3を使って
        // i = 3^((p-1)/4) と求まる(Tonelli-Shanksを持ち出すまでもない、
        // NTT-friendly素数の標準的なトリック)。i²≡-1(mod p)であることは
        // 事前に検証済み。
        let i = ModInt::new(3).pow((crate::mmp_math::PRIME - 1) / 4);
        let neg_i = -i;
        egraph.circ_i = egraph.create_entity("CircI".to_string(), Definition::ConstantHomogeneous(ModInt::new(1), i, ModInt::new(0)), EntityType::Point);
        egraph.circ_j = egraph.create_entity("CircJ".to_string(), Definition::ConstantHomogeneous(ModInt::new(1), neg_i, ModInt::new(0)), EntityType::Point);
        // 🌟 I,J は無限遠直線上の点なので、他の方向と同じく L∞ への接続で表す
        // (ConstantHomogeneous の apply_trivial_relations には該当する分岐が無いので、ここで張る)。
        egraph.link_logical_incidence(egraph.circ_i, egraph.line_infinity);
        egraph.link_logical_incidence(egraph.circ_j, egraph.line_infinity);
        egraph
    }

    // 🌟 heat_bonus を足す唯一の入口。degeneration_groups が Some なら、直接関連が観測された他の実体にも
    // degeneration_heat_factor 倍のボーナスを伝播する(推移閉包は取らない ― 異なる退化パターンの関係まで
    // 合併されて悪化した)。None なら entities[rep].heat_bonus += amount と同じ。
    pub fn bump_heat_bonus(&mut self, id: ClassId, amount: f64) {
        let rep = self.get_rep(id);
        self.entities[rep.0].heat_bonus += amount;
        // members_of は &self のみ(直接観測された辺を返すだけで推移閉包を
        // 取らないため経路圧縮も不要)なので、この不変借用はここで完結し、
        // 以降のself.entitiesへの可変アクセスと衝突しない。
        let members = match &self.degeneration_groups {
            Some(rel) => rel.members_of(rep),
            None => return,
        };
        let factor = self.degeneration_heat_factor;
        for m in members {
            let m_rep = self.get_rep(m);
            if m_rep != rep {
                self.entities[m_rep.0].heat_bonus += amount * factor;
            }
        }
    }

    // Union-Find: 代表元の取得 (経路圧縮付き)
    pub fn get_rep(&self, id: ClassId) -> ClassId {
        let mut curr = id.0;
        while self.parents[curr].get() != curr {
            let p = self.parents[curr].get();
            self.parents[curr].set(self.parents[p].get());
            curr = p;
        }
        ClassId(curr)
    }

    // 🌟 Hash Consingによる図形の生成
    pub fn create_entity(&mut self, name: String, def: Definition, e_type: EntityType) -> ClassId {
        let should_memoize = !matches!(def, Definition::FreePoint | Definition::GivenPoint);

        // 🌟 FIX: キャッシュを検索する前に必ず定義を正規化（ソート）する
        let norm_def = if should_memoize {
            self.normalize_definition(&def)
        } else {
            def.clone()
        };

        if should_memoize {
            // 正規化済みのシグネチャで検索するため、順序逆転による重複生成が完全に防がれる
            if let Some(&existing_id) = self.memo.get(&norm_def) {
                return self.get_rep(existing_id);
            }
        }

        let id = ClassId(self.entities.len());
        let entity = GeoEntity {
            id, original_name: name.clone(), name, entity_type: e_type,
            base_importance: 1.0, heat_bonus: 0.0,
            components: vec![LogicalComponent { definitions: vec![norm_def.clone()], subobjects: Vec::new() }],
            original_definition: norm_def.clone(),
            uses: rustc_hash::FxHashSet::default(),
            mcts_depth: 0,
            degree_cache: std::cell::Cell::new(None),
            origin: self.current_origin,
            origin_cascade: self.trivial_depth > 0,
        };

        self.entities.push(entity);
        self.parents.push(Cell::new(id.0));
        self.type_index.entry(e_type).or_default().push(id);
        // 🌟 新規エンティティの誕生そのものが「この型の候補集合が変わった」
        // 変化点(note_type_changedのドキュメント参照)。
        self.note_type_changed(e_type);
        // 🌟 angle_generation/plain_scalar_generationのドキュメント参照。
        if e_type == EntityType::Scalar {
            self.note_scalar_kind_changed(matches!(norm_def, Definition::AnglePair(_, _)));
        }

        for p in norm_def.get_parents() {
            let p_rep = self.get_rep(p);
            self.entities[p_rep.0].uses.insert(id);
        }

        if should_memoize {
            self.insert_memo(norm_def.clone(), id);
        }

        self.apply_trivial_relations(id, &norm_def);
        id
    }

    /// 🌟 このEntityTypeの実体数。logic_core::cost の estimate_cost が Connected(未束縛, 未束縛) の
    /// 見積もりのために DFS の各ノードで呼ぶので、type_generation が動いていなければ前回の値を返す
    /// (値は全走査と同じ)。
    pub fn count_of_type(&self, ty: EntityType) -> usize {
        let current = self.type_generation.get(&ty).copied().unwrap_or(0);
        if let Some(&(cached_gen, n)) = self.type_counts.borrow().get(&ty)
            && cached_gen == current { return n; }
        let n = self.entities.iter().filter(|e| e.entity_type == ty).count();
        self.type_counts.borrow_mut().insert(ty, (current, n));
        n
    }

    /// 🌟 type_generationのドキュメント参照。EGraphの生の構造フィールド
    /// (entities[..].components/subobjects/uses/self.memo)を書き換える
    /// create_entity/merge_entities/link_logical_incidence/insert_memoの
    /// 4つのゲートウェイだけがこれを呼ぶ――呼び出し忘れが起きないよう、
    /// 「新しいゲートウェイを追加するときは必ずここも呼ぶ」という単純な
    /// ルール1つに集約している。
    fn note_type_changed(&mut self, et: EntityType) {
        *self.type_generation.entry(et).or_insert(0) += 1;
    }

    /// 🌟 angle_generation/plain_scalar_generationのドキュメント参照。
    /// EntityType::Scalarに関する変化(生成・併合)が起きたときだけ、
    /// note_type_changedに加えて呼ぶ。is_angleは「この変化がAnglePair側
    /// (角度)か、それ以外のScalar(長さ・積・複比等)側か」を呼び出し側が
    /// 判定して渡す。
    fn note_scalar_kind_changed(&mut self, is_angle: bool) {
        if is_angle {
            self.angle_generation += 1;
        } else {
            self.plain_scalar_generation += 1;
        }
    }

    /// 🌟 self.memo への書き込みはここだけ。memo への登録は defined_by_valid_nodes などの memo 検索の
    /// 結果を変えるので、登録した実体の型を note_type_changed に通知する。
    fn insert_memo(&mut self, def: Definition, id: ClassId) {
        let et = self.entities[id.0].entity_type;
        // 🌟 angle_generation/plain_scalar_generationのドキュメント参照。
        // memoへの新規登録もdefined_by_valid_nodes等の列挙結果を変え得る、
        // note_type_changedと同格の「型の候補集合が変わった」変化点なので、
        // 同じ判定をここでも行う。
        if et == EntityType::Scalar {
            self.note_scalar_kind_changed(matches!(def, Definition::AnglePair(_, _)));
        }
        self.memo.insert(def, id);
        self.note_type_changed(et);
    }

    /// 🌟 type_indexを使い、指定した型を持つ「現在の代表元」だけを列挙する。
    /// type_index自体は吸収された側のClassIdも保持したままの単調増加リストなので、
    /// ここで必ずget_rep()により正規化し、代表元でなくなったものを除外する。
    /// 同じ代表元がuses等の経路で重複して積まれることは無い(1エンティティ
    /// につきtype_indexへの登録はcreate_entity内で1回だけ)ため、重複排除は不要。
    pub fn iter_reps_of_type(&self, et: EntityType) -> impl Iterator<Item = ClassId> + '_ {
        self.type_index.get(&et).into_iter().flatten()
            .copied()
            .filter(move |&id| self.get_rep(id) == id)
    }

    /// 🌟 定理マッチングの型シグネチャ事前フィルタ(logic_core.rs::schedule_full_sweep)
    /// が使う、「この型のエンティティが1つでも存在するか」の軽量な判定。
    /// type_indexへの登録は吸収後も残るので、空でなければ(たとえ全て吸収済みの
    /// 代表元でなくなっていたとしても、その型自体は少なくとも一度は作られている
    /// ため)実質的に「今この型の代表元が存在するか」の判定として十分安全。
    pub fn has_entity_of_type(&self, et: EntityType) -> bool {
        self.type_index.get(&et).is_some_and(|v| !v.is_empty())
    }
}

// 5. 論理コンポーネントと実体
#[derive(Debug, Clone)]
pub struct LogicalComponent {
    pub definitions: Vec<Definition>,
    // 🌟 挿入順を保つ Vec(重複除去は link_logical_incidence / merge_entities 側で行う)。HashSet に
    // すると反復順序がプロセスごとに変わり、局所伝播や候補列挙の順序、ひいては探索の結果が実行のたびに
    // ぶれる。
    pub subobjects: Vec<ClassId>,
}

/// 🌟 ClassId列から重複を除き、ClassId昇順に整列した決定的な順序のVecを作る。
/// 内部で使うHashSetは`.insert()`による所属判定だけに使い、絶対に反復しない
/// (反復するとその時点でHashSetのランダムな順序に逆戻りしてしまう)。
/// 最終的な順序は入力側の反復順にも依存しない、完全に再現可能なものになる。
pub(crate) fn dedup_sorted_ids(ids: impl IntoIterator<Item = ClassId>) -> Vec<ClassId> {
    let mut seen = HashSet::new();
    let mut out: Vec<ClassId> = ids.into_iter().filter(|id| seen.insert(*id)).collect();
    out.sort_by_key(|id| id.0);
    out
}

/// 🌟 その図形を「誰が作ったか」。create_entity で一度だけ刻み、マージでは書き換えない。
/// オンデマンド作図やマッチャのその場生成が証明に効いているかを後から測る(--origins)ためのもの。
/// 名前の接尾辞 (Auto) では事後に区別できないので、作る側で印を付ける。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum EntityOrigin {
    /// 問題文(あるいは作図スクリプト)で最初から与えられたもの。
    Given,
    /// 定理のマッチングが DefinedBy パターンを満たすためにその場で作ったもの
    /// (logic_core::matcher::defined_by_valid_nodes)。
    DefinedBy,
    /// 定理の結論テンプレート(constructions)が作ったもの。
    Construct,
    /// 需要駆動の補助線 (resolve_demands)。
    LineDemand,
    /// 需要駆動の交点 (resolve_point_demands)。
    PointDemand,
    /// 需要駆動の中点 (resolve_midpoint_demands)。
    MidDemand,
    /// 直線と円・円と円のもう一方の交点 (resolve_second_intersection_demands)。
    SecondDemand,
    /// 需要駆動の角・方向 (resolve_angle_demands)。
    AngleDemand,
    /// 目標駆動の補助線・複比 (resolve_target_demands / resolve_cross_ratio_demands)。
    TargetDemand,
    /// MCTS が選んだ補助構成。
    Mcts,
    /// 調和共役点の完全四辺形作図 (construct_harmonic_conjugate)。
    Harmonic,
}

impl EntityOrigin {
    /// 表示用の短い名前。
    pub fn label(&self) -> &'static str {
        match self {
            EntityOrigin::Given => "問題文",
            EntityOrigin::DefinedBy => "DefinedBy生成",
            EntityOrigin::Construct => "定理の結論",
            EntityOrigin::LineDemand => "需要:補助線",
            EntityOrigin::PointDemand => "需要:交点",
            EntityOrigin::MidDemand => "需要:中点",
            EntityOrigin::SecondDemand => "需要:もう一方の交点",
            EntityOrigin::AngleDemand => "需要:角/方向",
            EntityOrigin::TargetDemand => "目標駆動",
            EntityOrigin::Mcts => "MCTS",
            EntityOrigin::Harmonic => "調和共役作図",
        }
    }

    /// 報告で並べる順。
    pub const ALL: &'static [EntityOrigin] = &[
        EntityOrigin::Given, EntityOrigin::DefinedBy, EntityOrigin::Construct,
        EntityOrigin::LineDemand, EntityOrigin::PointDemand, EntityOrigin::SecondDemand, EntityOrigin::MidDemand,
        EntityOrigin::AngleDemand, EntityOrigin::TargetDemand, EntityOrigin::Mcts,
        EntityOrigin::Harmonic,
    ];
}

#[derive(Debug, Clone)]
pub struct GeoEntity {
    pub id: ClassId,
    // 🌟 表示用の名前。merge_entitiesで「短い方が勝つ」ヒューリスティックにより、
    // 生き残った側(union-find上のroot)のものであっても後から書き換わることがある
    // (例: "Ang_APB"というrootが"Ang90"を吸収すると、rootの.nameが短い"Ang90"に
    // 上書きされる)。そのため「このClassIdは元々何という名前だったか」を
    // 証明復元(generate_proof)で正確に知りたい場合はoriginal_nameを使うこと。
    pub name: String,
    // 🌟 create_entity時に一度だけ設定され、以後マージが起きても絶対に
    // 書き換えられない、そのスロット固有の不変な名前。証明復元が
    // 「そのステップの時点でこの図形が何と呼ばれていたか」を正確に表示するために
    // 導入した(これが無いと、生き残った側の名前が後から短い名前に上書きされて
    // しまい、証明の途中経過が実際の推論内容と食い違って見えることがあった)。
    pub original_name: String,
    pub entity_type: EntityType,
    pub base_importance: f64,
    pub heat_bonus: f64,
    pub components: Vec<LogicalComponent>,
    // 🌟 create_entity 時の元の定義。merge_entities で吸収された側の components は空になるので、
    // 「このIDは元々どんな定義で作られたか」をここで保つ。raw_proof::dump_raw_proof が DefinedBy 前提の
    // 本当の出どころ(最初にその定義を持っていた実体と、そこから result までの合流経路)を特定するのに使う。
    pub original_definition: Definition,
    pub uses: rustc_hash::FxHashSet<ClassId>,
    // 🌟 MCTSが自由な探索で作った補助構成が、他のMCTS補助構成の上にさらに
    // 積み重なった「連鎖の深さ」(mcts.rs::apply_action参照)。問題文で最初から
    // 与えられている点・直線や、需要駆動(resolve_demands等)の補助線はこの値を
    // 一切更新しないため常に0のままで、この上限による制限を受けない。MCTSが
    // MCTS自身の産物の上に何段も構成を積み増す(例:中点のまた中点のまた中点…)
    // ことだけを対象にした、ローカルな連鎖専用のカウンタ。
    pub mcts_depth: usize,
    // 🌟 動点法の次数(measure_numerical_degree)のメモ。None=未計算、Some(None)=測定不能、
    // Some(Some(d))=次数d。マッチングのホットパスから &self のまま読み書きするための Cell。
    pub degree_cache: std::cell::Cell<Option<Option<usize>>>,
    // 🌟 この図形を「誰が作ったか」(EntityOrigin 参照)。
    pub origin: EntityOrigin,
    // 🌟 上の origin が「直接そう頼まれて作られた」のか、「その作図に付随して
    // apply_trivial_relations が芋づる式に作った」のかの区別。補助線を1本引く
    // だけで方向・長さ等が何個も派生するので、分けないと「作った数」が実態より
    // 何倍にも見えてしまう。
    pub origin_cascade: bool,
}

// 🌟 「何が面白い図形か」を表す熱量の式は、ここの heat / heat_with_degree の2つだけに置く。
// DFS の束縛順序・コスト見積もり・MCTS の行動の重みは、式を直接書かずにどちらかを呼ぶ。
impl GeoEntity {
    /// 熱(heat_bonus) + 基本重要度(base_importance)。「直近マージされた/
    /// 予想の裏付けが取れた」対象を優先するための、次数を含まない素の熱量。
    pub fn heat(&self) -> f64 {
        self.base_importance + self.heat_bonus
    }

    /// heat() + 次数ボーナス(uses.len()による依存度、0.5倍)。この実体に
    /// 依存する他の実体が多いほど「図の中で参照され尽くしている=重要な
    /// 構成要素」とみなして優先度を上げる、calc_bind_heat/estimate_cost/
    /// action_space::entity_weightが使う完全版の熱量。
    pub fn heat_with_degree(&self) -> f64 {
        self.heat() + (self.uses.len() as f64 * 0.5)
    }

    /// base_importance > 0.0 の判定。MCTS産の使い捨て補助構成
    /// (base_importance=0.2〜0.5)や無視すべき実体を除外するための
    /// フィルタとして8箇所前後に直接比較が散らばっていたのをまとめる。
    pub fn is_active(&self) -> bool {
        self.base_importance > 0.0
    }
}

// 🌟 共円・共線は専用の Fact にせず、各点を円・直線に link_logical_incidence でつなぐだけで表す
// (Connected で問い合わせられる)。別の Fact として二重に持つと、記録漏れの温床になる。
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Fact {
    Identical(ClassId, ClassId),
    Connected(ClassId, ClassId), // (Child, Parent)
}

impl Fact {
    pub fn new_identical(mut a: ClassId, mut b: ClassId) -> Self {
        if a.0 > b.0 { std::mem::swap(&mut a, &mut b); }
        Fact::Identical(a, b)
    }
}

impl EGraph {
    // 🌟 論理的なリンク (incidence)
    // 互いの subobjects に ID を登録し合う。ポインタではなくIDなので循環参照は起きない。
    pub fn link_logical_incidence(&mut self, id1: ClassId, id2: ClassId) {
        let rep1 = self.get_rep(id1);
        let rep2 = self.get_rep(id2);

        let mut added_new_link = false;
        if let Some(comp1) = self.entities[rep1.0].components.first_mut()
            && !comp1.subobjects.contains(&rep2) { comp1.subobjects.push(rep2); added_new_link = true; }
        if let Some(comp2) = self.entities[rep2.0].components.first_mut()
            && !comp2.subobjects.contains(&rep1) { comp2.subobjects.push(rep1); added_new_link = true; }

        // 🌟 type_generationのドキュメント参照: 既存の2エンティティ間に
        // 新しい接続関係(incidence)ができるのは、マージでも新規生成でもない
        // 第三の「マッチングに影響し得る変化」。match_connected_factの
        // is_connected判定・subobjects列挙の結果を変え得るので、両側の型に
        // 通知する(実際に何も変わらなかった場合は通知しない)。
        if added_new_link {
            self.note_type_changed(self.entities[rep1.0].entity_type);
            self.note_type_changed(self.entities[rep2.0].entity_type);
        }

        // 🌟 新しい接続関係(incidence)ができたので、apply_congruence_closure の
        // worklist に積んでおく。merge_entities 経由の変化だけでなく、
        // create_entity 直後の apply_trivial_relations でできる新規の接続
        // (マージを伴わない)も、これが無いと「直線の一致条件」「2直線の
        // 交点の一意性」の局所伝播(propagate_line_uniqueness /
        // propagate_point_uniqueness)が一度も走らず見逃されてしまう。
        self.worklist.push(rep1);
        self.worklist.push(rep2);
    }

    /// 🌟 link_logical_incidenceに加えて、「なぜこの接続関係が成り立つか」を
    /// incidence_provenanceに記録する版。Concyclicの証明復元(explain_concyclic)
    /// で使う。既に記録済みなら上書きしない(最初に見つかった経路を採用する)。
    pub fn link_logical_incidence_justified(&mut self, id1: ClassId, id2: ClassId, justification: Justification) {
        self.link_logical_incidence(id1, id2);
        let rep1 = self.get_rep(id1);
        let rep2 = self.get_rep(id2);
        let key = if rep1.0 < rep2.0 { (rep1, rep2) } else { (rep2, rep1) };
        self.incidence_provenance.entry(key).or_insert(justification);
    }

    /// 種類と親から、memo を引ける正規化済みの定義を作る。親の数が合わなければ None。
    pub fn build_definition(&self, kind: DefKind, parents: &[ClassId]) -> Option<Definition> {
        kind.raw(parents).map(|d| self.normalize_definition(&d))
    }

    /// 定義内の親IDを最新の代表元に置き換え、順不同図形はソートして一意なシグネチャにする
    pub fn normalize_definition(&self, def: &Definition) -> Definition {
        match def {
            Definition::Midpoint(a, b) => {
                let r_a = self.get_rep(*a);
                let r_b = self.get_rep(*b);
                if r_a.0 > r_b.0 { Definition::Midpoint(r_b, r_a) } else { Definition::Midpoint(r_a, r_b) }
            },
            Definition::LineThroughPoints(a, b) => {
                let r_a = self.get_rep(*a);
                let r_b = self.get_rep(*b);
                if r_a.0 > r_b.0 { Definition::LineThroughPoints(r_b, r_a) } else { Definition::LineThroughPoints(r_a, r_b) }
            },
            Definition::Intersection(a, b) => {
                let r_a = self.get_rep(*a);
                let r_b = self.get_rep(*b);
                if r_a.0 > r_b.0 { Definition::Intersection(r_b, r_a) } else { Definition::Intersection(r_a, r_b) }
            },
            Definition::LengthSq(a, b) => {
                let r_a = self.get_rep(*a);
                let r_b = self.get_rep(*b);
                if r_a.0 > r_b.0 { Definition::LengthSq(r_b, r_a) } else { Definition::LengthSq(r_a, r_b) }
            },
            Definition::Circumcircle(a, b, c) => {
                let mut reps = [self.get_rep(*a), self.get_rep(*b), self.get_rep(*c)];
                reps.sort_unstable_by_key(|id| id.0);
                Definition::Circumcircle(reps[0], reps[1], reps[2])
            },
            Definition::AnglePair(d1, d2) => Definition::AnglePair(self.get_rep(*d1), self.get_rep(*d2)),
            Definition::PerpendicularLine(l, p) => Definition::PerpendicularLine(self.get_rep(*l), self.get_rep(*p)),
            Definition::ParallelLine(l, p) => Definition::ParallelLine(self.get_rep(*l), self.get_rep(*p)),
            Definition::TangentLine(c, p) => Definition::TangentLine(self.get_rep(*c), self.get_rep(*p)),
            Definition::DirectionOf(l) => Definition::DirectionOf(self.get_rep(*l)),
            Definition::PerpDirectionOf(d) => Definition::PerpDirectionOf(self.get_rep(*d)),
            Definition::HarmonicConjugateOf(a, b, c) => {
                // (A,B)は固定点の対(=対合の不動点対)なので順不同。Cとは意味が違うのでソートしない。
                let r_a = self.get_rep(*a);
                let r_b = self.get_rep(*b);
                let r_c = self.get_rep(*c);
                if r_a.0 > r_b.0 { Definition::HarmonicConjugateOf(r_b, r_a, r_c) } else { Definition::HarmonicConjugateOf(r_a, r_b, r_c) }
            },
            // 🌟 複比(A,B;C,D)の値を厳密に保つのは4元クライン群V4=
            // {id, (AB)(CD), (AC)(BD), (AD)(BC)}の4通りだけ(射影幾何の標準的な
            // 事実)。この4通りの中からClassId辞書順最小を正準形として選ぶ
            // ――Circumcircle(3点の6順列から選ぶ)と全く同じ発想の拡張。
            // 残り20通りの置換は(k,1/k,1-k,1/(1-k),k/(k-1),(k-1)/k という)
            // 6種の異なる値を生むため、意図的にここでは同一視しない
            // (定理側が「この特定の組み合わせの複比」を明示的に参照した時だけ、
            // そのための別エンティティがmemo経由で遅延生成される)。
            Definition::CrossRatio(a, b, c, d) => {
                let r = [self.get_rep(*a), self.get_rep(*b), self.get_rep(*c), self.get_rep(*d)];
                let candidates = [
                    (r[0], r[1], r[2], r[3]),
                    (r[1], r[0], r[3], r[2]),
                    (r[2], r[3], r[0], r[1]),
                    (r[3], r[2], r[1], r[0]),
                ];
                let best = candidates.into_iter()
                    .min_by_key(|t| (t.0.0, t.1.0, t.2.0, t.3.0))
                    .unwrap();
                Definition::CrossRatio(best.0, best.1, best.2, best.3)
            },
            // 🌟 CrossRatioOfLinesもCrossRatioと全く同じV4クライン群の正準化
            // (直線を"射影空間の点"とみなしているだけなので、置換に関する
            // 値の対称性も同一)。
            Definition::CrossRatioOfLines(a, b, c, d) => {
                let r = [self.get_rep(*a), self.get_rep(*b), self.get_rep(*c), self.get_rep(*d)];
                let candidates = [
                    (r[0], r[1], r[2], r[3]),
                    (r[1], r[0], r[3], r[2]),
                    (r[2], r[3], r[0], r[1]),
                    (r[3], r[2], r[1], r[0]),
                ];
                let best = candidates.into_iter()
                    .min_by_key(|t| (t.0.0, t.1.0, t.2.0, t.3.0))
                    .unwrap();
                Definition::CrossRatioOfLines(best.0, best.1, best.2, best.3)
            },
            // 🌟 二次曲線は5点の完全な順不同(Circumcircleの3点版と同じ発想)。
            // 二次曲線の方程式は5点それぞれの単項式ベクトルを並べた行列の
            // 零空間として求まり、点の順序には一切依存しないため、単純に
            // ClassId順にソートするだけでよい。
            Definition::ConicThrough5Points(a, b, c, d, e) => {
                let mut reps = [self.get_rep(*a), self.get_rep(*b), self.get_rep(*c), self.get_rep(*d), self.get_rep(*e)];
                reps.sort_unstable_by_key(|id| id.0);
                Definition::ConicThrough5Points(reps[0], reps[1], reps[2], reps[3], reps[4])
            },
            Definition::Product(a, b) => {
                let r_a = self.get_rep(*a);
                let r_b = self.get_rep(*b);
                if r_a.0 > r_b.0 { Definition::Product(r_b, r_a) } else { Definition::Product(r_a, r_b) }
            },
            // 🌟 known_point/line/conicはそれぞれ役割が違うので順序はそのまま、
            // get_repだけ適用する(併合後も同じ構成が正しくmemoで重複除去される
            // ようにする)。
            Definition::SecondIntersectionOfLineAndConic(p, l, c) => {
                Definition::SecondIntersectionOfLineAndConic(self.get_rep(*p), self.get_rep(*l), self.get_rep(*c))
            },
            // 🌟 根軸は2円について完全に対称なのでClassId順にソートする。
            Definition::RadicalAxis(c1, c2) => {
                let (r1, r2) = (self.get_rep(*c1), self.get_rep(*c2));
                if r1.0 > r2.0 { Definition::RadicalAxis(r2, r1) } else { Definition::RadicalAxis(r1, r2) }
            },
            // 🌟 known_pointは役割が違うので固定、2円だけをソートする。
            Definition::SecondIntersectionOfCircles(p, c1, c2) => {
                let (rp, r1, r2) = (self.get_rep(*p), self.get_rep(*c1), self.get_rep(*c2));
                if r1.0 > r2.0 { Definition::SecondIntersectionOfCircles(rp, r2, r1) } else { Definition::SecondIntersectionOfCircles(rp, r1, r2) }
            },
            _ => def.clone(),
        }
    }

    /// 🌟 作図に付随して生えた図形に印を付けるためだけの包み。中身から
    /// create_entity 経由で再帰するので、深さを数える。
    pub fn apply_trivial_relations(&mut self, new_id: ClassId, def: &Definition) {
        self.trivial_depth += 1;
        self.apply_trivial_relations_inner(new_id, def);
        self.trivial_depth -= 1;
    }

    /// 🌟 選ばれた出どころを一時的に差し替える。前の値を返すので、作り終えたら
    /// 必ず戻すこと。
    pub fn set_origin(&mut self, o: EntityOrigin) -> EntityOrigin {
        std::mem::replace(&mut self.current_origin, o)
    }

    // 🌟 Trivial Relations (作図時のおまけリンクと方向生成)
    fn apply_trivial_relations_inner(&mut self, new_id: ClassId, def: &Definition) {
        match def {
            // 🌟 方向(Direction)は create_entity 経由なら生成元を問わず必ずここを通るので、
            // ここ一箇所で「無限遠直線上の点」として構造的にリンクしておけば、
            // 定理・問題ファイル側のコードは一切変更せずに済む。
            Definition::DirectionOf(_) => {
                self.link_logical_incidence(new_id, self.line_infinity);
            },
            Definition::LineThroughPoints(p1, p2) => {
                self.link_logical_incidence(*p1, new_id);
                self.link_logical_incidence(*p2, new_id);
                let name = format!("Dir_{}_(Auto)", self.entities[new_id.0].name);
                let dir_def = Definition::DirectionOf(new_id);
                let dir_id = self.create_entity(name, dir_def, EntityType::Point);
                self.link_logical_incidence(new_id, dir_id);
            },
            Definition::Intersection(l1, l2) => {
                self.link_logical_incidence(new_id, *l1);
                self.link_logical_incidence(new_id, *l2);
            },
            Definition::Circumcircle(p1, p2, p3) => {
                let reason = "外接円の定義より、生成元の3点はこの円に乗っている".to_string();
                self.link_logical_incidence_justified(*p1, new_id, Justification::Trivial { reason: reason.clone() });
                self.link_logical_incidence_justified(*p2, new_id, Justification::Trivial { reason: reason.clone() });
                self.link_logical_incidence_justified(*p3, new_id, Justification::Trivial { reason });
                // 🌟 円は I,J を通る Conic と同じ計算で作られるので、I,J への接続も張る。これで
                // propagate_conic_uniqueness が「実点3つを共有」を「5点を共有」として扱え、円専用の規則が要らない。
                self.link_logical_incidence(new_id, self.circ_i);
                self.link_logical_incidence(new_id, self.circ_j);
            },
            Definition::AnglePair(d1, d2) => {
                self.link_logical_incidence(*d1, new_id);
                self.link_logical_incidence(*d2, new_id);
            },
            // 🌟 FIX: PerpendicularLine の独立したマッチブロックを削除し、この結合ブロックに一任
            Definition::PerpendicularLine(l, p) | Definition::ParallelLine(l, p) => {
                self.link_logical_incidence(*l, new_id);
                self.link_logical_incidence(*p, new_id);

                let dir1_def = Definition::DirectionOf(*l);
                let dir1_id = self.create_entity(format!("Dir_{}_(Auto)", self.entities[l.0].name), dir1_def, EntityType::Point);
                self.link_logical_incidence(*l, dir1_id);

                let dir2_def = Definition::DirectionOf(new_id);
                let dir2_id = self.create_entity(format!("Dir_{}_(Auto)", self.entities[new_id.0].name), dir2_def, EntityType::Point);
                self.link_logical_incidence(new_id, dir2_id);

                if matches!(def, Definition::PerpendicularLine(_, _)) {
                    // 🌟 既存の有向角ベースの表現(Ang90へのマージ)は、Ang90を直接
                    // パターンに持つ既存定理(接弦定理・直角三角形の斜辺の中線など)が
                    // 引き続き動くよう、そのまま残す。
                    let ang1_def = Definition::AnglePair(dir1_id, dir2_id);
                    let ang1_id = self.create_entity(format!("Ang90_{}_{}", dir1_id.0, dir2_id.0), ang1_def, EntityType::Scalar);
                    self.merge_entities_justified(ang1_id, self.ang90, Justification::Trivial { reason: "垂線の定義より2方向のなす角は90度".to_string() });

                    let ang2_def = Definition::AnglePair(dir2_id, dir1_id);
                    let ang2_id = self.create_entity(format!("Ang90_{}_{}", dir2_id.0, dir1_id.0), ang2_def, EntityType::Scalar);
                    self.merge_entities_justified(ang2_id, self.ang90, Justification::Trivial { reason: "垂線の定義より2方向のなす角は90度(逆順)".to_string() });

                    // 🌟 dir2 を PerpDirectionOf(dir1) としても登録し(対合 perp(perp(D))=D も両方向に)、「同じ直線への
                    // 垂線は平行」を専用の定理なしに合同閉包だけで導けるようにする。
                    // 名前は必ず get_rep を通して読む: 直前の merge_entities で dir2_id 側が吸収されると、その name は空になる。
                    let dir1_name = self.entities[self.get_rep(dir1_id).0].name.clone();
                    let perp1_id = self.create_entity(
                        format!("PerpDir_{}_(Auto)", dir1_name),
                        Definition::PerpDirectionOf(dir1_id), EntityType::Point);
                    self.merge_entities_justified(perp1_id, dir2_id, Justification::Trivial { reason: "垂線の対合性(PerpDirectionOf): dir1に垂直な方向がdir2そのもの".to_string() });

                    let dir2_name = self.entities[self.get_rep(dir2_id).0].name.clone();
                    let perp2_id = self.create_entity(
                        format!("PerpDir_{}_(Auto)", dir2_name),
                        Definition::PerpDirectionOf(dir2_id), EntityType::Point);
                    self.merge_entities_justified(perp2_id, dir1_id, Justification::Trivial { reason: "垂線の対合性(PerpDirectionOf): dir2に垂直な方向がdir1そのもの".to_string() });
                } else {
                    self.merge_entities_justified(dir1_id, dir2_id, Justification::Trivial { reason: "平行線の定義より2直線の方向は一致".to_string() });
                }
            },
            Definition::TangentLine(c, p) => {
                self.link_logical_incidence(*c, new_id);
                self.link_logical_incidence(*p, new_id);
                let dir_def = Definition::DirectionOf(new_id);
                let dir_id = self.create_entity(format!("Dir_{}_(Auto)", self.entities[new_id.0].name), dir_def, EntityType::Point);
                self.link_logical_incidence(new_id, dir_id);
            },
            // 🌟 新しくできた点は、定義上lineにもconicにも乗っている
            // (known_pointと同じ構造的な立場)。ここでincidenceを張って
            // おかないと、match_connected_factの「この直線/この曲線上の点」
            // 探索や、円の一意性局所伝播(propagate_conic_uniqueness)から
            // 見えなくなってしまう。
            Definition::SecondIntersectionOfLineAndConic(p, l, c) => {
                self.link_logical_incidence(new_id, *l);
                self.link_logical_incidence(new_id, *c);
                // 🌟 直線は二次曲線と高々2点でしか交わらない。したがって、
                // その直線上に既知点pとは別の「この二次曲線上の点」qが既に
                // あるなら、第2交点はqそのものである。この一意性を構造的に
                // 登録しておかないと、SecondIntersection(A; 直線AB, ABCの
                // 外接円)のような「実はBでしかないもの」が別実体として残り、
                // 発見報告に重複した無内容な項目として現れる(実測)。
                // 「2直線の交点の一意性」(PointUniqueness)の二次曲線版。
                let rp = self.get_rep(*p);
                let on_line: Vec<ClassId> = self.entities[self.get_rep(*l).0].components.first()
                    .map(|comp| comp.subobjects.iter().map(|&s| self.get_rep(s))
                        .filter(|&s| self.entities[s.0].entity_type == EntityType::Point)
                        .collect::<Vec<_>>())
                    .unwrap_or_default();
                for q in on_line {
                    if q == rp || q == self.get_rep(new_id) { continue; }
                    // 無限遠直線上の点(円周点I,Jなど)は全ての円に乗っているので、
                    // 「もう一方の交点」の候補にしてはいけない。
                    if self.is_connected(q, self.line_infinity) { continue; }
                    if !self.is_connected(q, *c) { continue; }
                    self.merge_entities_justified(new_id, q, Justification::Trivial {
                        reason: "直線と二次曲線は高々2点で交わるので、既知の交点でない方の交点は、その直線上にある残りの交点に一致する".to_string() });
                    break;
                }
            },
            // 🌟 根軸: 2円の共有点として既に構造的に分かっている点があれば、
            // その点は根軸上にある(方冪が両方0で等しい)。円と円の第2交点を
            // SecondIntersectionOfLineAndConic経由で扱えるようにするために
            // 必要な、根軸の一番基本的な性質。
            Definition::RadicalAxis(c1, c2) => {
                let mut shared: Vec<ClassId> = self.entities[self.get_rep(*c1).0].components.first()
                    .map(|comp| comp.subobjects.iter().map(|&s| self.get_rep(s))
                        .filter(|&s| self.entities[s.0].entity_type == EntityType::Point)
                        .filter(|&s| !self.is_connected(s, self.line_infinity))
                        .filter(|&s| self.is_connected(s, *c2))
                        .collect::<Vec<_>>())
                    .unwrap_or_default();
                shared.sort_unstable_by_key(|id| id.0);
                shared.dedup();
                // 🐛 FIX(実測で判明・崩壊の原因その2): 共有点が3つ以上あるなら、
                // 2つの「円」は(まだ記号的に統合されていないだけで)同じ円であり、
                // その根軸は 0=0 で全く定まらない。にもかかわらず、その定まらない
                // 直線に3点以上を接続してしまうと、「2点を共有する直線は同一」の
                // 局所伝播が次々に発火し、AB・BC・CAのような無関係な直線どうしが
                // 芋づる式に併合されてe-graphが潰れる(数値的な裏付け検査も、
                // この直線は評価不能=判定不能のため素通りしてしまう)。
                // 円の同一性の方は円の一意性伝播が別途正しく処理するので、
                // ここでは何も接続しないのが正しい。
                if shared.len() >= 3 { return; }
                for p in shared {
                    // 🐛 FIX(実測で判明・崩壊の原因その1): 円周点I=(1,i,0), J=(1,-i,0)は
                    // 「円である」ことの定義そのものなので、あらゆる円の上にある。
                    // だがI,Jは根軸の上には無い ―― 2円の差 A2·c1 - A1·c2 は
                    // 二次曲線としては z·(ax+by+cz)、つまり「無限遠直線 ∪ 根軸」に
                    // 退化した二次曲線であり、I,Jはそのうち無限遠直線の方に
                    // 乗っているだけだからである。ここでI,Jを根軸に接続すると、
                    // 「無限遠直線と2点(I,J)を共有する直線」として直線の一意性が
                    // 発火し、根軸が無限遠直線に併合されて、そこから
                    // e-graph全体が潰れた(292個の同値類が9個になる崩壊を実測)。
                    // (上のフィルタで既にI,Jは除いてある。)
                    self.link_logical_incidence_justified(p, new_id, Justification::Trivial {
                        reason: "2円の共有点は根軸上にある(方冪がどちらも0で等しい)".to_string() });
                }
            },
            // 🌟 2円の第2交点は、定義からその2円の両方に乗っており、かつ
            // (2交点はどちらも根軸上にあるので)根軸上にもある。根軸の実体も
            // ここで生成しておくことで、「2交点を結ぶ直線=根軸」という構造が
            // 探索側から見えるようになる。
            Definition::SecondIntersectionOfCircles(_p, c1, c2) => {
                self.link_logical_incidence(new_id, *c1);
                self.link_logical_incidence(new_id, *c2);
                let axis_def = self.normalize_definition(&Definition::RadicalAxis(*c1, *c2));
                let axis_name = format!("RadAxis_{}_{}_(Auto)",
                    self.entities[self.get_rep(*c1).0].name, self.entities[self.get_rep(*c2).0].name);
                let axis_id = self.create_entity(axis_name, axis_def, EntityType::Line);
                self.link_logical_incidence(new_id, axis_id);
            },
            Definition::Midpoint(a, b) => {
                self.link_logical_incidence(*a, new_id);
                self.link_logical_incidence(*b, new_id);
                let line_def = Definition::new_line(*a, *b);
                let line_id = self.create_entity(format!("Line_{}_{}_(Auto)", self.entities[a.0].name, self.entities[b.0].name), line_def, EntityType::Line);
                self.link_logical_incidence(new_id, line_id);
                // 🌟 中点の定義から直に従う MA = MB をここで登録する(垂線→Ang90 と同じく、定義から機械的に従う事実は
                // 構造的に入れる)。登録しないと、discover の検出器が中点を作るたびにこの等式を「発見」し直す。
                let la_def = self.normalize_definition(&Definition::LengthSq(*a, new_id));
                let la = self.create_entity(
                    format!("LenSq_{}_{}_(Auto)", self.entities[a.0].name, self.entities[new_id.0].name),
                    la_def, EntityType::Scalar);
                let lb_def = self.normalize_definition(&Definition::LengthSq(new_id, *b));
                let lb = self.create_entity(
                    format!("LenSq_{}_{}_(Auto)", self.entities[new_id.0].name, self.entities[b.0].name),
                    lb_def, EntityType::Scalar);
                self.merge_entities_justified(la, lb, Justification::Trivial {
                    reason: "中点の定義より、両端までの距離の二乗は等しい".to_string(),
                });
            },
            Definition::LengthSq(a, b) => {
                self.link_logical_incidence(*a, new_id);
                self.link_logical_incidence(*b, new_id);
            },
            // 🌟 Circumcircleと同じ要領で、生成元の5点はこの二次曲線に乗って
            // いることを構造的にConnectedとして登録しておく。これにより
            // 「点PはこのConic上にある」という前提を、既存のCircleと全く
            // 同じ Connected(P, Conic) パターン(型に依らないis_connected/
            // subobjectsベースの構造チェック)でそのまま参照できる。
            Definition::ConicThrough5Points(p1, p2, p3, p4, p5) => {
                let reason = "二次曲線の定義より、生成元の5点はこの二次曲線に乗っている".to_string();
                self.link_logical_incidence_justified(*p1, new_id, Justification::Trivial { reason: reason.clone() });
                self.link_logical_incidence_justified(*p2, new_id, Justification::Trivial { reason: reason.clone() });
                self.link_logical_incidence_justified(*p3, new_id, Justification::Trivial { reason: reason.clone() });
                self.link_logical_incidence_justified(*p4, new_id, Justification::Trivial { reason: reason.clone() });
                self.link_logical_incidence_justified(*p5, new_id, Justification::Trivial { reason });
            },
            _ => {}
        }
    }
}

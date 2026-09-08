use std::collections::{HashMap, HashSet};
use std::cell::Cell;
use crate::mmp_math::ModInt;

// 🌟 mmp_core はファイルが肥大化していたため、関心事ごとにサブモジュールへ分割した。
// 型定義・EGraphの基本操作(生成・union-find・論理リンク)はこのmod.rs自身に残し、
// それ以外は以下のサブモジュールへ委譲する:
//   congruence  - 合同閉包エンジン (merge_entities, propagate_*, apply_congruence_closure)
//   eval        - 数値評価/健全性チェック (evaluate_node系, numeric_plausibility_check系)
//   proof       - 証明復元 (Justification/ProofEdgeを人間可読な証明文へ変換)
//   construction- 調和共役点など、複数のエンティティ生成を伴う補助構成
//   query       - is_connected等、EGraphの状態を問い合わせるだけの読み取り専用ユーティリティ
// いずれも同じ EGraph 型への impl ブロックを追加しているだけなので、
// 呼び出し側(main.rs, logic_core.rs等)から見た公開APIは一切変わらない。
mod congruence;
mod eval;
mod proof;
mod construction;
mod query;
mod raw_proof;
pub use raw_proof::{RawProof, DeepProof, DeepStep};
#[cfg(test)]
mod tests;

// 1. 強力な型付きID (Newtype Pattern)
// オブジェクトの直接参照（ポインタ）を廃止し、すべてこのIDで管理する
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClassId(pub usize);

// 2. 図形の種類
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EntityType {
    Point, Line, Circle, Direction, Angle, Scalar,
    // 🌟 5点を通る一般二次曲線(Definition::ConicThrough5Points)専用の型。
    // Circleとは別型にしておくことで、既存のCircle前提のコード
    // (sample_point_on_circle等)を誤って二次曲線に適用してしまう事故を防ぐ
    // (このバージョンでは接線・直線との交点は未実装で、点の接続(Connected)
    // 判定の土台だけを提供する)。
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
    // 🌟 ユーザー提案:「複比の透視射影不変性は、4点複比(A,B;C,D)→4直線の
    // 複比(PA,PB;PC,PD)→4点複比(A',B';C',D')として扱えばマッチングが楽に
    // なりそう」への対応。4本の共点(同じ点を共有する)直線がなす線束の複比。
    // 「円も係数を射影空間の点だと思えばOK」と全く同じ発想で、直線の同次係数
    // (a,b,c)を射影平面の"点"とみなせば、4直線が共点である(=双対平面上で
    // 4つの係数点が共線)ときのCrossRatioと、通常のCrossRatio(4点の共線)は
    // 全く同じ計算式(calc_cross_ratio)で扱える。これにより「透視射影不変性」
    // という1つの巨大な定理(自由変数9個、天然のシードが無くdfs_capを
    // 食い潰す)を、
    //   定理A: 点の複比(直線L上のA,B,C,D) = 線束の複比(Oを通るPA,PB,PC,PD)
    //   定理B: 線束の複比(Oを通るPA,PB,PC,PD) = 点の複比(直線L'上のA',B',C',D')
    // という2つの小さな定理に分解できる――CrossRatioOfLines(PA,PB,PC,PD)を
    // 共通の"ハブ"として経由することで、それぞれの定理が同時に束縛すべき
    // 自由変数の数が減り(定理Aは実質O,A,B,C,Dの5点)、かつ定理Bの4直線は
    // 「Oに繋がっている既存の直線」というConnected(O,_)由来の自然なシードで
    // 絞り込める(定理Aが作ったPA..PDがまさにその候補になる)。
    CrossRatioOfLines(ClassId, ClassId, ClassId, ClassId),
    // 🌟 固定された同次座標を持つ定数エンティティ。GivenPointは(名前を
    // varsから引くが誰も登録しないので実質)常に(0,0,1)に評価されるだけで
    // 任意の定数は表現できないため、円周点(circular points) I=(1,i,0),
    // J=(1,-i,0)(有向角を複比として扱うための固定参照点。i=√-1はこの
    // プロジェクトの法998244353がp≡1(mod4)なので体内に存在する)のような
    // 「常にこの値」という定数を導入するために追加した。
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
}

impl Definition {
    pub fn new_line(mut a: ClassId, mut b: ClassId) -> Self {
        if a.0 > b.0 { std::mem::swap(&mut a, &mut b); }
        Definition::LineThroughPoints(a, b)
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
            Definition::Circumcircle(_, _, _) => EntityType::Circle,
            Definition::DirectionOf(_) => EntityType::Direction,
            Definition::PerpDirectionOf(_) => EntityType::Direction,
            Definition::AnglePair(_, _) => EntityType::Angle,
            Definition::LengthSq(_, _) => EntityType::Scalar,
            Definition::CrossRatio(_, _, _, _) => EntityType::Scalar,
            Definition::CrossRatioOfLines(_, _, _, _) => EntityType::Scalar,
            Definition::GivenPoint | Definition::FreePoint => EntityType::Point,
            // 🌟 円周点I,Jのように「同次座標を持つ定数」は、デフォルトでは
            // Point(GivenPoint/FreePointと同じ)として扱っておく。実際の型は
            // create_entity呼び出し側が明示するので(circ_i/circ_jはDirection)、
            // ここはMCTS等の型不明時のフォールバックとしてのみ使われる。
            Definition::ConstantHomogeneous(_, _, _) => EntityType::Point,
            Definition::ConicThrough5Points(_, _, _, _, _) => EntityType::Conic,
            Definition::Product(_, _) => EntityType::Scalar,
        }
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
    // 🌟 円周点(circular points at infinity) I, J。有向角AnglePair(D1,D2)を
    // 「無限遠直線上の4点D1,D2,I,Jの複比」として扱うための固定参照点。
    // ユーザー提案「有向角を複比として扱う」への対応で、AnglePairの数値評価
    // (eval.rs)がこの2点とcalc_cross_ratioを使うように変更されている。
    // I,Jは古典的に(1,±i,0)(iは虚数単位)で、この複比 (I,J;D1,D2) は
    // Möbius変換の比として D1→D2→D3 の加法性(掛け算則)・交替律
    // (a/b=c/d ⟹ a/c=b/d)をそのまま満たすため、既存の「有向角の加法性」
    // 「有向角の交替律」定理(AnglePairの値をIdenticalで比較するだけの
    // 純粋に構造的な定理で、値の具体的な計算式には一切依存しない)は
    // パターン・定理側を一切変更せずにそのまま複比としての意味を持つ。
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
    // 🌟 実際にunion-findの併合が起きるたび(merge_entities内で root1 != root2
    // だった回数だけ)単調増加するカウンタ。logic_core.rs::MatchTaskが
    // dfs_cap到達で再キューされる際、そのタスク専用のfailed_paths
    // (このタスクの中でどのbind/flip_states状態が「これ以上進めない」と
    // 分かったかのハッシュキャッシュ)を安全に持ち越せるかどうかの判定に使う。
    // failed_pathsはget_rep()した後のClassIdをハッシュに含めているため、
    // キャッシュを作った時点から1回でもマージが起きていれば、同じハッシュが
    // 別の(今はマージにより到達可能になったかもしれない)状態を指してしまい
    // 得る。そのため「保存時のこの値」と「再開時のこの値」が一致する場合
    // だけ再利用し、1つでもずれていれば安全側に倒して空から作り直す。
    pub merge_generation: u64,
    // 🌟 propagate_circle_uniqueness用の「却下済みペア」キャッシュ。
    // キーは(小さい方の代表元インデックス, 大きい方の代表元インデックス)、
    // 値はそのペアを数値的健全性チェックで却下した時点のmerge_generation。
    // 円は直線よりも同一点集合上に多数の重複エンティティが積み上がりやすく
    // (HAGeo-409ベンチマークで実測: ある問題では全円エンティティの100%が
    // 統合されるべき重複だった)、あるペアが一度「共有点はあるが数値的には
    // 別の円」と判定されても、そのペアの片方に別の(無関係な)点がマージ
    // されるたびに(円自体のrepは変わっていなくても)再チェックされてしまい、
    // 同じ却下を何度も繰り返すことがrealorthocenterで実測された(壁時計時間
    // 4.5秒→17.5秒への劣化の主因)。マージが1件も起きていない間は再チェック
    // しても結果が変わりようがないので、merge_generationが前回の却下時点から
    // 変わっていなければ即座にスキップする。
    pub rejected_circle_pairs: rustc_hash::FxHashMap<(usize, usize), u64>,
    // 🌟 ユーザー提案(定理マッチングの最適化)への対応その1: EntityTypeごとの
    // 生成済みエンティティID一覧のインデックス。create_entity内で追記するだけの
    // 単調増加リストで、union-findのマージでは更新しない(吸収された側の
    // ClassIdもそのまま残る)。そのため利用側は必ずget_rep()で正規化された
    // 代表元だけを拾う(iter_reps_of_type参照)。
    //
    // 従来、logic_core.rs側の複数箇所(Identical/Connectedの両変数未束縛分岐、
    // DefinedByの親変数も未束縛な場合のフルスキャン分岐)が「特定の型を持つ
    // 代表元」を探すために self.egraph.entities を毎回全件ループしていた。
    // 定理が増えるほどエンティティ数(補助図形)も増えるため、この種の
    // フルスキャンのコストが線形に効いてくる。型ごとに索引を引けるように
    // しておけば、目的の型のエンティティ数だけのスキャンで済む
    // (特にCircle/Conicのような個体数の少ない型で効果が大きい)。
    pub type_index: rustc_hash::FxHashMap<EntityType, Vec<ClassId>>,
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
    CircleUniqueness { shared_points: Vec<ClassId> },
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
            rejected_circle_pairs: rustc_hash::FxHashMap::default(),
            type_index: rustc_hash::FxHashMap::default(),
        };
        // 🌟 定数ノードの生成 (GivenPointをプレースホルダとして利用)
        egraph.ang90 = egraph.create_entity("Ang90".to_string(), Definition::GivenPoint, EntityType::Angle);
        egraph.ang0 = egraph.create_entity("Ang0".to_string(), Definition::GivenPoint, EntityType::Angle);
        egraph.line_infinity = egraph.create_entity("Line_infinity".to_string(), Definition::GivenPoint, EntityType::Line);
        // 🌟 円周点 I=(1,i,0), J=(1,-i,0) (i=√-1)。このプロジェクトの法
        // 998244353 は p≡1(mod4) なので体内に平方根が存在し、原始根3を使って
        // i = 3^((p-1)/4) と求まる(Tonelli-Shanksを持ち出すまでもない、
        // NTT-friendly素数の標準的なトリック)。i²≡-1(mod p)であることは
        // 事前に検証済み。
        let i = ModInt::new(3).pow((crate::mmp_math::PRIME - 1) / 4);
        let neg_i = -i;
        egraph.circ_i = egraph.create_entity("CircI".to_string(), Definition::ConstantHomogeneous(ModInt::new(1), i, ModInt::new(0)), EntityType::Direction);
        egraph.circ_j = egraph.create_entity("CircJ".to_string(), Definition::ConstantHomogeneous(ModInt::new(1), neg_i, ModInt::new(0)), EntityType::Direction);
        egraph
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
        };

        self.entities.push(entity);
        self.parents.push(Cell::new(id.0));
        self.type_index.entry(e_type).or_default().push(id);

        for p in norm_def.get_parents() {
            let p_rep = self.get_rep(p);
            self.entities[p_rep.0].uses.insert(id);
        }

        if should_memoize {
            self.memo.insert(norm_def.clone(), id);
        }

        self.apply_trivial_relations(id, &norm_def);
        id
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
    // 🌟 以前は std::collections::HashSet<ClassId>(標準のRandomState、
    // プロセスごとに異なるランダムシード)だった。重複除去自体は必要だが、
    // その反復順序がプロセス起動のたびに変わってしまうため、これに依存する
    // 局所伝播(propagate_line_uniqueness/propagate_point_uniqueness)や
    // 定理マッチングの候補列挙の探索順序までプロセスごとに変わってしまい、
    // 同じ問題・同じロジックでも実行時間が実行のたびに大きくばらつく
    // (実測: miquelで0.35秒/1.05秒の二峰性)原因になっていた。挿入順を保持する
    // Vecに変え、重複除去はlink_logical_incidence/merge_entities側で
    // 明示的に行う(小規模なので線形探索で十分)ことで、探索順序を完全に
    // 再現可能にする。
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
    // 🌟 create_entity時に一度だけ設定され、以後マージが起きても絶対に
    // 書き換えられない、そのスロット固有の不変な「元の定義」。components側は
    // merge_entities で(生き残った側に)吸収された実体からstd::mem::takeされ
    // 空になってしまうため、「このIDは元々どんな(引数の)定義で作られたか」を
    // 後から(raw_proof::dump_raw_proofが)正確に復元するために必要。
    // extract_proofの「DefinedBy(d1,d2,result)前提は、実は名前付き定理の合流の
    // 産物であることが多いのに一律『定義から自明』と表示してしまう」問題を、
    // 全合流履歴の総当たり列挙ではなく、この特定の(d1,d2)組み合わせを
    // 最初に持っていた"元の"実体1つとその実体からresultまでの最短合流経路だけを
    // ピンポイントで特定する形で解消するために導入した(ユーザー提案の
    // 「証明の先頭からDPで証明木を構築する」方針への対応)。
    pub original_definition: Definition,
    pub uses: rustc_hash::FxHashSet<ClassId>,
    // 🌟 MCTSが自由な探索で作った補助構成が、他のMCTS補助構成の上にさらに
    // 積み重なった「連鎖の深さ」(mcts.rs::apply_action参照)。問題文で最初から
    // 与えられている点・直線や、需要駆動(resolve_demands等)の補助線はこの値を
    // 一切更新しないため常に0のままで、この上限による制限を受けない。MCTSが
    // MCTS自身の産物の上に何段も構成を積み増す(例:中点のまた中点のまた中点…)
    // ことだけを対象にした、ローカルな連鎖専用のカウンタ。
    pub mcts_depth: usize,
    // 🌟 MMP(動点法)の次数(measure_numerical_degree)のメモ化キャッシュ。
    // heat_bonus/base_importance/usesと同じく「そのエンティティ固有の
    // 派生情報」なので、EGraph側に別立てのHashMapを持つのではなくここに
    // 置く(ユーザー指摘: 次数はGeoEntityの中にあった方が自然)。
    // None=未計算、Some(None)=計算済みだが測定不能、Some(Some(d))=次数d。
    // Cell(RefCellではない)で足りるのは中身がCopyだから。定理マッチングの
    // ホットパス(logic_core.rs::match_defined_by_fact)から&selfのまま
    // 読み書きできるようにするための内部可変性。
    pub degree_cache: std::cell::Cell<Option<Option<usize>>>,
}



// 🌟 Concyclic/Collinear は専用のFact型として持つのをやめた。
// 「N点が同じ円/直線に乗っている」ことは、各点をその円/直線に
// link_logical_incidence で構造的につなぐだけで既に表現できており
// (Connected述語で汎用的に問い合わせられる)、別建てのN項Factとして
// 二重に記録・維持する必要がなかった。実際、記録し忘れるバグの温床にも
// なっていた(simson/cyclic_quadで発生)。
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Fact {
    Identical(ClassId, ClassId),
    Connected(ClassId, ClassId), // (Child, Parent)
    Parallel(ClassId, ClassId),
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

        if let Some(comp1) = self.entities[rep1.0].components.first_mut() {
            if !comp1.subobjects.contains(&rep2) { comp1.subobjects.push(rep2); }
        }
        if let Some(comp2) = self.entities[rep2.0].components.first_mut() {
            if !comp2.subobjects.contains(&rep1) { comp2.subobjects.push(rep1); }
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
            _ => def.clone(),
        }
    }

    // 🌟 Trivial Relations (作図時のおまけリンクと方向生成)
    pub fn apply_trivial_relations(&mut self, new_id: ClassId, def: &Definition) {
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
                let dir_id = self.create_entity(name, dir_def, EntityType::Direction);
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
                let dir1_id = self.create_entity(format!("Dir_{}_(Auto)", self.entities[l.0].name), dir1_def, EntityType::Direction);
                self.link_logical_incidence(*l, dir1_id);

                let dir2_def = Definition::DirectionOf(new_id);
                let dir2_id = self.create_entity(format!("Dir_{}_(Auto)", self.entities[new_id.0].name), dir2_def, EntityType::Direction);
                self.link_logical_incidence(new_id, dir2_id);

                if matches!(def, Definition::PerpendicularLine(_, _)) {
                    // 🌟 既存の有向角ベースの表現(Ang90へのマージ)は、Ang90を直接
                    // パターンに持つ既存定理(接弦定理・直角三角形の斜辺の中線など)が
                    // 引き続き動くよう、そのまま残す。
                    let ang1_def = Definition::AnglePair(dir1_id, dir2_id);
                    let ang1_id = self.create_entity(format!("Ang90_{}_{}", dir1_id.0, dir2_id.0), ang1_def, EntityType::Angle);
                    self.merge_entities_justified(ang1_id, self.ang90, Justification::Trivial { reason: "垂線の定義より2方向のなす角は90度".to_string() });

                    let ang2_def = Definition::AnglePair(dir2_id, dir1_id);
                    let ang2_id = self.create_entity(format!("Ang90_{}_{}", dir2_id.0, dir1_id.0), ang2_def, EntityType::Angle);
                    self.merge_entities_justified(ang2_id, self.ang90, Justification::Trivial { reason: "垂線の定義より2方向のなす角は90度(逆順)".to_string() });

                    // 🌟 射影的な表現を追加: dir2 は「dir1に垂直な方向」そのものとして
                    // PerpDirectionOfでも構造的に登録しておく(対合性 perp(perp(D))=D
                    // も両方向に登録する)。これにより「同じ直線への垂線は全て平行」
                    // のような事実が、専用の角度チェイス定理を経由せず、
                    // f(a)=f(b) if a=b という通常の合同閉包(create_entityのmemo)
                    // だけで自動的に導かれるようになる。既存のAng90ベースの定理には
                    // 一切影響しない、純粋な追加。
                    // 🐛 バグ修正: 1つ目のmerge_entities(perp1_id, dir2_id)によって
                    // dir2_id側の生のエンティティ格納先が「敗者」になった場合、
                    // その.nameはmerge_entities内でstd::mem::takeされて空文字になる。
                    // その後dir2_idという生の(mergeを経ていない)IDのままself.entities[..].name
                    // を読むと空文字を拾ってしまい、"PerpDir__(Auto)"のような名前になる。
                    // 常にget_repを通した代表元の名前を読むようにする。
                    let dir1_name = self.entities[self.get_rep(dir1_id).0].name.clone();
                    let perp1_id = self.create_entity(
                        format!("PerpDir_{}_(Auto)", dir1_name),
                        Definition::PerpDirectionOf(dir1_id), EntityType::Direction);
                    self.merge_entities_justified(perp1_id, dir2_id, Justification::Trivial { reason: "垂線の対合性(PerpDirectionOf): dir1に垂直な方向がdir2そのもの".to_string() });

                    let dir2_name = self.entities[self.get_rep(dir2_id).0].name.clone();
                    let perp2_id = self.create_entity(
                        format!("PerpDir_{}_(Auto)", dir2_name),
                        Definition::PerpDirectionOf(dir2_id), EntityType::Direction);
                    self.merge_entities_justified(perp2_id, dir1_id, Justification::Trivial { reason: "垂線の対合性(PerpDirectionOf): dir2に垂直な方向がdir1そのもの".to_string() });
                } else {
                    self.merge_entities_justified(dir1_id, dir2_id, Justification::Trivial { reason: "平行線の定義より2直線の方向は一致".to_string() });
                }
            },
            Definition::TangentLine(c, p) => {
                self.link_logical_incidence(*c, new_id);
                self.link_logical_incidence(*p, new_id);
                let dir_def = Definition::DirectionOf(new_id);
                let dir_id = self.create_entity(format!("Dir_{}_(Auto)", self.entities[new_id.0].name), dir_def, EntityType::Direction);
                self.link_logical_incidence(new_id, dir_id);
            },
            Definition::Midpoint(a, b) => {
                self.link_logical_incidence(*a, new_id);
                self.link_logical_incidence(*b, new_id);
                let line_def = Definition::new_line(*a, *b);
                let line_id = self.create_entity(format!("Line_{}_{}_(Auto)", self.entities[a.0].name, self.entities[b.0].name), line_def, EntityType::Line);
                self.link_logical_incidence(new_id, line_id);
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

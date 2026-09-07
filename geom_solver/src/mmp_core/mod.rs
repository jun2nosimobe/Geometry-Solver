use std::collections::{HashMap, HashSet};
use std::cell::Cell;

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
            Definition::GivenPoint | Definition::FreePoint => EntityType::Point,
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
            worklist: Vec::new(),
            proof_edges: rustc_hash::FxHashMap::default(),
            incidence_provenance: rustc_hash::FxHashMap::default(),
            conjectures: std::cell::RefCell::new(rustc_hash::FxHashMap::default()),
        };
        // 🌟 定数ノードの生成 (GivenPointをプレースホルダとして利用)
        egraph.ang90 = egraph.create_entity("Ang90".to_string(), Definition::GivenPoint, EntityType::Angle);
        egraph.ang0 = egraph.create_entity("Ang0".to_string(), Definition::GivenPoint, EntityType::Angle);
        egraph.line_infinity = egraph.create_entity("Line_infinity".to_string(), Definition::GivenPoint, EntityType::Line);
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
            uses: rustc_hash::FxHashSet::default(),
        };

        self.entities.push(entity);
        self.parents.push(Cell::new(id.0));

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
    pub uses: rustc_hash::FxHashSet<ClassId>,
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
            _ => {}
        }
    }
}

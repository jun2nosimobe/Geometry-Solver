use std::collections::{HashMap, HashSet};
use std::cell::Cell;
use rustc_hash::FxHashMap;
use crate::mmp_math::ModInt;
use crate::mmp_calculators;

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

    // 🌟 以下の2つのメソッドを確実に追加する
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
            worklist: Vec::new()
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
            id, name, entity_type: e_type,
            base_importance: 1.0, heat_bonus: 0.0,
            components: vec![LogicalComponent { definitions: vec![norm_def.clone()], subobjects: std::collections::HashSet::new() }],
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
    pub subobjects: HashSet<ClassId>,
}

#[derive(Debug, Clone)]
pub struct GeoEntity {
    pub id: ClassId,
    pub name: String,
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
            comp1.subobjects.insert(rep2);
        }
        if let Some(comp2) = self.entities[rep2.0].components.first_mut() {
            comp2.subobjects.insert(rep1);
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


    // 🌟 マージロジック (merge_numerical)
    pub fn merge_entities(&mut self, id1: ClassId, id2: ClassId) -> bool {
        let root1 = self.get_rep(id1);
        let root2 = self.get_rep(id2);
        if root1 == root2 { return false; } 

        self.parents[root2.0].set(root1.0);

        let mut root2_comps = std::mem::take(&mut self.entities[root2.0].components);
        let root2_heat = self.entities[root2.0].heat_bonus;
        let root2_imp = self.entities[root2.0].base_importance;
        let root2_name = std::mem::take(&mut self.entities[root2.0].name);
        let mut root2_uses = std::mem::take(&mut self.entities[root2.0].uses);

        // 🌟 FIX: root1のコンポーネントも一度takeし、mutable borrowの競合を回避する
        let mut root1_comps = std::mem::take(&mut self.entities[root1.0].components);

        let mut merged_defs = std::collections::HashSet::new();
        let mut merged_subs = std::collections::HashSet::new();

        for comp in root1_comps.drain(..) {
            for def in comp.definitions {
                merged_defs.insert(self.normalize_definition(&def));
            }
            for sub in comp.subobjects {
                merged_subs.insert(self.get_rep(sub));
            }
        }
        for comp in root2_comps {
            for def in comp.definitions {
                merged_defs.insert(self.normalize_definition(&def));
            }
            for sub in comp.subobjects {
                merged_subs.insert(self.get_rep(sub));
            }
        }

        // ここで再度 root1_entity の可変参照を取得
        let root1_entity = &mut self.entities[root1.0];
        root1_entity.heat_bonus = root1_entity.heat_bonus.max(root2_heat);
        root1_entity.base_importance = root1_entity.base_importance.max(root2_imp);
        
        root1_entity.components = vec![LogicalComponent {
            definitions: merged_defs.into_iter().collect(),
            subobjects: merged_subs,
        }];

        if root2_name.len() < root1_entity.name.len() {
            root1_entity.name = root2_name;
        } else if root2_name.len() == root1_entity.name.len() 
            && !root2_name.contains("(Ghost)") 
            && root1_entity.name.contains("(Ghost)") {
            root1_entity.name = root2_name;
        }
        self.entities[root1.0].uses.extend(root2_uses);
        
        self.worklist.push(root1);
        true
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
                self.link_logical_incidence(*p1, new_id);
                self.link_logical_incidence(*p2, new_id);
                self.link_logical_incidence(*p3, new_id);
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
                    self.merge_entities(ang1_id, self.ang90);

                    let ang2_def = Definition::AnglePair(dir2_id, dir1_id);
                    let ang2_id = self.create_entity(format!("Ang90_{}_{}", dir2_id.0, dir1_id.0), ang2_def, EntityType::Angle);
                    self.merge_entities(ang2_id, self.ang90);

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
                    self.merge_entities(perp1_id, dir2_id);

                    let dir2_name = self.entities[self.get_rep(dir2_id).0].name.clone();
                    let perp2_id = self.create_entity(
                        format!("PerpDir_{}_(Auto)", dir2_name),
                        Definition::PerpDirectionOf(dir2_id), EntityType::Direction);
                    self.merge_entities(perp2_id, dir1_id);
                } else {
                    self.merge_entities(dir1_id, dir2_id);
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

    pub fn apply_congruence_closure(&mut self) -> bool {
        let mut changed_any = false;

        while let Some(changed_id) = self.worklist.pop() {
            let rep_id = self.get_rep(changed_id);
            let uses: Vec<ClassId> = self.entities[rep_id.0].uses.iter().copied().collect();

            let mut def_map: FxHashMap<Definition, ClassId> = FxHashMap::default();

            for used_id in uses {
                let u_rep = self.get_rep(used_id);
                if u_rep != used_id { continue; }

                // 🌟 FIX: 不変参照を維持し続けないように、definitions をクローンして借用を即座にドロップする
                let definitions = if let Some(comp) = self.entities[u_rep.0].components.first() {
                    comp.definitions.clone()
                } else {
                    continue;
                };

                for def in &definitions {
                    if matches!(def, Definition::FreePoint | Definition::GivenPoint) { continue; }
                    let norm_def = self.normalize_definition(def);

                    // 🌟 1. グローバルな memo (既存図形) との照合
                    if let Some(&global_existing) = self.memo.get(&norm_def) {
                        let g_rep = self.get_rep(global_existing);
                        if g_rep != u_rep {
                            if self.merge_entities(g_rep, u_rep) {
                                changed_any = true;
                                break;
                            }
                        }
                    }
                    // 🌟 2. 現在のループ内で新しく生成された同一定義との照合
                    else if let Some(&existing_rep) = def_map.get(&norm_def) {
                        if existing_rep != u_rep {
                            if self.merge_entities(existing_rep, u_rep) {
                                changed_any = true;
                                break;
                            }
                        }
                    } else {
                        def_map.insert(norm_def.clone(), u_rep);
                        self.memo.insert(norm_def, u_rep); // 🌟 グローバルにも登録
                    }
                }
            }

            // 🌟 [構造的マージ] 点・直線の接続関係(incidence)から従う合同閉包を、
            // 全図形×全図形の総当たりではなく、"今回変化した図形(rep_id)の
            // 局所的な隣接関係(subobjects)だけを辿る" DFS的な伝播で行う。
            //
            // - 直線が変化した場合:「直線の一致条件」(2直線が2点を共有、
            //   または1点を共有しつつ方向も等しいなら同一直線)を、
            //   この直線上の点それぞれが他にどの直線に乗っているかだけを見て判定する。
            // - 点が変化した場合:「2直線の交点の一意性」(この点が乗っている
            //   2直線の交点として既に登録済みの点があれば同一点)を、
            //   memoへのO(1)参照だけで判定する(全点を舐めない)。
            //
            // 以前はここを「全直線ペア×全点」のO(直線数^2 × 点数)の総当たりで
            // 実行しており(apply_congruence_closureが呼ばれるたびに無条件で
            // 走っていた)、かつ「点の一致」版は専用のBlackboard定理として
            // dfs_match経由でしか判定できず、どちらも無駄が大きかった。
            // ここでのマージも merge_entities 経由で worklist に積まれるので、
            // 連鎖的な合流はこの while ループが自然に続けて処理する。
            let rep_id = self.get_rep(changed_id); // 上のuses処理でrepが動いた可能性があるので取り直す
            match self.entities[rep_id.0].entity_type {
                EntityType::Line => {
                    if self.propagate_line_uniqueness(rep_id) { changed_any = true; }
                }
                // 🌟 Directionは「無限遠直線上の点」として扱うので、通常の点と同じく
                // propagate_point_uniquenessの対象にする。
                EntityType::Point | EntityType::Direction => {
                    if self.propagate_point_uniqueness(rep_id) { changed_any = true; }
                }
                _ => {}
            }
        }

        changed_any
    }

    /// 🌟 「直線の一致条件」の局所伝播版。
    /// line 自身が乗っている点(局所・少数)だけを見て、それらの点が他に
    /// 乗っている直線との共有点数を調べる。全直線を舐めない。
    ///
    /// Direction(方向)は「無限遠直線上の点」として扱うので、この関数では
    /// 通常の点と全く区別しない。これにより「2直線が1点を共有しかつ方向が
    /// 同じなら同一直線」という以前の特別扱い(same_dir)は、単に
    /// 「無限遠直線上の共有点も含めて2点共有」という同じルールに統合される
    /// (平行なだけの別々の直線は無限遠点1つしか共有しないので誤ってマージ
    /// されない。同一直線は通常の点+無限遠点の2つを共有するので正しく
    /// マージされる)。
    fn propagate_line_uniqueness(&mut self, line: ClassId) -> bool {
        let mut line = self.get_rep(line);
        let is_point_like = |et: EntityType| et == EntityType::Point || et == EntityType::Direction;

        // 🐛 FIX: 共有点を数える前に、この直線上の点(方向を含む)どうしの
        // 「2直線の交点の一意性」を先に局所的な不動点まで確定させておく。
        // これをやらないと、本来は同一になるはずだがまだ別IDのままの2つ
        // (例: 外心の候補O1とO2、あるいはまだ別々に導出された同じ方向)を
        // 「別々の2つの共有点」と誤認し、無関係な直線を誤ってマージして
        // しまうことがある(外心の証明で実際に発生した)。
        loop {
            let points: Vec<ClassId> = match self.entities[line.0].components.first() {
                Some(c) => c.subobjects.iter()
                    .map(|&id| self.get_rep(id))
                    .filter(|&id| is_point_like(self.entities[id.0].entity_type))
                    .collect(),
                None => return false,
            };
            let mut any = false;
            for p in points {
                if self.propagate_point_uniqueness(p) { any = true; }
            }
            line = self.get_rep(line);
            if !any { break; }
        }

        // 🐛 FIX: subobjects は merge 前の生のIDをそのまま持ち続けるため、
        // 同じ代表元を指す複数のエントリが残ることがある(例えばLineとその
        // Demand版が別々に同じ点へリンクされ、後で合流した場合)。
        // rep化した後に必ず重複を除いてから使う。
        let points: std::collections::HashSet<ClassId> = match self.entities[line.0].components.first() {
            Some(c) => c.subobjects.iter()
                .map(|&id| self.get_rep(id))
                .filter(|&id| is_point_like(self.entities[id.0].entity_type))
                .collect(),
            None => return false,
        };

        // line上の各点(方向を含む)について、他に乗っている直線ごとに共有数を数える。
        // 🐛 FIX: 1点につき同じ他直線への加算は高々1にする(重複subobjectsで
        // 1点しか共有していないのに2点共有と誤カウントするのを防ぐ)。
        let mut shared_counts: FxHashMap<ClassId, usize> = FxHashMap::default();
        for &p in &points {
            if let Some(comp) = self.entities[p.0].components.first() {
                let other_lines_of_p: std::collections::HashSet<ClassId> = comp.subobjects.iter()
                    .map(|&id| self.get_rep(id))
                    .filter(|&id| id != line && self.entities[id.0].entity_type == EntityType::Line)
                    .collect();
                for other in other_lines_of_p {
                    *shared_counts.entry(other).or_insert(0) += 1;
                }
            }
        }

        for (other_line, shared) in shared_counts {
            let line = self.get_rep(line); // 途中のマージでrepが変わっている可能性
            let other_line = self.get_rep(other_line);
            if line == other_line { continue; }

            if shared >= 2 {
                let name1 = self.entities[line.0].name.clone();
                let name2 = self.entities[other_line.0].name.clone();
                if self.merge_entities(line, other_line) {
                    println!("  ⚙️ [E-Graph自動マージ] 幾何条件(共有点={})により直線を結合: {} ≡ {}",
                        shared, name1, name2);
                    return true;
                }
            }
        }
        false
    }

    /// 🌟 「2直線の交点の一意性」の局所伝播版。
    /// point(方向を含む)自身が乗っている直線(局所・少数)のペアについて、
    /// その交点が memo に既に登録されていないかをO(1)参照するだけ。全点を舐めない。
    ///
    /// 方向(Direction)は Definition::Intersection(line, 無限遠直線) ではなく
    /// Definition::DirectionOf(line) という別のDefinitionで登録されている
    /// (定理側のパターンを変えずに済ませるため、あえて既存の表現のままにしてある)。
    /// そのため、ペアのどちらかが無限遠直線のときは DirectionOf での読み替えも試す。
    fn propagate_point_uniqueness(&mut self, point: ClassId) -> bool {
        let point = self.get_rep(point);
        // 🐛 FIX: subobjects の重複エントリを rep 化した後に除いてから使う(理由は
        // propagate_line_uniqueness と同様)。
        let lines: Vec<ClassId> = match self.entities[point.0].components.first() {
            Some(c) => {
                let set: std::collections::HashSet<ClassId> = c.subobjects.iter()
                    .map(|&id| self.get_rep(id))
                    .filter(|&id| self.entities[id.0].entity_type == EntityType::Line)
                    .collect();
                set.into_iter().collect()
            },
            None => return false,
        };

        let mut candidates: Vec<ClassId> = Vec::new();
        for i in 0..lines.len() {
            for j in (i + 1)..lines.len() {
                let (l1, l2) = (lines[i], lines[j]);
                let inter_def = self.normalize_definition(&Definition::Intersection(l1, l2));
                if let Some(&existing) = self.memo.get(&inter_def) { candidates.push(existing); }

                if l1 == self.line_infinity {
                    if let Some(&existing) = self.memo.get(&Definition::DirectionOf(l2)) { candidates.push(existing); }
                }
                if l2 == self.line_infinity {
                    if let Some(&existing) = self.memo.get(&Definition::DirectionOf(l1)) { candidates.push(existing); }
                }
            }
        }

        for existing in candidates {
            let existing_rep = self.get_rep(existing);
            let point_rep = self.get_rep(point);
            if existing_rep != point_rep {
                let name1 = self.entities[existing_rep.0].name.clone();
                let name2 = self.entities[point_rep.0].name.clone();
                if self.merge_entities(existing_rep, point_rep) {
                    println!("  ⚙️ [E-Graph自動マージ] 2直線の交点の一意性により点を結合: {} ≡ {}", name1, name2);
                    return true;
                }
            }
        }
        false
    }

    /// 🌟 数値評価環境 (MMPテスト用)
    pub fn evaluate_node(
        &self,
        node_id: ClassId,
        vars: &FxHashMap<String, ModInt>,
        cache: &mut FxHashMap<usize, Vec<ModInt>>,
    ) -> Option<Vec<ModInt>> {
        let mut in_progress = HashSet::new();
        self.evaluate_node_inner(node_id, vars, cache, &mut in_progress)
    }

    /// 🌟 evaluate_node の実体。PerpDirectionOf/HarmonicConjugateOfのように、
    /// マージによって「互いを参照し合う定義」が同じコンポーネントに同居する
    /// ことがある(例: D=Harm(A,B,C) と C=Harm(A,B,D) が対合として互いに
    /// マージされる)。素朴に再帰するとどちらの定義から計算しても計算不能な
    /// 組み合わせで無限再帰(スタックオーバーフロー)に陥るため、
    /// 計算中のIDへの再突入を in_progress で検出し、その場合はその定義を
    /// 諦めて(Noneを返して)コンポーネント内の他の定義を試す。
    fn evaluate_node_inner(
        &self,
        node_id: ClassId,
        vars: &FxHashMap<String, ModInt>,
        cache: &mut FxHashMap<usize, Vec<ModInt>>,
        in_progress: &mut HashSet<usize>,
    ) -> Option<Vec<ModInt>> {
        let rep_id = self.get_rep(node_id);
        if let Some(val) = cache.get(&rep_id.0) {
            return Some(val.clone());
        }
        if !in_progress.insert(rep_id.0) {
            return None;
        }

        let name = self.entities[rep_id.0].name.clone();
        let definitions = match self.entities[rep_id.0].components.first() {
            Some(c) => c.definitions.clone(),
            None => { in_progress.remove(&rep_id.0); return None; }
        };

        // 🌟 マージ後は1つのコンポーネントに複数の定義が同居し得るので、
        // 計算可能なものが見つかるまで順に試す(以前は.first()決め打ちで、
        // たまたま循環参照側が先頭に来ると即失敗していた)。
        let mut result = None;
        for def in &definitions {
            if let Some(v) = self.evaluate_definition(def, &name, vars, cache, in_progress) {
                result = Some(v);
                break;
            }
        }

        in_progress.remove(&rep_id.0);
        if let Some(ref v) = result {
            cache.insert(rep_id.0, v.clone());
        }
        result
    }

    fn evaluate_definition(
        &self,
        def: &Definition,
        name: &str,
        vars: &FxHashMap<String, ModInt>,
        cache: &mut FxHashMap<usize, Vec<ModInt>>,
        in_progress: &mut HashSet<usize>,
    ) -> Option<Vec<ModInt>> {
        match def {
            Definition::FreePoint | Definition::GivenPoint => {
                let x = vars.get(&format!("{}_x", name)).copied().unwrap_or(ModInt::new(0));
                let y = vars.get(&format!("{}_y", name)).copied().unwrap_or(ModInt::new(0));
                Some(vec![x, y, ModInt::new(1)])
            }
            Definition::Midpoint(p1, p2) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                Some(mmp_calculators::calc_midpoint(&v1, &v2))
            }
            Definition::LineThroughPoints(p1, p2) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                Some(mmp_calculators::calc_line_through_points(&v1, &v2))
            }
            Definition::Intersection(l1, l2) => {
                let v1 = self.evaluate_node_inner(*l1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*l2, vars, cache, in_progress)?;
                Some(mmp_calculators::calc_intersection(&v1, &v2))
            }
            Definition::DirectionOf(l) => {
                let v = self.evaluate_node_inner(*l, vars, cache, in_progress)?;
                if v.len() >= 3 {
                    // 直線 ax + by + c = 0 の方向ベクトルは (b, -a)
                    Some(mmp_calculators::normalize(&[v[1], -v[0]]))
                } else {
                    None
                }
            }
            Definition::AnglePair(d1, d2) => {
                let v1 = self.evaluate_node_inner(*d1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*d2, vars, cache, in_progress)?;
                if v1.len() >= 2 && v2.len() >= 2 {
                    // 外積(sin)と内積(cos)で有向角を一意に表現
                    let cross = v1[0] * v2[1] - v1[1] * v2[0];
                    let dot = v1[0] * v2[0] + v1[1] * v2[1];
                    Some(vec![cross, dot, ModInt::new(1)])
                } else {
                    None
                }
            }
            Definition::LengthSq(p1, p2) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                Some(vec![mmp_calculators::calc_squared_distance(&v1, &v2), ModInt::new(1), ModInt::new(1)])
            }
            Definition::PerpendicularLine(l, p) => {
                let vl = self.evaluate_node_inner(*l, vars, cache, in_progress)?;
                let vp = self.evaluate_node_inner(*p, vars, cache, in_progress)?;
                Some(mmp_calculators::calc_perpendicular(&vl, &vp))
            }
            Definition::Circumcircle(p1, p2, p3) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                let v3 = self.evaluate_node_inner(*p3, vars, cache, in_progress)?;
                Some(mmp_calculators::calc_circumcircle(&v1, &v2, &v3))
            }
            Definition::TangentLine(c, p) => {
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                let vp = self.evaluate_node_inner(*p, vars, cache, in_progress)?;
                Some(mmp_calculators::calc_tangent_line(&vc, &vp))
            }
            Definition::HarmonicConjugateOf(a, b, c) => {
                let va = self.evaluate_node_inner(*a, vars, cache, in_progress)?;
                let vb = self.evaluate_node_inner(*b, vars, cache, in_progress)?;
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                Some(mmp_calculators::calc_harmonic_conjugate(&va, &vb, &vc))
            }
            _ => None,
        }
    }

    pub fn is_connected(&self, id1: ClassId, id2: ClassId) -> bool {
        let r1 = self.get_rep(id1);
        let r2 = self.get_rep(id2);
        
        for comp in &self.entities[r1.0].components {
            if comp.subobjects.iter().any(|&s| self.get_rep(s) == r2) { return true; }
        }
        for comp in &self.entities[r2.0].components {
            if comp.subobjects.iter().any(|&s| self.get_rep(s) == r1) { return true; }
        }
        false
    }

    /// 🌟 points に含まれる全ての点が乗っている共通の円が存在するかを判定する。
    /// Concyclicを専用Factで持たなくなったので、目標判定などでこれを使う。
    /// 円の数は通常ごく少数なので、全円を舐めても軽い。
    pub fn points_share_a_circle(&self, points: &[ClassId]) -> bool {
        if points.is_empty() { return false; }
        for i in 0..self.entities.len() {
            let cand = ClassId(i);
            if self.get_rep(cand) != cand { continue; }
            if self.entities[i].entity_type != EntityType::Circle { continue; }
            if points.iter().all(|&p| self.is_connected(p, cand)) {
                return true;
            }
        }
        false
    }

    pub fn format_definition(&self, def: &Definition) -> String {
        let get_name = |id: &ClassId| self.entities[self.get_rep(*id).0].name.clone();
        match def {
            Definition::GivenPoint => "GivenPoint".to_string(),
            Definition::FreePoint => "FreePoint".to_string(),
            Definition::Intersection(a, b) => format!("Intersection({}, {})", get_name(a), get_name(b)),
            Definition::LineThroughPoints(a, b) => format!("LineThrough({}, {})", get_name(a), get_name(b)),
            Definition::Midpoint(a, b) => format!("Midpoint({}, {})", get_name(a), get_name(b)),
            Definition::DirectionOf(a) => format!("DirectionOf({})", get_name(a)),
            Definition::PerpDirectionOf(a) => format!("PerpDirectionOf({})", get_name(a)),
            Definition::AnglePair(a, b) => format!("AnglePair({}, {})", get_name(a), get_name(b)),
            Definition::PerpendicularLine(l, p) => format!("Perpendicular({} ⟂ {})", get_name(l), get_name(p)),
            Definition::ParallelLine(l, p) => format!("Parallel({} ∥ {})", get_name(l), get_name(p)),
            Definition::LengthSq(a, b) => format!("LengthSq({}, {})", get_name(a), get_name(b)),
            Definition::Circumcircle(a, b, c) => format!("Circumcircle({}, {}, {})", get_name(a), get_name(b), get_name(c)),
            Definition::TangentLine(c, p) => format!("TangentLine({}, {})", get_name(c), get_name(p)),
            Definition::HarmonicConjugateOf(a, b, c) => format!("HarmonicConjugate({}, {}; {})", get_name(a), get_name(b), get_name(c)),
        }
    }

    /// 🌟 与えられた図形群すべてが乗っている共通の直線を(あれば)1つ返す。
    /// 調和共役点の抽象エンティティを、実際にA,B,Cが乗っている直線に
    /// リンクするために使う(見つからなくても構成自体は成立するので失敗は許容)。
    pub fn find_common_line(&self, ids: &[ClassId]) -> Option<ClassId> {
        if ids.is_empty() { return None; }
        let mut candidates: Option<HashSet<ClassId>> = None;
        for &id in ids {
            let rep = self.get_rep(id);
            let lines: HashSet<ClassId> = self.entities[rep.0].components.first()
                .map(|c| c.subobjects.iter().map(|&s| self.get_rep(s))
                    .filter(|&s| self.entities[s.0].entity_type == EntityType::Line)
                    .collect())
                .unwrap_or_default();
            candidates = Some(match candidates {
                None => lines,
                Some(prev) => prev.intersection(&lines).copied().collect(),
            });
        }
        candidates.and_then(|s| s.into_iter().next())
    }

    /// 🌟 調和共役点の具体的な作図(完全四辺形)。円錐曲線を一切使わず、
    /// 直線と交点だけで A,B を固定点とする対合による C の像 D を作る:
    ///   1. 直線ABC上にない補助点 P を取る
    ///   2. 直線PC上に(P,Cと異なる)補助点 Q を取る
    ///   3. R = 直線AQ と 直線PB の交点
    ///   4. S = 直線BQ と 直線PA の交点
    ///   5. D = 直線RS と 直線ABC の交点
    /// (これは古典的な複比調和点の作図で、補助点P,Qの取り方に依らずDは一意に
    /// 定まることが射影幾何の定理として知られている。本エンジンはこの独立性を
    /// 内部で証明するのではなく、Midpoint/Circumcircle等と同様に既知の結果として
    /// 前提にし、実際に1回具体的に作図した点を抽象的な
    /// Definition::HarmonicConjugateOf(A,B,C) に紐付けることで、以後は
    /// 合同閉包だけで再利用できるようにする)。
    ///
    /// あわせて、対合性 H(A,B,D)=C と 交叉比のペア交換対称性
    /// (A,B;C,D)=-1 ⟹ (C,D;A,B)=-1 つまり H(C,D,A)=B も構造的に登録する。
    /// PerpDirectionOfと同じ理由(無限再帰の回避)で、HarmonicConjugateOf自体は
    /// apply_trivial_relationsの汎用ディスパッチには載せず、この関数だけが
    /// 有限個(3つ)の追加エンティティを明示的に作る。
    pub fn construct_harmonic_conjugate(&mut self, a: ClassId, b: ClassId, c: ClassId) -> ClassId {
        let a = self.get_rep(a);
        let b = self.get_rep(b);
        let c = self.get_rep(c);
        let name = |id: ClassId, eg: &Self| eg.entities[eg.get_rep(id).0].name.clone();

        // 直線ABC: A,Bを通る直線を(既存なら再利用して)確定させる。呼び出し側は
        // Cがこの直線上にあることを前提として呼ぶこと(既に共線でなければ
        // 「調和共役点」という概念自体が意味を持たないので、これは前提条件)。
        let line_abc = self.create_entity(format!("Line_{}_{}_(Aux)", name(a, self), name(b, self)), Definition::new_line(a, b), EntityType::Line);

        // 1. 補助点 P (直線ABC上にない自由点)
        let p = self.create_entity(format!("P_Harm_{}_{}_{}_(Aux)", name(a, self), name(b, self), name(c, self)), Definition::FreePoint, EntityType::Point);
        // 2. 補助点 Q (直線PC上の、P,Cと異なる自由点)
        let line_pc = self.create_entity(format!("Line_{}_{}_(Aux)", name(p, self), name(c, self)), Definition::new_line(p, c), EntityType::Line);
        let q = self.create_entity(format!("Q_Harm_{}_{}_{}_(Aux)", name(a, self), name(b, self), name(c, self)), Definition::FreePoint, EntityType::Point);
        self.link_logical_incidence(q, line_pc);

        // 3. R = AQ ∩ PB
        let line_aq = self.create_entity(format!("Line_{}_{}_(Aux)", name(a, self), name(q, self)), Definition::new_line(a, q), EntityType::Line);
        let line_pb = self.create_entity(format!("Line_{}_{}_(Aux)", name(p, self), name(b, self)), Definition::new_line(p, b), EntityType::Line);
        let r = self.create_entity(format!("R_Harm_{}_{}_{}_(Aux)", name(a, self), name(b, self), name(c, self)), Definition::Intersection(line_aq, line_pb), EntityType::Point);

        // 4. S = BQ ∩ PA
        let line_bq = self.create_entity(format!("Line_{}_{}_(Aux)", name(b, self), name(q, self)), Definition::new_line(b, q), EntityType::Line);
        let line_pa = self.create_entity(format!("Line_{}_{}_(Aux)", name(p, self), name(a, self)), Definition::new_line(p, a), EntityType::Line);
        let s = self.create_entity(format!("S_Harm_{}_{}_{}_(Aux)", name(a, self), name(b, self), name(c, self)), Definition::Intersection(line_bq, line_pa), EntityType::Point);

        // 5. D = RS ∩ ABC
        let line_rs = self.create_entity(format!("Line_{}_{}_(Aux)", name(r, self), name(s, self)), Definition::new_line(r, s), EntityType::Line);
        let d_concrete = self.create_entity(format!("D_Harm_{}_{}_{}_(Aux)", name(a, self), name(b, self), name(c, self)), Definition::Intersection(line_rs, line_abc), EntityType::Point);

        self.apply_congruence_closure();

        // 抽象的な調和共役点エンティティを作り、具体的な作図結果に結びつける
        let hc_def = self.normalize_definition(&Definition::HarmonicConjugateOf(a, b, c));
        let d_abstract = self.create_entity(format!("Harm_{}_{}_{}_(Auto)", name(a, self), name(b, self), name(c, self)), hc_def, EntityType::Point);
        self.merge_entities(d_abstract, d_concrete);
        let d = self.get_rep(d_abstract);
        self.link_logical_incidence(d, line_abc);

        // 対合性: H(A,B,D) ≡ C
        let inv_def = self.normalize_definition(&Definition::HarmonicConjugateOf(a, b, d));
        let inv_id = self.create_entity(format!("Harm_{}_{}_{}_(Auto)", name(a, self), name(b, self), name(d, self)), inv_def, EntityType::Point);
        self.merge_entities(inv_id, c);

        // 交叉比のペア交換対称性: (A,B;C,D)=-1 ⟹ (C,D;A,B)=-1 つまり H(C,D,A) ≡ B
        let c_after = self.get_rep(c);
        let d_after = self.get_rep(d);
        let swap_def = self.normalize_definition(&Definition::HarmonicConjugateOf(c_after, d_after, a));
        let swap_id = self.create_entity(format!("Harm_{}_{}_{}_(Auto)", name(c_after, self), name(d_after, self), name(a, self)), swap_def, EntityType::Point);
        self.merge_entities(swap_id, b);

        self.apply_congruence_closure();
        self.get_rep(d)
    }
    /// 現在のE-Graphの有効な同値類と、その作図履歴・関係を出力する
    pub fn dump_state(&self) {
        println!("\n=== 📊 E-Graph State Dump ===");
        let mut active_nodes = Vec::new();
        for i in 0..self.entities.len() {
            let id = ClassId(i);
            if self.get_rep(id) == id { // 代表元のみを抽出
                active_nodes.push(id);
            }
        }

        println!("Active Equivalence Classes: {}", active_nodes.len());
        
        // 型ごとにソートして出力すると見やすい
        active_nodes.sort_by_key(|&id| format!("{:?}", self.entities[id.0].entity_type));

        for &id in &active_nodes {
            let e = &self.entities[id.0];
            println!("🔹 [{:?}] {}", e.entity_type, e.name);
            
            for comp in &e.components {
                // 定義（どうやって作られたか）
                for def in &comp.definitions {
                    if !matches!(def, Definition::FreePoint | Definition::GivenPoint) {
                        println!("    └─ Def: {}", self.format_definition(def));
                    }
                }
                // 所属・接続関係 (Incidence)
                if !comp.subobjects.is_empty() {
                    let mut subs: Vec<String> = comp.subobjects.iter()
                        .map(|s| self.entities[self.get_rep(*s).0].name.clone())
                        .collect();
                    subs.sort();
                    subs.dedup();
                    println!("    └─ Contains/On: {:?}", subs);
                }
            }
        }
        println!("=============================\n");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_line_merge_by_two_points() {
        let mut egraph = EGraph::new();
        let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        
        let l1 = egraph.create_entity("L1".into(), Definition::new_line(p_a, p_b), EntityType::Line);
        let l2 = egraph.create_entity("L2".into(), Definition::new_line(p_b, p_a), EntityType::Line);
        
        egraph.apply_congruence_closure();
        assert_eq!(egraph.get_rep(l1), egraph.get_rep(l2), "2点を共有する直線はマージされるべき");
    }

    #[test]
    fn test_incidence_preservation_after_merge() {
        let mut egraph = EGraph::new();
        let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let p_c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
        
        let l1 = egraph.create_entity("L1".into(), Definition::new_line(p_a, p_b), EntityType::Line);
        let l2 = egraph.create_entity("L2".into(), Definition::FreePoint, EntityType::Line); // 仮の独立した直線
        
        // CをL2上に乗せる (論理リンク)
        egraph.link_logical_incidence(p_c, l2);
        assert!(egraph.is_connected(p_c, l2), "リンク直後は接続されている");

        // L1とL2を強制的にマージ
        egraph.merge_entities(l1, l2);
        egraph.apply_congruence_closure();

        // L2の代表元はL1になっているはずなので、CはL1に乗っていると判定されるべき
        assert!(egraph.is_connected(p_c, l1), "マージ後、所属関係(Incidence)が代表元に引き継がれるべき");
    }

    #[test]
    fn test_line_merge_by_point_and_direction() {
        let mut egraph = EGraph::new();
        let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let p_c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
        
        let l_ab = egraph.create_entity("L_AB".into(), Definition::new_line(p_a, p_b), EntityType::Line);
        let l_ac = egraph.create_entity("L_AC".into(), Definition::new_line(p_a, p_c), EntityType::Line);
        
        let dir_ab = egraph.create_entity("Dir_AB".into(), Definition::DirectionOf(l_ab), EntityType::Direction);
        let dir_ac = egraph.create_entity("Dir_AC".into(), Definition::DirectionOf(l_ac), EntityType::Direction);
        
        // 強制的に方向を同じにする (例えば同位角の定理などで証明されたと仮定)
        egraph.merge_entities(dir_ab, dir_ac);
        egraph.apply_congruence_closure(); // ここで直線の自動マージが走るはず

        // Aという1点を共有し、かつ方向が同じになったので、L_AB と L_AC は同一の直線になるべき
        assert_eq!(egraph.get_rep(l_ab), egraph.get_rep(l_ac), "1点と方向を共有する直線はマージされるべき");
    }

    #[test]
    fn test_perpendicular_creates_ang90() {
        let mut egraph = EGraph::new();
        let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let p_c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
        
        let l_ab = egraph.create_entity("L_AB".into(), Definition::new_line(p_a, p_b), EntityType::Line);
        
        // CからABへ垂線を下ろす
        let perp = egraph.create_entity("Perp_C_AB".into(), Definition::PerpendicularLine(l_ab, p_c), EntityType::Line);
        egraph.apply_congruence_closure();

        // 垂線と元の直線の方向からなる有向角を取得
        let dir_ab = egraph.memo.get(&Definition::DirectionOf(l_ab)).unwrap();
        let dir_perp = egraph.memo.get(&Definition::DirectionOf(perp)).unwrap();
        
        let ang = egraph.memo.get(&Definition::AnglePair(*dir_ab, *dir_perp)).unwrap();
        
        // 自動的にAng90とマージされているはず
        assert_eq!(egraph.get_rep(*ang), egraph.get_rep(egraph.ang90), "垂線から作られた有向角は自動的にAng90にマージされるべき");
    }

    #[test]
    fn test_parallel_merges_directions() {
        let mut egraph = EGraph::new();
        let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let p_c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
        
        let l_ab = egraph.create_entity("L_AB".into(), Definition::new_line(p_a, p_b), EntityType::Line);
        let para = egraph.create_entity("Para_C_AB".into(), Definition::ParallelLine(l_ab, p_c), EntityType::Line);
        egraph.apply_congruence_closure();

        let dir_ab = egraph.memo.get(&Definition::DirectionOf(l_ab)).unwrap();
        let dir_para = egraph.memo.get(&Definition::DirectionOf(para)).unwrap();
        
        assert_eq!(egraph.get_rep(*dir_ab), egraph.get_rep(*dir_para), "平行線として作図された直線の方向はマージされるべき");
    }

    #[test]
    fn test_midpoint_symmetry_and_incidence() {
        let mut egraph = EGraph::new();
        let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        
        let m1 = egraph.create_entity("M1".into(), Definition::Midpoint(p_a, p_b), EntityType::Point);
        let m2 = egraph.create_entity("M2".into(), Definition::Midpoint(p_b, p_a), EntityType::Point);
        egraph.apply_congruence_closure();

        assert_eq!(egraph.get_rep(m1), egraph.get_rep(m2), "引数の順序が逆の中点はマージされるべき");

        // 中点を作図すると自動的にその2点を結ぶ直線が作られ、中点がその上に乗る
        let l_ab = egraph.memo.get(&Definition::LineThroughPoints(p_a, p_b)).expect("ABを結ぶ直線が自動生成されているべき");
        assert!(egraph.is_connected(m1, *l_ab), "中点は元の2点を結ぶ直線上にあるべき");
    }
    #[test]
    fn test_angle_pair_symmetry_and_normalization() {
        let mut egraph = EGraph::new();
        let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let p_c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);

        let l1 = egraph.create_entity("L1".into(), Definition::new_line(p_a, p_b), EntityType::Line);
        let l2 = egraph.create_entity("L2".into(), Definition::new_line(p_b, p_c), EntityType::Line);

        // 🌟 FIX: `*` でデリファレンスして値(ClassId)としてコピーし、借用を即座に終わらせる
        let d1 = *egraph.memo.get(&Definition::DirectionOf(l1)).unwrap();
        let d2 = *egraph.memo.get(&Definition::DirectionOf(l2)).unwrap();

        // 異なる順序で有向角を作成
        let ang1 = egraph.create_entity("Ang1".into(), Definition::AnglePair(d1, d2), EntityType::Angle);
        let ang2 = egraph.create_entity("Ang2".into(), Definition::AnglePair(d1, d2), EntityType::Angle);

        egraph.apply_congruence_closure();
        assert_eq!(egraph.get_rep(ang1), egraph.get_rep(ang2), "同一の方向ペアから作られた有向角は一意にマージされるべき");
    }

    #[test]
    fn test_ang90_constant_propagation() {
        let mut egraph = EGraph::new();
        let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let p_c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);

        let l_ab = egraph.create_entity("L_AB".into(), Definition::new_line(p_a, p_b), EntityType::Line);
        
        let perp = egraph.create_entity("Perp".into(), Definition::PerpendicularLine(l_ab, p_c), EntityType::Line);
        egraph.apply_congruence_closure();

        // 🌟 FIX: 同様に値としてコピー
        let dir_ab = *egraph.memo.get(&Definition::DirectionOf(l_ab)).unwrap();
        let dir_perp = *egraph.memo.get(&Definition::DirectionOf(perp)).unwrap();

        let ang_test = egraph.create_entity("AngTest".into(), Definition::AnglePair(dir_ab, dir_perp), EntityType::Angle);
        egraph.apply_congruence_closure();

        assert_eq!(egraph.get_rep(ang_test), egraph.get_rep(egraph.ang90), "垂直な2直線の有向角はグローバルなang90と一致するべき");
    }

    #[test]
    fn test_parallel_direction_angle_zero() {
        let mut egraph = EGraph::new();
        let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let p_c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);

        let l1 = egraph.create_entity("L1".into(), Definition::new_line(p_a, p_b), EntityType::Line);
        let l2 = egraph.create_entity("L2".into(), Definition::ParallelLine(l1, p_c), EntityType::Line);
        egraph.apply_congruence_closure();

        // 🌟 FIX: 同様に値としてコピー
        let d1 = *egraph.memo.get(&Definition::DirectionOf(l1)).unwrap();
        let d2 = *egraph.memo.get(&Definition::DirectionOf(l2)).unwrap();

        assert_eq!(egraph.get_rep(d1), egraph.get_rep(d2), "平行線作図により方向ベクトルがマージされるべき");
    }

    #[test]
    fn test_perpendiculars_to_same_line_are_parallel() {
        // 🌟 垂線の射影的表現(PerpDirectionOf)の検証:
        // 同じ直線 L に対する2本の垂線(異なる点 B, C からそれぞれ下ろした)は、
        // 「有向角の加法性」等の角度チェイス定理を一切使わずとも、
        // PerpDirectionOf(Dir(L)) という同じ値への合同閉包だけで
        // 自動的に平行(同じ方向)だと判定されるべき。
        let mut egraph = EGraph::new();
        let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let p_c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);

        let l = egraph.create_entity("L".into(), Definition::new_line(p_a, p_b), EntityType::Line);
        let perp_from_b = egraph.create_entity("Perp_B".into(), Definition::PerpendicularLine(l, p_b), EntityType::Line);
        let perp_from_c = egraph.create_entity("Perp_C".into(), Definition::PerpendicularLine(l, p_c), EntityType::Line);
        egraph.apply_congruence_closure();

        let dir_perp_b = *egraph.memo.get(&Definition::DirectionOf(egraph.get_rep(perp_from_b))).unwrap();
        let dir_perp_c = *egraph.memo.get(&Definition::DirectionOf(egraph.get_rep(perp_from_c))).unwrap();

        assert_eq!(
            egraph.get_rep(dir_perp_b), egraph.get_rep(dir_perp_c),
            "同じ直線への2本の垂線は、角度チェイス定理を使わずとも合同閉包だけで方向が一致するべき"
        );
    }

    #[test]
    fn test_harmonic_conjugate_construction_is_numerically_correct() {
        // 🌟 完全四辺形(直線と交点だけ)による調和共役点の作図が、実際に
        // 交叉比 -1 を満たす点を計算していることを、独立した閉じた式
        // (calc_harmonic_conjugate)との数値一致で検証する。
        // A=(0,0), B=(4,0), C=(1,0) のとき、古典的な計算から
        // 調和共役点 D は (-2, 0) になる。
        let mut egraph = EGraph::new();
        let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);

        let d = egraph.construct_harmonic_conjugate(a, b, c);

        // 補助点 P, Q の名前は construct_harmonic_conjugate の命名規則に従う
        let mut vars: FxHashMap<String, ModInt> = FxHashMap::default();
        vars.insert("A_x".into(), ModInt::new(0));
        vars.insert("A_y".into(), ModInt::new(0));
        vars.insert("B_x".into(), ModInt::new(4));
        vars.insert("B_y".into(), ModInt::new(0));
        vars.insert("C_x".into(), ModInt::new(1));
        vars.insert("C_y".into(), ModInt::new(0));
        vars.insert("P_Harm_A_B_C_(Aux)_x".into(), ModInt::new(2));
        vars.insert("P_Harm_A_B_C_(Aux)_y".into(), ModInt::new(5));
        vars.insert("Q_Harm_A_B_C_(Aux)_x".into(), ModInt::new(0));
        vars.insert("Q_Harm_A_B_C_(Aux)_y".into(), ModInt::new(-5));

        let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
        let vd = egraph.evaluate_node(d, &vars, &mut cache).expect("Dが数値的に計算できるべき");
        let vd = mmp_calculators::normalize(&vd);

        // 期待値 D=(-2, 0, 1) (斉次座標)
        let x = vd[0] / vd[2];
        let y = vd[1] / vd[2];
        assert_eq!(x, ModInt::new(-2), "作図されたDのx座標は-2であるべき");
        assert_eq!(y, ModInt::new(0), "作図されたDのy座標は0であるべき");

        // 独立した閉じた式(calc_harmonic_conjugate)とも一致するはず
        let va = egraph.evaluate_node(a, &vars, &mut cache).unwrap();
        let vb = egraph.evaluate_node(b, &vars, &mut cache).unwrap();
        let vc = egraph.evaluate_node(c, &vars, &mut cache).unwrap();
        let vd_formula = mmp_calculators::normalize(&mmp_calculators::calc_harmonic_conjugate(&va, &vb, &vc));
        assert_eq!(vd, vd_formula, "完全四辺形による作図と閉じた式による計算が一致するべき");
    }

    #[test]
    fn test_harmonic_conjugate_is_an_involution() {
        // 🌟 対合性: H(A,B,D) は、Dを求めるための2回目の作図をやり直さずとも
        // 合同閉包だけで自動的にCへ一致するべき(construct_harmonic_conjugateの
        // 内部で登録される)。
        let mut egraph = EGraph::new();
        let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
        let d = egraph.construct_harmonic_conjugate(a, b, c);

        // 新規に作図せず、既存の合同閉包だけでH(A,B,D)=Cが引ける
        let inv_def = egraph.normalize_definition(&Definition::HarmonicConjugateOf(a, b, d));
        let &inv_id = egraph.memo.get(&inv_def).expect("対合の逆像は既にmemoに登録済みのはず");
        assert_eq!(egraph.get_rep(inv_id), egraph.get_rep(c), "H(A,B,H(A,B,C)) は C に一致するべき(対合性)");

        // 交叉比のペア交換対称性: H(C,D,A) は B に一致するべき
        let swap_def = egraph.normalize_definition(&Definition::HarmonicConjugateOf(c, d, a));
        let &swap_id = egraph.memo.get(&swap_def).expect("ペア交換の像も既にmemoに登録済みのはず");
        assert_eq!(egraph.get_rep(swap_id), egraph.get_rep(b), "(A,B;C,D)=-1 ⟹ (C,D;A,B)=-1 つまり H(C,D,A)=B であるべき");
    }
}
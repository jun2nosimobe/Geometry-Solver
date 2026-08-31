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
    AnglePair(ClassId, ClassId),
    Midpoint(ClassId, ClassId),
    LengthSq(ClassId, ClassId),
    TangentLine(ClassId, ClassId),
    ParallelLine(ClassId, ClassId),
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
        }
    }
    
    pub fn get_parents(&self) -> Vec<ClassId> {
        match self {
            Definition::Midpoint(a, b) => vec![*a, *b],
            Definition::DirectionOf(a) => vec![*a],
            Definition::LineThroughPoints(a, b) => vec![*a, *b],
            Definition::Intersection(a, b) => vec![*a, *b],
            Definition::AnglePair(a, b) => vec![*a, *b],
            Definition::PerpendicularLine(a, b) => vec![*a, *b],
            Definition::Circumcircle(a, b, c) => vec![*a, *b, *c],
            Definition::LengthSq(a, b) => vec![*a, *b],
            Definition::TangentLine(c, p) => vec![*c, *p],
            Definition::ParallelLine(l, p) => vec![*l, *p],
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
            worklist: Vec::new()
        };
        // 🌟 定数ノードの生成 (GivenPointをプレースホルダとして利用)
        egraph.ang90 = egraph.create_entity("Ang90".to_string(), Definition::GivenPoint, EntityType::Angle);
        egraph.ang0 = egraph.create_entity("Ang0".to_string(), Definition::GivenPoint, EntityType::Angle);
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
        if should_memoize {
            // 既に同じ定義が存在すれば、既存の代表元を返す (O(1))
            if let Some(&existing_id) = self.memo.get(&def) {
                return self.get_rep(existing_id);
            }
        }
        let id = ClassId(self.entities.len());
        let entity = GeoEntity {
            id, name, entity_type: e_type,
            base_importance: 1.0, heat_bonus: 0.0,
            components: vec![LogicalComponent { definitions: vec![def.clone()], subobjects: HashSet::new() }],
            uses: rustc_hash::FxHashSet::default(), // 🌟 初期化
        };

        self.entities.push(entity);
        self.parents.push(Cell::new(id.0));
        
        for p in def.get_parents() {
            let p_rep = self.get_rep(p);
            self.entities[p_rep.0].uses.insert(id);
        }
        
        if should_memoize {
            self.memo.insert(def.clone(), id);
        }

        // 🌟 重要: 作図した図形はその定義に応じて自動的に incidence/方向関係を張る
        // これを怠ると、Theorem pattern の Connected / DirectionOf が空振りし、
        // `tangent_orthic` のような問題で何も推論が進まなくなる。
        self.apply_trivial_relations(id, &def);
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



#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Fact {
    Collinear(ClassId, ClassId, ClassId),
    Concyclic(ClassId, ClassId, ClassId, ClassId),
    Identical(ClassId, ClassId),
    Connected(ClassId, ClassId), // (Child, Parent)
    Parallel(ClassId, ClassId),
}

impl Fact {
    // 🌟 コンストラクタでID順にソートし、24通りの順列爆発をO(1)で完全に刈り取る
    pub fn new_concyclic(mut a: ClassId, mut b: ClassId, mut c: ClassId, mut d: ClassId) -> Self {
        let mut arr = [a.0, b.0, c.0, d.0];
        arr.sort_unstable();
        Fact::Concyclic(ClassId(arr[0]), ClassId(arr[1]), ClassId(arr[2]), ClassId(arr[3]))
    }

    pub fn new_collinear(mut a: ClassId, mut b: ClassId, mut c: ClassId) -> Self {
        let mut arr = [a.0, b.0, c.0];
        arr.sort_unstable();
        Fact::Collinear(ClassId(arr[0]), ClassId(arr[1]), ClassId(arr[2]))
    }

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
    }

    // 🌟 マージロジック (merge_numerical)
    pub fn merge_entities(&mut self, id1: ClassId, id2: ClassId) -> bool {
        let root1 = self.get_rep(id1);
        let root2 = self.get_rep(id2);
        if root1 == root2 { return false; } // 既に同じ同値類

        // Union-Find のポインタを繋ぐ
        self.parents[root2.0].set(root1.0);

        // Rust特有の魔法 `std::mem::take`
        // root2 の中身を空にして奪い取り、root1 に結合する (クローン不要で爆速)
        let mut root2_comps = std::mem::take(&mut self.entities[root2.0].components);
        let root2_heat = self.entities[root2.0].heat_bonus;
        let root2_imp = self.entities[root2.0].base_importance;
        let root2_name = std::mem::take(&mut self.entities[root2.0].name);

        let root1_entity = &mut self.entities[root1.0];
        root1_entity.components.append(&mut root2_comps);
        root1_entity.heat_bonus = root1_entity.heat_bonus.max(root2_heat);
        root1_entity.base_importance = root1_entity.base_importance.max(root2_imp);

        // 最短名戦略 (Shortest Name Strategy)
        if root2_name.len() < root1_entity.name.len() {
            root1_entity.name = root2_name;
        } else if root2_name.len() == root1_entity.name.len() 
            && !root2_name.contains("(Ghost)") 
            && root1_entity.name.contains("(Ghost)") {
            root1_entity.name = root2_name;
        }
        let mut root2_uses = std::mem::take(&mut self.entities[root2.0].uses);
        self.entities[root1.0].uses.extend(root2_uses);
        
        // 🌟 マージされた代表元を再評価キューに積む (O(1))
        self.worklist.push(root1);
        true
    }

    // 🌟 Trivial Relations (作図時のおまけリンクと方向生成)
    pub fn apply_trivial_relations(&mut self, new_id: ClassId, def: &Definition) {
        match def {
            Definition::LineThroughPoints(p1, p2) => {
                self.link_logical_incidence(*p1, new_id);
                self.link_logical_incidence(*p2, new_id);

                // 自動的に方向 (Dir_...) を作図してリンクする
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
            Definition::PerpendicularLine(l, p) => {
                self.link_logical_incidence(*l, new_id);
                self.link_logical_incidence(*p, new_id);

                let dir1_def = Definition::DirectionOf(*l);
                let dir1_id = self.create_entity(format!("Dir_{}_(Auto)", self.entities[l.0].name), dir1_def, EntityType::Direction);
                
                let dir2_def = Definition::DirectionOf(new_id);
                let dir2_id = self.create_entity(format!("Dir_{}_(Auto)", self.entities[new_id.0].name), dir2_def, EntityType::Direction);

                self.link_logical_incidence(*l, dir1_id);
                self.link_logical_incidence(new_id, dir2_id);

                // 🌟 自動生成した角を「直角 (ang90)」としてE-Graph上でマージする
                let ang1_def = Definition::AnglePair(dir1_id, dir2_id);
                let ang1_id = self.create_entity(format!("Ang90_{}_{}", dir1_id.0, dir2_id.0), ang1_def, EntityType::Angle);
                self.merge_entities(ang1_id, self.ang90);
                
                let ang2_def = Definition::AnglePair(dir2_id, dir1_id);
                let ang2_id = self.create_entity(format!("Ang90_{}_{}", dir2_id.0, dir1_id.0), ang2_def, EntityType::Angle);
                self.merge_entities(ang2_id, self.ang90);
            },
            Definition::TangentLine(c, p) => {
                self.link_logical_incidence(*c, new_id);
                self.link_logical_incidence(*p, new_id);

                let name = format!("Dir_{}_(Auto)", self.entities[new_id.0].name);
                let dir_def = Definition::DirectionOf(new_id);
                let dir_id = self.create_entity(name, dir_def, EntityType::Direction);
                self.link_logical_incidence(new_id, dir_id);
            },
            Definition::AnglePair(d1, d2) => {
                self.link_logical_incidence(*d1, new_id);
                self.link_logical_incidence(*d2, new_id);
            },
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
                    // 垂線の場合は有向角を90度(ang90)にマージ
                    let ang1_def = Definition::AnglePair(dir1_id, dir2_id);
                    let ang1_id = self.create_entity(format!("Ang90_{}_{}", dir1_id.0, dir2_id.0), ang1_def, EntityType::Angle);
                    self.merge_entities(ang1_id, self.ang90);
                    
                    let ang2_def = Definition::AnglePair(dir2_id, dir1_id);
                    let ang2_id = self.create_entity(format!("Ang90_{}_{}", dir2_id.0, dir1_id.0), ang2_def, EntityType::Angle);
                    self.merge_entities(ang2_id, self.ang90);
                } else {
                    // 平行線の場合は方向ベクトルを同一視
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
                
                // MはAB上に乗っているという論理リンクを生成
                let line_def = Definition::new_line(*a, *b);
                let line_id = self.create_entity(format!("Line_{}_{}_(Auto)", self.entities[a.0].name, self.entities[b.0].name), line_def, EntityType::Line);
                self.link_logical_incidence(new_id, line_id);
            },
            _ => {}
        }
    }

    /// 定義内の親IDを最新の代表元に置き換え、順不同図形はソートして一意なシグネチャにする
    pub fn normalize_definition(&self, def: &Definition) -> Definition {
        match def {
            Definition::Midpoint(p1, p2) => {
                let r1 = self.get_rep(*p1);
                let r2 = self.get_rep(*p2);
                if r1.0 > r2.0 { Definition::Midpoint(r2, r1) } else { Definition::Midpoint(r1, r2) }
            },
            Definition::LineThroughPoints(p1, p2) => {
                Definition::new_line(self.get_rep(*p1), self.get_rep(*p2))
            },
            Definition::Intersection(l1, l2) => {
                let r1 = self.get_rep(*l1);
                let r2 = self.get_rep(*l2);
                if r1.0 > r2.0 { Definition::Intersection(r2, r1) } else { Definition::Intersection(r1, r2) }
            },
            Definition::AnglePair(d1, d2) => {
                Definition::AnglePair(self.get_rep(*d1), self.get_rep(*d2))
            },
            Definition::Circumcircle(p1, p2, p3) => {
                let mut arr = [self.get_rep(*p1).0, self.get_rep(*p2).0, self.get_rep(*p3).0];
                arr.sort_unstable();
                Definition::Circumcircle(ClassId(arr[0]), ClassId(arr[1]), ClassId(arr[2]))
            },
            Definition::LengthSq(p1, p2) => {
                let r1 = self.get_rep(*p1);
                let r2 = self.get_rep(*p2);
                if r1.0 > r2.0 { Definition::LengthSq(r2, r1) } else { Definition::LengthSq(r1, r2) }
            },
            Definition::TangentLine(c, p) => {
                Definition::TangentLine(self.get_rep(*c), self.get_rep(*p))
            },
            Definition::PerpendicularLine(l, p) => {
                Definition::PerpendicularLine(self.get_rep(*l), self.get_rep(*p))
            },
            Definition::ParallelLine(l, p) => {
                Definition::ParallelLine(self.get_rep(*l), self.get_rep(*p))
            },
            _ => def.clone(),
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
                    if let Some(&existing_rep) = def_map.get(&norm_def) {
                        if existing_rep != u_rep {
                            // これで安全に可変メソッドを呼び出せます
                            if self.merge_entities(existing_rep, u_rep) {
                                changed_any = true;
                                break; 
                            }
                        }
                    } else {
                        def_map.insert(norm_def, u_rep);
                    }
                }
            }
        }
        
        // 🌟 [構造的マージ] 直線の自動結合 (変更の有無に関わらず実行してグラフを正規化)
        let mut lines = Vec::new();
        for j in 0..self.entities.len() {
            let id = ClassId(j);
            if self.get_rep(id) == id && self.entities[j].entity_type == EntityType::Line {
                lines.push(id);
            }
        }
        
        let mut dir_to_lines: FxHashMap<ClassId, Vec<ClassId>> = FxHashMap::default();
        for &l in &lines {
            // E-Graphの性質上、DirectionOfは正規化されてmemoに格納されている
            if let Some(&dir_id) = self.memo.get(&Definition::DirectionOf(l)) {
                let dir_rep = self.get_rep(dir_id);
                dir_to_lines.entry(dir_rep).or_default().push(l);
            }
        }
        
        for x in 0..lines.len() {
            for y in (x + 1)..lines.len() {
                let l1 = lines[x];
                let l2 = lines[y];
                let mut shared_points = 0;
                
                for p_idx in 0..self.entities.len() {
                    let pt = ClassId(p_idx);
                    if self.get_rep(pt) == pt && self.entities[p_idx].entity_type == EntityType::Point {
                        let c1 = self.entities[pt.0].components.iter().any(|c| c.subobjects.contains(&l1))
                              || self.entities[l1.0].components.iter().any(|c| c.subobjects.contains(&pt));
                        let c2 = self.entities[pt.0].components.iter().any(|c| c.subobjects.contains(&l2))
                              || self.entities[l2.0].components.iter().any(|c| c.subobjects.contains(&pt));
                        
                        if c1 && c2 { shared_points += 1; }
                    }
                }
                
                // 1. 2点を共有していれば無条件でマージ
                // 2. 🌟 NEW: 方向が等しく1点を共有していればマージ
                let same_dir = {
                    let d1 = self.memo.get(&Definition::DirectionOf(l1)).map(|&id| self.get_rep(id));
                    let d2 = self.memo.get(&Definition::DirectionOf(l2)).map(|&id| self.get_rep(id));
                    d1.is_some() && d1 == d2
                };

                if shared_points >= 2 || (shared_points >= 1 && same_dir) {
                    if self.merge_entities(l1, l2) {
                        changed_any = true;
                        println!("  ⚙️ [E-Graph自動マージ] 幾何条件(共有点={}/同方向={})により直線を結合: {} ≡ {}", 
                            shared_points, same_dir, self.entities[l1.0].name, self.entities[l2.0].name);
                    }
                }
            }
        }
        
        changed_any
    }

    /// 🌟 数値評価環境 (MMPテスト用)
    pub fn evaluate_node(
        &self,
        node_id: ClassId,
        vars: &FxHashMap<String, ModInt>,
        cache: &mut FxHashMap<usize, Vec<ModInt>>,
    ) -> Option<Vec<ModInt>> {
        let rep_id = self.get_rep(node_id);
        if let Some(val) = cache.get(&rep_id.0) {
            return Some(val.clone());
        }

        let entity = &self.entities[rep_id.0];
        let def = entity.components.first()?.definitions.first()?;

        let val = match def {
            Definition::FreePoint | Definition::GivenPoint => {
                let x = vars.get(&format!("{}_x", entity.name)).copied().unwrap_or(ModInt::new(0));
                let y = vars.get(&format!("{}_y", entity.name)).copied().unwrap_or(ModInt::new(0));
                Some(vec![x, y, ModInt::new(1)])
            }
            Definition::Midpoint(p1, p2) => {
                let v1 = self.evaluate_node(*p1, vars, cache)?;
                let v2 = self.evaluate_node(*p2, vars, cache)?;
                Some(mmp_calculators::calc_midpoint(&v1, &v2))
            }
            Definition::LineThroughPoints(p1, p2) => {
                let v1 = self.evaluate_node(*p1, vars, cache)?;
                let v2 = self.evaluate_node(*p2, vars, cache)?;
                Some(mmp_calculators::calc_line_through_points(&v1, &v2))
            }
            Definition::Intersection(l1, l2) => {
                let v1 = self.evaluate_node(*l1, vars, cache)?;
                let v2 = self.evaluate_node(*l2, vars, cache)?;
                Some(mmp_calculators::calc_intersection(&v1, &v2))
            }
            Definition::DirectionOf(l) => {
                let v = self.evaluate_node(*l, vars, cache)?;
                if v.len() >= 3 {
                    // 直線 ax + by + c = 0 の方向ベクトルは (b, -a)
                    Some(mmp_calculators::normalize(&[v[1], -v[0]]))
                } else {
                    None
                }
            }
            Definition::AnglePair(d1, d2) => {
                let v1 = self.evaluate_node(*d1, vars, cache)?;
                let v2 = self.evaluate_node(*d2, vars, cache)?;
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
                let v1 = self.evaluate_node(*p1, vars, cache)?;
                let v2 = self.evaluate_node(*p2, vars, cache)?;
                Some(vec![mmp_calculators::calc_squared_distance(&v1, &v2), ModInt::new(1), ModInt::new(1)])
            }
            Definition::PerpendicularLine(l, p) => {
                let vl = self.evaluate_node(*l, vars, cache)?;
                let vp = self.evaluate_node(*p, vars, cache)?;
                Some(mmp_calculators::calc_perpendicular(&vl, &vp))
            }
            Definition::Circumcircle(p1, p2, p3) => {
                let v1 = self.evaluate_node(*p1, vars, cache)?;
                let v2 = self.evaluate_node(*p2, vars, cache)?;
                let v3 = self.evaluate_node(*p3, vars, cache)?;
                Some(mmp_calculators::calc_circumcircle(&v1, &v2, &v3))
            }
            Definition::TangentLine(c, p) => {
                let vc = self.evaluate_node(*c, vars, cache)?;
                let vp = self.evaluate_node(*p, vars, cache)?;
                Some(mmp_calculators::calc_tangent_line(&vc, &vp))
            }
            _ => None,
        };

        if let Some(ref v) = val {
            cache.insert(rep_id.0, v.clone());
        }
        val
    }
}
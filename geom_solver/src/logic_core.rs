use crate::mmp_core::{ClassId, Definition, EGraph, EntityType, Fact};
use rustc_hash::FxHashMap;
use std::collections::{BinaryHeap, VecDeque};
use std::cmp::Ordering;

#[derive(Debug, Clone)]
pub struct FactPatternDef {
    pub fact_type: String,
    pub args: Vec<String>,
    pub target_type: Option<String>,
    pub sub_type: Option<String>,
    pub allow_flip: bool,
    pub flip_group: Option<String>,
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Fact(FactPatternDef),
    Distinct(Vec<String>),
    Order(Vec<String>),
    Not(Box<Pattern>),
}

#[derive(Debug, Clone)]
pub struct ConstructTemplate {
    pub def_type: String,
    pub args: Vec<String>,
    pub target_type: String,
    pub bind_to: String,
}

#[derive(Debug, Clone)]
pub struct FactTemplate {
    pub fact_type: String,
    pub args: Vec<String>,
    pub target_type: Option<String>,
    pub sub_type: Option<String>,
}

#[derive(Debug, Clone)]
pub struct TheoremDef {
    pub name: String,
    pub entities: FxHashMap<String, EntityType>,
    pub patterns: Vec<Pattern>,
    pub constructions: Vec<ConstructTemplate>,
    pub conclusions: Vec<FactTemplate>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    FactProven(Fact),
    NodeMerged,
}

#[derive(Debug, Clone)]
pub struct MatchTask {
    pub priority: i32,
    pub theorem_idx: usize,
    pub bind: FxHashMap<String, ClassId>,
    pub flip_states: FxHashMap<String, bool>,
    pub remaining_patterns: Vec<crate::logic_core::Pattern>,
}

impl PartialEq for MatchTask { fn eq(&self, other: &Self) -> bool { self.priority == other.priority } }
impl Eq for MatchTask {}
impl PartialOrd for MatchTask { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) } }
impl Ord for MatchTask { fn cmp(&self, other: &Self) -> Ordering { self.priority.cmp(&other.priority) } }

pub struct ProverEngine {
    pub egraph: EGraph,
    pub facts: Vec<Fact>,
    pub theorems: Vec<TheoremDef>,
    pub dfs_calls: u64,
}

impl ProverEngine {
    pub fn new(egraph: EGraph) -> Self {
        Self { egraph, facts: Vec::new(), theorems: Vec::new(), dfs_calls: 0 }
    }

    fn estimate_cost(&self, pat: &Pattern, bind: &FxHashMap<String, ClassId>) -> f64 {
        match pat {
            Pattern::Fact(def) => {
                let unbound_count = def.args.iter().filter(|v| !bind.contains_key(*v)).count();
                if unbound_count == 0 { return 0.0; }
                
                if def.fact_type == "Identical" {
                    if unbound_count == 1 { return 1.0; }
                    // 🌟 FIX: (None, None) の Identical はグラフ全体の同値類グループを
                    // スキャンするだけ(O(N))なので、当てずっぽうな DefinedBy より優先する！
                    return 15.0; 
                }
                if def.fact_type == "Connected" {
                    if unbound_count == 1 { return 5.0; }
                    return 10000.0; 
                }
                if def.fact_type == "DefinedBy" {
                    // 🌟 FIX: 全て未バインドならペナルティ大。バインド済み変数がある場合は優先度を上げる
                    if unbound_count == def.args.len() { return 100.0 + (unbound_count as f64); }
                    return 10.0 + (unbound_count as f64) * 20.0;
                }
                if def.fact_type == "Collinear" || def.fact_type == "Concyclic" {
                    if unbound_count < def.args.len() { return 5.0; }
                    return 10.0;
                }
                100.0
            }
            Pattern::Order(vars) | Pattern::Distinct(vars) => {
                if vars.iter().any(|v| !bind.contains_key(v)) { std::f64::INFINITY } else { 0.0 }
            }
            Pattern::Not(inner_pat) => self.estimate_cost(inner_pat, bind),
        }
    }

    pub fn dfs_match(
        &mut self, 
        theorem: &TheoremDef, 
        mut remaining: Vec<Pattern>, 
        mut bind: FxHashMap<String, ClassId>, 
        mut flip_states: FxHashMap<String, bool>,
        on_match: &mut dyn FnMut(&FxHashMap<String, ClassId>)
    ) {
        self.dfs_calls += 1;
        if self.dfs_calls > 100_000 { return; }

        if remaining.is_empty() {
            on_match(&bind);
            return;
        }

        let mut best_idx = 0;
        let mut best_cost = std::f64::INFINITY;
        for (i, pat) in remaining.iter().enumerate() {
            let cost = self.estimate_cost(pat, &bind);
            if cost < best_cost { best_cost = cost; best_idx = i; }
        }

        let pat_to_eval = remaining.remove(best_idx);
        
        // 🌟 デバッグ用ツリー出力（二等辺三角形の定理のみ可視化）
        if theorem.name == "二等辺三角形の底角" {
            let indent = "  ".repeat(bind.len());
            println!("{}▶ 評価: {:?}", indent, pat_to_eval);
        }

        match pat_to_eval {
            Pattern::Order(vars) => {
                let mut is_ordered = true;
                for i in 0..vars.len().saturating_sub(1) {
                    if let (Some(id1), Some(id2)) = (bind.get(&vars[i]), bind.get(&vars[i+1])) {
                        if self.egraph.get_rep(*id1).0 >= self.egraph.get_rep(*id2).0 { is_ordered = false; break; }
                    }
                }
                if is_ordered { self.dfs_match(theorem, remaining.clone(), bind, flip_states, on_match); }
            }
            Pattern::Distinct(vars) => {
                let mut unique_ids = rustc_hash::FxHashSet::default();
                let mut is_distinct = true;

                for v in &vars {
                    if let Some(&id) = bind.get(v) {
                        let rep_id = self.egraph.get_rep(id);
                        if !unique_ids.insert(rep_id.0) { is_distinct = false; break; }
                    }
                }
                if is_distinct { self.dfs_match(theorem, remaining.clone(), bind, flip_states, on_match); }
            }
            Pattern::Fact(def) => {
                self.match_fact_pattern(theorem, &def, remaining.clone(), &bind, flip_states, on_match);
            }
            Pattern::Not(inner_pat) => {
                let mut matched_any = false;
                self.dfs_match(theorem, vec![*inner_pat.clone()], bind.clone(), flip_states.clone(), &mut |_| {
                    matched_any = true;
                });
                if !matched_any {
                    self.dfs_match(theorem, remaining.clone(), bind, flip_states, on_match);
                }
            }
        }
    }

    pub fn match_fact_pattern(
        &mut self, 
        theorem: &TheoremDef, 
        def: &FactPatternDef, 
        remaining: Vec<Pattern>, 
        bind: &FxHashMap<String, ClassId>, 
        flip_states: FxHashMap<String, bool>,
        on_match: &mut dyn FnMut(&FxHashMap<String, ClassId>)
    ) {
        match def.fact_type.as_str() {
            "Identical" => {
                let v1 = &def.args[0];
                let v2 = &def.args[1];
                match (bind.get(v1).copied(), bind.get(v2).copied()) {
                    (Some(id1), Some(id2)) => {
                        if self.egraph.get_rep(id1) == self.egraph.get_rep(id2) {
                            self.dfs_match(theorem, remaining.clone(), bind.clone(), flip_states.clone(), on_match);
                        }
                    }
                    (Some(id), None) | (None, Some(id)) => {
                        let unbound_var = if bind.get(v1).is_none() { v1 } else { v2 };
                        let mut next_bind = bind.clone();
                        next_bind.insert(unbound_var.clone(), self.egraph.get_rep(id));
                        self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), on_match);
                    }
                    (None, None) => {
                        // 🌟 FIX: グラフ全体から「同じ代表元を持つ別々の図形ペア」をO(N)で全て抽出し、起点にする
                        let mut matches = Vec::new();
                        let mut rep_groups: FxHashMap<ClassId, Vec<ClassId>> = FxHashMap::default();
                        
                        for i in 0..self.egraph.entities.len() {
                            let id = ClassId(i);
                            if self.egraph.entities[i].base_importance > 0.0 {
                                let rep = self.egraph.get_rep(id);
                                rep_groups.entry(rep).or_default().push(id);
                            }
                        }
                        
                        for group in rep_groups.values() {
                            if group.len() >= 2 {
                                for i in 0..group.len() {
                                    for j in 0..group.len() {
                                        if i != j {
                                            let mut next_bind = bind.clone();
                                            next_bind.insert(v1.clone(), group[i]);
                                            next_bind.insert(v2.clone(), group[j]);
                                            matches.push(next_bind);
                                        }
                                    }
                                }
                            }
                        }
                        
                        for new_bind in matches {
                            self.dfs_match(theorem, remaining.clone(), new_bind, flip_states.clone(), on_match);
                        }
                    }
                }
            },
            "Connected" => {
                let child_var = &def.args[0];
                let parent_var = &def.args[1];

                match (bind.get(child_var).copied(), bind.get(parent_var).copied()) {
                    (Some(c_id), Some(p_id)) => {
                        let p_rep = self.egraph.get_rep(p_id);
                        let c_rep = self.egraph.get_rep(c_id);
                        let mut found = false;
                        // 🌟 FIX: 全てのコンポーネントを走査する
                        for comp in &self.egraph.entities[p_rep.0].components {
                            if comp.subobjects.contains(&c_rep) { found = true; break; }
                        }
                        if found { self.dfs_match(theorem, remaining.clone(), bind.clone(), flip_states.clone(), on_match); }
                    }
                    (Some(c_id), None) => {
                        let c_rep = self.egraph.get_rep(c_id);
                        for i in 0..self.egraph.entities.len() {
                            let p_id = ClassId(i);
                            let p_rep = self.egraph.get_rep(p_id);
                            if p_rep != p_id || self.egraph.entities[i].base_importance <= 0.0 { continue; }
                            
                            let mut found = false;
                            // 🌟 FIX: 全てのコンポーネントを走査する
                            for comp in &self.egraph.entities[p_rep.0].components {
                                if comp.subobjects.contains(&c_rep) { found = true; break; }
                            }
                            if found {
                                let mut next_bind = bind.clone();
                                next_bind.insert(parent_var.clone(), p_rep);
                                self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), on_match);
                            }
                        }
                    }
                    (None, Some(p_id)) => {
                        let p_rep = self.egraph.get_rep(p_id);
                        let mut child_candidates = rustc_hash::FxHashSet::default();
                        // 🌟 FIX: 全てのコンポーネントを走査する
                        for comp in &self.egraph.entities[p_rep.0].components {
                            for &c_rep in &comp.subobjects {
                                if self.egraph.entities[c_rep.0].base_importance > 0.0 { child_candidates.insert(c_rep); }
                            }
                        }
                        for c_rep in child_candidates {
                            let mut next_bind = bind.clone();
                            next_bind.insert(child_var.clone(), c_rep);
                            self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), on_match);
                        }
                    }
                    _ => {}
                }
            },
            "DefinedBy" => {
                let target_type = def.target_type.as_deref().unwrap_or("");
                let result_var = &def.args[def.args.len() - 1];
                let parent_vars = &def.args[0..def.args.len() - 1];
                let mut matches = Vec::new();

                for i in 0..self.egraph.entities.len() {
                    let node_id = ClassId(i);
                    if self.egraph.get_rep(node_id) != node_id { continue; }
                    
                    // 🌟 FIX: `.first()` をやめ、マージされた図形の持つ全てのコンポーネントを走査する！
                    for comp in &self.egraph.entities[i].components {
                        for d in &comp.definitions {
                            if d.get_type_name() == target_type {
                                let d_parents = d.get_parents();
                                if d_parents.len() == parent_vars.len() {
                                    let is_unordered = target_type == "Midpoint" || target_type == "LineThroughPoints" || target_type == "Intersection" || target_type == "LengthSq" || target_type == "Circumcircle";
                                    
                                    let perms = if is_unordered {
                                        if d_parents.len() == 2 {
                                            vec![(vec![d_parents[0], d_parents[1]], None), (vec![d_parents[1], d_parents[0]], None)]
                                        } else if d_parents.len() == 3 {
                                            // 🌟 FIX: Circumcircle等の3変数順不同パターンのために6通りの順列を生成
                                            vec![
                                                (vec![d_parents[0], d_parents[1], d_parents[2]], None),
                                                (vec![d_parents[0], d_parents[2], d_parents[1]], None),
                                                (vec![d_parents[1], d_parents[0], d_parents[2]], None),
                                                (vec![d_parents[1], d_parents[2], d_parents[0]], None),
                                                (vec![d_parents[2], d_parents[0], d_parents[1]], None),
                                                (vec![d_parents[2], d_parents[1], d_parents[0]], None),
                                            ]
                                        } else {
                                            vec![(d_parents.clone(), None)]
                                        }
                                    } else if target_type == "AnglePair" && def.allow_flip && d_parents.len() == 2 {
                                        let mut valid_perms = Vec::new();
                                        let state = def.flip_group.as_ref().and_then(|g| flip_states.get(g).copied());
                                        if state != Some(true) { valid_perms.push((vec![d_parents[0], d_parents[1]], Some(false))); }
                                        if state != Some(false) { valid_perms.push((vec![d_parents[1], d_parents[0]], Some(true))); }
                                        valid_perms
                                    } else {
                                        vec![(d_parents.clone(), None)]
                                    };
                                    
                                    for (p_ids, flip_val) in perms {
                                        let mut next_bind = bind.clone();
                                        let mut conflict = false;
                                        
                                        for (v_name, &p_id) in parent_vars.iter().zip(p_ids.iter()) {
                                            if let Some(&existing) = next_bind.get(v_name) {
                                                if self.egraph.get_rep(existing) != self.egraph.get_rep(p_id) { conflict = true; break; }
                                            }
                                            next_bind.insert(v_name.clone(), p_id);
                                        }
                                        
                                        if let Some(&existing) = next_bind.get(result_var) {
                                            if self.egraph.get_rep(existing) != node_id { conflict = true; }
                                        }
                                        next_bind.insert(result_var.clone(), node_id);
                                        
                                        if !conflict {
                                            let mut next_flip = flip_states.clone();
                                            if let (Some(group), Some(val)) = (&def.flip_group, flip_val) {
                                                next_flip.insert(group.clone(), val);
                                            }
                                            matches.push((next_bind, next_flip)); 
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                
                if theorem.name == "二等辺三角形の底角" && matches.is_empty() {
                    let indent = "  ".repeat(bind.len());
                    println!("{}  ❌ 候補なし (Args: {:?})", indent, def.args);
                }

                matches.sort_by_key(|(b, _)| {
                    let mut keys: Vec<_> = b.iter().collect();
                    keys.sort_by_key(|k| k.0);
                    format!("{:?}", keys)
                });
                matches.dedup_by_key(|(b, _)| {
                    let mut keys: Vec<_> = b.iter().collect();
                    keys.sort_by_key(|k| k.0);
                    format!("{:?}", keys)
                });
                for (new_bind, new_flip) in matches { 
                    self.dfs_match(theorem, remaining.clone(), new_bind, new_flip, on_match); 
                }
            },
            _ => {
                let mut matches = Vec::new();
                for fact in &self.facts {
                    if let Some(new_bind) = self.try_bind_fact(fact, &def.fact_type, &def.args, bind) { matches.push(new_bind); }
                }
                for new_bind in matches { 
                    self.dfs_match(theorem, remaining.clone(), new_bind, flip_states.clone(), on_match); 
                }
            }
        }
    }

    pub fn execute_constructions(
        &mut self,
        theorem_name: &str,
        constructions: &[ConstructTemplate],
        bind: &mut FxHashMap<String, ClassId>,
    ) -> bool {
        for constr in constructions {
            let mut parent_ids = Vec::new();
            for arg in &constr.args {
                if let Some(&id) = bind.get(arg) {
                    parent_ids.push(self.egraph.get_rep(id));
                } else {
                    return false;
                }
            }
            
            let def = match constr.def_type.as_str() {
                "LineThroughPoints" => Definition::new_line(parent_ids[0], parent_ids[1]),
                "DirectionOf" => Definition::DirectionOf(parent_ids[0]),
                "Midpoint" => {
                    let (a, b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::Midpoint(a, b)
                },
                "AnglePair" => Definition::AnglePair(parent_ids[0], parent_ids[1]),
                "Intersection" => {
                    let (l1, l2) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::Intersection(l1, l2)
                },
                "PerpendicularLine" => Definition::PerpendicularLine(parent_ids[0], parent_ids[1]),
                "TangentLine" => Definition::TangentLine(parent_ids[0], parent_ids[1]),
                "Circumcircle" => {
                    let mut arr = [parent_ids[0].0, parent_ids[1].0, parent_ids[2].0];
                    arr.sort_unstable();
                    Definition::Circumcircle(ClassId(arr[0]), ClassId(arr[1]), ClassId(arr[2]))
                },
                _ => return false,
            };

            // 🌟 FIX: 既に同じ定義のエンティティがキャッシュ（memo）に存在する場合は、
            // 新規作成せずに既存のIDを再利用して無限ループ・ゴミ生成を防ぐ
            let new_id = if let Some(&existing_id) = self.egraph.memo.get(&def) {
                self.egraph.get_rep(existing_id)
            } else {
                let entity_type = match constr.target_type.as_str() {
                    "Line" => EntityType::Line, 
                    "Direction" => EntityType::Direction,
                    "Angle" => EntityType::Angle, 
                    "Circle" => EntityType::Circle,
                    _ => EntityType::Point,
                };
                
                // ネストした変数を防ぐために、定理名が既に含まれていたらそのまま使う
                let name = if theorem_name.contains("(Auto)") {
                    format!("{}_Auto", constr.def_type)
                } else {
                    format!("{}_{}_(Auto)", constr.def_type, theorem_name)
                };
                
                let id = self.egraph.create_entity(name, def.clone(), entity_type);
                self.egraph.apply_trivial_relations(id, &def);
                id
            };
            
            bind.insert(constr.bind_to.clone(), new_id);
        }
        true
    }

    pub fn apply_conclusions(&mut self, theorem_name: &str, conclusions: &[FactTemplate], bind: &FxHashMap<String, ClassId>) -> (bool, Vec<Fact>) {
        let mut applied_anything = false;
        let mut new_facts = Vec::new();

        for conc in conclusions {
            match conc.fact_type.as_str() {
                "Identical" => {
                    if let (Some(&id1), Some(&id2)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1])) {
                        // 🌟 FIX: マージで所有権(名前)を奪われる前に、表示用の名前を取得しておく
                        let name1 = self.egraph.entities[id1.0].name.clone();
                        let name2 = self.egraph.entities[id2.0].name.clone();
                        
                        if self.egraph.merge_entities(id1, id2) {
                            println!("  🟢 [マージ実行] {} ≡ {} (理由: {})", name1, name2, theorem_name);
                            applied_anything = true;
                        }
                    }
                },
                "Collinear" => {
                    if let (Some(&a), Some(&b), Some(&c)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1]), bind.get(&conc.args[2])) {
                        let fact = Fact::new_collinear(self.egraph.get_rep(a), self.egraph.get_rep(b), self.egraph.get_rep(c));
                        if !self.facts.contains(&fact) {
                            self.facts.push(fact.clone());
                            new_facts.push(fact);
                            applied_anything = true;
                        }
                    }
                },
                _ => {}
            }
        }
        (applied_anything, new_facts)
    }

    fn try_bind_fact(&self, _fact: &Fact, _fact_type: &str, _args: &[String], _current_bind: &FxHashMap<String, ClassId>) -> Option<FxHashMap<String, ClassId>> {
        None
    }
}

pub struct BlackboardEngine {
    pub prover: ProverEngine,
    pub task_queue: BinaryHeap<MatchTask>,
    pub event_queue: VecDeque<Event>,
    pub construction_demands: FxHashMap<(ClassId, ClassId), f64>,
}

impl BlackboardEngine {
    pub fn new(prover: ProverEngine) -> Self {
        Self { 
            prover, 
            task_queue: BinaryHeap::new(), 
            event_queue: VecDeque::new(),
            construction_demands: FxHashMap::default(), // 🌟 初期化
        }
    }

    pub fn schedule_full_sweep(&mut self) {
        self.task_queue.clear();
        for (idx, theorem) in self.prover.theorems.iter().enumerate() {
            let task = MatchTask { 
                priority: 0, 
                theorem_idx: idx, 
                bind: rustc_hash::FxHashMap::default(),
                flip_states: rustc_hash::FxHashMap::default(),
                remaining_patterns: theorem.patterns.clone() 
            };
            self.task_queue.push(task);
        }
    }

    fn schedule_matcher_task(&mut self, fact: &Fact) {
        let fact_type = match fact {
            Fact::Collinear(..) => "Collinear",
            Fact::Concyclic(..) => "Concyclic",
            Fact::Identical(..) => "Identical",
            Fact::Connected(..) => "Connected",
            Fact::Parallel(..) => "Parallel",
        };

        for (idx, theorem) in self.prover.theorems.iter().enumerate() {
            let contains_pattern = theorem.patterns.iter().any(|pat| {
                if let Pattern::Fact(def) = pat { def.fact_type == fact_type } else { false }
            });

            if contains_pattern {
                self.task_queue.push(MatchTask {
                    priority: 10,
                    theorem_idx: idx,
                    bind: rustc_hash::FxHashMap::default(),
                    flip_states: rustc_hash::FxHashMap::default(),
                    remaining_patterns: theorem.patterns.clone(),
                });
            }
        }
    }

    pub fn emit(&mut self, event: Event) {
        self.event_queue.push_back(event);
    }

    pub fn run_step(&mut self, budget: usize) -> bool {
        let mut applied_anything = false;
        let mut calls = 0;

        while calls < budget {
            while let Some(event) = self.event_queue.pop_front() {
                match event {
                    Event::NodeMerged => {
                        if self.prover.egraph.apply_congruence_closure() {
                            applied_anything = true;
                            self.event_queue.push_back(Event::NodeMerged);
                        }
                    },
                    Event::FactProven(fact) => {
                        if !self.prover.facts.contains(&fact) {
                            self.prover.facts.push(fact.clone());
                            self.schedule_matcher_task(&fact);
                        }
                    }
                }
            }

            if let Some(task) = self.task_queue.pop() {
                calls += 1;
                let theorem = self.prover.theorems[task.theorem_idx].clone();
                let mut new_binds = Vec::new();

                self.prover.dfs_match(&theorem, task.remaining_patterns, task.bind, task.flip_states, &mut |bind: &FxHashMap<String, ClassId>| {
                    if theorem.name == "二等辺三角形の底角" { println!("  🚀 リーチ！パターン全てマッチ"); }
                    new_binds.push(bind.clone());
                });

                for mut bind in new_binds {
                    if self.prover.execute_constructions(&theorem.name, &theorem.constructions, &mut bind) {
                        let (applied, generated_facts) = self.prover.apply_conclusions(&theorem.name, &theorem.conclusions, &bind);
                        if applied {
                            applied_anything = true;
                            self.emit(Event::NodeMerged); 
                            for f in generated_facts { self.emit(Event::FactProven(f)); }
                        }
                    }
                }
            } else { break; }
        }
        applied_anything
    }

    // 🌟 フェーズ1.5: 交点を持つ2直線のペアから有向角(AnglePair)を自動生成
    pub fn resolve_angle_demands(&mut self) -> bool {
        let mut applied = false;
        let mut angle_pairs_to_create = Vec::new();

        for i in 0..self.prover.egraph.entities.len() {
            let pt_id = ClassId(i);
            if self.prover.egraph.get_rep(pt_id) != pt_id { continue; }
            if self.prover.egraph.entities[i].entity_type != EntityType::Point { continue; }

            // この点を通る直線を収集
            let mut lines_on_pt = Vec::new();
            for comp in &self.prover.egraph.entities[i].components {
                for &sub_id in &comp.subobjects {
                    let sub_rep = self.prover.egraph.get_rep(sub_id);
                    if self.prover.egraph.entities[sub_rep.0].entity_type == EntityType::Line {
                        lines_on_pt.push(sub_rep);
                    }
                }
            }
            lines_on_pt.sort_unstable_by_key(|id| id.0);
            lines_on_pt.dedup();

            if lines_on_pt.len() >= 2 {
                for l1 in 0..lines_on_pt.len() {
                    for l2 in (l1 + 1)..lines_on_pt.len() {
                        // 2直線のDirectionを取得してペアにする
                        let d1 = self.get_or_create_direction(lines_on_pt[l1]);
                        let d2 = self.get_or_create_direction(lines_on_pt[l2]);
                        angle_pairs_to_create.push((d1, d2));
                    }
                }
            }
        }

        for (d1, d2) in angle_pairs_to_create {
            let def = Definition::AnglePair(d1, d2);
            if !self.prover.egraph.memo.contains_key(&def) {
                let name = format!("AnglePair_{}_{}_(Auto)", self.prover.egraph.entities[d1.0].name, self.prover.egraph.entities[d2.0].name);
                let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Angle);
                self.prover.egraph.apply_trivial_relations(new_id, &def);
                applied = true;
            }
        }

        if applied {
            println!("  💡 [スマート補完] 交点を持つ意味のある有向角を自動生成しました");
            self.schedule_full_sweep();
        }
        applied
    }

    fn get_or_create_direction(&mut self, line_id: ClassId) -> ClassId {
        let def = Definition::DirectionOf(line_id);
        if let Some(&dir_id) = self.prover.egraph.memo.get(&def) {
            return self.prover.egraph.get_rep(dir_id);
        }
        let name = format!("Dir_{}_(Fallback)", self.prover.egraph.entities[line_id.0].name);
        let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Direction);
        self.prover.egraph.apply_trivial_relations(new_id, &def);
        new_id
    }

    // 🌟 フェーズ2: 論理エンジンが欲しがっていた補助線(Demand)を引く
    pub fn resolve_demands(&mut self) -> bool {
        if self.construction_demands.is_empty() { return false; }

        let mut demands: Vec<_> = self.construction_demands.iter().collect();
        demands.sort_by(|a, b| b.1.partial_cmp(a.1).unwrap_or(Ordering::Equal));

        let mut applied = false;
        for (&(p1, p2), &score) in demands.into_iter().take(3) { // 上位3件のみ
            let def = Definition::new_line(p1, p2);
            if !self.prover.egraph.memo.contains_key(&def) {
                let name = format!("Line_{}_{}_(Demand)", self.prover.egraph.entities[p1.0].name, self.prover.egraph.entities[p2.0].name);
                println!("  💡 [オンデマンド作図] 要請により {} を生成 (需要: {:.1})", name, score);
                let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Line);
                self.prover.egraph.apply_trivial_relations(new_id, &def);
                applied = true;
            }
        }
        
        self.construction_demands.clear();
        if applied { self.schedule_full_sweep(); }
        applied
    }

    pub fn check_target_reached(&self) -> bool { false }
}
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
                if def.fact_type == "Collinear" || def.fact_type == "Concyclic" {
                    if unbound_count < def.args.len() { return 5.0; }
                    return 10.0;
                }
                if def.fact_type == "Identical" {
                    if unbound_count == 1 { return 1.0; }
                    return 15.0;
                }
                if def.fact_type == "Connected" {
                    if unbound_count == 1 { return 5.0; }
                    return 10000.0; 
                }
                100.0
            }
            Pattern::Order(vars) | Pattern::Distinct(vars) => {
                if vars.iter().any(|v| !bind.contains_key(v)) { std::f64::INFINITY } else { 0.0 }
            }
            Pattern::Not(inner_pat) => self.estimate_cost(inner_pat, bind),
        }
    }

    pub fn dfs_match<F>(&mut self, theorem: &TheoremDef, mut remaining: Vec<Pattern>, mut bind: FxHashMap<String, ClassId>, on_match: &mut F) 
    where F: FnMut(&FxHashMap<String, ClassId>) {
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

        match pat_to_eval {
            Pattern::Order(vars) => {
                let mut is_ordered = true;
                for i in 0..vars.len().saturating_sub(1) {
                    if let (Some(id1), Some(id2)) = (bind.get(&vars[i]), bind.get(&vars[i+1])) {
                        if self.egraph.get_rep(*id1).0 >= self.egraph.get_rep(*id2).0 { is_ordered = false; break; }
                    }
                }
                if is_ordered { self.dfs_match(theorem, remaining.clone(), bind, on_match); }
            }
            Pattern::Distinct(vars) => {
                let mut unique_ids = rustc_hash::FxHashSet::default();
                let mut is_distinct = true;
                let mut debug_binds = Vec::new(); // デバッグ用

                for v in &vars {
                    if let Some(&id) = bind.get(v) {
                        // 🌟 FIX: 未正規化のIDではなく、常に get_rep(id) で代表元を比較して重複を判定する
                        let rep_id = self.egraph.get_rep(id);
                        debug_binds.push((v.clone(), rep_id.0));
                        if !unique_ids.insert(rep_id.0) { is_distinct = false; break; }
                    }
                }
                
                if theorem.name == "中点連結定理" {
                    println!("  [DFS Step] Distinct判定: {:?} -> {}", debug_binds, is_distinct);
                }

                if is_distinct { self.dfs_match(theorem, remaining.clone(), bind, on_match); }
            }
            Pattern::Fact(def) => {
                self.match_fact_pattern(theorem, &def, remaining.clone(), &bind, on_match);
            }
            Pattern::Not(_) => {
                self.dfs_match(theorem, remaining.clone(), bind, on_match);
            }
        }
    }

    pub fn match_fact_pattern<F>(&mut self, theorem: &TheoremDef, def: &FactPatternDef, remaining: Vec<Pattern>, bind: &FxHashMap<String, ClassId>, on_match: &mut F) 
    where F: FnMut(&FxHashMap<String, ClassId>) {
        match def.fact_type.as_str() {
            "DefinedBy" => {
                let target_type = def.target_type.as_deref().unwrap_or("");
                let result_var = &def.args[def.args.len() - 1];
                let parent_vars = &def.args[0..def.args.len() - 1];
                let mut matches = Vec::new();

                for i in 0..self.egraph.entities.len() {
                    let node_id = ClassId(i);
                    if self.egraph.get_rep(node_id) != node_id { continue; }
                    
                    if let Some(comp) = self.egraph.entities[i].components.first() {
                        for d in &comp.definitions {
                            if d.get_type_name() == target_type {
                                let d_parents = d.get_parents();
                                if d_parents.len() == parent_vars.len() {
                                    let is_unordered = target_type == "Midpoint" || target_type == "LineThroughPoints" || target_type == "Intersection";
                                    let perms = if is_unordered && d_parents.len() == 2 {
                                        vec![vec![d_parents[0], d_parents[1]], vec![d_parents[1], d_parents[0]]]
                                    } else {
                                        vec![d_parents.clone()]
                                    };
                                    
                                    for p_ids in perms {
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
                                        
                                        if !conflict { matches.push(next_bind); }
                                    }
                                }
                            }
                        }
                    }
                }
                
                matches.sort_by_key(|b| {
                    let mut keys: Vec<_> = b.iter().collect();
                    keys.sort_by_key(|k| k.0);
                    format!("{:?}", keys)
                });
                matches.dedup();
                for new_bind in matches { self.dfs_match(theorem, remaining.clone(), new_bind, on_match); }
            },
            _ => {
                let mut matches = Vec::new();
                for fact in &self.facts {
                    if let Some(new_bind) = self.try_bind_fact(fact, &def.fact_type, &def.args, bind) { matches.push(new_bind); }
                }
                for new_bind in matches { self.dfs_match(theorem, remaining.clone(), new_bind, on_match); }
            }
        }
    }

    pub fn execute_constructions(&mut self, theorem_name: &str, constructions: &[ConstructTemplate], bind: &mut FxHashMap<String, ClassId>) -> bool {
        for constr in constructions {
            let mut parent_ids = Vec::new();
            for arg in &constr.args {
                if let Some(&id) = bind.get(arg) {
                    parent_ids.push(self.egraph.get_rep(id));
                } else {
                    println!("  ⚠️ [作図失敗] 変数 {} がバインドされていません", arg);
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
                _ => return false,
            };
            
            let entity_type = match constr.target_type.as_str() {
                "Line" => EntityType::Line, "Direction" => EntityType::Direction,
                "Angle" => EntityType::Angle, _ => EntityType::Point,
            };
            
            let name = format!("{}_{}_(Auto)", constr.def_type, theorem_name);
            let new_id = self.egraph.create_entity(name, def.clone(), entity_type);
            self.egraph.apply_trivial_relations(new_id, &def);
            bind.insert(constr.bind_to.clone(), new_id);
        }
        true
    }

    pub fn apply_conclusions(&mut self, theorem_name: &str, conclusions: &[FactTemplate], bind: &FxHashMap<String, ClassId>) -> bool {
        let mut applied_anything = false;

        for conc in conclusions {
            match conc.fact_type.as_str() {
                "Identical" => {
                    if let (Some(&id1), Some(&id2)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1])) {
                        if self.egraph.merge_entities(id1, id2) {
                            println!("  🟢 [マージ実行] {} ≡ {} (理由: {})", self.egraph.entities[id1.0].name, self.egraph.entities[id2.0].name, theorem_name);
                            applied_anything = true;
                        }
                    }
                },
                _ => {}
            }
        }
        applied_anything
    }

    fn try_bind_fact(&self, _fact: &Fact, _fact_type: &str, _args: &[String], _current_bind: &FxHashMap<String, ClassId>) -> Option<FxHashMap<String, ClassId>> {
        None
    }
}

pub struct BlackboardEngine {
    pub prover: ProverEngine,
    pub task_queue: BinaryHeap<MatchTask>,
    pub event_queue: VecDeque<Event>,
}

impl BlackboardEngine {
    pub fn new(prover: ProverEngine) -> Self {
        Self { prover, task_queue: BinaryHeap::new(), event_queue: VecDeque::new() }
    }

    pub fn schedule_full_sweep(&mut self) {
        self.task_queue.clear();
        for (idx, theorem) in self.prover.theorems.iter().enumerate() {
            let task = MatchTask { priority: 0, theorem_idx: idx, bind: rustc_hash::FxHashMap::default(), remaining_patterns: theorem.patterns.clone() };
            self.task_queue.push(task);
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
                if let Event::NodeMerged = event {
                    if self.prover.egraph.apply_congruence_closure() {
                        applied_anything = true;
                        self.event_queue.push_back(Event::NodeMerged);
                    }
                }
            }

            if let Some(task) = self.task_queue.pop() {
                calls += 1;
                let theorem = self.prover.theorems[task.theorem_idx].clone();
                let mut new_binds = Vec::new();

                self.prover.dfs_match(&theorem, task.remaining_patterns, task.bind, &mut |bind| {
                    println!("  🚀 リーチ！定理 '{}' のパターンが全てマッチしました", theorem.name);
                    new_binds.push(bind.clone());
                });

                for mut bind in new_binds {
                    if self.prover.execute_constructions(&theorem.name, &theorem.constructions, &mut bind) {
                        if self.prover.apply_conclusions(&theorem.name, &theorem.conclusions, &bind) {
                            applied_anything = true;
                            self.emit(Event::NodeMerged);
                        }
                    }
                }
            } else { break; }
        }
        applied_anything
    }

    pub fn check_target_reached(&self) -> bool { false }
}
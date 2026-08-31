use crate::mmp_core::{ClassId, Definition, EGraph, EntityType, Fact};
use rustc_hash::FxHashMap;
use std::collections::{BinaryHeap, VecDeque};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

fn get_permutations(items: &[ClassId]) -> Vec<Vec<ClassId>> {
    if items.len() <= 1 { return vec![items.to_vec()]; }
    let mut result = Vec::new();
    for i in 0..items.len() {
        let mut rest = items.to_vec();
        let val = rest.remove(i);
        for mut sub in get_permutations(&rest) {
            sub.insert(0, val);
            result.push(sub);
        }
    }
    result
}

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
    pub construction_demands: FxHashMap<(ClassId, ClassId), f64>, // 🌟 Blackboardから移動
}

impl ProverEngine {
    pub fn new(egraph: EGraph) -> Self {
        Self { 
            egraph, 
            facts: Vec::new(), 
            theorems: Vec::new(), 
            dfs_calls: 0,
            construction_demands: FxHashMap::default(), // 🌟 追加
        }
    }
    fn calc_bind_heat(&self, bind: &FxHashMap<String, ClassId>) -> f64 {
        let mut heat = 0.0;
        for &id in bind.values() {
            let rep = self.egraph.get_rep(id);
            let e = &self.egraph.entities[rep.0];
            // 熱(heat_bonus) + 基本重要度 + 次数(uses.len()による依存度)
            heat += e.base_importance + e.heat_bonus + (e.uses.len() as f64 * 0.5);
        }
        heat
    }

    fn estimate_cost(&self, pat: &Pattern, bind: &FxHashMap<String, ClassId>) -> f64 {
        match pat {
            Pattern::Fact(def) => {
                let unbound_count = def.args.iter().filter(|v| !bind.contains_key(*v)).count();
                if unbound_count == 0 { return 0.0; }
                
                let base_cost = if def.fact_type == "Identical" {
                    if unbound_count == 1 { 1.0 } else { 15.0 }
                } else if def.fact_type == "Connected" {
                    if unbound_count == 1 { 5.0 } else { 10000.0 }
                } else if def.fact_type == "DefinedBy" {
                    if unbound_count == def.args.len() { 
                        let penalty = match def.target_type.as_deref().unwrap_or("") {
                            "Midpoint" | "LengthSq" | "Intersection" => 0.0,
                            "LineThroughPoints" | "PerpendicularLine" | "TangentLine" => 10.0,
                            "DirectionOf" | "AnglePair" | "Circumcircle" => 20.0,
                            _ => 5.0,
                        };
                        100.0 + (unbound_count as f64) + penalty 
                    } else {
                        10.0 + (unbound_count as f64) * 20.0
                    }
                } else if def.fact_type == "Collinear" || def.fact_type == "Concyclic" {
                    if unbound_count < def.args.len() { 5.0 } else { 10.0 }
                } else {
                    100.0
                };

                // バインド済み変数の熱と次数が高いほどコストを下げる(優先探索)
                let mut heat = 0.0;
                for v in &def.args {
                    if let Some(&id) = bind.get(v) {
                        let rep = self.egraph.get_rep(id);
                        let e = &self.egraph.entities[rep.0];
                        heat += e.base_importance + e.heat_bonus + (e.uses.len() as f64 * 0.5);
                    }
                }
                
                (base_cost - heat).max(0.1) // 完全に0にはせず僅かなコストを残す[cite: 5]
            }
            Pattern::Order(vars) | Pattern::Distinct(vars) => {
                if vars.iter().any(|v| !bind.contains_key(v)) { std::f64::INFINITY } else { 0.0 }
            }
            Pattern::Not(inner_pat) => self.estimate_cost(inner_pat, bind),
        }
    }
    
    pub fn is_already_proven(&self, conclusions: &[FactTemplate], bind: &FxHashMap<String, ClassId>, flips: &FxHashMap<String, bool>) -> bool {
        for conc in conclusions {
            match conc.fact_type.as_str() {
                "Identical" => {
                    if let (Some(&id1), Some(&id2)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1])) {
                        let rep1 = self.egraph.get_rep(id1);
                        let rep2 = self.egraph.get_rep(id2);
                        // 🌟 FIX: 型に関わらず、代表元が同じなら証明済みとみなす
                        if rep1 != rep2 { return false; } 
                        
                        // 角の場合はフリップの向きも一致しているか確認
                        if self.egraph.entities[rep1.0].entity_type == crate::mmp_core::EntityType::Angle {
                            let f1 = flips.get(&conc.args[0]).copied().unwrap_or(false);
                            let f2 = flips.get(&conc.args[1]).copied().unwrap_or(false);
                            if f1 != f2 { return false; }
                        }
                    } else { return false; }
                },
                "Collinear" => {
                    if let (Some(&a), Some(&b), Some(&c)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1]), bind.get(&conc.args[2])) {
                        let fact = Fact::new_collinear(self.egraph.get_rep(a), self.egraph.get_rep(b), self.egraph.get_rep(c));
                        if !self.facts.contains(&fact) { return false; }
                    } else { return false; }
                },
                "Concyclic" => {
                    if let (Some(&a), Some(&b), Some(&c), Some(&d)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1]), bind.get(&conc.args[2]), bind.get(&conc.args[3])) {
                        let fact = Fact::new_concyclic(self.egraph.get_rep(a), self.egraph.get_rep(b), self.egraph.get_rep(c), self.egraph.get_rep(d));
                        if !self.facts.contains(&fact) { return false; }
                    } else { return false; }
                },
                "Connected" => {
                    if let (Some(&child), Some(&parent)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1])) {
                        if !self.egraph.is_connected(child, parent) { return false; }
                    } else { return false; }
                },
                _ => return false,
            }
        }
        true
    }

    pub fn dfs_match(
        &mut self, 
        theorem: &TheoremDef, 
        mut remaining: Vec<Pattern>, 
        bind: FxHashMap<String, ClassId>, 
        flip_states: FxHashMap<String, bool>,
        failed_paths: &mut rustc_hash::FxHashSet<u64>, // 🌟 追加
        on_match: &mut dyn FnMut(&FxHashMap<String, ClassId>, &FxHashMap<String, bool>)
    ) {
        self.dfs_calls += 1;
        if self.dfs_calls > 100_000 { return; }

        // 🌟 失敗パスのキャッシュチェック
        let state_sig = {
            let mut hasher = rustc_hash::FxHasher::default();
            remaining.len().hash(&mut hasher);
            
            let mut pairs: Vec<_> = bind.iter().collect();
            pairs.sort_unstable_by_key(|k| k.0);
            for (k, v) in pairs {
                k.hash(&mut hasher);
                self.egraph.get_rep(*v).0.hash(&mut hasher);
            }
            
            // 🌟 FIX: フリップ状態もハッシュに含めないと、向き違いの正当な探索が枝刈りされてしまう
            let mut flips: Vec<_> = flip_states.iter().collect();
            flips.sort_unstable_by_key(|k| k.0);
            for (k, v) in flips {
                k.hash(&mut hasher);
                v.hash(&mut hasher);
            }
            
            hasher.finish()
        };

        if failed_paths.contains(&state_sig) { return; }

        if remaining.is_empty() {
            for (v_name, id) in &bind {
                if let Some(expected_type) = theorem.entities.get(v_name) {
                    let actual_type = self.egraph.entities[self.egraph.get_rep(*id).0].entity_type;
                    if *expected_type != actual_type { return; }
                }
            }
            on_match(&bind, &flip_states);
            return;
        }

        let mut best_idx = 0;
        let mut best_cost = std::f64::INFINITY;
        for (i, pat) in remaining.iter().enumerate() {
            let cost = self.estimate_cost(pat, &bind);
            if cost < best_cost { best_cost = cost; best_idx = i; }
        }

        let pat_to_eval = remaining.remove(best_idx);
        let mut matched_any = false;

        // クロージャをラップして、1度でもマッチしたかを記録する
        let mut wrapped_on_match = |b: &FxHashMap<String, ClassId>, f: &FxHashMap<String, bool>| {
            matched_any = true;
            on_match(b, f);
        };

        match pat_to_eval {
            Pattern::Order(vars) => {
                let mut is_ordered = true;
                for i in 0..vars.len().saturating_sub(1) {
                    if let (Some(id1), Some(id2)) = (bind.get(&vars[i]), bind.get(&vars[i+1])) {
                        if self.egraph.get_rep(*id1).0 >= self.egraph.get_rep(*id2).0 { is_ordered = false; break; }
                    }
                }
                if is_ordered { self.dfs_match(theorem, remaining.clone(), bind, flip_states, failed_paths, &mut wrapped_on_match); }
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
                if is_distinct { self.dfs_match(theorem, remaining.clone(), bind, flip_states, failed_paths, &mut wrapped_on_match); }
            }
            Pattern::Fact(def) => {
                self.match_fact_pattern(theorem, &def, remaining.clone(), &bind, flip_states, failed_paths, &mut wrapped_on_match);
            }
            Pattern::Not(inner_pat) => {
                let mut inner_matched = false;
                self.dfs_match(theorem, vec![*inner_pat.clone()], bind.clone(), flip_states.clone(), failed_paths, &mut |_, _| {
                    inner_matched = true;
                });
                if !inner_matched {
                    self.dfs_match(theorem, remaining.clone(), bind, flip_states, failed_paths, &mut wrapped_on_match);
                }
            }
        }

        // 🌟 どこにも進めなかった場合、この状態を失敗として記録する
        if !matched_any {
            failed_paths.insert(state_sig);
        }
    }
    pub fn match_fact_pattern(
        &mut self, 
        theorem: &TheoremDef, 
        def: &FactPatternDef, 
        remaining: Vec<Pattern>, 
        bind: &FxHashMap<String, ClassId>, 
        flip_states: FxHashMap<String, bool>,
        failed_paths: &mut rustc_hash::FxHashSet<u64>,
        on_match: &mut dyn FnMut(&FxHashMap<String, ClassId>, &FxHashMap<String, bool>)
    ) {
        
        match def.fact_type.as_str() {
            "Identical" => {
                let v1 = &def.args[0];
                let v2 = &def.args[1];
                let expected_type = theorem.entities.get(v1).copied(); // 🌟 型情報取得

                match (bind.get(v1).copied(), bind.get(v2).copied()) {
                    (Some(id1), Some(id2)) => {
                        if self.egraph.get_rep(id1) == self.egraph.get_rep(id2) {
                            self.dfs_match(theorem, remaining.clone(), bind.clone(), flip_states.clone(), failed_paths, on_match);
                        }
                    }
                    (Some(id), None) | (None, Some(id)) => {
                        let unbound_var = if bind.get(v1).is_none() { v1 } else { v2 };
                        let mut next_bind = bind.clone();
                        next_bind.insert(unbound_var.clone(), self.egraph.get_rep(id));
                        self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), failed_paths, on_match);
                    }
                    (None, None) => {
                        let mut matches = Vec::new();
                        let mut rep_groups: FxHashMap<ClassId, Vec<ClassId>> = FxHashMap::default();
                        for i in 0..self.egraph.entities.len() {
                            let id = ClassId(i);
                            // 🌟 型が違うものは最初からグループに入れない (超高速化)
                            if let Some(et) = expected_type {
                                if self.egraph.entities[i].entity_type != et { continue; }
                            }
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
                        for new_bind in matches { self.dfs_match(theorem, remaining.clone(), new_bind, flip_states.clone(), failed_paths, on_match); 
                        }
                    }
                }
            },
            "Connected" => {
                let child_var = &def.args[0];
                let parent_var = &def.args[1];
                let expected_c_type = theorem.entities.get(child_var).copied(); 
                let expected_p_type = theorem.entities.get(parent_var).copied();

                match (bind.get(child_var).copied(), bind.get(parent_var).copied()) {
                    (Some(c_id), Some(p_id)) => {
                        // 🌟 FIX
                        if self.egraph.is_connected(c_id, p_id) { 
                            self.dfs_match(theorem, remaining.clone(), bind.clone(), flip_states.clone(), failed_paths, on_match); 
                        }
                    }
                    (Some(c_id), None) => {
                        let c_rep = self.egraph.get_rep(c_id);
                        for i in 0..self.egraph.entities.len() {
                            let p_id = ClassId(i);
                            let p_rep = self.egraph.get_rep(p_id);
                            if p_rep != p_id || self.egraph.entities[i].base_importance <= 0.0 { continue; }
                            
                            if let Some(et) = expected_p_type {
                                if self.egraph.entities[p_rep.0].entity_type != et { continue; }
                            }
                            // 🌟 FIX
                            if self.egraph.is_connected(c_rep, p_rep) {
                                let mut next_bind = bind.clone();
                                next_bind.insert(parent_var.clone(), p_rep);
                                self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), failed_paths, on_match);
                            }
                        }
                    }
                    (None, Some(p_id)) => {
                        let p_rep = self.egraph.get_rep(p_id);
                        let mut child_candidates = rustc_hash::FxHashSet::default();
                        for comp in &self.egraph.entities[p_rep.0].components {
                            for &sub in &comp.subobjects {
                                // 🌟 FIX: 必ず rep を通す
                                let s_rep = self.egraph.get_rep(sub);
                                if self.egraph.entities[s_rep.0].base_importance > 0.0 { child_candidates.insert(s_rep); }
                            }
                        }
                        for c_rep in child_candidates {
                            if let Some(et) = expected_c_type {
                                if self.egraph.entities[c_rep.0].entity_type != et { continue; }
                            }
                            let mut next_bind = bind.clone();
                            next_bind.insert(child_var.clone(), c_rep);
                            self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), failed_paths, on_match);
                        }
                    }
                    _ => {}
                }
            },
            "DefinedBy" => {
                let target_type = def.target_type.as_deref().unwrap_or("");
                let result_var = &def.args[def.args.len() - 1];
                let parent_vars = &def.args[0..def.args.len() - 1];
                let expected_r_type = theorem.entities.get(result_var).copied();

                
                
                let mut valid_nodes = Vec::new();

                if let Some(&res_id) = bind.get(result_var) {
                    valid_nodes.push(self.egraph.get_rep(res_id));
                }
                
                // 🌟 FIX: *v ではなく v をそのまま渡す
                else if parent_vars.iter().all(|v| bind.contains_key(v)) {
                    let parent_ids: Vec<ClassId> = parent_vars.iter().map(|v| self.egraph.get_rep(bind[v])).collect();
                    
                    // 🌟 FIX: 全ての DefinedBy 対象型を網羅する
                    let temp_def = match target_type {
                        "AnglePair" => Definition::AnglePair(parent_ids[0], parent_ids[1]),
                        "DirectionOf" => Definition::DirectionOf(parent_ids[0]),
                        "LineThroughPoints" => Definition::new_line(parent_ids[0], parent_ids[1]),
                        "Midpoint" => {
                            let (a,b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                            Definition::Midpoint(a, b)
                        },
                        "Intersection" => {
                            let (a,b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                            Definition::Intersection(a, b)
                        },
                        "LengthSq" => {
                            let (a,b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                            Definition::LengthSq(a, b)
                        },
                        "PerpendicularLine" => Definition::PerpendicularLine(parent_ids[0], parent_ids[1]),
                        "ParallelLine" => Definition::ParallelLine(parent_ids[0], parent_ids[1]),
                        "TangentLine" => Definition::TangentLine(parent_ids[0], parent_ids[1]),
                        "Circumcircle" => {
                            let mut arr = [parent_ids[0].0, parent_ids[1].0, parent_ids[2].0];
                            arr.sort_unstable();
                            Definition::Circumcircle(ClassId(arr[0]), ClassId(arr[1]), ClassId(arr[2]))
                        }
                        _ => Definition::GivenPoint, 
                    };

                    if let Some(&existing) = self.egraph.memo.get(&temp_def) {
                        valid_nodes.push(self.egraph.get_rep(existing));
                    } else if matches!(target_type, "AnglePair" | "DirectionOf" | "LengthSq") {
                        let e_type = match target_type { 
                            "AnglePair" => EntityType::Angle, 
                            "DirectionOf" => EntityType::Direction, 
                            _ => EntityType::Scalar 
                        };
                        
                        // 🌟 FIX: 親図形の名前を取得して結合し、誰と誰の角(方向)なのかを明示する
                        let p_names: Vec<String> = parent_ids.iter()
                            .map(|&id| self.egraph.entities[id.0].name.clone())
                            .collect();
                        
                        let prefix = if target_type == "DirectionOf" { "Dir" } else { target_type };
                        let name = format!("{}_{}_(Auto)", prefix, p_names.join("_"));
                        
                        let new_id = self.egraph.create_entity(name, temp_def.clone(), e_type);
                        self.egraph.apply_trivial_relations(new_id, &temp_def);
                        valid_nodes.push(new_id);
                    }
                }
                // 🌟 FIX 3: どちらも未バインドの場合のみフルスキャン
                else {
                    for i in 0..self.egraph.entities.len() {
                        let id = ClassId(i);
                        if self.egraph.get_rep(id) == id {
                            if let Some(et) = expected_r_type {
                                if self.egraph.entities[id.0].entity_type == et { valid_nodes.push(id); }
                            } else {
                                valid_nodes.push(id);
                            }
                        }
                    }
                }

                let mut matches = Vec::new();
                for node_id in valid_nodes {
                    for comp in &self.egraph.entities[node_id.0].components {
                        for d in &comp.definitions {
                            if d.get_type_name() == target_type {
                                let d_parents = d.get_parents();
                                if d_parents.len() == parent_vars.len() {
                                    let is_unordered = matches!(target_type, "Midpoint" | "LineThroughPoints" | "Intersection" | "LengthSq" | "Circumcircle");
                                    
                                    let perms = if is_unordered {
                                        if d_parents.len() == 2 {
                                            vec![(vec![d_parents[0], d_parents[1]], None), (vec![d_parents[1], d_parents[0]], None)]
                                        } else if d_parents.len() == 3 {
                                            // 🌟 FIX: Python版にあった3変数の全順列展開を復活
                                            vec![
                                                (vec![d_parents[0], d_parents[1], d_parents[2]], None),
                                                (vec![d_parents[0], d_parents[2], d_parents[1]], None),
                                                (vec![d_parents[1], d_parents[0], d_parents[2]], None),
                                                (vec![d_parents[1], d_parents[2], d_parents[0]], None),
                                                (vec![d_parents[2], d_parents[0], d_parents[1]], None),
                                                (vec![d_parents[2], d_parents[1], d_parents[0]], None),
                                            ]
                                        } else { vec![(d_parents.clone(), None)] }
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
                                            // 🌟 個別の角度のフリップ状態も記憶させる
                                            if let Some(val) = flip_val {
                                                next_flip.insert(result_var.clone(), val);
                                            }
                                            matches.push((next_bind, next_flip)); 
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                
                
                if matches.is_empty() && target_type == "LineThroughPoints" && parent_vars.len() == 2 {
                    if let (Some(&p1), Some(&p2)) = (bind.get(&parent_vars[0]), bind.get(&parent_vars[1])) {
                        let r1 = self.egraph.get_rep(p1);
                        let r2 = self.egraph.get_rep(p2);
                        if r1 != r2 {
                            *self.construction_demands.entry((r1, r2)).or_insert(0.0) += 1.0;
                        }
                    }
                }

                matches.sort_by(|(b1, _), (b2, _)| {
                    let heat1 = self.calc_bind_heat(b1);
                    let heat2 = self.calc_bind_heat(b2);
                    // 熱が高い(降順)ものを優先し、同値の場合はIDで決定論的にソート[cite: 5]
                    heat2.partial_cmp(&heat1).unwrap_or(Ordering::Equal)
                        .then_with(|| {
                            let mut k1: Vec<_> = b1.iter().collect(); k1.sort_by_key(|k| k.0);
                            let mut k2: Vec<_> = b2.iter().collect(); k2.sort_by_key(|k| k.0);
                            format!("{:?}", k1).cmp(&format!("{:?}", k2))
                        })
                });
                matches.dedup_by_key(|(b, _)| {
                    let mut keys: Vec<_> = b.iter().collect();
                    keys.sort_by_key(|k| k.0);
                    format!("{:?}", keys)
                });
                for (new_bind, new_flip) in matches { 
                    self.dfs_match(theorem, remaining.clone(), new_bind, new_flip, failed_paths, on_match); 
                }
            },
            _ => {
                let mut matches = Vec::new();
                for fact in &self.facts {
                    matches.extend(self.get_fact_bindings(theorem, fact, &def.fact_type, &def.args, bind));
                }
                
                matches.sort_by(|b1, b2| {
                    let heat1 = self.calc_bind_heat(b1);
                    let heat2 = self.calc_bind_heat(b2);
                    heat2.partial_cmp(&heat1).unwrap_or(Ordering::Equal)
                        .then_with(|| {
                            let mut k1: Vec<_> = b1.iter().collect(); k1.sort_by_key(|k| k.0);
                            let mut k2: Vec<_> = b2.iter().collect(); k2.sort_by_key(|k| k.0);
                            format!("{:?}", k1).cmp(&format!("{:?}", k2))
                        })
                });
                matches.dedup_by_key(|b| {
                    let mut keys: Vec<_> = b.iter().collect();
                    keys.sort_by_key(|k| k.0);
                    format!("{:?}", keys)
                });

                for new_bind in matches { 
                    self.dfs_match(theorem, remaining.clone(), new_bind, flip_states.clone(), failed_paths, on_match); 
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
                // 🌟 FIX: 不足していた作図定義を追加（これがないと return false で沈黙する）
                "LengthSq" => {
                    let (a, b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::LengthSq(a, b)
                },
                "ParallelLine" => Definition::ParallelLine(parent_ids[0], parent_ids[1]),
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
                    "Scalar" => EntityType::Scalar, // 🌟 スカラー型の追加
                    _ => EntityType::Point,
                };
                
                // 定理名と要求された変数名を組み合わせて一意な名前をつける
                let name = format!("{}_{}_(Auto)", constr.bind_to, theorem_name.replace(" ", ""));
                
                let id = self.egraph.create_entity(name, def.clone(), entity_type);
                self.egraph.apply_trivial_relations(id, &def);
                id
            };
            
            bind.insert(constr.bind_to.clone(), new_id);
        }
        true
    }

    pub fn apply_conclusions(&mut self, theorem_name: &str, conclusions: &[FactTemplate], bind: &FxHashMap<String, ClassId>, flips: &FxHashMap<String, bool>) -> (bool, Vec<Fact>) {
        let mut applied_anything = false;
        let mut new_facts = Vec::new();

        for conc in conclusions {
            match conc.fact_type.as_str() {
                "Identical" => {
                    if let (Some(&id1), Some(&id2)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1])) {
                        
                        let r1 = self.egraph.get_rep(id1);
                        let r2 = self.egraph.get_rep(id2);
                        if r1 == r2 { continue; } // 既にマージ済みならスキップ

                        // 🌟 FIX: EntityType::Angle 以外の図形 (Scalar, Direction等) はそのまま無条件でマージする
                        if self.egraph.entities[r1.0].entity_type == EntityType::Angle {
                            let f1 = flips.get(&conc.args[0]).copied().unwrap_or(false);
                            let f2 = flips.get(&conc.args[1]).copied().unwrap_or(false);
                            if f1 != f2 { continue; } // 向きが違うならマージしない
                        }
                        
                        let name1 = self.egraph.entities[r1.0].name.clone();
                        let name2 = self.egraph.entities[r2.0].name.clone();
                        if self.egraph.merge_entities(r1, r2) {
                            println!("  🟢 [マージ実行] {} ≡ {} (理由: {})", name1, name2, theorem_name);
                            // 🌟 マージされた代表元の熱を上げて今後のDFSで優先させる[cite: 5]
                            self.egraph.entities[r1.0].heat_bonus += 1.5; 
                            applied_anything = true;
                        }
                    }
                }
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
                "Concyclic" => {
                    if let (Some(&a), Some(&b), Some(&c), Some(&d)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1]), bind.get(&conc.args[2]), bind.get(&conc.args[3])) {
                        let rep_a = self.egraph.get_rep(a);
                        let rep_b = self.egraph.get_rep(b);
                        let rep_c = self.egraph.get_rep(c);
                        let rep_d = self.egraph.get_rep(d);
                        let fact = Fact::new_concyclic(rep_a, rep_b, rep_c, rep_d);
                        if !self.facts.contains(&fact) {
                            self.facts.push(fact.clone());
                            new_facts.push(fact);
                            applied_anything = true;
                            
                            // 🌟 ヒューリスティック: 新発見に関わった図形の熱を上げる
                            self.egraph.entities[rep_a.0].heat_bonus += 2.0;
                            self.egraph.entities[rep_b.0].heat_bonus += 2.0;
                            self.egraph.entities[rep_c.0].heat_bonus += 2.0;
                            self.egraph.entities[rep_d.0].heat_bonus += 2.0;
                        }
                    }
                },
                // 🌟 FIX: Connected によるE-Graphの物理リンク構築を追加
                "Connected" => {
                    if let (Some(&child), Some(&parent)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1])) {
                        let c_rep = self.egraph.get_rep(child);
                        let p_rep = self.egraph.get_rep(parent);
                        self.egraph.link_logical_incidence(c_rep, p_rep);
                        applied_anything = true;
                        println!("  🟢 [リンク構築] {} ∈ {} (理由: {})", 
                            self.egraph.entities[c_rep.0].name, self.egraph.entities[p_rep.0].name, theorem_name);
                    }
                },
                _ => {}
            }
        }
        (applied_anything, new_facts)
    }

    fn get_fact_bindings(&self, theorem: &TheoremDef, fact: &Fact, fact_type: &str, args: &[String], current_bind: &FxHashMap<String, ClassId>) -> Vec<FxHashMap<String, ClassId>> {
        let (f_type, f_objs) = match fact {
            Fact::Collinear(a, b, c) => ("Collinear", vec![*a, *b, *c]),
            Fact::Concyclic(a, b, c, d) => ("Concyclic", vec![*a, *b, *c, *d]),
            Fact::Identical(a, b) => ("Identical", vec![*a, *b]),
            Fact::Connected(c, p) => ("Connected", vec![*c, *p]),
            Fact::Parallel(a, b) => ("Parallel", vec![*a, *b]),
        };

        if f_type != fact_type || f_objs.len() != args.len() { return vec![]; }

        // 🌟 爆速化: 事実探索の段階でターゲット型と異なるエンティティを即座に破棄
        for (i, arg_name) in args.iter().enumerate() {
            if f_type == "Connected" {
                if let Some(expected_type) = theorem.entities.get(arg_name).copied() {
                    if self.egraph.entities[self.egraph.get_rep(f_objs[i]).0].entity_type != expected_type {
                        return vec![]; 
                    }
                }
            }
        }

        let is_unordered = f_type == "Collinear" || f_type == "Concyclic" || f_type == "Identical";
        let perms = if is_unordered { get_permutations(&f_objs) } else { vec![f_objs.clone()] };

        let mut matches = Vec::new();
        for perm in perms {
            let mut next_bind = current_bind.clone();
            let mut conflict = false;
            for (i, arg_name) in args.iter().enumerate() {
                // 🌟 型チェック
                if let Some(expected_type) = theorem.entities.get(arg_name).copied() {
                    if self.egraph.entities[self.egraph.get_rep(perm[i]).0].entity_type != expected_type {
                        conflict = true; break;
                    }
                }
                if let Some(&existing) = next_bind.get(arg_name) {
                    if self.egraph.get_rep(existing) != self.egraph.get_rep(perm[i]) {
                        conflict = true; break;
                    }
                }
                next_bind.insert(arg_name.clone(), perm[i]);
            }
            if !conflict { matches.push(next_bind); }
        }
        matches
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
        // 🌟 FIX: シード注入済みの優先タスク(priority > 0)は消さずに保持する！
        let mut keep = Vec::new();
        for task in self.task_queue.drain() {
            if task.priority > 0 { keep.push(task); }
        }
        self.task_queue = BinaryHeap::from(keep);

        for (idx, theorem) in self.prover.theorems.iter().enumerate() {
            let mut initial_bind = rustc_hash::FxHashMap::default();
            initial_bind.insert("Ang90".to_string(), self.prover.egraph.ang90);
            initial_bind.insert("Ang0".to_string(), self.prover.egraph.ang0);
            
            self.task_queue.push(MatchTask { 
                priority: 0, 
                theorem_idx: idx, 
                bind: initial_bind,
                flip_states: rustc_hash::FxHashMap::default(),
                remaining_patterns: theorem.patterns.clone() 
            });
        }
    }

    fn schedule_matcher_task(&mut self, fact: &Fact) {
        let (fact_type, fact_objs) = match fact {
            Fact::Collinear(a, b, c) => ("Collinear", vec![*a, *b, *c]),
            Fact::Concyclic(a, b, c, d) => ("Concyclic", vec![*a, *b, *c, *d]),
            Fact::Identical(a, b) => ("Identical", vec![*a, *b]),
            Fact::Connected(c, p) => ("Connected", vec![*c, *p]),
            Fact::Parallel(a, b) => ("Parallel", vec![*a, *b]),
        };

        for (idx, theorem) in self.prover.theorems.iter().enumerate() {
            for pat in &theorem.patterns {
                if let Pattern::Fact(def) = pat {
                    if def.fact_type == fact_type && def.args.len() == fact_objs.len() {
                        
                        // 🌟 FIX: Python版の _evaluate_patterns_with_seed_gen を再現[cite: 6]
                        // 発見された事実のオブジェクトの順列を作り、変数を事前バインド（シード化）する
                        let perms = match fact_type {
                            "Connected" => vec![fact_objs.clone()], // 有向関係なので順列なし
                            _ => get_permutations(&fact_objs),      // Identical, Collinear, Concyclic 等は全順列
                        };

                        for perm in perms {
                            let mut bind = rustc_hash::FxHashMap::default();
                            // 定数ノードの事前バインド
                            bind.insert("Ang90".to_string(), self.prover.egraph.ang90);
                            bind.insert("Ang0".to_string(), self.prover.egraph.ang0);
                            
                            // 🌟 シードの注入
                            for (i, v_name) in def.args.iter().enumerate() {
                                bind.insert(v_name.clone(), perm[i]);
                            }
                            
                            // シード済みリーチフォーマットとしてタスクを積む
                            self.task_queue.push(MatchTask {
                                priority: 10,
                                theorem_idx: idx,
                                bind,
                                flip_states: rustc_hash::FxHashMap::default(),
                                remaining_patterns: theorem.patterns.clone(),
                            });
                        }
                    }
                }
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

            if let Some(mut task) = self.task_queue.pop() {
                calls += 1;
                self.prover.dfs_calls = 0; 
                let theorem = self.prover.theorems[task.theorem_idx].clone();
                let mut new_binds = Vec::new();
                let mut failed_paths = rustc_hash::FxHashSet::default();

                self.prover.dfs_match(
                    &theorem, 
                    task.remaining_patterns.clone(), // 一旦cloneして渡す
                    task.bind.clone(), 
                    task.flip_states.clone(), 
                    &mut failed_paths,
                    &mut |bind, flips| {
                        new_binds.push((bind.clone(), flips.clone()));
                    }
                );

                // 🌟 スケジューリング工夫: DFSが上限(100,000)に張り付いた場合、
                // このタスクは重すぎるためペナルティを与えて後回しにする
                if self.prover.dfs_calls >= 99_000 {
                    task.priority -= 5;
                    if task.priority >= -20 { // 諦める閾値
                        self.task_queue.push(task);
                    }
                }

                for (mut bind, flips) in new_binds {
                    // 🌟 1. まず現在のE-Graphの状態で、この結論がすでに満たされているかチェックする
                    if self.prover.is_already_proven(&theorem.conclusions, &bind, &flips) {
                        continue;
                    }

                    // 🌟 2. 結論が満たされていない場合のみ、足りない図形を作図する
                    if self.prover.execute_constructions(&theorem.name, &theorem.constructions, &mut bind) {
                        
                        // 🌟 3. 作図後、もう一度チェック。ここで真になるなら「作図しただけでマージ済み」なのでスキップ
                        if self.prover.is_already_proven(&theorem.conclusions, &bind, &flips) {
                            continue;
                        }

                        println!("  🎯 [リーチ通知] 定理「{}」の前提条件がすべて満たされました！", theorem.name);
                        for (var_name, class_id) in &bind {
                            if var_name.starts_with("__") { continue; }
                            let entity_name = self.prover.egraph.entities[self.prover.egraph.get_rep(*class_id).0].name.clone();
                            println!("      - 割り当て: {} = {}", var_name, entity_name);
                        }

                        let (applied, generated_facts) = self.prover.apply_conclusions(&theorem.name, &theorem.conclusions, &bind, &flips);
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

        // 🌟 処理前にグラフを最新状態に正規化し、直線の重複を完全に消す
        self.prover.egraph.apply_congruence_closure();

        for i in 0..self.prover.egraph.entities.len() {
            let pt_id = ClassId(i);
            if self.prover.egraph.get_rep(pt_id) != pt_id { continue; }
            if self.prover.egraph.entities[i].entity_type != EntityType::Point { continue; }

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
                        let d1 = self.get_or_create_direction(lines_on_pt[l1]);
                        let d2 = self.get_or_create_direction(lines_on_pt[l2]);
                        
                        let r_d1 = self.prover.egraph.get_rep(d1);
                        let r_d2 = self.prover.egraph.get_rep(d2);

                        // 🌟 FIX: 方向が同じ(平行/同一)な直線のペアで0度角を生成しない
                        if r_d1 == r_d2 { continue; }

                        // 🌟 FIX: allow_flip があるため、ID順でソートして片方のみを生成（数を半分に！）
                        let (d_min, d_max) = if r_d1.0 < r_d2.0 { (r_d1, r_d2) } else { (r_d2, r_d1) };
                        angle_pairs_to_create.push((d_min, d_max));
                    }
                }
            }
        }

        angle_pairs_to_create.sort_unstable_by_key(|(d1, d2)| (d1.0, d2.0));
        angle_pairs_to_create.dedup();

        for (d1, d2) in angle_pairs_to_create {
            let def = Definition::AnglePair(d1, d2);
            if !self.prover.egraph.memo.contains_key(&def) {
                let name = format!("AnglePair_{}_{}_(Auto)", self.prover.egraph.entities[d1.0].name, self.prover.egraph.entities[d2.0].name);
                let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Angle);
                
                // 🌟 FIX: Auto生成されたAngleの重要度を下げ、無駄なヒューリスティック探索を抑制
                self.prover.egraph.entities[new_id.0].base_importance = 0.2;
                
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
        if self.prover.construction_demands.is_empty() { return false; }

        let mut demands: Vec<_> = self.prover.construction_demands.iter().collect();
        demands.sort_by(|a, b| b.1.partial_cmp(a.1).unwrap_or(std::cmp::Ordering::Equal));

        let mut applied = false;
        let mut count = 0;
        
        for (&(p1, p2), &score) in demands.into_iter() {
            let def = Definition::new_line(p1, p2);
            if !self.prover.egraph.memo.contains_key(&def) {
                let name = format!("Line_{}_{}_(Demand)", self.prover.egraph.entities[p1.0].name, self.prover.egraph.entities[p2.0].name);
                println!("  💡 [オンデマンド作図] 要請により {} を生成 (需要: {:.1})", name, score);
                let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Line);
                
                // 🌟 FIX: Demand線の重要度を下げ、推論の主軸がブレるのを防ぐ
                self.prover.egraph.entities[new_id.0].base_importance = 0.5;
                
                self.prover.egraph.apply_trivial_relations(new_id, &def);
                applied = true;
                count += 1;
                if count >= 3 { break; }
            }
        }
        
        self.prover.construction_demands.clear();
        if applied { 
            // 🌟 FIX: 作図直後に合同閉包を強制実行し、既存の直線と即座にマージさせる！
            self.prover.egraph.apply_congruence_closure();
            self.schedule_full_sweep(); 
        }
        applied
    }

    pub fn check_target_reached(&self) -> bool { false }
}
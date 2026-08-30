use crate::mmp_core::{ClassId, Definition, EGraph, EntityType, Fact};
use rustc_hash::FxHashMap;
use std::collections::{BinaryHeap, VecDeque};
use std::cmp::Ordering;

// ==========================================
// 定理とパターンの定義 (代数的データ型で堅牢に表現)
// ==========================================

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

// 🌟 探索タスク（ジェネレータの代わり）
#[derive(Debug, Clone)]
pub struct MatchTask {
    pub priority: i32,
    pub theorem_idx: usize,
    pub bind: FxHashMap<String, ClassId>,
    pub remaining_patterns: Vec<crate::logic_core::Pattern>,
}

// 優先度付きキュー (BinaryHeap) は最大値を取り出すため、Ordをカスタム実装
impl PartialEq for MatchTask {
    fn eq(&self, other: &Self) -> bool { self.priority == other.priority }
}
impl Eq for MatchTask {}
impl PartialOrd for MatchTask {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}
impl Ord for MatchTask {
    fn cmp(&self, other: &Self) -> Ordering {
        self.priority.cmp(&other.priority) // priorityが高い順
    }
}

// ==========================================
// 推論エンジン (BlackboardEngine相当)
// ==========================================
pub struct ProverEngine {
    pub egraph: EGraph,
    pub facts: Vec<Fact>,
    pub theorems: Vec<TheoremDef>,
    // 探索統計 (Pythonの stats 辞書相当)[cite: 15]
    pub dfs_calls: u64,
}

impl ProverEngine {
    pub fn new(egraph: EGraph) -> Self {
        Self {
            egraph,
            facts: Vec::new(),
            theorems: Vec::new(),
            dfs_calls: 0,
        }
    }

    // ==========================================
    // 動的コスト評価 (Cost-Based Optimizer)
    // ==========================================
    // Pythonの estimate_cost 関数をRustで厳密に型付け[cite: 15]
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
            Pattern::Order(vars) => {
                if vars.iter().any(|v| !bind.contains_key(v)) {
                    std::f64::INFINITY 
                } else {
                    0.0
                }
            }
            Pattern::Distinct(vars) => {
                if vars.iter().any(|v| !bind.contains_key(v)) {
                    std::f64::INFINITY
                } else {
                    0.0
                }
            }
            Pattern::Not(inner_pat) => {
                // NotPattern のコスト推定 (内部パターンの未バインド変数をチェック)
                self.estimate_cost(inner_pat, bind)
            }
        }
    }

    // ==========================================
    // DFSマッチャー (再帰とバックトラック)
    // ==========================================
    // Pythonの generator と異なり、クロージャで結果を直接収集する[cite: 15]
    pub fn dfs_match<F>(
        &mut self,
        theorem: &TheoremDef,
        mut remaining: Vec<Pattern>,
        mut bind: FxHashMap<String, ClassId>,
        on_match: &mut F,
    ) where
        F: FnMut(&FxHashMap<String, ClassId>),
    {
        self.dfs_calls += 1;
        if self.dfs_calls > 100_000 { return; } // 安全装置[cite: 15]

        if remaining.is_empty() {
            on_match(&bind);
            return;
        }

        // 最もコストの低いパターンを動的に選択 (貪欲法)[cite: 15]
        let mut best_idx = 0;
        let mut best_cost = std::f64::INFINITY;
        for (i, pat) in remaining.iter().enumerate() {
            let cost = self.estimate_cost(pat, &bind);
            if cost < best_cost {
                best_cost = cost;
                best_idx = i;
            }
        }

        let pat_to_eval = remaining.remove(best_idx);

        // パターンの評価と分岐
        match pat_to_eval {
            Pattern::Order(vars) => {
                // IDが単調増加 (A < B < C ...) になっている順列だけを許可する対称性破壊
                let mut is_ordered = true;
                for i in 0..vars.len().saturating_sub(1) {
                    if bind[&vars[i]].0 >= bind[&vars[i+1]].0 {
                        is_ordered = false;
                        break;
                    }
                }
                if is_ordered {
                    self.dfs_match(theorem, remaining.clone(), bind, on_match);
                }
            }
            Pattern::Distinct(vars) => {
                let mut unique_ids = rustc_hash::FxHashSet::default();
                let mut is_distinct = true;
                for v in &vars {
                    if !unique_ids.insert(bind[v].0) {
                        is_distinct = false;
                        break;
                    }
                }
                if is_distinct {
                    self.dfs_match(theorem, remaining.clone(), bind, on_match);
                }
            }
            Pattern::Fact(def) => {
                // 🌟 FIX: &def.fact_type と &def.args に分けるのをやめ、def そのものを渡す
                self.match_fact_pattern(
                    theorem,
                    &def, 
                    remaining.clone(),
                    &bind,
                    on_match,
                );
            }
            Pattern::Not(inner_pat) => {
                // Python版の NotPattern の実装
                // (内部パターンが1つもマッチしなかった場合のみ現在の bind を通すロジックをここに記述するか、
                // ひとまずスキップして `self.dfs_match(theorem, remaining, bind, on_match);` を通します)
                self.dfs_match(theorem, remaining.clone(), bind, on_match);
            }
        }
        
    }
    // 第一引数を theorem_name: &str から theorem: &TheoremDef に変更
    pub fn match_fact_pattern<F>(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef, // 🌟 引数を FactPatternDef に変更
        remaining: Vec<Pattern>,
        bind: &FxHashMap<String, ClassId>,
        on_match: &mut F,
    ) where
        F: FnMut(&FxHashMap<String, ClassId>),
    {
        match def.fact_type.as_str() {
            "Identical" => {
                let v1 = &def.args[0];
                let v2 = &def.args[1];
                let b1 = bind.get(v1).copied();
                let b2 = bind.get(v2).copied();

                match (b1, b2) {
                    (Some(id1), Some(id2)) => {
                        if self.egraph.get_rep(id1) == self.egraph.get_rep(id2) {
                            // theorem_name ではなく theorem を渡す
                            self.dfs_match(theorem, remaining.clone(), bind.clone(), on_match);
                        }
                    }
                    (Some(id), None) | (None, Some(id)) => {
                        let unbound_var = if b1.is_none() { v1 } else { v2 };
                        let target_rep = self.egraph.get_rep(id);
                        
                        for i in 0..self.egraph.entities.len() {
                            let curr_id = ClassId(i);
                            if self.egraph.entities[i].base_importance > 0.0 && self.egraph.get_rep(curr_id) == target_rep {
                                let mut next_bind = bind.clone();
                                next_bind.insert(unbound_var.clone(), curr_id);
                                // theorem を渡す
                                self.dfs_match(theorem, remaining.clone(), next_bind, on_match);
                            }
                        }
                    }
                    _ => {}
                }
            },
            "Connected" => {
                let child_var = &def.args[0];
                let parent_var = &def.args[1];
                
                let b_child = bind.get(child_var).copied();
                let b_parent = bind.get(parent_var).copied();

                match (b_child, b_parent) {
                    (Some(c_id), Some(p_id)) => {
                        let p_rep = self.egraph.get_rep(p_id);
                        let c_rep = self.egraph.get_rep(c_id);
                        if let Some(comp) = self.egraph.entities[p_rep.0].components.first() {
                            if comp.subobjects.contains(&c_rep) {
                                self.dfs_match(theorem, remaining.clone(), bind.clone(), on_match);
                            }
                        }
                    }
                    (Some(c_id), None) => {
                        let c_rep = self.egraph.get_rep(c_id);
                        for i in 0..self.egraph.entities.len() {
                            let p_id = ClassId(i);
                            if self.egraph.entities[i].base_importance <= 0.0 { continue; }
                            
                            let p_rep = self.egraph.get_rep(p_id);
                            if let Some(comp) = self.egraph.entities[p_rep.0].components.first() {
                                if comp.subobjects.contains(&c_rep) {
                                    let mut next_bind = bind.clone();
                                    next_bind.insert(parent_var.clone(), p_rep);
                                    self.dfs_match(theorem, remaining.clone(), next_bind, on_match);
                                }
                            }
                        }
                    }
                    (None, Some(p_id)) => {
                        let p_rep = self.egraph.get_rep(p_id);
                        
                        // 🌟 FIX: 読み取りフェーズ（ミュータブルな再帰を呼ぶ前に候補をVecに隔離する）
                        let mut child_candidates = Vec::new();
                        if let Some(comp) = self.egraph.entities[p_rep.0].components.first() {
                            for &c_rep in &comp.subobjects {
                                if self.egraph.entities[c_rep.0].base_importance > 0.0 {
                                    child_candidates.push(c_rep);
                                }
                            }
                        }
                        
                        // 🌟 FIX: 再帰フェーズ（読み取りロックが解除されたので安全に dfs_match を呼べる）
                        for c_rep in child_candidates {
                            let mut next_bind = bind.clone();
                            next_bind.insert(child_var.clone(), c_rep);
                            self.dfs_match(theorem, remaining.clone(), next_bind, on_match);
                        }
                    }
                    _ => {}
                }
            },
            "DefinedBy" => {
                // 🌟 NEW: E-Graphからの物理探索 (Midpointなどの発火に必須)
                let target_type = def.target_type.as_deref().unwrap_or("");
                let result_var = &def.args[def.args.len() - 1];
                let parent_vars = &def.args[0..def.args.len() - 1];
                let mut matches = Vec::new();

                for i in 0..self.egraph.entities.len() {
                    let node_id = ClassId(i);
                    if self.egraph.get_rep(node_id) != node_id || self.egraph.entities[i].base_importance <= 0.0 { continue; }
                    
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
                                        
                                        // 親のバインド検証
                                        for (v_name, &p_id) in parent_vars.iter().zip(p_ids.iter()) {
                                            if let Some(&existing) = next_bind.get(v_name) {
                                                if self.egraph.get_rep(existing) != self.egraph.get_rep(p_id) {
                                                    conflict = true; break;
                                                }
                                            }
                                            next_bind.insert(v_name.clone(), p_id);
                                        }
                                        
                                        // 結果ノードのバインド検証
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
                // 重複排除してから再帰
                matches.sort_by_key(|b| {
                    let mut keys: Vec<_> = b.iter().collect();
                    keys.sort_by_key(|k| k.0);
                    format!("{:?}", keys)
                });
                matches.dedup();
                for new_bind in matches {
                    self.dfs_match(theorem, remaining.clone(), new_bind, on_match);
                }
            },
            _ => {
                // 🌟 FIX: 同様に、Factの走査も Two-Phase (読み取り -> 再帰) に分離する
                let mut matches = Vec::new();
                for fact in &self.facts {
                    if let Some(new_bind) = self.try_bind_fact(fact, &def.fact_type, &def.args, bind) {
                        matches.push(new_bind);
                    }
                }
                
                for new_bind in matches {
                    self.dfs_match(theorem, remaining.clone(), new_bind, on_match);
                }
            }
        }
    }

    // 結論の適用とE-Graphの破壊的更新
    pub fn apply_conclusions(&mut self, theorem_name: &str, conclusions: &[FactTemplate], bind: &FxHashMap<String, ClassId>) -> bool {
        let mut applied_anything = false;
        let mut structural_changed = false;

        for conc in conclusions {
            match conc.fact_type.as_str() {
                "Identical" => {
                    let id1 = bind[&conc.args[0]];
                    let id2 = bind[&conc.args[1]];
                    
                    // E-Graph のマージを実行 (自己マージは内部で false を返す)
                    if self.egraph.merge_entities(id1, id2) {
                        applied_anything = true;
                        structural_changed = true;
                        // TODO: logger.info("🟢 [マージ実行] ...")
                    }
                },
                "Connected" => {
                    let child_id = bind[&conc.args[0]];
                    let parent_id = bind[&conc.args[1]];
                    
                    self.egraph.link_logical_incidence(child_id, parent_id);
                    applied_anything = true;
                    structural_changed = true;
                },
                "Concyclic" | "Collinear" => {
                    // Fact::new_concyclic などでソート済みの正規化ファクトを生成
                    // 新しい円・直線を create_entity するか、既存のものに link する
                    applied_anything = true;
                    structural_changed = true;
                },
                _ => {
                    // 純粋な論理ファクトの登録
                    let mut new_args = Vec::new();
                    for arg in &conc.args {
                        new_args.push(self.egraph.get_rep(bind[arg]));
                    }
                    
                    // Fact Enum を構築して self.facts に追加
                    // applied_anything = true;
                }
            }
        }

        // 構造変更があった場合、合同閉包キューにトリガーを送る
        if structural_changed {
            // self.emit(EventType::NodeMerged) に相当する処理
        }

        applied_anything
    }

    // ファクトのバインディング試行
    fn try_bind_fact(&self, fact: &Fact, fact_type: &str, args: &[String], current_bind: &FxHashMap<String, ClassId>) -> Option<FxHashMap<String, ClassId>> {
        // Fact Enum の中身を展開し、型が一致すれば引数をバインドする
        // (例: fact が Fact::Identical(id1, id2) で、fact_type が "Identical" の場合)
        // 矛盾があれば None を返す
        None // 実装省略
    }

    // --- logic_core.rs の `impl ProverEngine` 内に追加 ---

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
                _ => return false,
            };
            
            let entity_type = match constr.target_type.as_str() {
                "Line" => EntityType::Line,
                "Direction" => EntityType::Direction,
                "Point" => EntityType::Point,
                "Angle" => EntityType::Angle,
                _ => EntityType::Point,
            };
            
            let name = format!("{}_{}_(Auto)", constr.def_type, theorem_name);
            let new_id = self.egraph.create_entity(name, def.clone(), entity_type);
            self.egraph.apply_trivial_relations(new_id, &def);
            
            // 🌟 作図したIDをバインド辞書に記録！これが apply_conclusions に渡される
            bind.insert(constr.bind_to.clone(), new_id);
        }
        true
    }
}

pub struct BlackboardEngine {
    pub prover: ProverEngine,
    pub task_queue: BinaryHeap<MatchTask>,
    pub event_queue: VecDeque<Event>,
    pub processed_conjectures: rustc_hash::FxHashSet<String>, // MMP予想の重複排除用
}
impl BlackboardEngine {
    pub fn new(prover: ProverEngine) -> Self {
        Self {
            prover,
            task_queue: BinaryHeap::new(),
            event_queue: VecDeque::new(),
            processed_conjectures: rustc_hash::FxHashSet::default(),
        }
    }

    pub fn schedule_full_sweep(&mut self) {
        self.task_queue.clear();
        println!("  🔄 [Full Sweep] 全定理の探索をリセット・スケジュールします");
        
        for (idx, theorem) in self.prover.theorems.iter().enumerate() {
            let task = MatchTask {
                priority: 0, // Python版の heuristic cost 等を後で反映可能
                theorem_idx: idx,
                bind: rustc_hash::FxHashMap::default(),
                remaining_patterns: theorem.patterns.clone(),
            };
            self.task_queue.push(task);
        }
    }

    // 🌟 FIX: 証明完了の判定スタブ (今回はデバッグ用にダミーの false を返すか、特定の Fact を監視する)
    pub fn check_target_reached(&self) -> bool {
        // 本来は self.prover.facts の中に target_fact が含まれているかを確認する
        // 今回はコンパイル・実行ループのデバッグのため false を返して時間切れまで回す
        false
    }

    // イベントの発火 (Pythonの emit に相当)
    
    pub fn emit(&mut self, event: Event) {
        self.event_queue.push_back(event.clone());
        if let Event::FactProven(fact) = event {
            self.schedule_matcher_task(&fact);
        }
    }
    /// 新しいFactが証明された時、それをトリガーに発火しうる定理をキューに積む
    fn schedule_matcher_task(&mut self, fact: &Fact) {
        // ※ Python版の _schedule_matcher_task の移植
        // 関連する定理を探し、MatchTask を生成して self.task_queue.push() する
    }

    
    /// 🌟 メインループ
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
                        self.schedule_matcher_task(&fact);
                    }
                }
            }

            if let Some(task) = self.task_queue.pop() {
                calls += 1;
                
                // 🌟 FIX: DFSマッチャーを起動し、マッチした結果をベクタに集める
                let theorem = self.prover.theorems[task.theorem_idx].clone();
                let mut new_binds = Vec::new();

                self.prover.dfs_match(
                    &theorem,
                    task.remaining_patterns,
                    task.bind,
                    &mut |bind| {
                        new_binds.push(bind.clone());
                    }
                );

                // 🌟 FIX: 発見された新しいバインディングに対して結論を適用（マージ等）する
                for mut bind in new_binds {
                    // 🌟 FIX: 結論(マージ等)を適用する前に、定理に基づく作図(Direction等)を実行する
                    if self.prover.execute_constructions(&theorem.name, &theorem.constructions, &mut bind) {
                        if self.prover.apply_conclusions(&theorem.name, &theorem.conclusions, &bind) {
                            applied_anything = true;
                            self.emit(Event::NodeMerged);
                        }
                    }
                }
            } else {
                break;
            }
        }
        applied_anything
    }

    // 🌟 MCTSフォールバック作図の呼び出し口
    pub fn fallback_construction(&mut self) {
        // タスクが枯渇し、グラフに変化がなくなった場合の処理。
        // Python版の self.agent.run_step(num_simulations=10) を呼び出す。
        // RustからPythonのMCTSを呼ぶか、MCTS自体もRustに移植して実行する。
    }
}

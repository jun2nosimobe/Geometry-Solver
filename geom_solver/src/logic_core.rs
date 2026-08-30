use crate::mmp_core::{ClassId, Definition, EGraph, EntityType, Fact};
use rustc_hash::FxHashMap;
use std::collections::{BinaryHeap, VecDeque};
use std::cmp::Ordering;

// ==========================================
// 定理とパターンの定義 (代数的データ型で堅牢に表現)
// ==========================================
#[derive(Debug, Clone)]
pub enum Pattern {
    Fact { fact_type: String, args: Vec<String> }, // PythonのFactPattern相当
    Order(String, String),                         // 対称性破壊 (OrderPattern)
    Distinct(Vec<String>),                         // 否定・非同一制約
}

#[derive(Debug, Clone)]
pub struct TheoremDef {
    pub name: String,
    pub entities: FxHashMap<String, EntityType>,
    pub patterns: Vec<Pattern>,
    pub conclusions: Vec<FactTemplate>,
}

#[derive(Debug, Clone)]
pub struct FactTemplate {
    pub fact_type: String,
    pub args: Vec<String>,
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
            Pattern::Fact { fact_type, args } => {
                let unbound_count = args.iter().filter(|v| !bind.contains_key(*v)).count();
                
                // 全てバインド済みなら単なる検証 (O(1))[cite: 15]
                if unbound_count == 0 {
                    return 0.0;
                }

                // 幾何学の「大黒柱」は常に優先的に評価する[cite: 15]
                if fact_type == "Collinear" || fact_type == "Concyclic" {
                    if unbound_count < args.len() {
                        return 5.0; // 一部バインド済みなら高速フィルタ[cite: 15]
                    }
                    return 10.0; // ファクト数が増えても重く見せない[cite: 15]
                }

                if fact_type == "Identical" {
                    if unbound_count == 1 { return 1.0; }
                    return 15.0;
                }

                if fact_type == "Connected" {
                    if unbound_count == 1 { return 5.0; }
                    return 10000.0; // Cartesian Product を完全に封殺[cite: 15]
                }

                100.0
            }
            Pattern::Order(a, b) => {
                if !bind.contains_key(a) || !bind.contains_key(b) {
                    std::f64::INFINITY // 未バインド時は後回し[cite: 15]
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
            Pattern::Order(ref a, ref b) => {
                let id_a = bind[a];
                let id_b = bind[b];
                // ID順の強制による対称性の破壊 (Symmetry Breaking)[cite: 15]
                if id_a.0 < id_b.0 {
                    self.dfs_match(theorem, remaining.clone(), bind, on_match);
                }
            }
            Pattern::Distinct(ref vars) => {
                let mut unique_ids = rustc_hash::FxHashSet::default();
                let mut is_distinct = true;
                for v in vars {
                    if !unique_ids.insert(bind[v].0) {
                        is_distinct = false;
                        break;
                    }
                }
                if is_distinct {
                    self.dfs_match(theorem, remaining.clone(), bind, on_match);
                }
            }
            Pattern::Fact { ref fact_type, ref args } => {
                // ここに E-Graph と existing facts を走査して 
                // 新しいバインド候補を yield するロジックを実装します。
                // 見つかった候補ごとに bind をクローンして再帰呼び出しを行います。
                
                // (実装例)
                // for candidate in self.find_candidates(fact_type, args, &bind) {
                //     let mut next_bind = bind.clone();
                //     next_bind.insert(args[x].clone(), candidate);
                //     self.dfs_match(theorem, remaining.clone(), next_bind, on_match);
                // }
            }
        }
        
    }
    // 第一引数を theorem_name: &str から theorem: &TheoremDef に変更
    pub fn match_fact_pattern<F>(
        &mut self,
        theorem: &TheoremDef,
        fact_type: &str,
        args: &[String],
        remaining: Vec<Pattern>,
        bind: &FxHashMap<String, ClassId>,
        on_match: &mut F,
    ) where
        F: FnMut(&FxHashMap<String, ClassId>),
    {
        match fact_type {
            "Identical" => {
                let v1 = &args[0];
                let v2 = &args[1];
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
                let child_var = &args[0];
                let parent_var = &args[1];
                
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
            _ => {
                // 🌟 FIX: 同様に、Factの走査も Two-Phase (読み取り -> 再帰) に分離する
                let mut matches = Vec::new();
                for fact in &self.facts {
                    if let Some(new_bind) = self.try_bind_fact(fact, fact_type, args, bind) {
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
            // 1. 溜まっているイベント（マージや新しいFact）を全て処理する
            while let Some(event) = self.event_queue.pop_front() {
                match event {
                    Event::NodeMerged => {
                        // マージが発生したら、連鎖的な合同閉包を走らせる
                        if self.prover.egraph.apply_congruence_closure() {
                            applied_anything = true;
                            // 合同閉包によりさらにマージが発生した場合、再度イベントを積む
                            self.event_queue.push_back(Event::NodeMerged);
                        }
                    },
                    Event::FactProven(fact) => {
                        self.schedule_matcher_task(&fact);
                    }
                }
            }

            // 2. 探索タスク(DFSの1ステップ)を消化する
            if let Some(task) = self.task_queue.pop() {
                calls += 1;

                // 🌟 ここで prover.dfs_match を呼び出す
                // 新しい発見があれば self.emit(Event::FactProven(...)) や NodeMerged を呼ぶ
                
            } else {
                // タスクもイベントも枯渇したら探索終了（Stall状態）
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

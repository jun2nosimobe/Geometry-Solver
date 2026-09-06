use crate::mmp_core::{ClassId, Definition, EGraph, EntityType, Fact};
use rustc_hash::FxHashMap;
use std::collections::{BinaryHeap, VecDeque};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// 🌟 dfs_matchの探索木を1ノード進むたびに bind/flip_states を丸ごと
// ディープコピーしていた問題を解消するため、通常のHashMapではなく
// 構造共有型(永続データ構造)のHashMapを使う。要素を1つ追加しても
// 変更されたごく一部のノードだけを複製し、残りは元のインスタンスと
// ポインタ(Rc)を共有するので、.clone()の実質コストがO(1)に近くなる。
// 呼び出し側の書き方(.clone()や.insert())は通常のHashMapと同じままで良い。
// 🌟 検証メモ: FxHashに差し替えると(im::HashMap<..., FxBuild>)、内部のHAMT構造との
// 相性が悪いのか実測でむしろ悪化した(miquel: 0.36s→1.12s)。既定のハッシャーの
// ままにしている。
pub type Bind = im::HashMap<String, ClassId>;
pub type FlipStates = im::HashMap<String, bool>;

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
    pub bind: Bind,
    pub flip_states: FlipStates,
    // 🌟 Rc化: タスクの複製・再キュー時に Vec<Pattern> をディープコピーせず、
    // ポインタ共有だけで済ませる(パターン列自体は不変なので安全)
    pub remaining_patterns: Rc<Vec<crate::logic_core::Pattern>>,
    // 🌟 UCB1バンディット用: このタスクが schedule_matcher_task 由来の
    // シード済みタスク(発見済みの事実から変数の多くを具体的に束縛済み、
    // 速く失敗/成功する)か、schedule_full_sweep 由来のシードなしタスク
    // (変数が全て未束縛、定理によっては膨大な探索の末にしか成否が
    // 分からない)かを区別する。priorityはcap到達時のペナルティで
    // 実行中に減算されて変動するため、"どちらの経路で生まれたか"という
    // 由来はpriorityの値から逆算せず、この専用フラグで明示的に持つ。
    // バンディット統計(TheoremBanditStats)はシードなしタスクの成否だけを
    // 学習対象にする(シード済みタスクは既に高確率で成功するとわかっている
    // 別種の試行なので、混ぜると「シードでよく呼ばれるが素の全探索では
    // ほぼ失敗する定理」の見込みスコアを不当に引き上げてしまう)。
    pub is_seeded: bool,
}

impl PartialEq for MatchTask { fn eq(&self, other: &Self) -> bool { self.priority == other.priority } }
impl Eq for MatchTask {}
impl PartialOrd for MatchTask { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) } }
impl Ord for MatchTask { fn cmp(&self, other: &Self) -> Ordering { self.priority.cmp(&other.priority) } }

/// 🌟 定理マッチングのUCB1バンディット統計。theorem_idxごとに、
/// schedule_full_sweep由来のシードなしタスクを実際にdfs_matchまで走らせた
/// 回数(attempts)と、その報酬の累積(total_reward)を数える。
///
/// 🐛 以前はsuccesses(結論を適用できた回数)を単純にカウントするだけの
/// 二値報酬だったため、「dfs_cap一杯まで探索してようやく1回成功した定理」と
/// 「一瞬で成功した定理」が同じ扱いになってしまい、まさに元々問題視していた
/// 「有向角の加法性」のような重い定理を正しく罰せなかった(A/B測定で
/// nine_point_fullにおいて有効化がむしろ約11%遅くなるという結果になった
/// 一因と見ている)。record_theorem_reward側でdfs_calls_used/dfs_capの
/// 比率をコストとして報酬に織り込むことで、「成功はしたが高くついた」
/// 定理と「安く成功した」定理を区別できるようにする。
#[derive(Debug, Clone, Copy, Default)]
pub struct TheoremBanditStats {
    pub attempts: u64,
    pub total_reward: f64,
}

impl TheoremBanditStats {
    /// UCB1スコア = 経験的な平均報酬 + 探索ボーナス。一度も試していない定理は
    /// 常に無限大を返し、必ず一度は(素の全探索からでも)試されるようにする
    /// (標準的なUCB1の初期化: 全アームを1回ずつ引いてから本題に入る)。
    fn ucb1_score(&self, total_attempts: u64, exploration_c: f64) -> f64 {
        if self.attempts == 0 { return f64::INFINITY; }
        let mean = self.total_reward / self.attempts as f64;
        let bonus = exploration_c * ((total_attempts.max(1) as f64).ln() / self.attempts as f64).sqrt();
        mean + bonus
    }
}

pub struct ProverEngine {
    pub egraph: EGraph,
    pub facts: Vec<Fact>,
    // 🌟 Rc化: 定理定義(文字列・パターン列を大量に持つ重い構造体)は実行中不変なので、
    // タスク処理のたびに丸ごとディープコピーする代わりに Rc でポインタ共有する
    pub theorems: Vec<Rc<TheoremDef>>,
    pub dfs_calls: u64,
    // 🐛 バグ修正: 以前は dfs_match の探索上限が常に100,000固定だった。
    // schedule_full_sweep() から生成される「シードなし(priority<=0)」タスクは、
    // 変数が全て未束縛のまま定理を試すため、変数の多い定理(例: 有向角の加法性)では
    // ほぼ必ず失敗するのに毎回上限いっぱいまで探索してしまい、しかも
    // schedule_full_sweep() は要求解決のたびに何度も呼ばれるため、
    // 同じ「失敗するだけの巨大探索」を繰り返して秒単位の時間を浪費していた
    // (simsonで実測: この1定理だけで5秒中3秒以上を消費)。
    // schedule_matcher_task() 由来のシード済みタスク(priority>=10)は
    // 既に変数の多くが具体的な値に束縛されているため速く失敗/成功するので
    // 上限は据え置き、シードなしタスクだけ上限を大幅に下げて早期に諦めさせる。
    pub dfs_cap: u64,
    pub construction_demands: FxHashMap<(ClassId, ClassId), f64>, // 🌟 Blackboardから移動
    // 🌟 UCB1バンディット統計。theorems と同じインデックス(theorem_idx)で
    // 引く。theoremsはProverEngine::new後にmain.rs側で流し込まれるため、
    // ここでは空のまま初期化し、実際に使う直前にensure_theorem_statsで
    // theorems.len()に合わせてリサイズする。
    pub theorem_stats: Vec<TheoremBanditStats>,
}

impl ProverEngine {
    pub fn new(egraph: EGraph) -> Self {
        Self {
            egraph,
            facts: Vec::new(),
            theorems: Vec::new(),
            dfs_calls: 0,
            dfs_cap: 100_000,
            construction_demands: FxHashMap::default(), // 🌟 追加
            theorem_stats: Vec::new(),
        }
    }

    fn ensure_theorem_stats(&mut self) {
        if self.theorem_stats.len() != self.theorems.len() {
            self.theorem_stats.resize(self.theorems.len(), TheoremBanditStats::default());
        }
    }

    /// 🌟 UCB1スコアを MatchTask.priority (i32) に足し込める小さな整数
    /// ボーナスに変換する。schedule_matcher_task由来のシード済みタスク
    /// (priority=10)よりは必ず低くなるレンジ(-5..=5)にクランプすることで、
    /// 「発見済みの事実に基づく具体的な一手」を常に最優先しつつ、
    /// 同格のシードなし全探索タスクどうしの中では経験的に見込みの高い
    /// 定理から先に試せるようにする。
    pub fn theorem_priority_bonus(&mut self, idx: usize) -> i32 {
        self.ensure_theorem_stats();
        if idx >= self.theorem_stats.len() { return 0; }
        let total: u64 = self.theorem_stats.iter().map(|s| s.attempts).sum();
        let score = self.theorem_stats[idx].ucb1_score(total, 1.0);
        if !score.is_finite() { return 5; } // 未試行の定理は最優先で一度試す
        ((score * 5.0).round() as i32).clamp(-5, 5)
    }

    /// 🌟 schedule_full_sweep由来のシードなしタスクを実際にdfs_matchまで
    /// 走らせた結果をバンディット統計に反映する。シード済みタスク
    /// (is_seeded=true)はここでは記録しない(MatchTask::is_seededの
    /// ドキュメント参照)。
    ///
    /// コスト考慮型の報酬: dfs_calls_used(このタスク1回のdfs_match呼び出しが
    /// 実際に消費したdfs_call数)をdfs_capに対する比率(cost_ratio)として、
    /// - 成功時: 1.0 - 0.5*cost_ratio を 0.1 を下限にクランプ
    ///   (一瞬で成功すれば報酬1.0に近く、cap一杯まで探索してようやく
    ///   成功しても最低0.1は残る = 成功は常に失敗より高評価だが、
    ///   探索コストが高いほど徐々に割り引かれる)
    /// - 失敗時: -0.5*cost_ratio (0以下)
    ///   (何も見つからずに終わった場合、安く諦めたなら0に近く、
    ///   dfs_cap一杯まで無駄に探索したなら-0.5まで下がる)
    /// この結果、「dfs_cap一杯まで探索した末にようやく1回成功する」定理
    /// (以前の二値報酬では"成功"として高く評価されていた)を、実際の
    /// 探索コストに見合った低めのスコアに補正できる。
    pub fn record_theorem_attempt(&mut self, idx: usize, succeeded: bool, dfs_calls_used: u64) {
        self.ensure_theorem_stats();
        let cost_ratio = (dfs_calls_used as f64 / self.dfs_cap.max(1) as f64).min(1.0);
        let reward = if succeeded {
            (1.0 - 0.5 * cost_ratio).max(0.1)
        } else {
            -0.5 * cost_ratio
        };
        if let Some(stats) = self.theorem_stats.get_mut(idx) {
            stats.attempts += 1;
            stats.total_reward += reward;
        }
    }
    fn calc_bind_heat(&self, bind: &Bind) -> f64 {
        let mut heat = 0.0;
        for &id in bind.values() {
            let rep = self.egraph.get_rep(id);
            let e = &self.egraph.entities[rep.0];
            // 熱(heat_bonus) + 基本重要度 + 次数(uses.len()による依存度)
            heat += e.base_importance + e.heat_bonus + (e.uses.len() as f64 * 0.5);
        }
        heat
    }

    fn estimate_cost(&self, pat: &Pattern, bind: &Bind, theorem: &TheoremDef) -> f64 {
        match pat {
            Pattern::Fact(def) => {
                let unbound_count = def.args.iter().filter(|v| !bind.contains_key(*v)).count();
                if unbound_count == 0 { return 0.0; }

                let base_cost = if def.fact_type == "Identical" {
                    if unbound_count == 1 { 1.0 } else { 15.0 }
                } else if def.fact_type == "Connected" {
                    if unbound_count == 1 { 5.0 } else {
                        // 🐛 FIX: 以前は両方未束縛のConnectedを「(None,None)は何もしない」
                        // 前提でコスト10000(=事実上最後回し)にしていたが、(None,None)を
                        // きちんと実装した今は「親の型で絞り込んだ局所探索」でしかない。
                        // 固定値のままだと、円のように個体数が少ない型を親に持つ場合
                        // (安く見積もるべき)と、点のように個体数が多い型を親に持つ場合
                        // (高く見積もるべき)を区別できない。親変数の宣言型を引いて、
                        // 実際にその型が今グラフに何個あるかで見積もる。
                        let parent_var = &def.args[1];
                        match theorem.entities.get(parent_var) {
                            Some(&expected_type) => {
                                let count = self.egraph.entities.iter()
                                    .filter(|e| e.entity_type == expected_type)
                                    .count();
                                (count as f64) * 5.0 + 10.0
                            }
                            None => 10000.0, // 型情報すら無ければ従来通り最後回し
                        }
                    }
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
            Pattern::Not(inner_pat) => self.estimate_cost(inner_pat, bind, theorem),
        }
    }
    
    pub fn is_already_proven(&self, conclusions: &[FactTemplate], bind: &Bind, flips: &FlipStates) -> bool {
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
        remaining: Rc<Vec<Pattern>>,
        bind: Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashSet<u64>, // 🌟 追加
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
        self.dfs_calls += 1;
        if self.dfs_calls > self.dfs_cap { return; }

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
            let cost = self.estimate_cost(pat, &bind, theorem);
            if cost < best_cost { best_cost = cost; best_idx = i; }
        }

        // 🌟 以前は `remaining: Vec<Pattern>` を分岐のたびに丸ごと clone() していたため、
        // 候補が複数ある(順列展開やマッチ候補が多い)ケースで同じパターン列が何度も
        // ディープコピーされていた。ここで一度だけ「評価対象を除いた残り」を作り、
        // Rc に包んで以降は全てポインタコピーで共有する。
        let pat_to_eval = remaining[best_idx].clone();
        let remaining: Rc<Vec<Pattern>> = if remaining.len() == 1 {
            Rc::new(Vec::new())
        } else {
            let mut owned = Vec::with_capacity(remaining.len() - 1);
            for (i, p) in remaining.iter().enumerate() {
                if i != best_idx { owned.push(p.clone()); }
            }
            Rc::new(owned)
        };
        let mut matched_any = false;

        // クロージャをラップして、1度でもマッチしたかを記録する
        let mut wrapped_on_match = |b: &Bind, f: &FlipStates| {
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
                self.dfs_match(theorem, Rc::new(vec![*inner_pat.clone()]), bind.clone(), flip_states.clone(), failed_paths, &mut |_, _| {
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
    /// 🌟 match_fact_pattern はfact_typeごとの処理を振り分けるだけの薄いディスパッチャ。
    /// 以前はこの関数自体が360行あり(Identical/Connected/DefinedBy/汎用の4種の
    /// マッチングロジックが全て1つのmatchの中に同居していた)、可読性の観点から
    /// fact_typeごとの専用メソッドに分割した。挙動は一切変えていない。
    pub fn match_fact_pattern(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef,
        remaining: Rc<Vec<Pattern>>,
        bind: &Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashSet<u64>,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
        match def.fact_type.as_str() {
            "Identical" => self.match_identical_fact(theorem, def, remaining, bind, flip_states, failed_paths, on_match),
            "Connected" => self.match_connected_fact(theorem, def, remaining, bind, flip_states, failed_paths, on_match),
            "DefinedBy" => self.match_defined_by_fact(theorem, def, remaining, bind, flip_states, failed_paths, on_match),
            _ => self.match_generic_fact(theorem, def, remaining, bind, flip_states, failed_paths, on_match),
        }
    }

    /// 🌟 "Identical" パターン: v1, v2 の束縛状況(両方束縛済み/片方だけ/どちらも未束縛)
    /// に応じて分岐する。
    fn match_identical_fact(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef,
        remaining: Rc<Vec<Pattern>>,
        bind: &Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashSet<u64>,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
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
                // 🐛 移植バグ修正: 以前はここで「同じ代表元(=既にマージ済み)を持つ
                // 異なる ClassId のペア」を全列挙しており、1つの等価クラスに
                // N個のエンティティが吸収されていると N*(N-1) 通りに爆発していた
                // (「有向角の加法性」のように、この分岐から探索を始める定理で
                // simsonのタイムアウトの主因になっていた)。
                //
                // Python版の対応する _match_identical (両方未束縛) は、対象の型を
                // 持つ「異なる代表元」それぞれについて v1=v2=その代表元、という
                // 自己束縛を O(代表元の数) で列挙するだけだった。この定理は本来
                // schedule_matcher_task によるシード付き起動(実際に発見された
                // Identical事実からD1..D6を具体的に束縛する経路)で使われる前提であり、
                // シード無しの全探索(schedule_full_sweep)から来た場合はこの程度の
                // 軽い足がかりで十分。Python版と同じ挙動に合わせて計算量を落とす。
                let mut reps: Vec<ClassId> = Vec::new();
                for i in 0..self.egraph.entities.len() {
                    let id = ClassId(i);
                    if self.egraph.get_rep(id) != id { continue; } // 代表元のみ
                    if let Some(et) = expected_type {
                        if self.egraph.entities[i].entity_type != et { continue; }
                    }
                    if self.egraph.entities[i].base_importance > 0.0 {
                        reps.push(id);
                    }
                }
                for rep in reps {
                    let mut next_bind = bind.clone();
                    next_bind.insert(v1.clone(), rep);
                    next_bind.insert(v2.clone(), rep);
                    self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), failed_paths, on_match);
                }
            }
        }
    }

    /// 🌟 "Connected" パターン: child/parent の束縛状況の4通り(両方/片方×2/どちらも未束縛)
    /// で分岐する。
    fn match_connected_fact(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef,
        remaining: Rc<Vec<Pattern>>,
        bind: &Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashSet<u64>,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
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
                // 🌟 最適化: 以前はここが「全エンティティを舐めてis_connectedで
                // 判定する」O(全エンティティ数)の総当たりになっていた
                // ((None, Some(p_id))側の分岐は既にp_rep自身のsubobjectsだけを
                // 見る局所探索に最適化済みで、この分岐だけ非対称に取り残されて
                // いた)。link_logical_incidenceは常に双方向にリンクを張るので
                // (is_connectedの実装もこれを前提に両側を見ている)、c_rep自身の
                // subobjects(局所的で少数)だけを見れば取りこぼしなく同じ結果が
                // 得られる。大きい問題(entities数が多い)ほど効果が大きい。
                let c_rep = self.egraph.get_rep(c_id);
                // 🌟 (None, Some(p_id))側の分岐と同じく、まず候補を(重複除去しつつ)
                // 集め切ってから、egraphへの不変借用を終わらせた後でdfs_matchを呼ぶ
                // (dfs_matchは&mut selfを要求するため)。
                let mut candidates = rustc_hash::FxHashSet::default();
                for comp in &self.egraph.entities[c_rep.0].components {
                    for &sub in &comp.subobjects {
                        let p_rep = self.egraph.get_rep(sub);
                        if p_rep == c_rep || self.egraph.entities[p_rep.0].base_importance <= 0.0 { continue; }
                        if let Some(et) = expected_p_type {
                            if self.egraph.entities[p_rep.0].entity_type != et { continue; }
                        }
                        candidates.insert(p_rep);
                    }
                }
                for p_rep in candidates {
                    let mut next_bind = bind.clone();
                    next_bind.insert(parent_var.clone(), p_rep);
                    self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), failed_paths, on_match);
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
            // 🐛 FIX: 以前は子・親どちらも未束縛の場合に何もせず候補ゼロで
            // 諦めていた(Concyclicを専用Factから「N点が同じ円にConnected」
            // という形に置き換えたことで、この分岐が実際に必要になり発覚した)。
            // 親の型(例:Circle)で絞り込み、各親候補についてはその親自身が
            // 繋がっている子(局所的で少数)だけを見る形で列挙する。
            (None, None) => {
                let mut parent_candidates: Vec<ClassId> = Vec::new();
                for i in 0..self.egraph.entities.len() {
                    let p_id = ClassId(i);
                    let p_rep = self.egraph.get_rep(p_id);
                    if p_rep != p_id || self.egraph.entities[i].base_importance <= 0.0 { continue; }
                    if let Some(et) = expected_p_type {
                        if self.egraph.entities[p_rep.0].entity_type != et { continue; }
                    }
                    parent_candidates.push(p_rep);
                }

                for p_rep in parent_candidates {
                    let child_candidates: Vec<ClassId> = match self.egraph.entities[p_rep.0].components.first() {
                        Some(comp) => comp.subobjects.iter()
                            .map(|&id| self.egraph.get_rep(id))
                            .filter(|&id| {
                                if self.egraph.entities[id.0].base_importance <= 0.0 { return false; }
                                match expected_c_type {
                                    Some(et) => self.egraph.entities[id.0].entity_type == et,
                                    None => true,
                                }
                            })
                            .collect(),
                        None => vec![],
                    };
                    for c_rep in child_candidates {
                        let mut next_bind = bind.clone();
                        next_bind.insert(child_var.clone(), c_rep);
                        next_bind.insert(parent_var.clone(), p_rep);
                        self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), failed_paths, on_match);
                    }
                }
            }
        }
    }

    /// 🌟 "DefinedBy" パターン: result_var(定義された図形そのもの)の束縛状況から
    /// 候補ノードを絞り込み(defined_by_valid_nodes)、それぞれの候補が実際に
    /// target_type型の定義を持っているかを親変数との整合性込みで展開する
    /// (defined_by_collect_matches)。どちらも元は1つの巨大なmatchアームだった。
    fn match_defined_by_fact(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef,
        remaining: Rc<Vec<Pattern>>,
        bind: &Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashSet<u64>,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
        let target_type = def.target_type.as_deref().unwrap_or("");
        let result_var = &def.args[def.args.len() - 1];
        let parent_vars = &def.args[0..def.args.len() - 1];
        let expected_r_type = theorem.entities.get(result_var).copied();

        let valid_nodes = self.defined_by_valid_nodes(target_type, result_var, parent_vars, expected_r_type, bind);
        let mut matches = self.defined_by_collect_matches(def, target_type, parent_vars, result_var, &valid_nodes, bind, &flip_states);

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
    }

    /// 🌟 "DefinedBy" の候補ノード列挙: result_var が既に束縛されていればそれ1つ、
    /// 親変数が全て束縛されていれば対応する定義をmemoから探す(無ければ
    /// AnglePair/DirectionOf/LengthSqに限り新規生成する)、どちらでもなければ
    /// 型が合う全エンティティをフルスキャンする。
    fn defined_by_valid_nodes(
        &mut self,
        target_type: &str,
        result_var: &String,
        parent_vars: &[String],
        expected_r_type: Option<EntityType>,
        bind: &Bind,
    ) -> Vec<ClassId> {
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

        valid_nodes
    }

    /// 🌟 "DefinedBy" の候補ノードそれぞれについて、実際にtarget_type型の定義を
    /// 持っているかを確認し、親変数との束縛の整合性(順不同図形は順列展開、
    /// 有向角のフリップ許可時は両方向)を取りながら (Bind, FlipStates) の
    /// 候補列を作る。読み取り専用(egraphを変更しない)。
    fn defined_by_collect_matches(
        &self,
        def: &FactPatternDef,
        target_type: &str,
        parent_vars: &[String],
        result_var: &String,
        valid_nodes: &[ClassId],
        bind: &Bind,
        flip_states: &FlipStates,
    ) -> Vec<(Bind, FlipStates)> {
        let mut matches = Vec::new();
        for &node_id in valid_nodes {
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
        matches
    }

    /// 🌟 "Identical"/"Connected"/"DefinedBy" 以外の汎用フォールバック:
    /// 既知の事実(self.facts)一覧から get_fact_bindings で束縛候補を集める。
    fn match_generic_fact(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef,
        remaining: Rc<Vec<Pattern>>,
        bind: &Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashSet<u64>,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
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

    pub fn execute_constructions(
        &mut self,
        _theorem_name: &str, // 🌟 命名には親図形の実名を使うので、定理名はもう使わない(呼び出し側との互換のため残置)
        constructions: &[ConstructTemplate],
        bind: &mut Bind,
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
                
                // 🐛 バグ修正: 以前はテンプレートの変数名(bind_to、例: "Ang_MH_CH")と
                // 定理名をそのまま繋げていたため、"Ang_MH_CH_直角三角形の斜辺の中線_(Auto)"
                // のように、実際にどの図形から作られたのか全く追跡できない名前になっていた。
                // match_defined_by の自動生成箇所と同じ規則で、実際に束縛された親図形の
                // 名前をそのまま繋げる(例: "AnglePair_H_C_(Auto)")ようにし、名前から
                // 構成を逆に辿れるようにする。
                let parent_names: Vec<String> = parent_ids.iter()
                    .map(|&id| self.egraph.entities[id.0].name.clone())
                    .collect();
                let prefix = if constr.def_type == "DirectionOf" { "Dir" } else { constr.def_type.as_str() };
                let name = format!("{}_{}_(Auto)", prefix, parent_names.join("_"));

                let id = self.egraph.create_entity(name, def.clone(), entity_type);
                self.egraph.apply_trivial_relations(id, &def);
                id
            };
            
            bind.insert(constr.bind_to.clone(), new_id);
        }
        true
    }

    /// 🌟 証明復元(explain)用: この定理が実際に使った前提事実だけを、
    /// bindを通じて具体的なClassIdに解決して集める。
    /// Python版はbind.values()を丸ごと前提として記録していたため、
    /// マッチの過程でたまたま一緒に束縛されていただけの無関係な図形まで
    /// 証明ツリーに混入していた(ユーザー指摘の「不要な定理が多く含まれる」原因)。
    /// ここではtheorem.patterns中のPattern::Fact節(実際に検証された前提)だけを
    /// 辿るので、そのような無関係な図形は含まれない。
    fn compute_theorem_premises(theorem: &TheoremDef, bind: &Bind) -> Vec<(String, Vec<ClassId>)> {
        let mut premises = Vec::new();
        for pat in &theorem.patterns {
            if let Pattern::Fact(fpd) = pat {
                let resolved: Option<Vec<ClassId>> = fpd.args.iter().map(|a| bind.get(a).copied()).collect();
                if let Some(args) = resolved {
                    premises.push((fpd.fact_type.clone(), args));
                }
            }
        }
        premises
    }

    pub fn apply_conclusions(&mut self, theorem: &TheoremDef, bind: &Bind, flips: &FlipStates) -> (bool, Vec<Fact>) {
        let mut applied_anything = false;
        let mut new_facts = Vec::new();
        let theorem_name = theorem.name.as_str();
        let premises = Self::compute_theorem_premises(theorem, bind);

        for conc in &theorem.conclusions {
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
                        let justification = crate::mmp_core::Justification::Theorem {
                            name: theorem_name.to_string(),
                            premises: premises.clone(),
                        };
                        if self.egraph.merge_entities_justified(r1, r2, justification) {
                            println!("  🟢 [マージ実行] {} ≡ {} (理由: {})", name1, name2, theorem_name);
                            // 🌟 マージされた代表元の熱を上げて今後のDFSで優先させる[cite: 5]
                            self.egraph.entities[r1.0].heat_bonus += 1.5;
                            applied_anything = true;
                        }
                    }
                }
                // 🌟 FIX: Connected によるE-Graphの物理リンク構築を追加
                // (Concyclic/Collinearを専用Factとして結論に持つのはやめ、
                // 「N点が同じ円/直線にConnectedである」という形に統一した)
                "Connected" => {
                    if let (Some(&child), Some(&parent)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1])) {
                        let c_rep = self.egraph.get_rep(child);
                        let p_rep = self.egraph.get_rep(parent);
                        let justification = crate::mmp_core::Justification::Theorem {
                            name: theorem_name.to_string(),
                            premises: premises.clone(),
                        };
                        self.egraph.link_logical_incidence_justified(c_rep, p_rep, justification);
                        applied_anything = true;
                        println!("  🟢 [リンク構築] {} ∈ {} (理由: {})",
                            self.egraph.entities[c_rep.0].name, self.egraph.entities[p_rep.0].name, theorem_name);

                        // 🐛 FIX: 以前はここでe-graphへの物理リンクを張るだけで、
                        // Fact::Connected を一切生成・記録していなかった。そのため
                        // schedule_matcher_task によるシード付き再マッチングが
                        // 一度も起きず、この新しい接続に依存する他の定理(円周角の定理など)
                        // が「シードなしの全探索(schedule_full_sweep)頼み」になって
                        // 見逃されることがあった(miquelで実際に退行した)。
                        // Identical/他のFactと同様にFactとして記録し、FactProvenイベント
                        // 経由でシード付き再マッチングが起きるようにする。
                        let fact = Fact::Connected(c_rep, p_rep);
                        if !self.facts.contains(&fact) {
                            self.facts.push(fact.clone());
                            new_facts.push(fact);
                        }
                    }
                },
                _ => {}
            }
        }
        (applied_anything, new_facts)
    }

    fn get_fact_bindings(&self, theorem: &TheoremDef, fact: &Fact, fact_type: &str, args: &[String], current_bind: &Bind) -> Vec<Bind> {
        let (f_type, f_objs) = match fact {
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

        let is_unordered = f_type == "Identical";
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
    // 🌟 UCB1バンディットの効果測定用のA/Bスイッチ。false にすると
    // schedule_full_sweep がシードなしタスクの優先度を常に0固定にする
    // (バンディット導入前の挙動に戻す)。既定は有効(true)。
    pub bandit_enabled: bool,
}

impl BlackboardEngine {
    pub fn new(prover: ProverEngine) -> Self {
        Self {
            prover,
            task_queue: BinaryHeap::new(),
            event_queue: VecDeque::new(),
            bandit_enabled: true,
        }
    }

    pub fn schedule_full_sweep(&mut self) {
        // 🌟 FIX: シード注入済みのタスクは消さずに保持する!
        // 🐛 以前は「priority > 0」で判定していたが、UCB1バンディットの
        // 導入でシードなしタスクの優先度も +5 まで上がり得るようになったため、
        // priorityの値ではなく専用フラグ(is_seeded)で由来を判定する。
        let mut keep = Vec::new();
        for task in self.task_queue.drain() {
            if task.is_seeded { keep.push(task); }
        }
        self.task_queue = BinaryHeap::from(keep);

        // 🌟 UCB1バンディット: シードなし全探索タスクどうしの優先度を、
        // これまでの経験的な成功率(+探索ボーナス)で差別化する。
        // self.prover.theorems.iter() で theorems を借用したまま
        // self.prover.theorem_priority_bonus(&mut self.prover) は呼べない
        // (借用の競合)ため、先にインデックスごとの優先度だけを計算しておく。
        // bandit_enabled=false の場合は全定理を優先度0固定にし、導入前と
        // 同じ挙動に戻す(A/B比較用)。
        let theorem_count = self.prover.theorems.len();
        let priorities: Vec<i32> = if self.bandit_enabled {
            (0..theorem_count).map(|idx| self.prover.theorem_priority_bonus(idx)).collect()
        } else {
            vec![0; theorem_count]
        };

        for (idx, theorem) in self.prover.theorems.iter().enumerate() {
            let mut initial_bind = Bind::new();
            initial_bind.insert("Ang90".to_string(), self.prover.egraph.ang90);
            initial_bind.insert("Ang0".to_string(), self.prover.egraph.ang0);

            self.task_queue.push(MatchTask {
                priority: priorities[idx],
                theorem_idx: idx,
                bind: initial_bind,
                flip_states: FlipStates::new(),
                remaining_patterns: Rc::new(theorem.patterns.clone()),
                is_seeded: false,
            });
        }
    }

    fn schedule_matcher_task(&mut self, fact: &Fact) {
        let (fact_type, fact_objs) = match fact {
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
                            _ => get_permutations(&fact_objs),      // Identical 等は全順列
                        };

                        for perm in perms {
                            let mut bind = Bind::new();
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
                                flip_states: FlipStates::new(),
                                remaining_patterns: Rc::new(theorem.patterns.clone()),
                                is_seeded: true,
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
                // 🌟 task はcap到達時に self.task_queue.push(task) で再キューされ
                // 得るため(move)、後段のバンディット記録で使うフィールドは
                // Copy型としてここで先に控えておく。
                let task_theorem_idx = task.theorem_idx;
                let task_is_seeded = task.is_seeded;
                // 🌟 theorems は Vec<Rc<TheoremDef>> なので、この clone() はもう
                // ディープコピーではなく参照カウントのインクリメントのみ(ポインタコピー相当)
                let theorem = self.prover.theorems[task.theorem_idx].clone();
                let mut new_binds = Vec::new();
                let mut failed_paths = rustc_hash::FxHashSet::default();

                // 🌟 検証メモ: 当初は schedule_full_sweep() 由来のシードなしタスク
                // (priority<=0) だけ上限を 20,000 に下げる案を試したが、miquel の
                // 「有向角の加法性」「円周角の定理の逆」はまさにシードなし状態から
                // 20,000〜100,000回の間で成功しており、上限を下げるとリトライのたびに
                // failed_paths キャッシュが空の状態から探索をやり直すだけになって
                // かえって遅くなった(0.69s→1.15s)ため撤回した。
                // 上限自体は104行目のフィールド定義の通り常に100,000のまま。

                self.prover.dfs_match(
                    &theorem,
                    task.remaining_patterns.clone(), // Rc なのでポインタコピーのみ
                    task.bind.clone(), 
                    task.flip_states.clone(), 
                    &mut failed_paths,
                    &mut |bind, flips| {
                        new_binds.push((bind.clone(), flips.clone()));
                    }
                );
                // 🌟 コスト考慮型バンディット報酬のために、このタスク1回が
                // 実際に消費したdfs_call数を控えておく(次のタスクの
                // self.prover.dfs_calls = 0 まではこの値のまま変わらない)。
                let dfs_calls_used = self.prover.dfs_calls;

                // 🌟 スケジューリング工夫: DFSが上限(100,000)に張り付いた場合、
                // このタスクは重すぎるためペナルティを与えて後回しにする。
                //
                // 🐛 バグ修正: 以前はキューが空(＝他に実行できるタスクが無い)の場合でも
                // 無条件に再キューしていた。この場合 e-graph も bind も何一つ変化しないまま
                // 全く同じ 100,000 回の探索を優先度が尽きるまで(最大5回)繰り返すだけになり、
                // 実測で simson 問題では1つの定理(有向角の加法性)のリトライだけで
                // 5秒の予算のうち3秒以上を無駄にしていた。他に実行可能なタスクが残っている
                // 場合のみ再キューし、無い場合はその場で諦めてリカバリーフェーズに委ねる。
                if self.prover.dfs_calls >= self.prover.dfs_cap {
                    if !self.task_queue.is_empty() {
                        task.priority -= 5;
                        if task.priority >= -20 { // 諦める閾値
                            self.task_queue.push(task);
                        }
                    }
                }

                // 🌟 UCB1バンディット: このタスク(1回のdfs_match呼び出し)が
                // 実際に何か結論を適用できたかどうかを、シードなしタスクに限って
                // theorem_statsに反映する。「試したが何も生まなかった」も
                // 立派な学習対象(失敗)である。
                let mut task_succeeded = false;

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

                        let (applied, generated_facts) = self.prover.apply_conclusions(&theorem, &bind, &flips);
                        if applied {
                            applied_anything = true;
                            task_succeeded = true;
                            self.emit(Event::NodeMerged);
                            for f in generated_facts { self.emit(Event::FactProven(f)); }
                        }
                    }
                }

                if !task_is_seeded {
                    self.prover.record_theorem_attempt(task_theorem_idx, task_succeeded, dfs_calls_used);
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
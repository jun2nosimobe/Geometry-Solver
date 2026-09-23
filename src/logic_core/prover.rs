//! 証明器の状態そのもの(ProverEngine)と、定理の適用。
//!
//! e-graph・既知の事実・定理ごとの統計・失敗パスのキャッシュを保持し、マッチが成立した後の
//! 作図(execute_constructions)と結論の適用(apply_conclusions)を行う。
//! 探索は matcher.rs、見積もりは cost.rs。

use std::rc::Rc;

use crate::mmp_core::{ClassId, EGraph, EntityType, Fact};
use super::*;
use rustc_hash::FxHashMap;

/// 型だけで決まる候補の組の列挙結果(定理をまたいで共有する)。
pub type PairList = Rc<Vec<(ClassId, ClassId)>>;

pub struct ProverEngine {
    pub egraph: EGraph,
    /// 記録済みの事実(同じ事実でシード付き再マッチングを二度積まないため)。
    pub facts: rustc_hash::FxHashSet<Fact>,
    /// 実行中は不変なので Rc で共有する(タスクごとの複製をポインタのコピーにする)。
    pub theorems: Vec<Rc<TheoremDef>>,
    /// いま走っているタスク1回分の dfs_match 呼び出し回数。
    pub dfs_calls: u64,
    /// タスク1回あたりの dfs_match 呼び出しの上限。達したタスクは優先度を下げて再キューする。
    pub dfs_cap: u64,
    /// 候補を熱の降順に並べて打ち切る上限(Identical の自己束縛、Connected の局所スキャン・ジョイン)。
    pub heat_cap: usize,
    /// 自己束縛の候補数が下流の分岐係数に掛け算で効く定理向けの、狭い上限。
    /// 需要駆動の作図が尽きた手詰まりのときに main が段階的に広げるので、これは初期値。
    pub fanout_heat_cap: usize,
    /// 🌟 Connected の片側だけ束縛の候補も、heat_cap(既定40)ではなく fanout_heat_cap(既定5、行き詰まったら
    /// 広げる)で絞るか。図に無関係な作図が増えると、この分岐の候補が毎段40まで広がって掛け算で爆発する。
    pub fanout_connected: bool,
    /// 🌟 熱の cap が実際に候補を切り捨てた回数(前回 cap を広げてからの分)。0 なら cap を広げても候補は
    /// 増えないので、広げる意味がない ― 「広げるのを先にするか」の判断に使う。
    pub fanout_truncations: u64,
    /// 「2点はあるのに結ぶ直線が無い」需要(点の組 → 回数)。resolve_demands が消費する。
    pub construction_demands: FxHashMap<(ClassId, ClassId), f64>,
    /// 「2直線はあるのに交点が無い」需要(ソート済みの直線の組 → 回数)。resolve_point_demands が消費する。
    pub point_construction_demands: FxHashMap<(ClassId, ClassId), f64>,
    /// theorems と同じ添字で引く。theorems が確定してから ensure_* で遅延初期化する。
    pub theorem_stats: Vec<TheoremBanditStats>,
    pub theorem_required_types: Vec<Vec<EntityType>>,
    /// 定理ごとの、パターンから変数へのビット索引(失敗キャッシュの鍵を絞るのに使う)。
    pub theorem_var_index: Vec<Rc<PatternVarIndex>>,
    /// 🌟 失敗キャッシュの鍵を「残っているパターンが実際に見る変数」だけで作るか。
    /// 無関係な変数を鍵から外すと、同じ理由の失敗が1つにまとまる。
    pub nogood_core: bool,
    /// 型だけで結果が決まる候補列挙の、定理をまたいだ共有キャッシュ(値は結果と計算時の型世代)。
    /// Connected 両方未束縛のジョイン。キーは (子の型, 親の型)。
    pub connected_join_cache: FxHashMap<(EntityType, EntityType), (PairList, u64, u64)>,
    /// Identical 自己束縛の候補。キーは宣言型。
    pub identical_self_bind_cache: FxHashMap<EntityType, (Rc<Vec<ClassId>>, u64)>,
    /// Scalar の自己束縛候補を角度とそれ以外に分けたもの。Scalar 全体の世代で無効化すると、
    /// 無関係な側の生成のたびに作り直しになる。
    pub identical_self_bind_angle_cache: Option<(Rc<Vec<ClassId>>, u64)>,
    pub identical_self_bind_plain_scalar_cache: Option<(Rc<Vec<ClassId>>, u64)>,
    /// DefinedBy で親も結果も未束縛のときの候補。キーは結果の型。
    pub defined_by_full_scan_cache: FxHashMap<EntityType, (Rc<Vec<ClassId>>, u64)>,
    /// 定理ごとの失敗パス。状態署名は束縛の中身だけで決まるので、タスクをまたいで共有できる。
    /// 各エントリの有効性は参照時に依存マスクと型世代で検証する。
    pub global_failed_paths: Vec<FailedPaths>,
    pub profile: ProfileStats,
    /// いま伸ばそうとしている枝がどの種類のパターンから出たか(BRANCH_LABELS の添字)。
    /// dfs_match の直前に控え、入口で数える。
    pub branch_tag: u8,
    /// --trace の発火ログ。None なら apply_conclusions は何も記録しない。
    pub trace: Option<crate::trace::TraceLog>,
    /// --audit-merges の集計。None なら定理の結論を検算しない。
    pub merge_audit: Option<MergeAudit>,
}

/// 定理の結論(マージ・接続)を適用する直前に、前提を満たす乱数座標で検算した結果の集計(--audit-merges)。
/// 定理の書き方の誤りは、結論が数値で裏付けられずにマージされるので、最終目標の検算に引っかかるまで気づけない。
/// 検算は探索の乱数を消費しないので、付けても探索の結果は変わらない。
#[derive(Default)]
pub struct MergeAudit {
    /// 定理名 -> [真, 偽, 判定不能]。
    pub per_theorem: std::collections::BTreeMap<String, [u64; 3]>,
    /// 偽だった結論の例(定理ごとに最初の数件)。
    pub false_examples: Vec<(String, String)>,
}

impl MergeAudit {
    const EXAMPLES_PER_THEOREM: usize = 3;

    fn record(&mut self, theorem: &str, verdict: Option<bool>, describe: impl FnOnce() -> String) {
        let slot = match verdict { Some(true) => 0, Some(false) => 1, None => 2 };
        let counts = self.per_theorem.entry(theorem.to_string()).or_default();
        counts[slot] += 1;
        if verdict == Some(false) && counts[1] as usize <= Self::EXAMPLES_PER_THEOREM {
            self.false_examples.push((theorem.to_string(), describe()));
        }
    }
}

/// ProfileStats::branch_counts の添字の意味。
pub const BRANCH_LABELS: [&str; 11] = [
    "制約(Order/Distinct/Not)", "Identical 両方束縛済み", "Identical 片方束縛済み",
    "Identical 自己束縛(両方未束縛)", "Connected 両方束縛済み", "Connected 親のみ束縛",
    "Connected 子のみ束縛", "Connected 局所スキャン", "Connected 局所スキャン2",
    "Connected 両方未束縛ジョイン", "DefinedBy",
];

/// --profile 用の計測。証明の結果には影響しない。
#[derive(Debug, Clone, Copy, Default)]
pub struct ProfileStats {
    pub sfs_calls: u64,
    pub sfs_time: std::time::Duration,
    pub sfs_tasks_created: u64,
    pub run_step_time: std::time::Duration,
    pub recovery_time: std::time::Duration,
    pub mcts_time: std::time::Duration,
    pub seeded_pops: u64,
    pub seeded_dfs_calls: u64,
    pub unseeded_pops: u64,
    pub unseeded_dfs_calls: u64,
    pub branch_counts: [u64; BRANCH_LABELS.len()],
}

impl ProverEngine {
    /// これまでに消費した仕事量(dfs_match の呼び出し回数の累計)。探索の予算はこれで測るので、
    /// 同じ問題は機械の混み具合に関係なく同じ結果になる。
    pub fn work_done(&self) -> u64 {
        self.profile.seeded_dfs_calls + self.profile.unseeded_dfs_calls
    }

    pub fn new(egraph: EGraph) -> Self {
        Self {
            egraph,
            facts: rustc_hash::FxHashSet::default(),
            theorems: Vec::new(),
            dfs_calls: 0,
            dfs_cap: 100_000,
            heat_cap: 40,
            fanout_heat_cap: 5,
            fanout_connected: false,
            fanout_truncations: 0,
            construction_demands: FxHashMap::default(),
            point_construction_demands: FxHashMap::default(),
            theorem_stats: Vec::new(),
            theorem_required_types: Vec::new(),
            theorem_var_index: Vec::new(),
            nogood_core: false,
            connected_join_cache: FxHashMap::default(),
            identical_self_bind_cache: FxHashMap::default(),
            identical_self_bind_angle_cache: None,
            identical_self_bind_plain_scalar_cache: None,
            defined_by_full_scan_cache: FxHashMap::default(),
            global_failed_paths: Vec::new(),
            profile: ProfileStats::default(),
            branch_tag: 0,
            trace: None,
            merge_audit: None,
        }
    }

    pub(crate) fn ensure_global_failed_paths(&mut self) {
        if self.global_failed_paths.len() != self.theorems.len() {
            self.global_failed_paths.resize_with(self.theorems.len(), FailedPaths::default);
        }
    }

    pub(crate) fn ensure_theorem_stats(&mut self) {
        if self.theorem_stats.len() != self.theorems.len() {
            self.theorem_stats.resize(self.theorems.len(), TheoremBanditStats::default());
        }
    }

    pub(crate) fn ensure_theorem_var_index(&mut self) {
        if self.theorem_var_index.len() != self.theorems.len() {
            self.theorem_var_index = self.theorems.iter()
                .map(|t| Rc::new(PatternVarIndex::build(t)))
                .collect();
        }
    }

    /// 失敗キャッシュに溜まっているエントリの総数(鍵の絞り込みが効いているかの目安)。
    pub fn failed_path_entries(&self) -> usize {
        self.global_failed_paths.iter().map(|m| m.len()).sum()
    }

    pub(crate) fn ensure_theorem_required_types(&mut self) {
        if self.theorem_required_types.len() != self.theorems.len() {
            self.theorem_required_types = self.theorems.iter()
                .map(|t| required_hard_types(t))
                .collect();
        }
    }

    /// 定理が前提で要求する「その場で作られない型」の実体が、図に1つずつはあるか。
    /// 無ければ全探索を試すだけ無駄なので、スケジュールしない。
    pub fn theorem_types_available(&mut self, idx: usize) -> bool {
        self.ensure_theorem_required_types();
        match self.theorem_required_types.get(idx) {
            Some(types) => types.iter().all(|&t| self.egraph.has_entity_of_type(t)),
            None => true,
        }
    }

    /// UCB1 スコアを全探索タスクの優先度(-50..=50)に直す。未試行の定理は 50。
    /// シード済みタスク(優先度100)より必ず低い。
    pub fn theorem_priority_bonus(&mut self, idx: usize) -> i32 {
        self.ensure_theorem_stats();
        if idx >= self.theorem_stats.len() { return 0; }
        let total: u64 = self.theorem_stats.iter().map(|s| s.attempts).sum();
        let score = self.theorem_stats[idx].ucb1_score(total, 1.0);
        if !score.is_finite() { return 50; }
        ((score * 50.0).round() as i32).clamp(-50, 50)
    }

    /// 全探索タスク1回の結果を統計に記録する。報酬はコストで割り引く:
    /// 成功なら 1 - 0.5·(使った仕事量/dfs_cap)(下限0.1)、失敗なら -0.5·(同)。
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
            stats.total_dfs_calls += dfs_calls_used;
            if dfs_calls_used >= self.dfs_cap {
                stats.cap_hits += 1;
            }
        }
    }

    /// 定理の作図テンプレートを実行し、作った(または既にあった)図形を bind に入れる。
    /// 親が束縛されていない・親の数が合わないときは false。
    pub fn execute_constructions(&mut self, constructions: &[Construction], bind: &mut Bind) -> bool {
        for constr in constructions {
            let Some(parent_ids) = constr.args.iter()
                .map(|arg| bind.get(arg).map(|&id| self.egraph.get_rep(id)))
                .collect::<Option<Vec<ClassId>>>() else { return false };
            let Some(def) = self.egraph.build_definition(constr.kind, &parent_ids) else { return false };

            let new_id = if let Some(&existing_id) = self.egraph.memo.get(&def) {
                self.egraph.get_rep(existing_id)
            } else {
                // 名前は実際に束縛された親の名前から作る(どの図形から作ったか辿れるように)。
                let parent_names: Vec<String> = parent_ids.iter()
                    .map(|&id| self.egraph.entities[id.0].name.clone())
                    .collect();
                let name = format!("{}_{}_(Auto)", constr.kind.label(), parent_names.join("_"));
                let prev_origin = self.egraph.set_origin(crate::mmp_core::EntityOrigin::Construct);
                let id = self.egraph.create_entity(name, def.clone(), def.default_entity_type());
                self.egraph.apply_trivial_relations(id, &def);
                self.egraph.set_origin(prev_origin);
                id
            };
            bind.insert(constr.bind_to.clone(), new_id);
        }
        true
    }

    /// 証明の記録に残す前提: 定理のトップレベルの事実パターンだけを bind で解決したもの
    /// (マッチの途中でたまたま束縛されていただけの図形を混ぜない)。
    pub(crate) fn compute_theorem_premises(theorem: &TheoremDef, bind: &Bind) -> Vec<(String, Vec<ClassId>)> {
        theorem.patterns.iter().filter_map(|pat| {
            let label = pat.premise_label()?;
            let args: Option<Vec<ClassId>> = pat.fact_args()?.iter().map(|a| bind.get(*a).copied()).collect();
            Some((label, args?))
        }).collect()
    }

    /// 結論を e-graph に反映する。何か変えたら true と、新しく記録した Connected の事実を返す。
    pub fn apply_conclusions(&mut self, theorem: &TheoremDef, bind: &Bind, flips: &FlipStates) -> (bool, Vec<Fact>) {
        let mut applied_anything = false;
        let mut new_facts = Vec::new();
        let theorem_name = theorem.name.as_str();
        let premises = Self::compute_theorem_premises(theorem, bind);
        // --trace: この発火が作ったマージ/接続を控え、後で証明から逆にたどった集合と突き合わせる。
        let tracing = self.trace.is_some();
        let mut traced_merges: Vec<(usize, usize)> = Vec::new();
        let mut traced_incidences: Vec<(usize, usize)> = Vec::new();
        let justification = || crate::mmp_core::Justification::Theorem {
            name: theorem_name.to_string(),
            premises: premises.clone(),
        };

        for conc in &theorem.conclusions {
            match conc {
                Conclusion::Identical(a, b) => {
                    let (Some(&id1), Some(&id2)) = (bind.get(a), bind.get(b)) else { continue };
                    let r1 = self.egraph.get_rep(id1);
                    let r2 = self.egraph.get_rep(id2);
                    if r1 == r2 { continue; }
                    // 向きの違う有向角は同じ値ではない。
                    if flips.get(a).copied().unwrap_or(false) != flips.get(b).copied().unwrap_or(false) { continue; }

                    let name1 = self.egraph.entities[r1.0].name.clone();
                    let name2 = self.egraph.entities[r2.0].name.clone();
                    let verdict = self.merge_audit.as_ref()
                        .map(|_| self.egraph.without_consuming_rng(|eg| eg.numeric_plausibility_check(r1, r2, 2)));
                    if self.egraph.merge_entities_justified(r1, r2, justification()) {
                        if let (Some(audit), Some(v)) = (self.merge_audit.as_mut(), verdict) {
                            audit.record(theorem_name, v, || format!("{} ≡ {}", name1, name2));
                        }
                        if tracing {
                            traced_merges.push(if r1.0 <= r2.0 { (r1.0, r2.0) } else { (r2.0, r1.0) });
                        }
                        println!("  🟢 [マージ実行] {} ≡ {} (理由: {})", name1, name2, theorem_name);
                        // マージされた代表元を熱くして、今後の探索で先に試させる。
                        self.egraph.bump_heat_bonus(r1, 1.5);
                        applied_anything = true;
                    }
                }
                Conclusion::Connected(c, p) => {
                    let (Some(&child), Some(&parent)) = (bind.get(c), bind.get(p)) else { continue };
                    let c_rep = self.egraph.get_rep(child);
                    let p_rep = self.egraph.get_rep(parent);
                    if self.merge_audit.is_some() {
                        let v = self.egraph.without_consuming_rng(|eg| eg.numeric_incidence_check(c_rep, p_rep, 2));
                        let (cn, pn) = (self.egraph.entities[c_rep.0].name.clone(), self.egraph.entities[p_rep.0].name.clone());
                        if let Some(audit) = self.merge_audit.as_mut() {
                            audit.record(theorem_name, v, || format!("{} ∈ {}", cn, pn));
                        }
                    }
                    self.egraph.link_logical_incidence_justified(c_rep, p_rep, justification());
                    if tracing {
                        traced_incidences.push(if c_rep.0 <= p_rep.0 { (c_rep.0, p_rep.0) } else { (p_rep.0, c_rep.0) });
                    }
                    applied_anything = true;
                    println!("  🟢 [リンク構築] {} ∈ {} (理由: {})",
                        self.egraph.entities[c_rep.0].name, self.egraph.entities[p_rep.0].name, theorem_name);

                    let fact = Fact::Connected(c_rep, p_rep);
                    if self.facts.insert(fact.clone()) {
                        new_facts.push(fact);
                    }
                }
            }
        }
        if tracing {
            let work_at = self.work_done();
            let used = self.dfs_calls;
            if let Some(t) = self.trace.as_mut() {
                t.record(theorem_name, work_at, used, traced_merges, traced_incidences);
            }
        }
        (applied_anything, new_facts)
    }
}

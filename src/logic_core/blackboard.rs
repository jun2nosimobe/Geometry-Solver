//! 探索の司令塔(BlackboardEngine)。
//!
//! どの定理をどの順で試すかのタスク待ち行列を回し(run_step)、行き詰まったときは需要駆動の
//! 補助作図(resolve_*)で図を伸ばす。

use std::collections::{BinaryHeap, HashSet, VecDeque};

use crate::mmp_core::{ClassId, Definition, EGraph, EntityOrigin, EntityType, Fact};
use super::*;
use super::matcher::Search;
use rustc_hash::FxHashMap;

/// 候補cap(fanout_heat_cap)を広げるときの上限。
pub const FANOUT_HEAT_CAP_CEILING: usize = 40;

/// 行き詰まったときの決定的な手(BlackboardEngine::recover)の設定。
#[derive(Clone, Debug, Default)]
pub struct RecoveryOptions {
    /// 需要駆動の中点(resolve_midpoint_demands)も使うか。
    pub midpoint_demands: bool,
    /// 外す手の名前(line, point, angle, second, mid, target)。
    pub skip: Vec<String>,
    /// 🌟 図を広げる手(有向角・第2交点・中点・目標からの逆算)より先に、候補capの拡大を試すか。
    /// cap を広げても図は増えず、失敗キャッシュも効くので安い。図が大きいほど「広げるのが遅れる」代償が大きい。
    pub widen_first: bool,
    /// 先に広げるのはこの値までとし、それ以上は従来どおり需要作図の後に広げる。
    /// 小さい図では広げるほど探索が重くなるので、早い拡大は控えめにする。
    pub widen_first_ceiling: usize,
    /// 🌟 行き詰まり何回ごとに、需要作図より先に候補capの拡大を試すか(0 なら試さない。solve の既定は2)。
    /// 需要作図は図が大きいほど尽きにくく、そのままだと cap を広げる番が来る前に図が膨らみ切ってしまう。
    pub widen_every: usize,
}

impl RecoveryOptions {
    fn skipped(&self, name: &str) -> bool {
        self.skip.iter().any(|s| s == name)
    }
}

/// BlackboardEngine::recover が打った手。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Recovered {
    /// 需要駆動の作図で図を伸ばした。
    Construction,
    /// 候補capを広げて全探索をやり直す(値は広げた後の cap)。
    WidenedCap(usize),
    /// 決定的な手が尽きた。
    Exhausted,
}

pub struct BlackboardEngine {
    pub prover: ProverEngine,
    pub task_queue: BinaryHeap<MatchTask>,
    pub event_queue: VecDeque<Event>,
    /// UCB1 バンディットで全探索タスクの優先度を付けるか(既定は無効: 実測で仕事量が20%増えた)。
    pub bandit_enabled: bool,
    /// 証明された事実で変数を固定したタスクを積むか(既定は無効: 積む量が多すぎて全体が悪化する)。
    pub seeded_rematch_enabled: bool,
    /// 🌟 1回の run_step の中で結論をすぐ適用せず、全タスクを試してからまとめて適用するか(--batch-conclusions)。
    /// 既定(false)だと、先に発火した定理のマージが同じ全探索の後続タスクから見えるので、定理を試す順序で
    /// 探索の進み方が変わる(§05 の順序依存)。true にすると、その全探索の中では全タスクが同じ図を見る。
    pub batch_conclusions: bool,
    /// 前回 cap を広げてからの行き詰まりの回数(widen_every の判定に使う)。
    pub stalls_since_widen: usize,
    /// 仕事量(ProverEngine::work_done)の上限。run_step はタスクごとにこれを確かめるので、
    /// 1回の run_step の途中でも予算を使い切ったら止まる。
    pub work_limit: u64,
}

impl BlackboardEngine {
    pub fn new(prover: ProverEngine) -> Self {
        Self {
            prover,
            task_queue: BinaryHeap::new(),
            event_queue: VecDeque::new(),
            bandit_enabled: false,
            seeded_rematch_enabled: false,
            batch_conclusions: false,
            stalls_since_widen: 0,
            work_limit: u64::MAX,
        }
    }

    /// 行き詰まったときの決定的な手を順に打つ。solve・serve・discover の証明試行で共通。
    ///
    /// 補助線と交点は毎回試す。それ以降は、狙いの定まった手が何も出さなかったときだけ広げる
    /// (有向角の総当たり・もう一方の交点は、毎回回すと解ける問題を遠回りさせる)。目標からの逆算は、
    /// 未達の目標を rotate の位置から順に回し、最初に何か作れたところで止める。
    /// 作図が何も出なければ候補capを広げる: 狭い cap で除外されていただけの候補なら MCTS よりずっと安く届き、
    /// 失敗キャッシュが既に試した候補を再利用するので同じ探索を繰り返さない。
    pub fn recover(&mut self, open_targets: &[(String, Vec<ClassId>)], rotate: &mut usize, opts: &RecoveryOptions) -> Recovered {
        self.stalls_since_widen += 1;
        let mut recovered = !opts.skipped("line") && self.resolve_demands();
        if !opts.skipped("point") && self.resolve_point_demands() { recovered = true; }
        // cap の拡大を先に試す(--widen-first)。広げられたらそこで戻り、次の全探索を同じ図でやり直す。
        // cap が一度も候補を切り捨てていなければ、広げても候補は増えないので先に広げる意味がない。
        // widen_every 回の行き詰まりごとに、需要作図より先に広げる番を作る(需要作図が尽きるのを待たない)。
        let due = opts.widen_first || (opts.widen_every > 0 && self.stalls_since_widen >= opts.widen_every);
        if !recovered && due && self.prover.fanout_truncations > 0
            && self.prover.fanout_heat_cap < opts.widen_first_ceiling.min(FANOUT_HEAT_CAP_CEILING) {
            self.prover.fanout_heat_cap = (self.prover.fanout_heat_cap * 2).min(FANOUT_HEAT_CAP_CEILING);
            self.prover.fanout_truncations = 0;
            self.stalls_since_widen = 0;
            self.schedule_full_sweep();
            return Recovered::WidenedCap(self.prover.fanout_heat_cap);
        }
        if !recovered && !opts.skipped("angle") && self.resolve_angle_demands() { recovered = true; }
        if !recovered && !opts.skipped("second") && self.resolve_second_intersection_demands() { recovered = true; }
        if !recovered && opts.midpoint_demands && !opts.skipped("mid") && self.resolve_midpoint_demands() { recovered = true; }
        if !recovered && !opts.skipped("target") {
            for _ in 0..open_targets.len() {
                let goal = Some(open_targets[*rotate % open_targets.len()].clone());
                *rotate += 1;
                if self.resolve_target_demands(&goal) || self.resolve_cross_ratio_demands(&goal) {
                    recovered = true;
                    break;
                }
            }
        }
        if recovered { return Recovered::Construction; }

        if self.prover.fanout_heat_cap < FANOUT_HEAT_CAP_CEILING {
            self.prover.fanout_heat_cap = (self.prover.fanout_heat_cap * 2).min(FANOUT_HEAT_CAP_CEILING);
            self.schedule_full_sweep();
            return Recovered::WidenedCap(self.prover.fanout_heat_cap);
        }
        Recovered::Exhausted
    }

    /// 数値的な偶然の一致(予想)を評価して熱に反映する(実体は EGraph 側)。
    pub fn process_pending_conjectures(&mut self, target: &Option<(String, Vec<ClassId>)>) -> usize {
        self.prover.egraph.process_pending_conjectures(target)
    }

    /// 予想 a ≡ b を使い捨ての複製の上でだけ真と仮定して定理探索を回し、その仮定の下で
    /// 新たに統合された(現実には別々の)代表元の組を返す。現実の e-graph は変更しない。
    pub fn probe_conjecture(&self, a: ClassId, b: ClassId, dfs_budget: usize, sweep_rounds: usize) -> Vec<(ClassId, ClassId)> {
        if self.prover.egraph.get_rep(a) == self.prover.egraph.get_rep(b) { return Vec::new(); }
        let real_len = self.prover.egraph.entities.len();

        let mut sim_prover = ProverEngine::new(self.prover.egraph.clone());
        sim_prover.theorems = self.prover.theorems.clone();
        sim_prover.dfs_cap = dfs_budget as u64;
        let mut sim_engine = BlackboardEngine::new(sim_prover);
        sim_engine.bandit_enabled = false;

        if !sim_engine.prover.egraph.merge_entities_justified(a, b, crate::mmp_core::Justification::Trivial {
            reason: "仮説プロービング: 予想を一時的に真と仮定(discover.rs::probe_and_expand_conjectures)".to_string(),
        }) {
            return Vec::new();
        }
        sim_engine.prover.egraph.apply_congruence_closure();
        sim_engine.schedule_full_sweep();
        for _ in 0..sweep_rounds {
            if !sim_engine.run_step(dfs_budget) { break; }
        }

        // 現実にも存在する代表元どうしで、シミュレーションでだけ統合された組を拾う。
        let mut discovered = Vec::new();
        let mut seen_reps: FxHashMap<ClassId, ClassId> = FxHashMap::default();
        for i in 0..real_len {
            let id = ClassId(i);
            if self.prover.egraph.get_rep(id) != id { continue; }
            let sim_rep = sim_engine.prover.egraph.get_rep(id);
            if let Some(&other_real_id) = seen_reps.get(&sim_rep) {
                discovered.push((other_real_id, id));
            } else {
                seen_reps.insert(sim_rep, id);
            }
        }
        discovered
    }

    /// 全定理の全探索タスクを積み直す(シード済みタスクは残す)。
    pub fn schedule_full_sweep(&mut self) {
        let sfs_start = std::time::Instant::now();
        self.prover.profile.sfs_calls += 1;

        let keep: Vec<MatchTask> = self.task_queue.drain().filter(|t| t.is_seeded).collect();
        self.task_queue = BinaryHeap::from(keep);

        let theorem_count = self.prover.theorems.len();
        let priorities: Vec<i32> = if self.bandit_enabled {
            (0..theorem_count).map(|idx| self.prover.theorem_priority_bonus(idx)).collect()
        } else {
            vec![0; theorem_count]
        };
        let types_available: Vec<bool> = (0..theorem_count)
            .map(|idx| self.prover.theorem_types_available(idx))
            .collect();

        for idx in 0..theorem_count {
            if !types_available[idx] { continue; }
            self.task_queue.push(MatchTask {
                priority: priorities[idx],
                theorem_idx: idx,
                bind: self.constant_bind(),
                flip_states: FlipStates::default(),
                is_seeded: false,
            });
            self.prover.profile.sfs_tasks_created += 1;
        }
        self.prover.profile.sfs_time += sfs_start.elapsed();
    }

    /// どの定理でも最初から束縛しておく定数(直角・零角)。
    fn constant_bind(&self) -> Bind {
        let mut bind = Bind::default();
        bind.insert("Ang90".to_string(), self.prover.egraph.ang90);
        bind.insert("Ang0".to_string(), self.prover.egraph.ang0);
        bind
    }

    /// 証明された事実と同じ形のパターンを持つ定理について、そのパターンの変数を事実の図形で
    /// 固定したタスクを積む(Identical は両方の向き)。
    fn schedule_matcher_task(&mut self, fact: &Fact) {
        let base = self.constant_bind();
        for (idx, theorem) in self.prover.theorems.iter().enumerate() {
            for pat in &theorem.patterns {
                let seeds: Vec<[(&String, ClassId); 2]> = match (pat, fact) {
                    (Pattern::Identical { a, b, .. }, Fact::Identical(x, y)) => vec![[(a, *x), (b, *y)], [(a, *y), (b, *x)]],
                    (Pattern::Connected { child, parent, .. }, Fact::Connected(c, p)) => vec![[(child, *c), (parent, *p)]],
                    _ => continue,
                };
                for seed in seeds {
                    let mut bind = base.clone();
                    for (var, id) in seed {
                        bind.insert(var.clone(), id);
                    }
                    self.task_queue.push(MatchTask {
                        priority: 100,
                        theorem_idx: idx,
                        bind,
                        flip_states: FlipStates::default(),
                        is_seeded: true,
                    });
                }
            }
        }
    }

    pub fn emit(&mut self, event: Event) {
        self.event_queue.push_back(event);
    }

    /// タスクを最大 budget 個(仕事量が work_limit に達したらそこまで)処理する。
    /// 何か結論を適用できたら true。
    pub fn run_step(&mut self, budget: usize) -> bool {
        let mut applied_anything = false;
        let mut calls = 0;
        // --batch-conclusions のとき、この全探索で見つかったマッチを溜めておく(定理・束縛・向き・タスクの出どころ)。
        let mut pending: Vec<(std::rc::Rc<TheoremDef>, Bind, FlipStates, usize, bool)> = Vec::new();

        while calls < budget && self.prover.work_done() < self.work_limit {
            while let Some(event) = self.event_queue.pop_front() {
                match event {
                    Event::NodeMerged => {
                        if self.prover.egraph.apply_congruence_closure() {
                            applied_anything = true;
                            self.event_queue.push_back(Event::NodeMerged);
                        }
                    }
                    Event::FactProven(fact) => {
                        // apply_conclusions が既に facts に入れてから返すので、ここで入るのは
                        // 問題文の初期条件だけ。
                        self.prover.facts.insert(fact.clone());
                        if self.seeded_rematch_enabled {
                            self.schedule_matcher_task(&fact);
                        }
                    }
                }
            }

            let Some(mut task) = self.task_queue.pop() else { break };
            calls += 1;
            self.prover.dfs_calls = 0;
            if let Some(t) = self.prover.trace.as_mut() {
                t.current = (task.priority, task.is_seeded);
                t.task_seq += 1;
            }
            let theorem = self.prover.theorems[task.theorem_idx].clone();

            // 失敗パスは定理ごとの共有キャッシュ。dfs_match が &mut self を取るので一時的に取り出す。
            self.prover.ensure_global_failed_paths();
            self.prover.ensure_theorem_var_index();
            let var_index = self.prover.theorem_var_index[task.theorem_idx].clone();
            let mut failed_paths = std::mem::take(&mut self.prover.global_failed_paths[task.theorem_idx]);
            let all_active: u64 = if theorem.patterns.len() >= 64 { u64::MAX } else { (1u64 << theorem.patterns.len()) - 1 };
            let mut new_binds: Vec<(Bind, FlipStates)> = Vec::new();
            {
                let mut collect = |bind: &Bind, flips: &FlipStates| new_binds.push((bind.clone(), flips.clone()));
                let mut search = Search {
                    theorem: &theorem,
                    patterns: &theorem.patterns,
                    scope: 0,
                    failed_paths: &mut failed_paths,
                    on_match: &mut collect,
                    var_index: &var_index,
                    pattern_masks: &var_index.per_pattern,
                };
                let mut dep_mask: u8 = 0;
                self.prover.dfs_match(&mut search, all_active, task.bind.clone(), task.flip_states.clone(), &mut dep_mask);
            }
            self.prover.global_failed_paths[task.theorem_idx] = failed_paths;

            let dfs_calls_used = self.prover.dfs_calls;
            if task.is_seeded {
                self.prover.profile.seeded_pops += 1;
                self.prover.profile.seeded_dfs_calls += dfs_calls_used;
            } else {
                self.prover.profile.unseeded_pops += 1;
                self.prover.profile.unseeded_dfs_calls += dfs_calls_used;
            }

            let (task_theorem_idx, task_is_seeded) = (task.theorem_idx, task.is_seeded);
            // 上限に達したタスクは後回しにして再挑戦する。ただし他に待ちタスクが無いときは、
            // 何も変わらないまま同じ探索を繰り返すだけなので諦める。
            if dfs_calls_used >= self.prover.dfs_cap && !self.task_queue.is_empty() {
                task.priority -= 50;
                if task.priority >= -200 {
                    self.task_queue.push(task);
                }
            }

            if self.batch_conclusions {
                let matched = !new_binds.is_empty();
                for (bind, flips) in new_binds {
                    pending.push((theorem.clone(), bind, flips, task_theorem_idx, task_is_seeded));
                }
                // マッチが無かったタスクはここで記録する(マッチしたタスクは適用してから記録する)。
                if !task_is_seeded && !matched {
                    self.prover.record_theorem_attempt(task_theorem_idx, false, dfs_calls_used);
                }
                continue;
            }

            let mut task_succeeded = false;
            for (mut bind, flips) in new_binds {
                if self.prover.is_already_proven(&theorem.conclusions, &bind, &flips) { continue; }
                if !self.prover.execute_constructions(&theorem.constructions, &mut bind) { continue; }
                // 作図しただけで合同閉包により既に成り立った場合。
                if self.prover.is_already_proven(&theorem.conclusions, &bind, &flips) { continue; }

                println!("  🎯 [リーチ通知] 定理「{}」の前提条件がすべて満たされました！", theorem.name);
                for (var_name, class_id) in &bind {
                    if var_name.starts_with("__") { continue; }
                    let entity_name = &self.prover.egraph.entities[self.prover.egraph.get_rep(*class_id).0].name;
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

            if !task_is_seeded {
                self.prover.record_theorem_attempt(task_theorem_idx, task_succeeded, dfs_calls_used);
            }
        }

        // 溜めた結論をまとめて適用する。ここまでは全タスクが同じ図を見ている。
        for (theorem, mut bind, flips, theorem_idx, is_seeded) in pending {
            let mut succeeded = false;
            if !self.prover.is_already_proven(&theorem.conclusions, &bind, &flips)
                && self.prover.execute_constructions(&theorem.constructions, &mut bind)
                && !self.prover.is_already_proven(&theorem.conclusions, &bind, &flips)
            {
                println!("  🎯 [リーチ通知] 定理「{}」の前提条件がすべて満たされました！", theorem.name);
                for (var_name, class_id) in &bind {
                    if var_name.starts_with("__") { continue; }
                    let entity_name = &self.prover.egraph.entities[self.prover.egraph.get_rep(*class_id).0].name;
                    println!("      - 割り当て: {} = {}", var_name, entity_name);
                }
                let (applied, generated_facts) = self.prover.apply_conclusions(&theorem, &bind, &flips);
                if applied {
                    applied_anything = true;
                    succeeded = true;
                    self.emit(Event::NodeMerged);
                    for f in generated_facts { self.emit(Event::FactProven(f)); }
                }
            }
            if !is_seeded {
                self.prover.record_theorem_attempt(theorem_idx, succeeded, 0);
            }
        }
        applied_anything
    }

    /// 補助作図を1つ図に足す。出どころを刻み(--origins 用)、importance が与えられれば
    /// 重要度を下げて推論の主軸がぶれないようにする。
    fn add_aux(&mut self, name: String, def: Definition, ty: EntityType, origin: EntityOrigin, importance: Option<f64>) -> ClassId {
        let eg = &mut self.prover.egraph;
        let prev = eg.set_origin(origin);
        let id = eg.create_entity(name, def.clone(), ty);
        if let Some(imp) = importance {
            eg.entities[id.0].base_importance = imp;
        }
        eg.apply_trivial_relations(id, &def);
        eg.set_origin(prev);
        id
    }

    /// 作図の直後に既存の図形と合流させてから、全定理を試し直す。
    fn settle_and_resweep(&mut self) {
        self.prover.egraph.apply_congruence_closure();
        self.schedule_full_sweep();
    }

    /// 2本以上の直線が通る点について、その直線の組の有向角を作る。
    pub fn resolve_angle_demands(&mut self) -> bool {
        self.prover.egraph.apply_congruence_closure();

        let mut angle_pairs_to_create = Vec::new();
        for i in 0..self.prover.egraph.entities.len() {
            let pt_id = ClassId(i);
            if self.prover.egraph.get_rep(pt_id) != pt_id { continue; }
            if self.prover.egraph.entities[i].entity_type != EntityType::Point { continue; }

            // L∞ は普通の直線として数えない(方向の点は必ず L∞ に乗るので、退化した角ができる)。
            let mut lines_on_pt = Vec::new();
            for comp in &self.prover.egraph.entities[i].components {
                for &sub_id in &comp.subobjects {
                    let sub_rep = self.prover.egraph.get_rep(sub_id);
                    if sub_rep == self.prover.egraph.line_infinity { continue; }
                    if self.prover.egraph.entities[sub_rep.0].entity_type == EntityType::Line {
                        lines_on_pt.push(sub_rep);
                    }
                }
            }
            lines_on_pt.sort_unstable_by_key(|id| id.0);
            lines_on_pt.dedup();

            for l1 in 0..lines_on_pt.len() {
                for l2 in (l1 + 1)..lines_on_pt.len() {
                    let d1 = self.get_or_create_direction(lines_on_pt[l1]);
                    let d2 = self.get_or_create_direction(lines_on_pt[l2]);
                    let (r_d1, r_d2) = (self.prover.egraph.get_rep(d1), self.prover.egraph.get_rep(d2));
                    // 平行(同じ方向)な組は零角なので作らない。フリップで向きは吸収されるので片方だけ作る。
                    if r_d1 == r_d2 { continue; }
                    angle_pairs_to_create.push(if r_d1.0 < r_d2.0 { (r_d1, r_d2) } else { (r_d2, r_d1) });
                }
            }
        }

        angle_pairs_to_create.sort_unstable_by_key(|(d1, d2)| (d1.0, d2.0));
        angle_pairs_to_create.dedup();

        let mut applied = false;
        for (d1, d2) in angle_pairs_to_create {
            let def = Definition::AnglePair(d1, d2);
            if self.prover.egraph.memo.contains_key(&def) { continue; }
            let name = format!("AnglePair_{}_{}_(Auto)", self.prover.egraph.entities[d1.0].name, self.prover.egraph.entities[d2.0].name);
            self.add_aux(name, def, EntityType::Scalar, EntityOrigin::AngleDemand, Some(0.2));
            applied = true;
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
        self.add_aux(name, def, EntityType::Point, EntityOrigin::AngleDemand, None)
    }

    /// 定理のマッチが「2点を結ぶ直線」を欲しがって空振りした組に、補助線を引く(1回に3本まで)。
    ///
    /// 並べ方は需要の回数に、2点の「相性」(直線の次数が 次数(A)+次数(B) より小さい分)を
    /// 加点したもの。単純な組に見えて隠れた関係がある組を先に試す。
    pub fn resolve_demands(&mut self) -> bool {
        if self.prover.construction_demands.is_empty() { return false; }

        const AFFINITY_MAX_D: usize = 4;
        const AFFINITY_WEIGHT: f64 = 2.0;
        const LINES_PER_STALL: usize = 3;
        type Demand = ((ClassId, ClassId), f64, Option<(usize, usize, usize)>);
        let priority = |&(_, score, aff): &Demand| -> f64 {
            let bonus = aff.map_or(0.0, |(da, db, dab)| (da as f64 + db as f64 - dab as f64).max(0.0));
            score + AFFINITY_WEIGHT * bonus
        };
        let mut demands: Vec<Demand> = self.prover.construction_demands.iter()
            .map(|(&(p1, p2), &score)| ((p1, p2), score, self.prover.egraph.measure_line_affinity(p1, p2, AFFINITY_MAX_D)))
            .collect();
        demands.sort_by(|a, b| {
            priority(b).partial_cmp(&priority(a)).unwrap_or(std::cmp::Ordering::Equal)
                .then_with(|| (a.0).0.0.cmp(&(b.0).0.0))
                .then_with(|| (a.0).1.0.cmp(&(b.0).1.0))
        });

        let mut count = 0;
        for ((p1, p2), score, affinity) in demands {
            let def = Definition::new_line(p1, p2);
            if self.prover.egraph.memo.contains_key(&def) { continue; }
            let name = format!("Line_{}_{}_(Demand)", self.prover.egraph.entities[p1.0].name, self.prover.egraph.entities[p2.0].name);
            match affinity {
                Some((da, db, dab)) if da + db > dab => {
                    println!("  💡 [オンデマンド作図] 要請により {} を生成 (需要: {:.1}, 相性◎: 次数{}+{}→{})", name, score, da, db, dab);
                }
                _ => println!("  💡 [オンデマンド作図] 要請により {} を生成 (需要: {:.1})", name, score),
            }
            self.add_aux(name, def, EntityType::Line, EntityOrigin::LineDemand, Some(0.5));
            count += 1;
            if count >= LINES_PER_STALL { break; }
        }

        self.prover.construction_demands.clear();
        if count > 0 { self.settle_and_resweep(); }
        count > 0
    }

    /// 目標に現れる点のうち、まだ直線で結ばれていない組に補助線を引く(1回に3本まで)。
    ///
    /// 他の需要はどれも「定理のマッチが欲しがった」ところからしか出ないので、どの定理からも
    /// 束縛されない目標の点には需要が生まれない。その穴を埋める最後の手。
    pub fn resolve_target_demands(&mut self, target: &Option<(String, Vec<ClassId>)>) -> bool {
        let Some((_, target_args)) = target else { return false; };

        let mut points: Vec<ClassId> = target_args.iter()
            .map(|&id| self.prover.egraph.get_rep(id))
            .filter(|&id| self.prover.egraph.entities[id.0].entity_type == EntityType::Point)
            .collect();
        points.sort_unstable_by_key(|id| id.0);
        points.dedup();

        let mut count = 0;
        'outer: for i in 0..points.len() {
            for j in (i + 1)..points.len() {
                let (p1, p2) = (points[i], points[j]);
                let def = Definition::new_line(p1, p2);
                if self.prover.egraph.memo.contains_key(&def) { continue; }
                // 既に2点を通る直線があるのに別の直線を作ると、点が互いに矛盾しうる接続を持つと
                // 見なされて数値サンプリングが壊れる。
                if self.prover.egraph.find_common_line(&[p1, p2]).is_some() { continue; }
                let name = format!("Line_{}_{}_(TargetDemand)", self.prover.egraph.entities[p1.0].name, self.prover.egraph.entities[p2.0].name);
                println!("  💡 [目標駆動オンデマンド作図] 証明目標に現れる点を結ぶ {} を生成", name);
                self.add_aux(name, def, EntityType::Line, EntityOrigin::TargetDemand, Some(0.5));
                count += 1;
                if count >= 3 { break 'outer; }
            }
        }

        if count > 0 { self.settle_and_resweep(); }
        count > 0
    }

    /// 目標が「同じ直線上の2点 P, Q が一致すること」のとき、その直線上の他の3点 X, Y, Z で
    /// 複比 (X,Y;Z,P) と (X,Y;Z,Q) を作る。両者が等しいと示せれば、合同閉包の
    /// 複比の一意性(propagate_cross_ratio_uniqueness)が P ≡ Q を結論する。
    pub fn resolve_cross_ratio_demands(&mut self, target: &Option<(String, Vec<ClassId>)>) -> bool {
        let Some((kind, args)) = target else { return false; };
        if kind != "Identical" || args.len() < 2 { return false; }
        let (p, q) = (self.prover.egraph.get_rep(args[0]), self.prover.egraph.get_rep(args[1]));
        if p == q { return false; }
        let is_point = |eg: &EGraph, id: ClassId| eg.entities[id.0].entity_type == EntityType::Point;
        if !is_point(&self.prover.egraph, p) || !is_point(&self.prover.egraph, q) { return false; }

        let line = match self.prover.egraph.find_common_line(&[p, q]) { Some(l) => l, None => return false };
        if line == self.prover.egraph.line_infinity { return false; }
        let mut others: Vec<ClassId> = self.prover.egraph.entities[line.0].components.first()
            .map(|c| c.subobjects.clone()).unwrap_or_default()
            .into_iter()
            .map(|x| self.prover.egraph.get_rep(x))
            .filter(|&x| is_point(&self.prover.egraph, x) && x != p && x != q)
            .collect();
        others.sort_unstable_by_key(|id| id.0);
        others.dedup();
        if others.len() < 3 { return false; }
        // 図の要になっている(熱い)点から選ぶ。
        others.sort_by(|&a, &b| self.prover.egraph.entities[b.0].heat_with_degree()
            .partial_cmp(&self.prover.egraph.entities[a.0].heat_with_degree())
            .unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| a.0.cmp(&b.0)));
        let (x, y, z) = (others[0], others[1], others[2]);

        let mut applied = false;
        for (fourth, label) in [(p, "P"), (q, "Q")] {
            let def = self.prover.egraph.normalize_definition(&Definition::CrossRatio(x, y, z, fourth));
            if self.prover.egraph.memo.contains_key(&def) { continue; }
            let name = format!("CR_{}_(TargetDemand)", label);
            println!("  💡 [目標駆動オンデマンド作図] 複比の一意性に持ち込むため {} を生成", name);
            self.add_aux(name, def, EntityType::Scalar, EntityOrigin::TargetDemand, Some(0.5));
            applied = true;
        }
        if applied { self.settle_and_resweep(); }
        applied
    }

    /// 交点を作る(1回に2点まで)。候補は次の2つ:
    ///   (a) 定理のマッチが「2直線の交点」を欲しがって空振りした組(今はそういうパターンを
    ///       持つ定理が無いので、実際には出てこない)
    ///   (b) 既存の垂線と、その垂線の基準の直線の交点(=垂線の足)がまだ無い組
    /// 次数(図形の複雑さ)の低い順に並べ、高すぎるもの(DEGREE_CAP 超)は作らない。
    pub fn resolve_point_demands(&mut self) -> bool {
        for i in 0..self.prover.egraph.entities.len() {
            let id = ClassId(i);
            if self.prover.egraph.get_rep(id) != id { continue; }
            if self.prover.egraph.entities[i].entity_type != EntityType::Line { continue; }
            let bases: Vec<ClassId> = self.prover.egraph.entities[i].components.iter()
                .flat_map(|c| c.definitions.iter())
                .filter_map(|d| if let Definition::PerpendicularLine(base, _) = d { Some(*base) } else { None })
                .collect();
            for base in bases {
                let base_rep = self.prover.egraph.get_rep(base);
                if base_rep == id { continue; }
                let key = if id.0 < base_rep.0 { (id, base_rep) } else { (base_rep, id) };
                self.prover.point_construction_demands.entry(key).or_insert(0.0);
            }
        }

        if self.prover.point_construction_demands.is_empty() { return false; }

        const DEGREE_CAP: usize = 4;
        const MAX_D: usize = 6;
        // 一度に全部作ると探索が拡散して届かなくなる。必要なら次の行き詰まりでまた候補に挙がる。
        const POINTS_PER_STALL: usize = 2;
        let mut demands: Vec<((ClassId, ClassId), f64, Option<usize>)> = self.prover.point_construction_demands.iter()
            .map(|(&(l1, l2), &score)| ((l1, l2), score, self.prover.egraph.measure_intersection_degree_candidate(l1, l2, MAX_D)))
            .filter(|&(_, _, deg)| deg.is_none_or(|d| d <= DEGREE_CAP))
            .collect();
        demands.sort_by(|a, b| {
            let da = a.2.unwrap_or(usize::MAX);
            let db = b.2.unwrap_or(usize::MAX);
            da.cmp(&db)
                .then_with(|| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal))
                .then_with(|| (a.0).0.0.cmp(&(b.0).0.0))
                .then_with(|| (a.0).1.0.cmp(&(b.0).1.0))
        });

        let mut count = 0;
        for ((l1, l2), score, deg) in demands {
            // 需要を記録してからマージが進んでいるかもしれないので、今の代表元に直して照合する。
            let def = self.prover.egraph.normalize_definition(&Definition::Intersection(l1, l2));
            let (l1, l2) = match def { Definition::Intersection(a, b) => (a, b), _ => (l1, l2) };
            if l1 == l2 { continue; }
            if self.prover.egraph.memo.contains_key(&def) { continue; }
            let name = format!("Pt_{}_{}_(Demand)",
                self.prover.egraph.entities[l1.0].name, self.prover.egraph.entities[l2.0].name);
            let deg_str = deg.map(|d| d.to_string()).unwrap_or_else(|| "不明".to_string());
            println!("  💡 [オンデマンド作図] 要請により {} (交点、次数{})を生成 (需要: {:.1})", name, deg_str, score);
            self.add_aux(name, def, EntityType::Point, EntityOrigin::PointDemand, Some(0.5));
            count += 1;
            if count >= POINTS_PER_STALL { break; }
        }

        self.prover.point_construction_demands.clear();
        if count > 0 { self.settle_and_resweep(); }
        count > 0
    }

    /// 直線と円・円と円で「一方の交点は図にあるのに、もう一方が無い」組の、もう一方の交点を
    /// 作る(1回に2点まで、点と2曲線の熱の合計の降順)。
    ///
    /// 連鎖と氾濫を防ぐため、この手で作ったもの(とそれを材料にしたもの)だけでできた同値類は
    /// 起点にも曲線にも使わず、曲線は問題文にあるものか、補助線・交点の需要で引いたものに限る。
    pub fn resolve_second_intersection_demands(&mut self) -> bool {
        let eg = &self.prover.egraph;
        let linf = eg.line_infinity;
        let finite_points_on = |id: ClassId| -> HashSet<ClassId> {
            eg.entities[id.0].components.iter()
                .flat_map(|c| c.subobjects.iter())
                .map(|&s| eg.get_rep(s))
                .filter(|&s| eg.entities[s.0].entity_type == EntityType::Point && !eg.is_connected(s, linf))
                .collect()
        };
        let is_circle = |id: ClassId| eg.is_connected(id, eg.circ_i) && eg.is_connected(id, eg.circ_j);

        let mut tainted = vec![false; eg.entities.len()];
        for (i, e) in eg.entities.iter().enumerate() {
            tainted[i] = e.origin == EntityOrigin::SecondDemand
                || e.original_definition.get_parents().iter().any(|q| q.0 < i && tainted[q.0]);
        }
        let clean: HashSet<ClassId> = (0..eg.entities.len())
            .filter(|&i| !tainted[i]).map(|i| eg.get_rep(ClassId(i))).collect();
        let established: HashSet<ClassId> = eg.entities.iter().enumerate()
            .filter(|(_, e)| matches!(e.origin, EntityOrigin::Given | EntityOrigin::LineDemand | EntityOrigin::PointDemand))
            .map(|(i, _)| eg.get_rep(ClassId(i))).collect();

        let mut cands: Vec<(Definition, f64)> = Vec::new();
        for i in 0..eg.entities.len() {
            let p = ClassId(i);
            if eg.get_rep(p) != p || eg.entities[i].entity_type != EntityType::Point { continue; }
            if !eg.entities[i].is_active() || eg.is_connected(p, linf) || !clean.contains(&p) { continue; }
            let mut lines = Vec::new();
            let mut circles = Vec::new();
            for &s in eg.entities[i].components.iter().flat_map(|c| c.subobjects.iter()) {
                let r = eg.get_rep(s);
                if !clean.contains(&r) || !established.contains(&r) { continue; }
                match eg.entities[r.0].entity_type {
                    EntityType::Line if r != linf => lines.push(r),
                    EntityType::Conic if is_circle(r) => circles.push(r),
                    _ => {}
                }
            }
            lines.sort_unstable_by_key(|x| x.0); lines.dedup();
            circles.sort_unstable_by_key(|x| x.0); circles.dedup();
            if circles.is_empty() { continue; }
            let heat_p = eg.entities[i].heat();

            for &c in &circles {
                let on_c = finite_points_on(c);
                for &l in &lines {
                    let tangent = eg.entities[l.0].components.iter().flat_map(|k| k.definitions.iter())
                        .any(|d| matches!(d, Definition::TangentLine(..)));
                    if tangent { continue; }
                    if finite_points_on(l).iter().any(|q| *q != p && on_c.contains(q)) { continue; }
                    let def = eg.normalize_definition(&Definition::SecondIntersectionOfLineAndConic(p, l, c));
                    if eg.memo.contains_key(&def) { continue; }
                    cands.push((def, heat_p + eg.entities[l.0].heat() + eg.entities[c.0].heat()));
                }
            }
            for a in 0..circles.len() {
                for b in (a + 1)..circles.len() {
                    let (c1, c2) = (circles[a], circles[b]);
                    let on2 = finite_points_on(c2);
                    if finite_points_on(c1).iter().any(|q| *q != p && on2.contains(q)) { continue; }
                    let def = eg.normalize_definition(&Definition::SecondIntersectionOfCircles(p, c1, c2));
                    if eg.memo.contains_key(&def) { continue; }
                    cands.push((def, heat_p + eg.entities[c1.0].heat() + eg.entities[c2.0].heat()));
                }
            }
        }
        if cands.is_empty() { return false; }
        cands.sort_by(|x, y| y.1.partial_cmp(&x.1).unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| format!("{:?}", x.0).cmp(&format!("{:?}", y.0))));

        let mut applied = false;
        for (def, heat) in cands.into_iter().take(2) {
            if self.prover.egraph.memo.contains_key(&def) { continue; }
            let name = {
                let eg = &self.prover.egraph;
                let n = |id: &ClassId| eg.entities[id.0].name.clone();
                match &def {
                    Definition::SecondIntersectionOfLineAndConic(p, l, c) => format!("Second_{}_{}_{}_(Demand)", n(p), n(l), n(c)),
                    Definition::SecondIntersectionOfCircles(p, a, b) => format!("Second_{}_{}_{}_(Demand)", n(p), n(a), n(b)),
                    _ => continue,
                }
            };
            println!("  💡 [オンデマンド作図] 要請により {} (もう一方の交点)を生成 (熱: {:.1})", name, heat);
            self.add_aux(name, def, EntityType::Point, EntityOrigin::SecondDemand, Some(0.5));
            applied = true;
        }
        if applied { self.settle_and_resweep(); }
        applied
    }

    /// 図に既に中点があるとき、その端点どうしのまだ取られていない中点を補う(1回に2点まで、
    /// 両端の熱の合計の降順)。中点が1つも無い図では何もしない。
    pub fn resolve_midpoint_demands(&mut self) -> bool {
        let eg = &self.prover.egraph;
        let mut anchors: Vec<ClassId> = Vec::new();
        let mut seen = HashSet::new();
        for i in 0..eg.entities.len() {
            let id = ClassId(i);
            if eg.get_rep(id) != id { continue; }
            for c in &eg.entities[i].components {
                for d in &c.definitions {
                    if let Definition::Midpoint(a, b) = d {
                        for p in [eg.get_rep(*a), eg.get_rep(*b)] {
                            if seen.insert(p) { anchors.push(p); }
                        }
                    }
                }
            }
        }
        if anchors.len() < 3 { return false; }
        anchors.sort_unstable_by_key(|id| id.0);

        let mut candidates: Vec<(ClassId, ClassId, f64)> = Vec::new();
        for i in 0..anchors.len() {
            for j in (i + 1)..anchors.len() {
                let (a, b) = (anchors[i], anchors[j]);
                let def = eg.normalize_definition(&Definition::Midpoint(a, b));
                if eg.memo.contains_key(&def) { continue; }
                candidates.push((a, b, eg.entities[a.0].heat() + eg.entities[b.0].heat()));
            }
        }
        if candidates.is_empty() { return false; }
        candidates.sort_by(|x, y| y.2.partial_cmp(&x.2).unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| x.0.0.cmp(&y.0.0)).then_with(|| x.1.0.cmp(&y.1.0)));

        let mut applied = false;
        for (a, b, heat) in candidates.into_iter().take(2) {
            let def = self.prover.egraph.normalize_definition(&Definition::Midpoint(a, b));
            if self.prover.egraph.memo.contains_key(&def) { continue; }
            let name = format!("Mid_{}_{}_(Demand)",
                self.prover.egraph.entities[a.0].name, self.prover.egraph.entities[b.0].name);
            println!("  💡 [オンデマンド作図] 要請により {} (中点)を生成 (需要: {:.1})", name, heat);
            self.add_aux(name, def, EntityType::Point, EntityOrigin::MidDemand, Some(0.5));
            applied = true;
        }
        if applied { self.settle_and_resweep(); }
        applied
    }
}

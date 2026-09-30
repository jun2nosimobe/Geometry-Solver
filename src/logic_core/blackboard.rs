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
    /// 🌟 決定的な手が全部尽きたとき、最後に熱い点どうしの中点と熱い直線どうしの交点を足すか(--generic-aux)。
    pub generic_aux: bool,
    /// 手が全部尽きたとき、汎用の補助作図の前に、候補を座標で試作して新しい一致を生むものを作る(numeric_aux.rs)。
    pub numeric_aux: bool,
    /// 数値で選ぶ補助作図を、最後の手ではなく行き詰まりのたびに(需要の補助線・交点の直後に)試す。
    pub numeric_aux_early: bool,
}

impl RecoveryOptions {
    /// solve の既定(中点の需要なし・汎用と数値で選ぶ補助作図あり・2回の行き詰まりごとに cap の拡大)。
    /// serve・discover の証明試行もここから作る(中点の需要だけ足す)。
    pub fn standard() -> Self {
        RecoveryOptions { midpoint_demands: false, skip: Vec::new(), widen_first: false, widen_first_ceiling: 40, widen_every: 2,
            generic_aux: true, numeric_aux: true, numeric_aux_early: false }
    }

    fn skipped(&self, name: &str) -> bool {
        self.skip.iter().any(|s| s == name)
    }
}

/// 探索の前の数値の準備(BlackboardEngine::prepare)。既定は全て使う。
#[derive(Clone, Debug)]
pub struct SearchSetup {
    /// 前提が乱数座標で成り立つなら固定座標を置く(--no-fixed-coords で外す)。
    pub fixed_coords: bool,
    /// マージ前の数値チェック(--no-merge-checks で外す)。
    pub merge_checks: bool,
    /// 定理の「図の上でも相異なる」の数値判定(--no-nondegeneracy で外す)。
    pub nondegeneracy: bool,
    /// 定理の結論の検算(--no-conclusion-check で外す。前提が成り立たない図では効かない)。
    pub conclusion_check: bool,
}

impl Default for SearchSetup {
    fn default() -> Self { SearchSetup { fixed_coords: true, merge_checks: true, nondegeneracy: true, conclusion_check: true } }
}

/// BlackboardEngine::prepare の結果。
#[derive(Clone, Copy, Debug)]
pub struct Prepared {
    /// 前提が乱数座標で成り立つか(成り立たない図では、数値の検算は誤警報になりうるので結論の検算を切る)。
    pub hypotheses_hold: bool,
    /// 固定座標を置いたか(AR と数値で選ぶ補助作図はこれが要る)。
    pub fixed: bool,
    /// 乱数の座標では前提が成り立たず、代数的な置き方(平方根などを取る、検算専用)で置いたか。
    pub algebraic: bool,
}

/// BlackboardEngine::recover が打った手。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Recovered {
    /// 需要駆動の作図で図を伸ばした。
    Construction,
    /// 候補capを広げて全探索をやり直す(値は広げた後の cap)。
    WidenedCap(usize),
    /// 代数的な追跡(AR)が併合した(作図の手は尽きていても進んだ)。
    Algebra,
    /// 決定的な手が尽きた。
    Exhausted,
}

pub struct BlackboardEngine {
    pub prover: ProverEngine,
    pub task_queue: BinaryHeap<MatchTask>,
    pub event_queue: VecDeque<Event>,
    /// UCB1 バンディットで全探索タスクの優先度を付けるか(既定は無効: 実測で仕事量が20%増えた)。
    pub bandit_enabled: bool,
    /// 使われなかった作図の刈り込み(リスタート、b48)。有効な実体が前回の刈り込みの後の数のこの倍を超えたら、手が止まった
    /// ときに刈り込む。None なら刈り込まない。
    pub prune_growth: Option<f64>,
    /// 前回の刈り込みの後の有効な実体の数(0 ならまだ基準を取っていない)。
    pub prune_base: usize,
    /// 直近の手詰まりの時刻(EGraph::clock)。刈り込むのは、この2回前より前に作った(2回の手詰まりを経ても使われなかった)作図だけ。
    pub stall_clocks: std::collections::VecDeque<u64>,
    pub pruned_total: u64,
    /// 問題文の作図も刈り込むときに必ず残す実体(目標の実体)。空なら問題文の作図は刈り込まない。
    pub prune_roots: Vec<ClassId>,
    /// 証明された事実で変数を固定したタスクを積むか(既定は無効: 積む量が多すぎて全体が悪化する)。
    pub seeded_rematch_enabled: bool,
    /// 前回 cap を広げてからの行き詰まりの回数(widen_every の判定に使う)。
    pub stalls_since_widen: usize,
    /// resolve_generic_aux が今までに足した作図の数(上限 GENERIC_AUX_TOTAL)。
    pub generic_aux_added: usize,
    /// resolve_numeric_aux が今までに足した作図の数。
    pub numeric_aux_added: usize,
    /// 代数的な追跡(ar.rs)で併合した数と、数値で偽と分かって見送った数。
    pub ar_merged: u64,
    pub ar_rejected: u64,
    /// 代数的な追跡の行演算の数(仕事量に数えている)と、追跡の回数。
    pub ar_ops: u64,
    pub ar_rounds: u64,
    /// 代数的な追跡が検出した相似な三角形の組の数。
    pub ar_similar: u64,
    /// 代数的な追跡で、前回の規則の結果を使い回した回数と、その状態。
    pub ar_reused: u64,
    pub(crate) ar_cache: Option<super::ar::ArCache>,
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
            prune_growth: None,
            prune_base: 0,
            stall_clocks: std::collections::VecDeque::new(),
            pruned_total: 0,
            prune_roots: Vec::new(),
            seeded_rematch_enabled: false,
            stalls_since_widen: 0,
            generic_aux_added: 0,
            numeric_aux_added: 0,
            ar_merged: 0,
            ar_rejected: 0,
            ar_ops: 0,
            ar_rounds: 0,
            ar_similar: 0,
            ar_reused: 0,
            ar_cache: None,
            work_limit: u64::MAX,
        }
    }

    /// 前提を入れ終えた後、探索の前に一度だけ呼ぶ: 前提の接続を凍結し、前提が乱数座標で成り立つなら固定座標を置いて、
    /// 数値の検査の設定を決める。solve・serve・discover の証明試行で共通。
    pub fn prepare(&mut self, setup: &SearchSetup) -> Prepared {
        // 前提が座標への制約(「OP = OA」など)だと乱数座標はそれを満たさず、監査の「偽」や結論の数値チェックは誤警報になりうる。
        self.prover.egraph.freeze_premise_incidences();
        let mut hypotheses_hold = self.prover.egraph.hypotheses_hold_numerically();
        // 座標はここで固定して以後の検算に使う(マージに依存せず、構造が変わっても捨てない)。
        let mut fixed = hypotheses_hold && setup.fixed_coords && self.prover.egraph.fix_coordinates();
        // 乱数の座標では前提が成り立たない図(直線と円の両方に乗る点・「OP = OA」のような方程式の前提)は、前提を方程式として
        // 解いて置く(検算専用。次数の評価には使わない)。
        let mut algebraic = false;
        if !hypotheses_hold && setup.fixed_coords
            && let Some(samples) = self.prover.egraph.algebraic_premise_samples()
            && self.prover.egraph.fix_coordinates_from(samples) {
            fixed = true;
            hypotheses_hold = true;
            algebraic = true;
        }
        self.prover.egraph.merge_checks = setup.merge_checks;
        self.prover.numeric_distinct = setup.nondegeneracy;
        self.prover.guard_conclusions = setup.merge_checks && setup.conclusion_check && hypotheses_hold;
        Prepared { hypotheses_hold, fixed, algebraic }
    }

    /// 手が止まったときの一手: 代数的な追跡(ar が真なら)と決定的な手(recover)を同じ回に行う(AR だけで次の回に
    /// 進むと、補助作図が要る問題で全定理の試し直しが余分に挟まる。来歴 #82)。solve・serve・discover で共通。
    pub fn on_stall(&mut self, open_targets: &[(String, Vec<ClassId>)], rotate: &mut usize, opts: &RecoveryOptions, ar: bool) -> Recovered {
        if let Some(g) = self.prune_growth {
            self.stall_clocks.push_back(self.prover.egraph.clock);
            if self.stall_clocks.len() > 3 { self.stall_clocks.pop_front(); }
            let active = self.active_count();
            if self.prune_base == 0 { self.prune_base = active; }
            else if active as f64 > self.prune_base as f64 * g && active >= self.prune_base + 20 {
                let k = self.prune_unused();
                self.prune_base = self.active_count();
                println!("  🧹 [刈り込み] 使われなかった作図 {} 件を無効にしました(有効な実体 {} → {})", k, active, self.prune_base);
            }
        }
        let merged = ar && self.run_ar();
        // AR で予算を使い切ったら、回復の手は打たない(次の回の予算の確認で止まる)。
        if self.work_limit > 0 && self.prover.work_done() >= self.work_limit {
            return if merged { Recovered::Algebra } else { Recovered::Exhausted };
        }
        match self.recover(open_targets, rotate, opts) {
            Recovered::Exhausted if merged => Recovered::Algebra,
            r => r,
        }
    }

    fn active_count(&self) -> usize {
        let eg = &self.prover.egraph;
        (0..eg.entities.len()).filter(|&i| eg.get_rep(ClassId(i)).0 == i && eg.entities[i].is_active()).count()
    }

    /// 使われなかった作図を無効にする(リスタート、b48)。問題文の図形と、使われた図形(ほかの図形と合流した・定義から
    /// 従う以外の接続を持つ)を根にして、その作図の親を辿った集合に入らない実体を無効にする。消さないのでマージの履歴や
    /// 証明は壊れず、同じ作図がもう一度求められたら有効に戻る(EGraph::revive)。無効にした数を返す。
    pub fn prune_unused(&mut self) -> usize {
        use crate::mmp_core::{EntityOrigin, LinkKind};
        let eg = &mut self.prover.egraph;
        let n = eg.entities.len();
        let mut used = vec![false; n];
        for (&(a, b), &(_, kind)) in &eg.incidence_time {
            if kind == LinkKind::Bare { used[eg.get_rep(a).0] = true; used[eg.get_rep(b).0] = true; }
        }
        for i in 0..n {
            let rep = eg.get_rep(ClassId(i)).0;
            let merged = rep != i || eg.entities[i].components.first().map_or(0, |c| c.definitions.len()) > 1;
            let given = eg.entities[i].origin == EntityOrigin::Given;
            // 問題文の作図も刈り込むとき(prune_roots が空でない)は、自由点・定数だけを無条件に残す。
            let keep_given = given && (self.prune_roots.is_empty()
                || matches!(eg.entities[i].original_definition, Definition::FreePoint | Definition::GivenPoint | Definition::ConstantHomogeneous(..)));
            if keep_given || merged { used[i] = true; used[rep] = true; }
        }
        for &r in &self.prune_roots { used[r.0] = true; used[eg.get_rep(r).0] = true; }
        if let Some(pairs) = &eg.premise_incidences { for &(p, c) in pairs { used[eg.get_rep(p).0] = true; used[eg.get_rep(c).0] = true; } }
        for s in [eg.line_infinity, eg.circ_i, eg.circ_j, eg.ang0, eg.ang90] { used[eg.get_rep(s).0] = true; }
        // 使われた図形の作図の親(同値類の全ての定義の親)を辿る。
        let mut needed = vec![false; n];
        let mut stack: Vec<usize> = (0..n).filter(|&i| used[i]).collect();
        while let Some(i) = stack.pop() {
            if needed[i] { continue; }
            needed[i] = true;
            let rep = eg.get_rep(ClassId(i));
            let mut parents = eg.entities[i].original_definition.get_parents();
            if let Some(c) = eg.entities[rep.0].components.first() { for d in &c.definitions { parents.extend(d.get_parents()); } }
            for p in parents {
                for q in [p.0, eg.get_rep(p).0] { if !needed[q] { stack.push(q); } }
            }
        }
        // 刈り込むのは、使われなかった補助作図(需要駆動・MCTS・調和共役など)と、それに依存して作られた使われなかった実体だけ。
        // 定理の照合がその場で作る実体(角の組・方向など)は、問題文の図形だけから作られたものなら次の総当たりですぐ作り直される
        // ので刈り込まない(刈り込むと作り直しと刈り込みを繰り返す)。実体は親より後に作られるので、番号の順に1回で決まる。
        let given_too = !self.prune_roots.is_empty();
        let aux = |o: EntityOrigin| match o {
            EntityOrigin::Given => given_too,
            EntityOrigin::DefinedBy | EntityOrigin::Construct => false,
            _ => true,
        };
        let mut tainted = vec![false; n];
        for i in 0..n {
            if needed[i] { continue; }
            let e = &eg.entities[i];
            tainted[i] = aux(e.origin) || e.original_definition.get_parents().iter().any(|p| tainted[p.0] || tainted[eg.get_rep(*p).0]);
        }
        // 2回前の手詰まりより後に作ったものは、まだ使われる機会が無かったかもしれないので残す。
        let cutoff = if self.stall_clocks.len() >= 3 { self.stall_clocks[0] } else { 0 };
        let mut count = 0;
        for i in 0..n {
            let id = ClassId(i);
            if eg.get_rep(id) != id || !tainted[i] || !eg.entities[i].is_active() { continue; }
            if eg.entity_time.get(i).is_none_or(|&t| t >= cutoff) { continue; }
            eg.prune_entity(id);
            count += 1;
        }
        self.pruned_total += count as u64;
        count
    }

    /// 行き詰まったときの決定的な手を順に打つ(on_stall から呼ぶ)。
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
        if !recovered && opts.numeric_aux_early
            && self.resolve_numeric_aux(super::numeric_aux::EARLY_MIN_SCORE, super::numeric_aux::EARLY_PER_STALL) { recovered = true; }
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
        // 汎用の補助作図と、数値で選ぶ補助作図を同じ回に両方試す(数値の側が汎用の側を押しのけると、汎用の補助作図に頼る
        // 解の道筋が変わる。汎用の側は予算の中で使い切られないので、後ろに回すと数値の側が一度も呼ばれない)。
        let generic = opts.generic_aux && self.resolve_generic_aux();
        let numeric = opts.numeric_aux && self.resolve_numeric_aux(super::numeric_aux::LAST_MIN_SCORE, super::numeric_aux::LAST_PER_STALL);
        if generic || numeric { return Recovered::Construction; }
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

        applied_anything
    }

    /// 補助作図を1つ図に足す。出どころを刻み(--origins 用)、importance が与えられれば
    /// 重要度を下げて推論の主軸がぶれないようにする。図の上で値の定まらない作図(同じ2点を通る直線など)は作らず None。
    pub(crate) fn add_aux(&mut self, name: String, def: Definition, ty: EntityType, origin: EntityOrigin, importance: Option<f64>) -> Option<ClassId> {
        let eg = &mut self.prover.egraph;
        if eg.nondegeneracy && !matches!(def, Definition::DirectionOf(_)) && eg.without_consuming_rng(|g| g.definition_is_degenerate(&def)) {
            println!("  📐 [退化した作図を見送り] {}", name);
            return None;
        }
        let prev = eg.set_origin(origin);
        let id = eg.create_entity(name, def.clone(), ty);
        if let Some(imp) = importance {
            eg.entities[id.0].base_importance = imp;
        }
        eg.apply_trivial_relations(id, &def);
        eg.set_origin(prev);
        Some(id)
    }

    /// 作図の直後に既存の図形と合流させてから、全定理を試し直す。
    pub(crate) fn settle_and_resweep(&mut self) {
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
            if self.prover.egraph.live_memo(&def) { continue; }
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
            .expect("直線の方向は退化の検査をしないので必ず作れる")
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
        // 🌟 需要の補助線には、性質の違う2種類が混ざっている(既定で分ける。--no-collinear-extra で戻せる)。
        //   既に2点が同じ直線上にある組: 作った直線は即座に既存の直線へ併合される。
        //     図は1つも増えず、残るのは定理が欲しがっていた Line(A,B) という呼び名と、
        //     その併合が生む事実だけ ― つまり「ほぼ無料」。
        //   それ以外: 本当に図が増える。
        // 同じ枠(LINES_PER_STALL)を奪い合わせると、ノイズで前者が増えたときに
        // 後者が引かれなくなる。枠を分ければ図の大きさに影響されない(来歴 #62)。
        let mut count = 0;
        let mut free_count = 0;
        for ((p1, p2), score, affinity) in demands {
            let def = Definition::new_line(p1, p2);
            if self.prover.egraph.live_memo(&def) { continue; }
            let free = self.prover.collinear_extra
                && self.prover.egraph.find_common_line(&[p1, p2]).is_some();
            if free {
                if free_count >= LINES_PER_STALL { continue; }
            } else if count >= LINES_PER_STALL { continue; }
            let name = format!("Line_{}_{}_(Demand)", self.prover.egraph.entities[p1.0].name, self.prover.egraph.entities[p2.0].name);
            match affinity {
                Some((da, db, dab)) if da + db > dab => {
                    println!("  💡 [オンデマンド作図] 要請により {} を生成 (需要: {:.1}, 相性◎: 次数{}+{}→{})", name, score, da, db, dab);
                }
                _ => println!("  💡 [オンデマンド作図] 要請により {} を生成 (需要: {:.1})", name, score),
            }
            self.add_aux(name, def, EntityType::Line, EntityOrigin::LineDemand, Some(0.5));
            if free { free_count += 1; } else { count += 1; }
            if count >= LINES_PER_STALL && (!self.prover.collinear_extra || free_count >= LINES_PER_STALL) {
                break;
            }
        }
        let count = count + free_count;

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
                if self.prover.egraph.live_memo(&def) { continue; }
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
            if self.prover.egraph.live_memo(&def) { continue; }
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
            if self.prover.egraph.live_memo(&def) { continue; }
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
                    if eg.live_memo(&def) { continue; }
                    cands.push((def, heat_p + eg.entities[l.0].heat() + eg.entities[c.0].heat()));
                }
            }
            for a in 0..circles.len() {
                for b in (a + 1)..circles.len() {
                    let (c1, c2) = (circles[a], circles[b]);
                    let on2 = finite_points_on(c2);
                    if finite_points_on(c1).iter().any(|q| *q != p && on2.contains(q)) { continue; }
                    let def = eg.normalize_definition(&Definition::SecondIntersectionOfCircles(p, c1, c2));
                    if eg.live_memo(&def) { continue; }
                    cands.push((def, heat_p + eg.entities[c1.0].heat() + eg.entities[c2.0].heat()));
                }
            }
        }
        if cands.is_empty() { return false; }
        cands.sort_by(|x, y| y.1.partial_cmp(&x.1).unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| format!("{:?}", x.0).cmp(&format!("{:?}", y.0))));

        let mut applied = false;
        for (def, heat) in cands.into_iter().take(2) {
            if self.prover.egraph.live_memo(&def) { continue; }
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

    /// 🌟 最後の手(--generic-aux)。ここまでの手が全部尽きたとき、熱い点どうしの中点と、熱い直線どうしの交点を少しずつ足す
    /// (1回に交点6・中点8まで、候補は熱い上位だけ)。人間の証明が要る補助作図は中点と交点がほとんどで(来歴 #68)、
    /// 需要から出る手はそのどちらも一部しか作らない。手が尽きて止まる問題にしか効かないので、今解けている問題の探索は変わらない。
    pub fn resolve_generic_aux(&mut self) -> bool {
        const HOT_LINES: usize = 14;
        const HOT_POINTS: usize = 12;
        const INTERSECTIONS_PER_STALL: usize = 6;
        const MIDPOINTS_PER_STALL: usize = 8;
        // 図が膨らみ続けると1回の run_step が時間の安全弁(--time)より長くなる(数値チェックが仕事量に数えられない)ので、総数に上限を置く。
        const GENERIC_AUX_TOTAL: usize = 60;
        if self.generic_aux_added >= GENERIC_AUX_TOTAL { return false; }
        let eg = &self.prover.egraph;
        let linf = eg.line_infinity;
        let hot = |ty: EntityType| -> Vec<ClassId> {
            let mut v: Vec<(f64, ClassId)> = (0..eg.entities.len()).map(ClassId)
                .filter(|&id| eg.get_rep(id) == id && eg.entities[id.0].entity_type == ty && eg.entities[id.0].is_active())
                .filter(|&id| id != linf && !(ty == EntityType::Point && eg.is_connected(id, linf)))
                .map(|id| (eg.entities[id.0].heat(), id)).collect();
            v.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap_or(std::cmp::Ordering::Equal).then_with(|| a.1.0.cmp(&b.1.0)));
            v.into_iter().map(|(_, id)| id).collect()
        };
        let mut lines = hot(EntityType::Line);
        lines.truncate(HOT_LINES);
        let mut points = hot(EntityType::Point);
        points.truncate(HOT_POINTS);
        let shares_a_point = |l1: ClassId, l2: ClassId| -> bool {
            eg.entities[l1.0].components.iter().flat_map(|c| c.subobjects.iter())
                .map(|&s| eg.get_rep(s))
                .any(|p| eg.entities[p.0].entity_type == EntityType::Point && eg.is_connected(p, l2))
        };

        let mut inters: Vec<(f64, Definition)> = Vec::new();
        for i in 0..lines.len() {
            for j in (i + 1)..lines.len() {
                let (l1, l2) = (lines[i], lines[j]);
                let def = eg.normalize_definition(&Definition::Intersection(l1, l2));
                if eg.live_memo(&def) || shares_a_point(l1, l2) { continue; }
                // 平行な2直線の交点は無限遠点(既存の方向)なので作らない。
                if let (Some(&d1), Some(&d2)) = (
                    eg.memo.get(&eg.normalize_definition(&Definition::DirectionOf(l1))),
                    eg.memo.get(&eg.normalize_definition(&Definition::DirectionOf(l2))),
                ) && eg.get_rep(d1) == eg.get_rep(d2) { continue; }
                inters.push((eg.entities[l1.0].heat() + eg.entities[l2.0].heat(), def));
            }
        }
        let mut mids: Vec<(f64, Definition)> = Vec::new();
        for i in 0..points.len() {
            for j in (i + 1)..points.len() {
                let def = eg.normalize_definition(&Definition::Midpoint(points[i], points[j]));
                if eg.live_memo(&def) { continue; }
                mids.push((eg.entities[points[i].0].heat() + eg.entities[points[j].0].heat(), def));
            }
        }
        let by_score = |a: &(f64, Definition), b: &(f64, Definition)|
            b.0.partial_cmp(&a.0).unwrap_or(std::cmp::Ordering::Equal).then_with(|| format!("{:?}", a.1).cmp(&format!("{:?}", b.1)));
        inters.sort_by(by_score);
        mids.sort_by(by_score);

        let mut applied = false;
        for (_, def) in inters.into_iter().take(INTERSECTIONS_PER_STALL) {
            let Definition::Intersection(l1, l2) = def else { continue };
            if self.prover.egraph.live_memo(&def) { continue; }
            let name = format!("Pt_{}_{}_(GenericAux)", self.prover.egraph.entities[l1.0].name, self.prover.egraph.entities[l2.0].name);
            println!("  💡 [汎用の補助作図] {} (熱い直線どうしの交点)を生成", name);
            self.add_aux(name, def, EntityType::Point, EntityOrigin::PointDemand, Some(0.5));
            self.generic_aux_added += 1;
            applied = true;
        }
        for (_, def) in mids.into_iter().take(MIDPOINTS_PER_STALL) {
            let Definition::Midpoint(a, b) = def else { continue };
            if self.prover.egraph.live_memo(&def) { continue; }
            let name = format!("Mid_{}_{}_(GenericAux)", self.prover.egraph.entities[a.0].name, self.prover.egraph.entities[b.0].name);
            println!("  💡 [汎用の補助作図] {} (熱い点どうしの中点)を生成", name);
            self.add_aux(name, def, EntityType::Point, EntityOrigin::MidDemand, Some(0.5));
            self.generic_aux_added += 1;
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
                if eg.live_memo(&def) { continue; }
                candidates.push((a, b, eg.entities[a.0].heat() + eg.entities[b.0].heat()));
            }
        }
        if candidates.is_empty() { return false; }
        candidates.sort_by(|x, y| y.2.partial_cmp(&x.2).unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| x.0.0.cmp(&y.0.0)).then_with(|| x.1.0.cmp(&y.1.0)));

        let mut applied = false;
        for (a, b, heat) in candidates.into_iter().take(2) {
            let def = self.prover.egraph.normalize_definition(&Definition::Midpoint(a, b));
            if self.prover.egraph.live_memo(&def) { continue; }
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

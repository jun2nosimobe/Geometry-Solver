//! 問題を1つ解く(`geom_solver <問題名>`)。
//!
//! 一巡: 定理マッチング(run_step) → 図の崩壊と目標到達の判定 → 何も進まなければ回復
//! (需要駆動の補助作図 → 候補capの拡大 → MCTS)。予算は仕事量(--steps)で測り、
//! --time は暴走を止める安全弁。
//!
//! sweep / diagnose は子プロセスの標準出力から「🎉 証明完了」「消費した仕事量:」「SKETCH\t」を
//! 拾うので、これらの表示は変えないこと。

use std::fs;
use std::time::{Duration, Instant};

use crate::logic_core::{self, BlackboardEngine, ProverEngine, Recovered, RecoveryOptions, BRANCH_LABELS};
use crate::mcts::MCTSSearchEngine;
use crate::mmp_core::{self, ClassId, EGraph, GoalStatus, RawProof};
use crate::{cli, padic_eval, problems, sketch, theorems, trace};

/// `--name` が付いているか。
fn flag(args: &[String], name: &str) -> bool {
    args.iter().any(|a| a == name)
}

/// `--name=値` の値(`name` は `=` まで含めて渡す)。無い・読めないときは None。
fn value<T: std::str::FromStr>(args: &[String], name_eq: &str) -> Option<T> {
    args.iter().find_map(|a| a.strip_prefix(name_eq)).and_then(|v| v.parse().ok())
}

pub struct SolveOptions {
    pub step_budget: u64,
    pub time_budget_secs: u64,
    pub use_mcts: bool,
    pub mcts_target_bias: bool,
    pub bandit: bool,
    pub seeded_rematch: bool,
    pub heat_cap: usize,
    pub fanout_heat_cap: usize,
    pub midpoint_demands: bool,
    /// 手が尽きたとき最後に、熱い点どうしの中点と熱い直線どうしの交点を足す(既定で有効。--no-generic-aux で外す)。
    pub generic_aux: bool,
    /// 数値で選ぶ補助作図(既定。手が全部尽きたとき、汎用の補助作図と一緒に作る。--no-numeric-aux で外す)。
    pub numeric_aux: bool,
    /// 代数的な追跡(複比・有向角の線形関係。既定、--no-ar で外す)と、角の足し算の規則を外してそれに任せる(--ar-replace)。
    pub ar: bool,
    pub ar_replace: bool,
    /// 名前で外す定理(--drop-theorems=名前,名前。AR への置き換えを試すため)。
    pub drop_theorems: Vec<String>,
    /// AR があっても、方冪・交わる弦の相似の2つの定理を残す(--chord-theorems)。
    pub chord_theorems: bool,
    pub numeric_aux_early: bool,
    pub length_theorems: bool,
    pub no_central_angle: bool,
    /// 追加の規則(--rules=chord,parallelogram,spiral,spiral-prop)。既定では入らない。
    pub rules: Vec<String>,
    /// 交わる弦の相似(既定で入る)を外す。
    pub no_spiral_opp: bool,
    /// 定理の結論の数値チェック(既定で有効、前提が乱数座標で成り立つ問題だけ)を外す。
    pub no_conclusion_check: bool,
    /// マージ前の数値チェック(局所伝播の却下と定理の結論の検算)を全て外す。規則だけで健全かを確かめるため。
    pub no_merge_checks: bool,
    /// 非退化条件(定理の NonDegenerate・局所伝播の条件・値の定まらない作図の見送り)を全て外す(A/B 用)。
    pub no_nondegeneracy: bool,
    /// 固定座標の数値モデルを使わず、従来の(構造が変わるたびに置き直す)経路で検算する(A/B 用)。
    pub no_fixed_coords: bool,
    pub no_projective: bool,
    pub degen_heat: bool,
    pub degen_heat_seed: u64,
    pub degen_heat_min_hits: u32,
    pub degen_heat_factor: f64,
    /// 行き詰まったときの手のうち外すもの(line, point, second, mid, angle, target)。
    pub skip_recovery: Vec<String>,
    pub sketch: Option<sketch::Rung>,
    /// 問題ファイルの筋書きの代わりに読む筋書き(コンパイルし直さずに試すため)。
    pub sketch_file: Option<String>,
    pub show_stats: bool,
    pub show_profile: bool,
    pub show_trace: bool,
    pub show_origins: bool,
    pub audit_merges: bool,
    /// 初期作図に足す無関係な作図の数(方針E: ノイズへの頑健性の計測)。
    pub fanout_connected: bool,
    pub nogood_core: bool,
    pub semijoin: bool,
    pub var_order: bool,
    pub collinear_extra: bool,
    pub widen_first: bool,
    pub widen_first_ceiling: usize,
    pub widen_every: usize,
    pub noise: usize,
    pub noise_seed: u64,
}

impl SolveOptions {
    pub fn parse(args: &[String]) -> Result<Self, String> {
        let sketch = match args.iter().find_map(|a| a.strip_prefix("--sketch=")) {
            None => None,
            Some(v) => Some(sketch::Rung::parse(v)
                .ok_or_else(|| format!("--sketch は pure / aux / 前提にする手順の数 のどれかです: {}", v))?),
        };
        let show_trace = flag(args, "--trace");
        Ok(Self {
            step_budget: value(args, "--steps=").unwrap_or(cli::DEFAULT_STEP_BUDGET),
            time_budget_secs: value(args, "--time=").unwrap_or(cli::DEFAULT_TIME_CAP_SECS),
            use_mcts: flag(args, "--mcts"),
            mcts_target_bias: !flag(args, "--no-mcts-target-bias"),
            bandit: flag(args, "--bandit"),
            seeded_rematch: flag(args, "--seeded-rematch"),
            heat_cap: value(args, "--heat-cap=").unwrap_or(40),
            fanout_heat_cap: value(args, "--fanout-heat-cap=").unwrap_or(5),
            midpoint_demands: flag(args, "--midpoint-demands"),
            generic_aux: !flag(args, "--no-generic-aux"),
            numeric_aux: !flag(args, "--no-numeric-aux"),
            ar: !flag(args, "--no-ar"),
            ar_replace: flag(args, "--ar-replace"),
            drop_theorems: args.iter().filter_map(|a| a.strip_prefix("--drop-theorems="))
                .flat_map(|v| v.split(',').map(|s| s.trim().to_string())).filter(|s| !s.is_empty()).collect(),
            chord_theorems: flag(args, "--chord-theorems"),
            numeric_aux_early: !flag(args, "--no-numeric-aux") && flag(args, "--numeric-aux-early"),
            length_theorems: !flag(args, "--no-length-theorems"),
            no_central_angle: flag(args, "--no-central-angle"),
            no_spiral_opp: flag(args, "--no-spiral-opp"),
            no_conclusion_check: flag(args, "--no-conclusion-check"),
            no_merge_checks: flag(args, "--no-merge-checks"),
            no_nondegeneracy: flag(args, "--no-nondegeneracy"),
            no_fixed_coords: flag(args, "--no-fixed-coords"),
            rules: args.iter()
                .filter_map(|a| a.strip_prefix("--rules="))
                .flat_map(|v| v.split(',').map(|s| s.trim().to_string()))
                .filter(|s| !s.is_empty())
                .collect(),
            no_projective: flag(args, "--no-projective"),
            degen_heat: flag(args, "--degen-heat"),
            degen_heat_seed: value(args, "--degen-heat-seed=").unwrap_or(12345),
            degen_heat_min_hits: value(args, "--degen-heat-min-hits=").unwrap_or(2),
            degen_heat_factor: value(args, "--degen-heat-factor=").unwrap_or(0.5),
            skip_recovery: args.iter()
                .filter_map(|a| a.strip_prefix("--skip-recovery="))
                .flat_map(|v| v.split(',').map(|s| s.trim().to_string()))
                .filter(|s| !s.is_empty())
                .collect(),
            sketch,
            sketch_file: args.iter().find_map(|a| a.strip_prefix("--sketch-file=")).map(str::to_string),
            show_stats: flag(args, "--stats"),
            show_profile: flag(args, "--profile"),
            show_trace,
            show_origins: flag(args, "--origins") || show_trace,
            audit_merges: flag(args, "--audit-merges"),
            fanout_connected: flag(args, "--fanout-connected"),
            nogood_core: flag(args, "--nogood-core"),
            semijoin: !flag(args, "--no-semijoin"),
            var_order: flag(args, "--var-order"),
            collinear_extra: !flag(args, "--no-collinear-extra"),
            widen_first: flag(args, "--widen-first"),
            widen_first_ceiling: value(args, "--widen-first-ceiling=").unwrap_or(40),
            widen_every: value(args, "--widen-every=").unwrap_or(2),
            noise: value(args, "--noise=").unwrap_or(0),
            noise_seed: value(args, "--noise-seed=").unwrap_or(12345),
        })
    }

    fn recovery_options(&self) -> RecoveryOptions {
        RecoveryOptions { midpoint_demands: self.midpoint_demands, skip: self.skip_recovery.clone(), widen_first: self.widen_first, widen_first_ceiling: self.widen_first_ceiling, widen_every: self.widen_every, generic_aux: self.generic_aux, numeric_aux: self.numeric_aux, numeric_aux_early: self.numeric_aux_early }
    }

    fn search_setup(&self) -> logic_core::SearchSetup {
        logic_core::SearchSetup { fixed_coords: !self.no_fixed_coords, merge_checks: !self.no_merge_checks, nondegeneracy: !self.no_nondegeneracy, conclusion_check: !self.no_conclusion_check }
    }
}

fn theorem_set(opts: &SolveOptions) -> Vec<logic_core::TheoremDef> {
    theorems::theorem_set(&theorems::TheoremSetOptions {
        projective: !opts.no_projective,
        length_bridge: opts.length_theorems,
        central_angle: !opts.no_central_angle,
        chord: opts.rules.iter().any(|r| r == "chord"),
        parallelogram: opts.rules.iter().any(|r| r == "parallelogram"),
        spiral: opts.rules.iter().any(|r| r == "spiral"),
        spiral_opp: !opts.no_spiral_opp,
        ar_replaces_chord: opts.ar && !opts.no_fixed_coords && !opts.chord_theorems,
    })
}

/// 証明を人間向けに復元し、コンソールと result/proof_<問題名>.txt に出す。
fn output_proof(egraph: &EGraph, problem_name: &str, fact_type: &str, target_args: &[ClassId]) {
    let proof_text = egraph.generate_proof(fact_type, target_args);
    println!("\n{}", proof_text);
    write_result(&format!("proof_{}.txt", problem_name), &proof_text, "証明");
}

/// マージ履歴を丸ごと機械可読な形で result/raw_proof_<問題名>.txt に出す(extract-proof が読む)。
fn output_raw_proof(egraph: &EGraph, problem_name: &str) -> String {
    let raw_text = egraph.dump_raw_proof();
    write_result(&format!("raw_proof_{}.txt", problem_name), &raw_text, "raw_proof");
    raw_text
}

/// extract-proof の結果: コンソールには要約、ファイルには深い証明と、重複を圧縮した証明。
pub fn output_extract_report(report: &mmp_core::DeepProof, problem_name: &str) {
    print!("{}", report.format_summary());
    write_result(&format!("extracted_proof_{}.txt", problem_name), &report.format_deep(), "extract_proof(深い証明)");
    write_result(&format!("compressed_proof_{}.txt", problem_name), &report.format_compressed(), "compressed_proof(圧縮された証明)");
}

fn write_result(file_name: &str, text: &str, label: &str) {
    let dir = "result";
    if fs::create_dir_all(dir).is_err() { return; }
    let path = format!("{}/{}", dir, file_name);
    match fs::write(&path, text) {
        Ok(_) => println!("📄 {}を '{}' に保存しました。", label, path),
        Err(e) => println!("⚠️ {}ファイルの書き込みに失敗しました ({}): {}", label, path, e),
    }
}

enum Goal {
    Proved,
    /// 図が壊れている・数値的に偽なので打ち切る。
    Abort,
    NotYet,
}

/// 目標到達の判定。MCTS が構成に関わった実行では、数値検証だけが根拠の局所ショートカットを
/// 経路に含む到達を証明と認めない(予想として記録して探索を続ける)。
struct GoalChecker {
    shortcut_noted: bool,
}

impl GoalChecker {
    fn check(&mut self, engine: &BlackboardEngine, problem_name: &str, target: &Option<(String, Vec<ClassId>)>,
             mcts_ever_committed: bool, start_time: Instant) -> Goal {
        let eg = &engine.prover.egraph;
        match eg.goal_status(target.as_ref()) {
            GoalStatus::NotYet => return Goal::NotYet,
            GoalStatus::Collapsed(p, q) => {
                println!("🚨 [図の崩壊を検出] 自由点 {} と {} が同じ同値類に入りました。", p, q);
                println!("    -> 自由点は互いに独立なので、正しい推論だけでは絶対に一致しません。どこかの局所マージが無関係な図形を結合して図全体が潰れています。この状態からはどんな目標も\"証明\"できてしまうため、探索を打ち切ります。");
                return Goal::Abort;
            }
            GoalStatus::NumericallyFalse => {
                let (_, target_args) = target.as_ref().expect("NumericallyFalse は目標があるときだけ");
                let r1 = eg.get_rep(target_args[0]);
                let r2 = eg.get_rep(target_args[1]);
                println!("🚨 [数値サニティチェック失敗] {} ≡ {} は構造的にはマージされましたが、ランダムな具体例では成り立ちません。",
                    eg.entities[r1.0].name, eg.entities[r2.0].name);
                println!("    -> どこかの局所マージ(直線/点の一意性判定)が本来無関係な図形を誤って結合した可能性が高く、証明成立とは認めません。探索を打ち切ります。");
                return Goal::Abort;
            }
            GoalStatus::Reached => {}
        }
        let Some((fact_type, target_args)) = target else { return Goal::NotYet };
        if fact_type == "Identical" {
            let uses_shortcut = mcts_ever_committed
                && EGraph::proof_uses_numeric_shortcut(&eg.explain_identical(target_args[0], target_args[1]));
            if uses_shortcut {
                if !self.shortcut_noted {
                    let r1 = eg.get_rep(target_args[0]);
                    let r2 = eg.get_rep(target_args[1]);
                    println!("🔮 [目標到達を却下・予想として記録] {} ≡ {} は構造的には統合されましたが、経路に数値的検証のみに基づく局所ショートカットが含まれ、かつMCTSがこの実行で構成に関与しているため、証明成立とは認めません。",
                        eg.entities[r1.0].name, eg.entities[r2.0].name);
                    println!("    -> 名前付き定理の連鎖による厳密な経路が別に見つかるまで、これは(反例が出なかったという意味で強い根拠のある)予想として扱い、探索を継続します。");
                    self.shortcut_noted = true;
                }
                return Goal::NotYet;
            }
        }
        println!("🎉 証明完了！ (Time: {:.2?}s)", start_time.elapsed().as_secs_f64());
        output_proof(eg, problem_name, fact_type, target_args);
        // 上の判定は目標の直接の経路しか見ないので、定理の前提まで再帰的にたどって、名前付き定理の連鎖だけで
        // 繋がっているかを監査する(接続・共円の目標は、目標の接続の由来から)。
        let raw_text = output_raw_proof(eg, problem_name);
        let raw = RawProof::parse(&raw_text);
        let report = if fact_type == "Identical" {
            raw.verify_identical(target_args[0].0, target_args[1].0)
        } else {
            let target = (fact_type.clone(), target_args.clone());
            let links: Vec<(usize, usize, Option<(usize, usize)>)> = eg.goal_incidences(&target).into_iter()
                .map(|(p, c, rec)| (p.0, c.0, rec.map(|(x, y)| (x.0, y.0)))).collect();
            raw.verify_incidences(&links)
        };
        output_extract_report(&report, problem_name);
        Goal::Proved
    }
}

/// 探索が進まなくなったときの手。
struct Recovery {
    mcts: MCTSSearchEngine,
    mcts_consecutive_failures: usize,
    mcts_ever_committed: bool,
}

const MCTS_MAX_CONSECUTIVE_FAILURES: usize = 3;

impl Recovery {
    /// 何か手を打てたら true。打つ手が無ければ false(探索を打ち切る)。
    fn run(&mut self, engine: &mut BlackboardEngine, target: &Option<(String, Vec<ClassId>)>, opts: &SolveOptions) -> bool {
        println!("⏳ ロジックがStallしました。リカバリーフェーズに移行します...");
        let recovery_start = Instant::now();
        let open: Vec<(String, Vec<ClassId>)> = target.iter().cloned().collect();
        let mut rotate = 0;
        let step = engine.on_stall(&open, &mut rotate, &opts.recovery_options(), opts.ar);
        engine.prover.profile.recovery_time += recovery_start.elapsed();
        match step {
            Recovered::Construction | Recovered::Algebra => return true,
            Recovered::WidenedCap(cap) => {
                println!("  -> 需要による補助線が尽きたため、MCTSの前に候補capを広げて再探索します(fanout_heat_cap={})。", cap);
                return true;
            }
            Recovered::Exhausted => {}
        }

        // MCTS は既定で無効: 無方向な作図は、数値検証が判定不能(None)を返す構造的な前提の
        // 死角を突いて偽の合流を作りうる。
        if !opts.use_mcts {
            println!("  -> 要求がなく、MCTSも無効(--mctsで有効化できます)なため探索を打ち切ります。");
            return false;
        }
        if self.mcts_consecutive_failures >= MCTS_MAX_CONSECUTIVE_FAILURES {
            println!("  -> MCTSも{}回連続で有効な一手を見つけられなかったため、探索を打ち切ります。", MCTS_MAX_CONSECUTIVE_FAILURES);
            return false;
        }
        println!("  -> 需要による補助線がないため、MCTSで補助的な構成を探索します...");
        let mcts_start = Instant::now();
        let found = self.mcts.run_step(&mut engine.prover.egraph, target, 200);
        engine.prover.profile.mcts_time += mcts_start.elapsed();
        if found {
            engine.schedule_full_sweep();
            self.mcts_consecutive_failures = 0;
            self.mcts_ever_committed = true;
        } else {
            self.mcts_consecutive_failures += 1;
            println!("  -> MCTSも有効な一手を見つけられませんでした({}/{})。", self.mcts_consecutive_failures, MCTS_MAX_CONSECUTIVE_FAILURES);
        }
        true
    }
}

/// 戻り値は証明できたか。定理の証人テスト(theorem_lint)がこれを見る。
pub fn run(problem_name: &str, opts: &SolveOptions) -> bool {
    println!("🚀 幾何ソルバーを起動します (対象問題: {}, 時間予算: {}秒, UCB1バンディット: {}, MCTS目標バイアス: {}, heat-cap: {}/{})",
        problem_name, opts.time_budget_secs,
        if opts.bandit { "有効" } else { "無効" },
        if opts.mcts_target_bias { "有効" } else { "無効" },
        opts.heat_cap, opts.fanout_heat_cap);

    let mut egraph = EGraph::new();
    let problem = problems::load_problem(problem_name, &mut egraph);
    let sketch_ctx = match opts.sketch {
        None => None,
        Some(rung) => {
            let Some(text) = sketch::text_for(problem_name, opts.sketch_file.as_deref()) else {
                println!("⚠️ 「{}」には証明の筋書き(SKETCH)がまだありません。", problem_name);
                return false;
            };
            match sketch::prepare(&mut egraph, &text, rung) {
                Ok(p) => { sketch::check_before_search(&egraph, &p); Some(p) }
                Err(e) => { println!("⚠️ {}", e); return false; }
            }
        }
    };

    egraph.nondegeneracy = !opts.no_nondegeneracy;
    if opts.noise > 0 {
        let added = crate::noise::add_noise(&mut egraph, opts.noise, opts.noise_seed);
        println!("  🎲 [ノイズ] 証明と無関係な作図を{}個足しました(実体は{}個増えた、seed={})。", opts.noise, added, opts.noise_seed);
    }

    if opts.degen_heat {
        let start = Instant::now();
        let groups = padic_eval::compute_degeneration_groups(&egraph, opts.degen_heat_seed, opts.degen_heat_min_hits);
        println!("  🧊 [退化発見] 自由点の退化ペアを走査して関連グループを計算しました ({:.2?}, factor={})。以後、熱の伝播ボーナスに使います。", start.elapsed(), opts.degen_heat_factor);
        egraph.degeneration_groups = Some(groups);
        egraph.degeneration_heat_factor = opts.degen_heat_factor;
    }

    if opts.rules.iter().any(|r| r == "spiral-prop") {
        // 局所伝播は変化した角の同値類でしか走らないので、最初に今ある角の同値類を全部積んで一巡させる。
        egraph.spiral_propagation = true;
        egraph.spiral_work_limit = opts.step_budget;
        let angles: Vec<ClassId> = (0..egraph.entities.len()).map(ClassId)
            .filter(|&id| egraph.get_rep(id) == id && egraph.is_angle_value(id)).collect();
        for &a in &angles {
            let defs: Vec<(ClassId, ClassId)> = egraph.entities[a.0].components.iter().flat_map(|c| c.definitions.iter())
                .filter_map(|d| if let mmp_core::Definition::AnglePair(x, y) = d { Some((*x, *y)) } else { None }).collect();
            if defs.len() >= 2 { egraph.spiral_pending.insert(a.0, defs); }
        }
        egraph.worklist.extend(angles);
        egraph.apply_congruence_closure();
    }
    let mut prover = ProverEngine::new(egraph);
    prover.heat_cap = opts.heat_cap;
    prover.fanout_heat_cap = opts.fanout_heat_cap;
    prover.fanout_connected = opts.fanout_connected;
    prover.nogood_core = opts.nogood_core;
    prover.semijoin = opts.semijoin;
    prover.var_order = opts.var_order;
    prover.collinear_extra = opts.collinear_extra;
    let mut theorems = theorem_set(opts);
    // --ar-replace: 角の足し算の規則(加法性・交替律)を外し、代数的な追跡に任せる。
    if opts.ar_replace { theorems.retain(|t| t.name != "有向角の加法性" && t.name != "有向角の交替律"); }
    // 名前が一致する定理を外す。末尾が * なら前方一致(「円周角の定理」で「円周角の定理の逆」まで外さないため)。
    theorems.retain(|t| !opts.drop_theorems.iter().any(|d| match d.strip_suffix('*') {
        Some(prefix) => t.name.starts_with(prefix),
        None => t.name == *d,
    }));
    prover.theorems = theorems.into_iter().map(std::rc::Rc::new).collect();
    let mut engine = BlackboardEngine::new(prover);
    engine.bandit_enabled = opts.bandit;
    engine.seeded_rematch_enabled = opts.seeded_rematch;
    engine.work_limit = opts.step_budget;
    if opts.show_trace { engine.prover.trace = Some(trace::TraceLog::default()); }

    let mut mcts = MCTSSearchEngine::new();
    mcts.target_bias_enabled = opts.mcts_target_bias;
    let mut recovery = Recovery { mcts, mcts_consecutive_failures: 0, mcts_ever_committed: false };
    let mut goal = GoalChecker { shortcut_noted: false };

    for fact in &problem.initial_facts {
        match fact {
            mmp_core::Fact::Identical(id1, id2) => {
                engine.prover.egraph.merge_entities_justified(*id1, *id2, mmp_core::Justification::Given);
                engine.emit(logic_core::Event::NodeMerged);
            }
            mmp_core::Fact::Connected(c, p) => {
                engine.prover.egraph.link_logical_incidence_justified(*c, *p, mmp_core::Justification::Given);
            }
        }
        engine.emit(logic_core::Event::FactProven(fact.clone()));
    }

    let prepared = engine.prepare(&opts.search_setup());
    if !prepared.fixed { println!("📐 固定座標は使いません(数値チェックは従来の経路)"); }
    if !prepared.hypotheses_hold { println!("🛡️ 結論の数値チェックは無効(前提どおりに座標を置けない図)"); }
    if opts.audit_merges {
        engine.prover.merge_audit = Some(logic_core::MergeAudit::default());
        engine.prover.egraph.merge_census = Some(mmp_core::MergeCensus::default());
    }

    let mut proved = false;
    let start_time = Instant::now();
    engine.schedule_full_sweep();
    while engine.prover.work_done() < opts.step_budget
        && start_time.elapsed() < Duration::from_secs(opts.time_budget_secs) {
        let run_step_start = Instant::now();
        let applied_logic = engine.run_step(10000);
        engine.prover.profile.run_step_time += run_step_start.elapsed();

        // 数値的な偶然の一致(予想)を使い捨ての複製の上で評価し、熱に反映する。
        engine.process_pending_conjectures(&problem.target_fact);

        match goal.check(&engine, problem_name, &problem.target_fact, recovery.mcts_ever_committed, start_time) {
            Goal::Proved => { proved = true; break; }
            Goal::Abort => break,
            Goal::NotYet => {}
        }
        // 手が止まったら、代数的な追跡(--ar)と回復の手(補助作図など)を同じ回に両方行う。追跡だけで次の回に進むと、
        // 補助作図が要る問題で全定理の試し直しが余分に挟まる(nine_point_full が4倍遅くなった)。
        if !applied_logic && !recovery.run(&mut engine, &problem.target_fact, opts) {
            break;
        }
    }

    // 解けたかどうかに関わらず、後から extract-proof で監査できるようマージ履歴を残す。
    let sk = engine.prover.egraph.nondegenerate_skips;
    if sk.iter().any(|&n| n > 0) {
        println!("📐 局所伝播が非退化条件で見送った回数: 交点の一意性 {} / 二次曲線の一意性 {} / 複比の一意性 {}", sk[0], sk[1], sk[2]);
    }
    if opts.ar {
        println!("🧮 代数的な追跡: {} 件併合(数値で偽と分かって見送り {} 件)、{} 回、行演算 {}(仕事量に含む)",
            engine.ar_merged, engine.ar_rejected, engine.ar_rounds, engine.ar_ops);
    }
    if engine.prover.degenerate_matches > 0 {
        println!("📐 図の上で退化した配置(「相異なる」図形が数値的に一致)のマッチを {} 件捨てました。", engine.prover.degenerate_matches);
    }
    if engine.prover.rejected_conclusions > 0 {
        println!("🛡️ 数値的に成り立たない定理の結論を {} 件却下しました。", engine.prover.rejected_conclusions);
    }
    println!("🧮 消費した仕事量: {} ステップ (予算 {})", engine.prover.work_done(), opts.step_budget);
    output_raw_proof(&engine.prover.egraph, problem_name);
    engine.prover.egraph.dump_state();

    if let Some(log) = &engine.prover.trace {
        trace::report(&engine.prover.egraph, log, &problem.target_fact,
            engine.prover.work_done(), engine.prover.heat_cap, engine.prover.fanout_heat_cap);
    }
    if let Some(audit) = &engine.prover.merge_audit {
        print_merge_audit(audit, problem_name, prepared.hypotheses_hold);
    }
    if let Some(census) = &engine.prover.egraph.merge_census {
        print_merge_census(census, problem_name, prepared.hypotheses_hold);
    }
    if opts.show_origins {
        trace::report_origins(&engine.prover.egraph, &problem.target_fact, problem_name);
    }
    if let Some(p) = &sketch_ctx {
        sketch::report(&engine.prover.egraph, p);
    }
    if opts.show_stats {
        print_stats(&engine.prover);
    }
    if opts.show_profile {
        print_profile(&engine.prover, start_time.elapsed());
    }
    proved
}

/// --audit-merges の集計。`MERGE_AUDIT\t問題\t定理\t真\t偽\t判定不能\t前提` の行は全問の掃引で集計しやすいように出す
/// (前提は、探索前の前提が乱数座標で成り立つなら ok、成り立たないなら hypothesis ― その問題の「偽」は誤警報の可能性)。
fn print_merge_audit(audit: &logic_core::MergeAudit, problem_name: &str, hypotheses_hold: bool) {
    println!("\n=== 🔍 定理の結論の数値監査 (--audit-merges) ===");
    if !hypotheses_hold {
        println!("  ⚠️ この問題の前提は乱数座標で成り立たない(座標への制約を等式で与えている)ので、「偽」は誤警報の可能性があります。");
    }
    let tag = if hypotheses_hold { "ok" } else { "hypothesis" };
    for (theorem, [t, f, u]) in &audit.per_theorem {
        println!("  真 {:>5} / 偽 {:>4} / 判定不能 {:>5} : {}", t, f, u, theorem);
        println!("MERGE_AUDIT\t{}\t{}\t{}\t{}\t{}\t{}", problem_name, theorem, t, f, u, tag);
    }
    for (theorem, example) in &audit.false_examples {
        println!("  ❌ 偽: {} (理由: {})", example, theorem);
    }
    println!("=============================\n");
}

/// --audit-merges の、全てのマージ・接続の監査(出どころ別)。`MERGE_CENSUS\t問題\t出どころ\t真\t偽\t判定不能\t前提` の行も出す。
fn print_merge_census(census: &mmp_core::MergeCensus, problem_name: &str, hypotheses_hold: bool) {
    println!("\n=== 🔍 全てのマージ・接続の数値監査 (--audit-merges、{} 件) ===", census.seq);
    let tag = if hypotheses_hold { "ok" } else { "hypothesis" };
    for (source, [t, f, u]) in &census.per_source {
        println!("  真 {:>6} / 偽 {:>5} / 判定不能 {:>6} : {}", t, f, u, source);
        println!("MERGE_CENSUS\t{}\t{}\t{}\t{}\t{}\t{}", problem_name, source, t, f, u, tag);
    }
    println!("=============================\n");
}

/// 定理ごとの試行回数・cap到達・平均dfs_call・平均報酬(1回あたりの消費が大きい順に20件)。
fn print_stats(prover: &ProverEngine) {
    println!("\n=== 📊 定理ごとのUCB1統計 (1回あたりの消費が大きい順、全件) ===");
    let mut rows: Vec<(String, u64, u64, u64, f64)> = prover.theorem_stats.iter().enumerate()
        .filter(|(_, s)| s.attempts > 0)
        .map(|(idx, s)| (prover.theorems[idx].name.clone(), s.attempts, s.cap_hits, s.total_dfs_calls, s.total_reward / s.attempts as f64))
        .collect();
    // 平均どうしの比較を交差乗算で行う(丸め誤差を避ける)。
    rows.sort_by(|a, b| (b.3 as u128 * a.1 as u128).cmp(&(a.3 as u128 * b.1 as u128)));
    for (name, attempts, cap_hits, total_dfs_calls, avg_reward) in rows.iter() {
        let avg_dfs = *total_dfs_calls as f64 / *attempts as f64;
        println!("  {:>6}回試行 (うちcap到達{:>3}回) / 平均dfs_call {:>9.0} / 平均報酬 {:>+6.3} : {}", attempts, cap_hits, avg_dfs, avg_reward, name);
    }
    println!("=============================\n");
}

fn print_profile(prover: &ProverEngine, total: Duration) {
    let p = &prover.profile;
    let accounted = p.run_step_time + p.recovery_time + p.mcts_time;
    let pct = |d: Duration| -> f64 {
        if total.as_secs_f64() > 0.0 { 100.0 * d.as_secs_f64() / total.as_secs_f64() } else { 0.0 }
    };
    println!("\n=== ⏱️  実行時間の内訳 (--profile) ===");
    println!("  合計実行時間          : {:>7.2}s", total.as_secs_f64());
    println!("  ├─ dfs_match本体      : {:>7.2}s ({:>5.1}%)", p.run_step_time.as_secs_f64(), pct(p.run_step_time));
    println!("  ├─ 回復フェーズ       : {:>7.2}s ({:>5.1}%)", p.recovery_time.as_secs_f64(), pct(p.recovery_time));
    println!("  ├─ MCTS               : {:>7.2}s ({:>5.1}%)", p.mcts_time.as_secs_f64(), pct(p.mcts_time));
    println!("  └─ 未計測(数値検証等) : {:>7.2}s ({:>5.1}%)",
        total.saturating_sub(accounted).as_secs_f64(), pct(total.saturating_sub(accounted)));
    println!("  失敗キャッシュのエントリ数 : {} (鍵の絞り込み{})",
        prover.failed_path_entries(), if prover.nogood_core { "あり" } else { "なし" });
    println!("  --- schedule_full_sweep自体の内訳 ---");
    println!("  呼び出し回数          : {}", p.sfs_calls);
    println!("  累計所要時間          : {:.3}s ({:.1}% of 合計)", p.sfs_time.as_secs_f64(), pct(p.sfs_time));
    println!("  作成したシードなしタスク数 : {} (呼び出し1回あたり平均 {:.1}個)",
        p.sfs_tasks_created,
        if p.sfs_calls > 0 { p.sfs_tasks_created as f64 / p.sfs_calls as f64 } else { 0.0 });
    println!("  --- タスクポップ数とdfs_call消費量の内訳(シード有無別) ---");
    let total_calls = p.seeded_dfs_calls + p.unseeded_dfs_calls;
    let calls_pct_of = |c: u64, t: u64| -> f64 { if t > 0 { 100.0 * c as f64 / t as f64 } else { 0.0 } };
    println!("  失敗キャッシュで即打ち切り : {} (dfs_match の{:.1}%) / 世代が違って使えず {} ({:.1}%)",
        p.cache_hits, calls_pct_of(p.cache_hits, total_calls), p.cache_stale, calls_pct_of(p.cache_stale, total_calls));
    let calls_pct = |c: u64| -> f64 { if total_calls > 0 { 100.0 * c as f64 / total_calls as f64 } else { 0.0 } };
    println!("  シード済みタスク      : {:>8}回ポップ / dfs_call計 {:>10} ({:>5.1}%)",
        p.seeded_pops, p.seeded_dfs_calls, calls_pct(p.seeded_dfs_calls));
    println!("  シードなしタスク      : {:>8}回ポップ / dfs_call計 {:>10} ({:>5.1}%)",
        p.unseeded_pops, p.unseeded_dfs_calls, calls_pct(p.unseeded_dfs_calls));
    {
        let h = &p.dep_mask_bits;
        let total: u64 = h.iter().sum();
        println!("  --- 失敗を記録したときの依存マスクの幅(立っているビット数 / 全8ビット) ---");
        print!("  ");
        for (bits, n) in h.iter().enumerate() {
            if *n > 0 { print!("{}bit:{} ({:.0}%)  ", bits, n, 100.0 * *n as f64 / total.max(1) as f64); }
        }
        println!();
    }
    println!("  --- 失敗キャッシュを無効にした型世代の変化(理由 × 型) ---");
    {
        let g = &prover.egraph.generation_bumps;
        let total: u64 = g.iter().flatten().sum();
        print!("  {:<14}", "");
        for t in crate::mmp_core::BUMP_TYPE_LABELS { print!("{:>10}", t); }
        println!("{:>10}", "計");
        for (ci, row) in g.iter().enumerate() {
            print!("  {:<14}", crate::mmp_core::BUMP_CAUSE_LABELS[ci]);
            for v in row { print!("{:>10}", v); }
            let sub: u64 = row.iter().sum();
            println!("{:>10} ({:>4.1}%)", sub, if total > 0 { 100.0 * sub as f64 / total as f64 } else { 0.0 });
        }
    }
    println!("  --- 枝の出どころ(どのパターンの結合が探索を吐いているか) ---");
    let branch_total: u64 = p.branch_counts.iter().sum();
    let mut rows: Vec<(usize, u64)> = p.branch_counts.iter().copied().enumerate().collect();
    rows.sort_by_key(|&(_, n)| std::cmp::Reverse(n));
    for (i, n) in rows {
        if n == 0 { continue; }
        println!("  {:>10} ({:>5.1}%)  {}", n,
            if branch_total > 0 { 100.0 * n as f64 / branch_total as f64 } else { 0.0 },
            BRANCH_LABELS[i]);
    }
    println!("=============================\n");
}

//! 🌟 ユーザー要望:「MCTSと自由作図を通して、初等幾何の『綺麗な』問題を
//! 発見する(証明はできればでOK)」への対応。初等幾何的に筋の良い作図や
//! 熱の分配がどのようなものかを実際の探索結果から観察するための、
//! 証明目標を一切持たない自由探索モード。
//!
//! 既存の定理探索エンジン(logic_core.rs)・MCTS(mcts.rs)は常に固定の
//! 証明目標(target_fact)へ向けて探索するが、このモードには目標を渡さない
//! (target: &None)。代わりに:
//!   1. 生成的な種配置(汎用三角形、既定でA,B,Cの3自由点)からMCTSに、
//!      target=Noneのまま自由に補助構成(中点・垂線・平行線・外接円・交点・
//!      方向・調和共役点)を積ませる。target=Noneでは
//!      MCTSSearchEngine::evaluate_stepのtarget_bonus/target_reachedが
//!      常に0/falseになるため、報酬は純粋に「合同閉包で実際に何件
//!      同値類が減ったか」+「構成された図形自体の構造的な面白さ
//!      (heat_with_degree + 作図の種類 + 共線/共円の強さ)」だけになる
//!      ――これがまさに人間が"手が空いた時にとりあえず補助線を引いて
//!      みる"素朴な探索に近い、目標非依存の版。
//!   2. 数値評価(eval.rs::log_conjecture_candidate)が「記号的にはまだ
//!      別物として扱われている2つの図形が、独立な乱数サンプルで数値的に
//!      一致した」ことを自動検出する(Schwartz-Zippel補題により、単発の
//!      観測でも約10億分の1の偶然でしか起こらない、ほぼ確実な兆候)たびに、
//!      それを「未証明だが数値的根拠のある予想」(EGraph::conjectures)
//!      として記録する既存の仕組みをそのまま利用する――新しい発見の
//!      仕組みを作るのではなく、既にある「予想検出器」を目標無しの
//!      自由探索の上で走らせるだけ、というのがこのモードの骨子。
//!   3. 探索終了後、蓄積された予想候補を「美しさ」スコア(v1、今後の
//!      チューニング対象)で順位付けし、構成手順(どうやってその2つの
//!      図形にたどり着いたか)とともに提示する。
//!   4. (--prove指定時のみ)最上位の予想について、既存の定理探索エンジン
//!      (schedule_full_sweep + dfs_match + 需要駆動の回復フェーズ、MCTSは
//!      使わない)で実際に名前付き定理の連鎖による証明を試みる。証明できな
//!      くても「名前付き定理の連鎖では見つからなかった」というだけで、
//!      数値的な根拠(Schwartz-Zippel)自体の確からしさは変わらない。
//!   5. 熱量(GeoEntity::heat_with_degree)ランキングも併せて表示する。
//!      これは「探索が何を"注目に値する"と判断したか」をそのまま可視化
//!      したもので、人間の直感(中点・垂心・共円点のような"要"の図形が
//!      上位に来るべき)と実際の分配を見比べるための診断材料。
//!
//! 🌟 ユーザー提案(「定理を無マージで動かし、conjectureのみでも定理を
//! 適用させるモード」):自由構築の後、蓄積された各予想(a≡b)について
//! BlackboardEngine::probe_conjectureで「その予想を一時的に真だと仮定した
//! 使い捨てのクローン上で、実際に名前付き定理の連鎖を走らせたら何が
//! 追加で導かれるか」を調べ、見つかった新しい等式を"条件付きの"予想として
//! 同じconjecturesマップに合流させる(probe_and_expand_conjectures)。
//! 既存のestimate_conjecture_value(合同閉包1回だけの浅い見積もり)より
//! ずっと深く「その仮説が本当に効くとしたら何が起きるか」を覗ける一方、
//! 定理マッチングの本予算を使うため計算コストは高い――既定では検出済みの
//! 予想1件あたり1回だけ(連鎖の深追いはしない)に留めている。

use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};
use crate::logic_core::{ProverEngine, BlackboardEngine};
use crate::mcts::MCTSSearchEngine;
use crate::theorems;
use std::time::{Duration, Instant};

pub fn run(args: &[String]) {
    let time_budget_secs: u64 = args.iter()
        .find_map(|a| a.strip_prefix("--time="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(60);
    let max_steps: usize = args.iter()
        .find_map(|a| a.strip_prefix("--steps="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(80);
    let sims_per_step: usize = args.iter()
        .find_map(|a| a.strip_prefix("--sims="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(150);
    let top_n: usize = args.iter()
        .find_map(|a| a.strip_prefix("--top="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(5);
    let try_prove = args.iter().any(|a| a == "--prove");
    let prove_time_secs: u64 = args.iter()
        .find_map(|a| a.strip_prefix("--prove-time="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(15);
    // 🌟 3未満(点1つ・2つ)では外接円すら作れず自由作図として貧弱すぎるため
    // 最低3(汎用三角形)を保証する。4以上を指定すれば汎用四角形等になる。
    let seed_points: usize = args.iter()
        .find_map(|a| a.strip_prefix("--seed-points="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(3)
        .max(3);
    // 🌟 仮説駆動の定理プロービング(probe_and_expand_conjectures)の制御。
    // 既定で有効。--no-probeで従来通り(数値的コンフリクトのみ)に戻せる。
    let skip_probe = args.iter().any(|a| a == "--no-probe");
    let probe_dfs_budget: usize = args.iter()
        .find_map(|a| a.strip_prefix("--probe-dfs-budget="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(3000);
    let probe_rounds: usize = args.iter()
        .find_map(|a| a.strip_prefix("--probe-rounds="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(5);

    println!("🔭 自由作図による「綺麗な問題」発見モードを開始します (初期自由点: {}個, ステップ上限: {}, 時間予算: {}秒, 1ステップあたりのMCTSシミュレーション: {}回)",
        seed_points, max_steps, time_budget_secs, sims_per_step);

    let mut egraph = EGraph::new();
    let names = ["A", "B", "C", "D", "E", "F", "G", "H"];
    for i in 0..seed_points {
        let name = names.get(i).map(|s| s.to_string()).unwrap_or_else(|| format!("P{}", i));
        egraph.create_entity(name, Definition::FreePoint, EntityType::Point);
    }
    egraph.apply_congruence_closure();

    // 🌟 target_bias_enabledはtarget=Noneの下では実質何もしない
    // (action_space.rs::target_weight_bonusがtarget=Noneで常に0を返す)が、
    // 「このモードは意図的に目標非依存である」ことをコード上明示するために
    // falseにしておく。
    let mut mcts = MCTSSearchEngine::new();
    mcts.target_bias_enabled = false;

    let start = Instant::now();
    let mut steps_done = 0usize;
    let mut consecutive_failures = 0usize;
    const MAX_CONSECUTIVE_FAILURES: usize = 5;
    while start.elapsed() < Duration::from_secs(time_budget_secs) && steps_done < max_steps {
        let found = mcts.run_step(&mut egraph, &None, sims_per_step);
        steps_done += 1;
        if found {
            consecutive_failures = 0;
        } else {
            consecutive_failures += 1;
            if consecutive_failures >= MAX_CONSECUTIVE_FAILURES {
                println!("  -> MCTSが{}回連続で新しい手を見つけられなかったため、探索をここで打ち切ります。", MAX_CONSECUTIVE_FAILURES);
                break;
            }
        }
    }
    println!("\n🔭 探索終了 ({}ステップ、{:.1}秒経過)。アクティブな同値類数: {}",
        steps_done, start.elapsed().as_secs_f64(), egraph.count_active_classes());

    // 🌟 ここから先は定理探索エンジン(schedule_full_sweep/dfs_match)を使うため、
    // egraphの所有権をBlackboardEngineへ渡す。
    let mut engine = build_full_engine(egraph);
    if !skip_probe {
        probe_and_expand_conjectures(&mut engine, probe_dfs_budget, probe_rounds);
    }

    report_conjectures(&mut engine.prover.egraph, top_n, try_prove, prove_time_secs);
    report_heat_ranking(&engine.prover.egraph, 10);
}

/// 🌟 discover.rs内の各所(仮説駆動プロービング/--proveの証明試行)が
/// 使う、全定理を登録済みのBlackboardEngineを組み立てる共通処理。
/// main.rsの通常の問題実行と同じ定理集合(get_all_theorems +
/// get_projective_theorems)を使う。
fn build_full_engine(egraph: EGraph) -> BlackboardEngine {
    let mut prover = ProverEngine::new(egraph);
    let mut all_theorems = theorems::get_all_theorems();
    all_theorems.extend(theorems::get_projective_theorems());
    prover.theorems = all_theorems.into_iter().map(std::rc::Rc::new).collect();
    let mut engine = BlackboardEngine::new(prover);
    // 🌟 プロービング・単発の証明試行はどちらも1回限りの短い実行なので、
    // UCB1バンディットの学習(複数回の試行で徐々に賢くなる仕組み)は
    // 恩恵が薄く、むしろ毎回同じ優先順位から始まる方が結果を再現しやすい。
    engine.bandit_enabled = false;
    engine
}

/// 🌟 ユーザー提案:「定理を無マージで動かし、conjectureのみでも定理を
/// 適用させるモード」。蓄積されている予想それぞれについて
/// BlackboardEngine::probe_conjectureを1回適用し、「その予想を仮定すると
/// さらに導かれる」新しい等式を"条件付きの"予想として同じconjectures
/// マップに追加する。連鎖はここでは1段階だけ(見つかった条件付き予想を
/// さらに再帰的にプロービングする深追いは、組み合わせ爆発のリスクが
/// あるためv2の課題として残す)。
fn probe_and_expand_conjectures(engine: &mut BlackboardEngine, dfs_budget: usize, sweep_rounds: usize) {
    let seeds: Vec<((usize, usize), String)> = {
        let map = engine.prover.egraph.conjectures.borrow();
        map.iter().map(|(&k, e)| (k, e.hypothesis.clone())).collect()
    };
    if seeds.is_empty() {
        println!("\n🧪 プロービング対象の予想がまだ無いため、この段階はスキップします。");
        return;
    }
    println!("\n🧪 蓄積された{}件の予想それぞれについて、実際に名前付き定理を発火させてみます(仮説駆動プロービング、1件あたりdfs予算{}×{}ラウンド)...",
        seeds.len(), dfs_budget, sweep_rounds);
    // 🌟 conjecturesのキーは記録した"時点"のget_rep(ClassId)で正規化されている
    // (eval.rs::log_conjecture_candidateのドキュメント参照)ため、union-findの
    // 経路圧縮・マージが進んだ後では、複数のキーが現在は同じ代表元ペアに
    // 解決されることがある。プロービング1回はdfs_match本体を走らせる高価な
    // 処理なので、現在の代表元ペア単位で重複除去してから実行する。
    let mut probed_pairs = rustc_hash::FxHashSet::default();
    let mut new_count = 0usize;
    for ((ai, bi), parent_hypothesis) in &seeds {
        let (a, b) = (engine.prover.egraph.get_rep(ClassId(*ai)), engine.prover.egraph.get_rep(ClassId(*bi)));
        if a == b { continue; }
        let key = if a.0 < b.0 { (a, b) } else { (b, a) };
        if !probed_pairs.insert(key) { continue; }
        let name_a = engine.prover.egraph.entities[engine.prover.egraph.get_rep(a).0].name.clone();
        let name_b = engine.prover.egraph.entities[engine.prover.egraph.get_rep(b).0].name.clone();
        let discovered = engine.probe_conjecture(a, b, dfs_budget, sweep_rounds);
        if !discovered.is_empty() {
            println!("  🧪 {} ≡ {} を仮定すると、定理の連鎖により{}件の別の等式が追加で導かれました。",
                name_a, name_b, discovered.len());
        }
        for (x, y) in discovered {
            if x == y { continue; }
            let hypothesis = format!("[定理連鎖] {} ≡ {}(仮説: {})を仮定すると導かれる", name_a, name_b, parent_hypothesis);
            engine.prover.egraph.log_conjecture_candidate(x, y, &hypothesis);
            new_count += 1;
        }
    }
    println!("🧪 プロービング終了: 新たに{}件の条件付きの予想を発見しました。", new_count);
}

struct RankedConjecture {
    a: ClassId,
    b: ClassId,
    hypothesis: String,
    occurrences: u32,
    additional_merges: usize,
    beauty: f64,
}

/// 🌟 探索中に蓄積されたEGraph::conjectures(数値的な偶然の一致候補)を
/// 「美しさ」スコアで順位付けして表示する。
fn report_conjectures(egraph: &mut EGraph, top_n: usize, try_prove: bool, prove_time_secs: u64) {
    let entries: Vec<((usize, usize), String, u32)> = {
        let map = egraph.conjectures.borrow();
        map.iter().map(|(&k, e)| (k, e.hypothesis.clone(), e.occurrences)).collect()
    };
    if entries.is_empty() {
        println!("\n😶 探索中に数値的な偶然の一致は見つかりませんでした。この乱数試行・この配置では、まだ知られていない関係を検出できませんでした(ステップ数や1ステップあたりのシミュレーション回数を増やすと見つかりやすくなります)。");
        return;
    }

    let total_entries = entries.len();
    let mut ranked: Vec<RankedConjecture> = Vec::new();
    for ((ai, bi), hypothesis, occurrences) in entries {
        let (a, b) = (egraph.get_rep(ClassId(ai)), egraph.get_rep(ClassId(bi)));
        if a == b { continue; } // 探索の続きで別経路により既に証明済みになっていた
        let value = egraph.estimate_conjecture_value(a, b, &None);
        let depth_a = egraph.entities[a.0].mcts_depth;
        let depth_b = egraph.entities[b.0].mcts_depth;
        // 🌟 美しさスコア(v1、今後の調整対象として意図的に単純にしてある):
        // ・additional_merges(この等式1つを仮定するだけで合同閉包が連鎖的に
        //   引き起こす追加の統合の数)を主軸にする――これが大きいほど
        //   「単発の偶然」ではなく、図形全体を支配する中心的な関係である
        //   可能性が高い(方冪の定理・オイラー線のような"効く"定理は、まさに
        //   1つの等式から芋づる式に他の関係が従う)。
        // ・occurrences(観測回数)は単発でも既にSchwartz-Zippelにより
        //   確信度が極めて高いため、頭打ち(min 5)にして小さくしか効かせない。
        // ・mcts_depthの和(構成手順の長さ)は大きいほど減点する――定規と
        //   コンパスで再現する手順が短いほど、1つの命題として提示しやすい
        //   "エレガントな問題"に近いという仮定に基づく。
        // ・仮説駆動プロービング(probe_and_expand_conjectures)由来の"条件付き"
        //   予想([定理連鎖]接頭辞で識別)は、既に一度「実際に名前付き定理を
        //   発火させて出てきた」という単なる数値的偶然より強い根拠を持つため、
        //   ボーナスを与えて優先的に上位へ来るようにする。
        let chain_bonus = if hypothesis.starts_with("[定理連鎖]") { 5.0 } else { 0.0 };
        let beauty = value.additional_merges as f64 * 3.0
            + (occurrences.min(5) as f64) * 0.5
            - (depth_a + depth_b) as f64 * 1.5
            + chain_bonus;
        ranked.push(RankedConjecture { a, b, hypothesis, occurrences, additional_merges: value.additional_merges, beauty });
    }
    ranked.sort_by(|x, y| y.beauty.partial_cmp(&x.beauty).unwrap_or(std::cmp::Ordering::Equal));

    // 🌟 検出された予想候補が(局所的な一意性判定propagate_line_uniqueness/
    // propagate_point_uniqueness等により)報告時点までに既に記号的に統合
    // 済みだった場合、ranked は空になり得る。これは「何も見つからなかった」
    // (total_entries==0)とは違う状態(何かは見つかったが、報告に値する
    // 未解決の関係としては残らなかった)なので、区別してメッセージを出す。
    if ranked.is_empty() {
        println!("\n😶 探索中に{}件の数値的な偶然の一致が検出されましたが、いずれも(局所的な一意性判定などにより)報告時点までに既に記号的に統合済みでした。まだ知られていない関係として提示できるものは残っていません。",
            total_entries);
        return;
    }

    println!("\n=== 🏛️  発見された「綺麗な」関係の候補 (美しさスコア降順、上位{}件 / 全{}件) ===",
        top_n.min(ranked.len()), ranked.len());
    for (rank, c) in ranked.iter().take(top_n).enumerate() {
        let name_a = egraph.entities[c.a.0].name.clone();
        let name_b = egraph.entities[c.b.0].name.clone();
        println!("\n{}. [美しさ {:.1}] {} ≡ {}  (仮説: {}, 追加的帰結{}件, 観測{}回, 構成の深さ{}+{})",
            rank + 1, c.beauty, name_a, name_b, c.hypothesis, c.additional_merges, c.occurrences,
            egraph.entities[c.a.0].mcts_depth, egraph.entities[c.b.0].mcts_depth);
        println!("   構成手順:");
        for line in describe_construction(egraph, c.a, c.b) {
            println!("     {}", line);
        }
    }

    if try_prove {
        if let Some(top) = ranked.first() {
            attempt_proof(egraph, top.a, top.b, prove_time_secs);
        }
    }
}

/// 🌟 実体a, bにたどり着くまでに実際に使われた作図を、依存関係の順
/// (親が先)に列挙する。original_definition(create_entity時に一度だけ
/// 設定され、以後マージが起きても書き換わらない)を辿ることで、
/// 「後から短い名前に上書きされた」影響を受けずに、本当にその実体が
/// 何から作られたかを正確に復元する。
fn describe_construction(egraph: &EGraph, a: ClassId, b: ClassId) -> Vec<String> {
    let mut seen = rustc_hash::FxHashSet::default();
    let mut order: Vec<ClassId> = Vec::new();
    fn visit(egraph: &EGraph, id: ClassId, seen: &mut rustc_hash::FxHashSet<ClassId>, order: &mut Vec<ClassId>) {
        let rep = egraph.get_rep(id);
        if !seen.insert(rep) { return; }
        for p in egraph.entities[rep.0].original_definition.get_parents() {
            visit(egraph, p, seen, order);
        }
        order.push(rep);
    }
    visit(egraph, a, &mut seen, &mut order);
    visit(egraph, b, &mut seen, &mut order);
    order.iter().map(|&id| {
        let e = &egraph.entities[id.0];
        match &e.original_definition {
            Definition::FreePoint | Definition::GivenPoint => format!("{} := 自由点", e.name),
            def => format!("{} := {}", e.name, egraph.format_definition(def)),
        }
    }).collect()
}

/// 🌟 発見した予想candid(a≡b)について、既存の定理探索エンジンで名前付き
/// 定理の連鎖による証明を試みる。MCTSは使わない(発見時点で既に構成は
/// 出揃っているはずで、ここでは"名前付き定理だけで説明できるか"を見たい)。
fn attempt_proof(egraph: &EGraph, a: ClassId, b: ClassId, time_budget_secs: u64) {
    let name_a = egraph.entities[a.0].name.clone();
    let name_b = egraph.entities[b.0].name.clone();
    println!("\n🔍 最有力候補の証明を試みます: {} ≡ {} (時間予算: {}秒、MCTSは使わず名前付き定理の連鎖のみ)",
        name_a, name_b, time_budget_secs);

    let mut engine = build_full_engine(egraph.clone());
    let target: Option<(String, Vec<ClassId>)> = Some(("Identical".to_string(), vec![a, b]));

    engine.schedule_full_sweep();
    let start = Instant::now();
    let mut solved = false;
    while start.elapsed() < Duration::from_secs(time_budget_secs) {
        let applied = engine.run_step(10000);
        if engine.prover.egraph.get_rep(a) == engine.prover.egraph.get_rep(b) {
            solved = true;
            break;
        }
        if !applied {
            let mut recovered = engine.resolve_demands();
            if engine.resolve_point_demands() { recovered = true; }
            if engine.resolve_angle_demands() { recovered = true; }
            if !recovered && engine.resolve_target_demands(&target) { recovered = true; }
            if !recovered { break; }
        }
    }

    if solved {
        println!("🎉 名前付き定理の連鎖による証明が見つかりました! (Time: {:.2}s)", start.elapsed().as_secs_f64());
        let proof_text = engine.prover.egraph.generate_proof("Identical", &[a, b]);
        println!("{}", proof_text);
    } else {
        println!("🤷 名前付き定理の連鎖による証明は{}秒以内には見つかりませんでした。ただし数値的には独立な乱数サンプルでの一致という極めて強い根拠(Schwartz-Zippel補題により偶然の確率は約10億分の1)があるため、真である可能性は非常に高い予想です――時間予算(--prove-time)を増やすか、証明ではなく予想として提示するのも一案です。",
            time_budget_secs);
    }
}

/// 🌟 熱量(GeoEntity::heat_with_degree)ランキング。探索が実際に何を
/// 「注目に値する」と判断したかをそのまま可視化する診断出力――ユーザー
/// 要望「熱の分配がどのようなものかを深めてみる」への直接の対応。
fn report_heat_ranking(egraph: &EGraph, top_n: usize) {
    let mut reps: Vec<ClassId> = (0..egraph.entities.len())
        .map(ClassId)
        .filter(|&id| egraph.get_rep(id) == id)
        .collect();
    reps.sort_by(|&a, &b| egraph.entities[b.0].heat_with_degree()
        .partial_cmp(&egraph.entities[a.0].heat_with_degree())
        .unwrap_or(std::cmp::Ordering::Equal));

    println!("\n=== 🌡️  熱量ランキング (上位{}件、探索が「注目」した図形) ===", top_n.min(reps.len()));
    for (i, &id) in reps.iter().take(top_n).enumerate() {
        let e = &egraph.entities[id.0];
        println!("  {:>2}. 熱{:>6.1} (基本{:.1} + 熱{:>5.1} + 次数{:>4.1})  {:<32} {:?}",
            i + 1, e.heat_with_degree(), e.base_importance, e.heat_bonus,
            e.uses.len() as f64 * 0.5, e.name, e.entity_type);
    }
    println!("=============================\n");
}

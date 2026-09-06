mod mmp_math;
mod mmp_core;
mod logic_core;
mod mmp_calculators;
mod mmp_tester;
mod theorems;
mod action_space;
mod mcts;
mod problems;

use mmp_core::EGraph;
use logic_core::{ProverEngine, BlackboardEngine};
use mmp_tester::MMPTester;
use mcts::MCTSSearchEngine;
use std::time::Instant;
use std::env;
use std::fs;

/// 🌟 証明復元(generate_proof)の結果を、コンソールとファイル(result/proof_<問題名>.txt)
/// の両方に出力する。ファイルに残しておくことで、ターミナルのログをスクロールして
/// 探さなくても後から見返せるようにする。
fn output_proof(egraph: &EGraph, problem_name: &str, fact_type: &str, target_args: &[mmp_core::ClassId]) {
    let proof_text = egraph.generate_proof(fact_type, target_args);
    println!("\n{}", proof_text);

    let dir = "result";
    if fs::create_dir_all(dir).is_ok() {
        let path = format!("{}/proof_{}.txt", dir, problem_name);
        match fs::write(&path, &proof_text) {
            Ok(_) => println!("📄 証明を '{}' に保存しました。", path),
            Err(e) => println!("⚠️ 証明ファイルの書き込みに失敗しました ({}): {}", path, e),
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let problem_name = if args.len() > 1 {
        &args[1]
    } else {
        "cyclic_quad" // 引数がない場合のデフォルト
    };
    // 🌟 MCTSはデフォルトでは無効(--mctsで明示的に有効化)。
    // 経緯: MCTSの実験中、propagate_line_uniqueness/propagate_point_uniqueness
    // (「2直線が2点を共有していれば同一とみなす」等の局所ショートカット)が、
    // MCTSの無方向な探索が持ち込む偶然の一致の連鎖によって、本来別々であるべき
    // 直線(例:三角形の辺と、それとは無関係な頂点からの垂線)を誤って同一視して
    // しまうケースが実際に見つかった(orthocenter問題)。証明目標の結論自体が
    // (垂心の存在のように)常に真である定理だと、最終的な数値サニティチェック
    // (tester.sanity_check_identical、下記)だけでは「たまたま正しい値に
    // 一致してしまう」ため検出できなかった。
    // → その後、propagate_line_uniqueness/propagate_point_uniqueness自身に
    // マージ確定前の数値的裏付けチェック(EGraph::numeric_plausibility_check)を
    // 組み込んで根本修正済み(このメソッドが実際に不健全なマージをその場で
    // 却下するので、上記のorthocenter問題は再現しなくなったことをMCTS有効時の
    // 繰り返し実行で確認済み)。それでもなおMCTSをデフォルト無効のままにして
    // いるのは、この安全網が「座標を持たない構造的前提(例: PがこのCircle上に
    // あるとlink_logical_incidenceで直接与えるパターン)にしか依存しない
    // 比較」では判定不能(None)を返して素通りする既知の限界を残しているため、
    // MCTSの無方向な探索がそこを突く可能性を完全には排除できないという
    // 慎重さによるもの。
    let use_mcts = args.iter().any(|a| a == "--mcts");
    // 🌟 探索の時間予算をCLIから調整できるようにする(--time=<秒>)。
    // 既定の12問題はどれも5秒以内に解けるため今まで固定値で十分だったが、
    // nine_point_full のようなより長時間かかる問題を実際に解き切らせて
    // 確認したい場合や、UCB1バンディットの学習(schedule_full_sweepの
    // 呼び出し回数)をより多く積ませて効果を見たい場合に必要になる。
    let time_budget_secs: u64 = args.iter()
        .find_map(|a| a.strip_prefix("--time="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(5);

    println!("🚀 幾何ソルバーを起動します (対象問題: {}, 時間予算: {}秒)", problem_name, time_budget_secs);

    let mut egraph = EGraph::new();
    let tester = MMPTester::new();

    // コマンドライン引数で問題を動的にロード
    let problem = problems::load_problem(problem_name, &mut egraph);

    let mut prover = ProverEngine::new(egraph);
    // 🌟 Rc化: theorems は Vec<Rc<TheoremDef>>。定理は実行中不変なので、
    // ここで一度だけ Rc に包めば、以降の参照はすべてポインタ共有になる。
    prover.theorems = theorems::get_all_theorems().into_iter().map(std::rc::Rc::new).collect();
    let mut engine = BlackboardEngine::new(prover);
    // 🌟 MCTSを再有効化。以前は実際のロールアウト評価をせずスコア固定
    // (=常に1.0)だったが、合同閉包による実際のマージ数と、構造的な
    // ヒューリスティック(次数・作図の種類・目標への近さ)による本物の
    // 報酬関数に置き換えた。DFSマッチャー+需要駆動の補助線(resolve_demands/
    // resolve_angle_demands)の両方が手詰まりになった時の最後の手段としてのみ
    // 使う(まだe-graph全体をcloneする実装のままなので、呼び出し頻度は絞る)。
    let mut mcts = MCTSSearchEngine::new();
    let mut mcts_consecutive_failures = 0;
    const MCTS_MAX_CONSECUTIVE_FAILURES: usize = 3;
    
    for fact in &problem.initial_facts {
        match fact {
            crate::mmp_core::Fact::Identical(id1, id2) => {
                engine.prover.egraph.merge_entities_justified(*id1, *id2, crate::mmp_core::Justification::Given);
                engine.emit(logic_core::Event::NodeMerged);
            },
            crate::mmp_core::Fact::Connected(c, p) => {
                engine.prover.egraph.link_logical_incidence_justified(*c, *p, crate::mmp_core::Justification::Given);
            },
            _ => {}
        }
        engine.emit(logic_core::Event::FactProven(fact.clone()));
    }
    let start_time = Instant::now();

    engine.schedule_full_sweep();

    while start_time.elapsed() < std::time::Duration::from_secs(time_budget_secs) {
        let applied_logic = engine.run_step(10000);

        // 🌟 FIX: & をつけて参照としてパターンマッチし、所有権の移動（move）を防ぐ
        if let Some((fact_type, target_args)) = &problem.target_fact {
            if fact_type == "Identical" {
                let r1 = engine.prover.egraph.get_rep(target_args[0]);
                let r2 = engine.prover.egraph.get_rep(target_args[1]);
                if r1 == r2 {
                    // 🌟 最終防衛ライン: propagate_line_uniqueness/propagate_point_uniqueness の
                    // 「十分な数の接続関係を共有していれば同一とみなす」ショートカットは、
                    // MCTSのような「とりあえず作ってみる」式の構成を大量に試すと、
                    // 噛み合わせの偶然だけで図形全体が退化(例:三角形の3辺が同一直線に潰れる)し、
                    // 目標の等式が「矛盾からは何でも従う」形で偽陽性になることがある
                    // (実際にMCTS導入直後、orthocenterでこれが発生した)。
                    // 座標を持たない有向角(Ang90など)ベースの証明はNone(判定不能)を返すので、
                    // その場合は従来通り構造的な証明をそのまま信用する。
                    match tester.sanity_check_identical(&engine.prover.egraph, target_args[0], target_args[1], 3) {
                        Some(false) => {
                            println!("🚨 [数値サニティチェック失敗] {} ≡ {} は構造的にはマージされましたが、ランダムな具体例では成り立ちません。",
                                engine.prover.egraph.entities[r1.0].name, engine.prover.egraph.entities[r2.0].name);
                            println!("    -> どこかの局所マージ(直線/点の一意性判定)が本来無関係な図形を誤って結合した可能性が高く、証明成立とは認めません。探索を打ち切ります。");
                            break;
                        }
                        _ => {
                            println!("🎉 証明完了！ (Time: {:.2?}s)", start_time.elapsed().as_secs_f64());
                            output_proof(&engine.prover.egraph, problem_name, fact_type, target_args);
                            break;
                        }
                    }
                }
            } else if fact_type == "Concyclic" {
                // 🌟 Concyclicは専用Factをやめたので、target_argsの全点が
                // 共通の円にConnectedかどうかで判定する。
                // 🌟 既知の制約: Identicalと違い、ここには上記の数値サニティチェックを
                // まだ導入していない(「共有する円」を一意に特定してから数値検証する
                // 実装が必要で、今回のスコープでは見送った)。MCTSがConcyclicを目標とする
                // 問題で暴走した場合、同種の偽陽性が起こり得る点に注意。
                let reps: Vec<_> = target_args.iter().map(|&id| engine.prover.egraph.get_rep(id)).collect();
                if engine.prover.egraph.points_share_a_circle(&reps) {
                    println!("🎉 証明完了！ (Time: {:.2?}s)", start_time.elapsed().as_secs_f64());
                    output_proof(&engine.prover.egraph, problem_name, fact_type, target_args);
                    break;
                }
            }
        }

        if !applied_logic {
            println!("⏳ ロジックがStallしました。リカバリーフェーズに移行します...");
            let mut recovered = engine.resolve_demands();
            if engine.resolve_angle_demands() {
                recovered = true;
            }
            if !recovered {
                if !use_mcts {
                    println!("  -> 要求がなく、MCTSも無効(--mctsで有効化できます)なため探索を打ち切ります。");
                    break;
                }
                if mcts_consecutive_failures >= MCTS_MAX_CONSECUTIVE_FAILURES {
                    println!("  -> MCTSも{}回連続で有効な一手を見つけられなかったため、探索を打ち切ります。", MCTS_MAX_CONSECUTIVE_FAILURES);
                    break;
                }
                println!("  -> 需要による補助線がないため、MCTSで補助的な構成を探索します...");
                if mcts.run_step(&mut engine.prover.egraph, &problem.target_fact, 200) {
                    engine.schedule_full_sweep();
                    mcts_consecutive_failures = 0;
                } else {
                    mcts_consecutive_failures += 1;
                    println!("  -> MCTSも有効な一手を見つけられませんでした({}/{})。", mcts_consecutive_failures, MCTS_MAX_CONSECUTIVE_FAILURES);
                }
            }
        }
    }
    engine.prover.egraph.dump_state();
}
mod mmp_math;
mod mmp_core;
mod logic_core;
mod mmp_calculators;
mod mmp_tester;
mod theorems;
mod action_space;
mod mcts;
mod problems;
mod discover;
mod discover_viz;

use mmp_core::{EGraph, RawProof};
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

/// 🌟 raw_proof: EGraphが保持する証明関連情報(union-findの証明の森+
/// incidenceの由来)を一切フィルタせず丸ごとテキストへダンプし、
/// result/raw_proof_<問題名>.txtに保存する。generate_proofと違いこれは
/// 人間が読むためのものではなく、後からextract_proof(RawProof::verify_identical)
/// が独立に読み込んで検証をやり直せるようにするための、Rust側が読み書き
/// しやすい機械可読な完全な記録。実行のたびに(証明が完了したかどうかに
/// 関わらず)必ず書き出す。
fn output_raw_proof(egraph: &EGraph, problem_name: &str) -> String {
    let raw_text = egraph.dump_raw_proof();
    let dir = "result";
    if fs::create_dir_all(dir).is_ok() {
        let path = format!("{}/raw_proof_{}.txt", dir, problem_name);
        match fs::write(&path, &raw_text) {
            Ok(_) => println!("📄 raw_proofを '{}' に保存しました。", path),
            Err(e) => println!("⚠️ raw_proofファイルの書き込みに失敗しました ({}): {}", path, e),
        }
    }
    raw_text
}

/// 🌟 extract_proofの検証結果を出力する。コンソールには短い要約
/// (DeepProof::format_summary、ギャップの有無とresolved_shortcuts件数だけ)を
/// 表示し、result/extracted_proof_<問題名>.txtには「深い証明」全文
/// (DeepProof::format_deep、Theoremの前提やLineUniqueness/PointUniquenessの
/// 共有点の由来まで再帰的に展開した完全な証明)を保存する。コンソールを
/// 深い証明で埋め尽くさないための使い分け(output_proof/output_raw_proofと
/// 同じ「コンソールには要点、ファイルには詳細」の方針)。
///
/// 🌟 ユーザー要望: extracted_proofは「目標から遡って根拠を展開」という
/// 木構造(同じ事実がその場その場で(既出...)として何度も顔を出す)なので、
/// これとは別にresult/compressed_proof_<問題名>.txtへ、(Auto)/(Demand)
/// ラベルを除去し前提→結論の順に並べ替え、重複するステップは参照に
/// 圧縮した版(DeepProof::format_compressed)も併せて保存する。
fn output_extract_report(report: &mmp_core::DeepProof, problem_name: &str) {
    print!("{}", report.format_summary());
    let dir = "result";
    if fs::create_dir_all(dir).is_ok() {
        let path = format!("{}/extracted_proof_{}.txt", dir, problem_name);
        match fs::write(&path, report.format_deep()) {
            Ok(_) => println!("📄 extract_proof(深い証明)を '{}' に保存しました。", path),
            Err(e) => println!("⚠️ extract_proof結果ファイルの書き込みに失敗しました ({}): {}", path, e),
        }
        let compressed_path = format!("{}/compressed_proof_{}.txt", dir, problem_name);
        match fs::write(&compressed_path, report.format_compressed()) {
            Ok(_) => println!("📄 compressed_proof(圧縮された証明)を '{}' に保存しました。", compressed_path),
            Err(e) => println!("⚠️ compressed_proof結果ファイルの書き込みに失敗しました ({}): {}", compressed_path, e),
        }
    }
}

/// 🌟 extract_proof: 保存済みraw_proofテキストを読み込み、指定した2つの
/// 実体(名前で指定)が名前付き定理の連鎖だけで(Theoremの前提も再帰的に)
/// 厳密に合流しているかを検証し、結果を標準出力とファイルの両方へ出力する。
/// ソルバーを再実行せずに済むので、「実際に証明が完了しているか、どこかに
/// 未証明のギャップが眠っているのか」を後から(別プロセスからでも)監査できる。
/// `geom_solver extract-proof <raw_proofファイル> <名前A> <名前B>` で呼ぶ。
fn run_extract_proof(args: &[String]) {
    if args.len() < 5 {
        println!("使い方: geom_solver extract-proof <raw_proofファイル> <名前A> <名前B>");
        return;
    }
    let path = &args[2];
    let name_a = &args[3];
    let name_b = &args[4];
    let text = match fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => { println!("⚠️ '{}' を読み込めませんでした: {}", path, e); return; }
    };
    let raw = RawProof::parse(&text);
    let (Some(a), Some(b)) = (raw.id_of(name_a), raw.id_of(name_b)) else {
        println!("⚠️ '{}' または '{}' という名前の実体がraw_proof中に見つかりませんでした。", name_a, name_b);
        return;
    };
    let report = raw.verify_identical(a, b);
    // 🌟 raw_proofファイル名(result/raw_proof_<問題名>.txt)から問題名を
    // 復元し、対応するresult/extracted_proof_<問題名>.txtに保存する
    // (ファイル名を素直に指定されない限り、main.rs実行時と同じ命名規則で
    // 揃えたいため)。復元できない場合はファイル名全体をそのまま使う。
    let stem = std::path::Path::new(path).file_stem().and_then(|s| s.to_str()).unwrap_or(path);
    let problem_name = stem.strip_prefix("raw_proof_").unwrap_or(stem);
    output_extract_report(&report, problem_name);
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 && args[1] == "extract-proof" {
        run_extract_proof(&args);
        return;
    }
    // 🌟 ユーザー要望:「MCTSと自由作図を通して初等幾何の『綺麗な』問題を
    // 発見する」への対応。証明目標を持つ通常の問題実行とは別の入口として
    // 用意した(discover.rsのドキュメント参照)。
    // 使い方: geom_solver discover [--time=60] [--steps=80] [--sims=150]
    //         [--top=5] [--prove] [--prove-time=15] [--seed-points=3]
    if args.len() > 1 && args[1] == "discover" {
        discover::run(&args);
        return;
    }
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
    // 🌟 HAGeo-409ベンチマーク拡充にあたり、「なぜ解けない/遅いのか」を
    // 事後に切り分けるための診断フラグ。--statsを付けると終了時に
    // UCB1バンディットのtheorem_stats(定理ごとの試行回数・平均報酬)を
    // 試行回数の多い順に一覧表示する。試行回数が多いのに平均報酬が低い
    // 定理は「CPU時間を大量に消費しているのに成果が薄い」ことを示す
    // ので、探索の無駄がどこにあるかを特定する手がかりになる。
    let show_stats = args.iter().any(|a| a == "--stats");
    // 🌟 ユーザー提案(「schedule_full_sweepの改善を続ける」)への対応:
    // 2度の撤回(DefinedBy遅延構築・スケジューラ精密化)がいずれも
    // 「schedule_full_sweepが重いはず」という実測に基づかない推測止まりで
    // 原因を特定できなかった反省から、--profileを付けると終了時に
    // メインループの3大フェーズ(dfs_match本体・回復フェーズ・MCTS)の
    // 壁時計時間の内訳と、schedule_full_sweep自体の呼び出し回数・
    // 所要時間・作り直したシードなしタスク数を表示する
    // (ProverEngine::ProfileStatsのドキュメント参照)。
    let show_profile = args.iter().any(|a| a == "--profile");
    // 🌟 探索の時間予算をCLIから調整できるようにする(--time=<秒>)。
    // 既定の12問題はどれも5秒以内に解けるため今まで固定値で十分だったが、
    // nine_point_full のようなより長時間かかる問題を実際に解き切らせて
    // 確認したい場合や、UCB1バンディットの学習(schedule_full_sweepの
    // 呼び出し回数)をより多く積ませて効果を見たい場合に必要になる。
    let time_budget_secs: u64 = args.iter()
        .find_map(|a| a.strip_prefix("--time="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(5);
    // 🌟 UCB1バンディットの効果測定用A/Bスイッチ。--no-banditを付けると
    // schedule_full_sweepのシードなしタスクの優先度を常に0固定にし、
    // バンディット導入前と同じ挙動に戻す。既定はバンディット有効。
    let bandit_enabled = !args.iter().any(|a| a == "--no-bandit");
    // 🌟 MCTSの目標指向ヒューリスティック(action_space.rsのget_possible_actions
    // が候補の点・直線をサンプリングする際、証明目標に構造的に近い図形を
    // 優先する)の効果測定用A/Bスイッチ。--no-mcts-target-biasを付けると
    // 導入前の「entity_weightのみによる完全に目標非依存なサンプリング」に
    // 戻す。既定は有効。
    let mcts_target_bias_enabled = !args.iter().any(|a| a == "--no-mcts-target-bias");

    println!("🚀 幾何ソルバーを起動します (対象問題: {}, 時間予算: {}秒, UCB1バンディット: {}, MCTS目標バイアス: {})",
        problem_name, time_budget_secs,
        if bandit_enabled { "有効" } else { "無効" },
        if mcts_target_bias_enabled { "有効" } else { "無効" });

    let mut egraph = EGraph::new();
    let tester = MMPTester::new();

    // コマンドライン引数で問題を動的にロード
    let problem = problems::load_problem(problem_name, &mut egraph);

    let mut prover = ProverEngine::new(egraph);
    // 🌟 Rc化: theorems は Vec<Rc<TheoremDef>>。定理は実行中不変なので、
    // ここで一度だけ Rc に包めば、以降の参照はすべてポインタ共有になる。
    let mut all_theorems = theorems::get_all_theorems();
    // 🌟 複比の透視射影不変性/シュタイナーの定理群(get_projective_theorems)は
    // 「点→線束→点」の2定理分解によりシード自体は軽くなったが、その後
    // シュタイナー系3定理(順方向・接線版・逆)が追加されたことで、実際には
    // 依然として全問題共通のデフォルト集合に混ぜると無視できないコストに
    // なっていた。ユーザー指示(「射影幾何のタスクを一旦無視して最適化した
    // らどうなるか」)に基づき実測した結果、この5定理を全問題共通から
    // 外すだけで、bench_2011armog10p6・bench_2010g1・nine_point_full・
    // orthocenter・orthocenter_alt・miquel_quadrilateralが軒並み(3回集計で
    // 一度も落ちない)安定してパスするようになった――つまりこれらの問題は
    // この5定理を全く必要としておらず、単に探索予算を奪われて不安定に
    // なっていただけだった。この5定理を本当に必要とするのは、それ自体を
    // 検証するために書かれたtest_*問題(cross_ratio/steiner/involution系)
    // だけなので、opt-in(元々の設計方針に戻す)にする: 問題名で判定し、
    // 該当する場合だけ追加する。
    let needs_projective_theorems = matches!(problem_name,
        "test_cross_ratio" | "test_steiner" | "test_steiner_tangent"
        | "test_involution" | "test_steiner_converse");
    if needs_projective_theorems {
        all_theorems.extend(theorems::get_projective_theorems());
    }
    prover.theorems = all_theorems.into_iter().map(std::rc::Rc::new).collect();
    let mut engine = BlackboardEngine::new(prover);
    engine.bandit_enabled = bandit_enabled;
    // 🌟 MCTSを再有効化。以前は実際のロールアウト評価をせずスコア固定
    // (=常に1.0)だったが、合同閉包による実際のマージ数と、構造的な
    // ヒューリスティック(次数・作図の種類・目標への近さ)による本物の
    // 報酬関数に置き換えた。DFSマッチャー+需要駆動の補助線(resolve_demands/
    // resolve_angle_demands)の両方が手詰まりになった時の最後の手段としてのみ
    // 使う(まだe-graph全体をcloneする実装のままなので、呼び出し頻度は絞る)。
    let mut mcts = MCTSSearchEngine::new();
    mcts.target_bias_enabled = mcts_target_bias_enabled;
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
    // 🌟 目標が数値ショートカットのみの経路で到達された場合、登録(🎉)を拒否して
    // 探索を継続する(下記)が、union-findは既に統合済みで巻き戻らないため
    // 同じ理由で毎ループ再検出してしまう。通知の重複を防ぐためのフラグ。
    let mut shortcut_target_noted = false;
    // 🌟 MCTSがこの実行で実際に少なくとも1手を採用したか。この後で説明する
    // 「数値ショートカットのみの経路は登録を拒否する」ポリシーを、MCTSが
    // 一度も使われていない実行(=circumcenterのような従来通りのDFSのみの
    // 実行)には適用しないためのフラグ。
    let mut mcts_ever_committed = false;

    engine.schedule_full_sweep();

    while start_time.elapsed() < std::time::Duration::from_secs(time_budget_secs) {
        // 🌟 ProverEngine::ProfileStatsのドキュメント参照: メインループの
        // 3大フェーズ(dfs_match本体・回復フェーズ・MCTS)それぞれに
        // 実際どれだけの壁時計時間が使われているかを計測する。
        // --profileでこの内訳を終了時に表示し、schedule_full_sweep周りを
        // 今後改善する際の実測の土台にする。
        let run_step_start = std::time::Instant::now();
        let applied_logic = engine.run_step(10000);
        engine.prover.profile.run_step_time += run_step_start.elapsed();

        // 🌟 数値評価が偶然の一致(予想候補)を検出していれば、使い捨てクローン
        // 上での価値推定を経てheat_bonusにフィードバックする(現実の証明状態は
        // 一切変更しない)。呼び出しごとに未評価の予想を最大3件だけ処理するので
        // (BlackboardEngine::process_pending_conjectures参照)、コストは
        // ループの他の処理に対して無視できる程度に収まる。
        engine.process_pending_conjectures(&problem.target_fact);

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
                            // 🌟 数値サニティチェックはあくまで最終的な等式そのものの
                            // 妥当性(=偽陽性でないか)を見るだけで、そこに至る経路の
                            // 「厳密さ」までは保証しない。経路上にLineUniqueness/
                            // PointUniqueness局所伝播ショートカット(数値サンプリング
                            // だけが根拠であり、名前付き定理を前提から結論へ連鎖させる
                            // 形式的な演繹ではない)が含まれることがある。
                            //
                            // 🐛 FIX: 当初は「経路にこのショートカットが含まれる場合は
                            // 一律に登録を拒否する」実装にしたが、circumcenter(MCTS無し、
                            // 常に解ける問題)ですら、実際にはこの経路を(既に他の定理で
                            // 厳密に確立済みの接続関係から)ごく普通に、正しく使っていた
                            // ことが判明した(回帰テストで発覚)。ショートカット自体は
                            // 危険なのではなく、「MCTSの無方向な探索が、根拠の薄い
                            // 偶然の接続関係を大量に積み重ねた末にこれを踏み抜く」
                            // ケースだけが危険。そこでMCTSがこの実行で実際に少なくとも
                            // 1手を採用した後(mcts_ever_committed)にだけ、この
                            // ショートカットを理由に登録を拒否しconjectureとして扱う
                            // (ユーザー要望)。MCTSが一度も使われていない(=circumcenterの
                            // ような従来通りのDFSのみの)実行では、これまで通り無条件に
                            // 受理する。union-find自体はもう統合されており安価に
                            // 巻き戻せないため、「勝利条件として認めない」という形の
                            // 拒否になる: 🎉もoutput_proofも出さずbreakせず、探索を
                            // 継続する。同じ理由での重複通知を防ぐため、この
                            // (fact_type, target_args)の組については初回だけ通知する。
                            let uses_shortcut = mcts_ever_committed && {
                                let edges = engine.prover.egraph.explain_identical(target_args[0], target_args[1]);
                                EGraph::proof_uses_numeric_shortcut(&edges)
                            };
                            if uses_shortcut {
                                if !shortcut_target_noted {
                                    println!("🔮 [目標到達を却下・予想として記録] {} ≡ {} は構造的には統合されましたが、経路に数値的検証のみに基づく局所ショートカットが含まれ、かつMCTSがこの実行で構成に関与しているため、証明成立とは認めません。",
                                        engine.prover.egraph.entities[r1.0].name, engine.prover.egraph.entities[r2.0].name);
                                    println!("    -> 名前付き定理の連鎖による厳密な経路が別に見つかるまで、これは(反例が出なかったという意味で強い根拠のある)予想として扱い、探索を継続します。");
                                    shortcut_target_noted = true;
                                }
                            } else {
                                println!("🎉 証明完了！ (Time: {:.2?}s)", start_time.elapsed().as_secs_f64());
                                output_proof(&engine.prover.egraph, problem_name, fact_type, target_args);
                                // 🌟 raw_proofを出力し、そのテキストを(実行中のEGraphの
                                // 状態からではなく)独立に読み込み直してextract_proofの
                                // 検証をやり直す。uses_shortcutの判定は目標そのものの
                                // 直接のマージ経路(explain_identicalの最上位の辺)しか
                                // 見ていないため、Theoremの前提が再帰的に別のショート
                                // カットへ依存しているケース(circumcenterの調査で実在が
                                // 判明)を見逃しうる――ここではraw_proofに記録された
                                // Theoremのpremisesまで再帰的に遡って検証することで、
                                // 「本当に最初から最後まで名前付き定理の連鎖だけで
                                // 繋がっているか」をより深く監査する。
                                let raw_text = output_raw_proof(&engine.prover.egraph, problem_name);
                                let raw = RawProof::parse(&raw_text);
                                let report = raw.verify_identical(target_args[0].0, target_args[1].0);
                                output_extract_report(&report, problem_name);
                                break;
                            }
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
            } else if fact_type == "Connected" {
                // 🌟 「シュタイナーの定理の逆」のように、結論がConnected(点,二次曲線)
                // であるような定理を直接目標にできるようにする(Concyclicが
                // Circle専用なのに対し、こちらはis_connectedが対応する任意の型に
                // 使える汎用版)。Concyclicと同じくMCTSの数値サニティチェックは
                // まだ導入していない。
                let r1 = engine.prover.egraph.get_rep(target_args[0]);
                let r2 = engine.prover.egraph.get_rep(target_args[1]);
                if engine.prover.egraph.is_connected(r1, r2) {
                    println!("🎉 証明完了！ (Time: {:.2?}s)", start_time.elapsed().as_secs_f64());
                    output_proof(&engine.prover.egraph, problem_name, fact_type, target_args);
                    break;
                }
            }
        }

        if !applied_logic {
            println!("⏳ ロジックがStallしました。リカバリーフェーズに移行します...");
            let recovery_start = std::time::Instant::now();
            let mut recovered = engine.resolve_demands();
            if engine.resolve_point_demands() {
                recovered = true;
            }
            if engine.resolve_angle_demands() {
                recovered = true;
            }
            // 🌟 最後の砦(MCTSに頼る直前): 証明目標に現れる点同士でまだ
            // 直線が引かれていないペアに補助線を引いてみる
            // (BlackboardEngine::resolve_target_demandsのドキュメント参照)。
            if !recovered && engine.resolve_target_demands(&problem.target_fact) {
                recovered = true;
            }
            engine.prover.profile.recovery_time += recovery_start.elapsed();
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
                let mcts_start = std::time::Instant::now();
                let mcts_found = mcts.run_step(&mut engine.prover.egraph, &problem.target_fact, 200);
                engine.prover.profile.mcts_time += mcts_start.elapsed();
                if mcts_found {
                    engine.schedule_full_sweep();
                    mcts_consecutive_failures = 0;
                    mcts_ever_committed = true;
                } else {
                    mcts_consecutive_failures += 1;
                    println!("  -> MCTSも有効な一手を見つけられませんでした({}/{})。", mcts_consecutive_failures, MCTS_MAX_CONSECUTIVE_FAILURES);
                }
            }
        }
    }
    // 🌟 ループが🎉に到達せず終わった(タイムアウト/Stall/ショートカット拒否の
    // まま)場合でも、raw_proofは「全てのマージ履歴を記録」する無条件の
    // 出力なので必ず書き出す(成功時は既に上で書き出し済みだが、その後に
    // 状態が変わっていないので上書きは無害)。後からextract_proofで
    // (どこまで進んで、どこで止まったかを含め)監査できるようにするため。
    output_raw_proof(&engine.prover.egraph, problem_name);
    engine.prover.egraph.dump_state();

    if show_stats {
        println!("\n=== 📊 定理ごとのUCB1統計 (試行回数の多い順、上位20件) ===");
        // 🌟 cap_hits(dfs_capにほぼ到達した試行の回数)も併記する。
        // --profileが「dfs_match本体が壁時計時間の大半を占める」ことを
        // 示した後の自然な追跡調査: attempts列だけでは分からない
        // 「1回あたりどれだけ高くついたか」を可視化する。
        // 🌟 Simsonクラスの問題を1秒未満で解く目標のための追跡調査:
        // cap_hitsだけでは「上限未満だが毎回数千〜数万call消費する」定理を
        // 名指しできないため、平均dfs_call消費量(total_dfs_calls/attempts)で
        // 降順ソートする(cap_hits→attemptsのソートから変更)。これにより
        // 「壁時計時間を実際に一番食っている定理」がそのまま上位に来る。
        let mut rows: Vec<(String, u64, u64, u64, f64)> = engine.prover.theorem_stats.iter().enumerate()
            .filter(|(_, s)| s.attempts > 0)
            .map(|(idx, s)| (engine.prover.theorems[idx].name.clone(), s.attempts, s.cap_hits, s.total_dfs_calls, s.total_reward / s.attempts as f64))
            .collect();
        // 整数除算での丸め誤差を避けるため、平均同士の比較を交差乗算で行う
        // (avg(b) vs avg(a) を b.3*a.1 vs a.3*b.1 の比較に置き換え、降順ソート)。
        rows.sort_by(|a, b| (b.3 as u128 * a.1 as u128).cmp(&(a.3 as u128 * b.1 as u128)));
        for (name, attempts, cap_hits, total_dfs_calls, avg_reward) in rows.iter().take(20) {
            let avg_dfs = *total_dfs_calls as f64 / *attempts as f64;
            println!("  {:>6}回試行 (うちcap到達{:>3}回) / 平均dfs_call {:>9.0} / 平均報酬 {:>+6.3} : {}", attempts, cap_hits, avg_dfs, avg_reward, name);
        }
        println!("=============================\n");
    }

    if show_profile {
        let p = &engine.prover.profile;
        let total = start_time.elapsed();
        let accounted = p.run_step_time + p.recovery_time + p.mcts_time;
        let pct = |d: std::time::Duration| -> f64 {
            if total.as_secs_f64() > 0.0 { 100.0 * d.as_secs_f64() / total.as_secs_f64() } else { 0.0 }
        };
        println!("\n=== ⏱️  実行時間の内訳 (--profile) ===");
        println!("  合計実行時間          : {:>7.2}s", total.as_secs_f64());
        println!("  ├─ dfs_match本体      : {:>7.2}s ({:>5.1}%)", p.run_step_time.as_secs_f64(), pct(p.run_step_time));
        println!("  ├─ 回復フェーズ       : {:>7.2}s ({:>5.1}%)", p.recovery_time.as_secs_f64(), pct(p.recovery_time));
        println!("  ├─ MCTS               : {:>7.2}s ({:>5.1}%)", p.mcts_time.as_secs_f64(), pct(p.mcts_time));
        println!("  └─ 未計測(数値検証等) : {:>7.2}s ({:>5.1}%)",
            (total.saturating_sub(accounted)).as_secs_f64(), pct(total.saturating_sub(accounted)));
        println!("  --- schedule_full_sweep自体の内訳 ---");
        println!("  呼び出し回数          : {}", p.sfs_calls);
        println!("  累計所要時間          : {:.3}s ({:.1}% of 合計)", p.sfs_time.as_secs_f64(), pct(p.sfs_time));
        println!("  作成したシードなしタスク数 : {} (呼び出し1回あたり平均 {:.1}個)",
            p.sfs_tasks_created,
            if p.sfs_calls > 0 { p.sfs_tasks_created as f64 / p.sfs_calls as f64 } else { 0.0 });
        println!("  --- タスクポップ数とdfs_call消費量の内訳(シード有無別) ---");
        let total_calls = p.seeded_dfs_calls + p.unseeded_dfs_calls;
        let calls_pct = |c: u64| -> f64 { if total_calls > 0 { 100.0 * c as f64 / total_calls as f64 } else { 0.0 } };
        println!("  シード済みタスク      : {:>8}回ポップ / dfs_call計 {:>10} ({:>5.1}%)",
            p.seeded_pops, p.seeded_dfs_calls, calls_pct(p.seeded_dfs_calls));
        println!("  シードなしタスク      : {:>8}回ポップ / dfs_call計 {:>10} ({:>5.1}%)",
            p.unseeded_pops, p.unseeded_dfs_calls, calls_pct(p.unseeded_dfs_calls));
        println!("=============================\n");
    }
}
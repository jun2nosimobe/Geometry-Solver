//! 🌟 discover: 証明目標を持たない自由探索で、初等幾何の「綺麗な」関係を発見する(証明はできれば)。
//!   1. 種配置(既定は汎用三角形。--preset で問題の配置を再利用)から、MCTS に target=None のまま補助構成を
//!      積ませる。報酬は「合同閉包で同値類が何件減ったか」と構成された図形の構造的な面白さだけになる。
//!   2. 数値評価が「記号的には別物の2つの図形が乱数座標で一致した」ことを予想(EGraph::conjectures)として
//!      記録する既存の仕組みを、目標なしの探索の上で走らせる。
//!   3. 探索後、予想や総当たり検出(report_sweep_discoveries)の結果を「美しさ」で順位付けし、構成手順と
//!      ともに提示する(図は discover_viz で HTML に書き出す)。
//!   4. --prove 指定時だけ、最上位の予想を定理探索エンジン(MCTS なし)で証明してみる。
//!   5. 熱量(heat_with_degree)のランキングも表示し、探索が何を注目に値すると判断したかを見られるようにする。
//! --probe 指定時だけ、各予想を仮定したクローン上で定理を走らせ、そこから導かれる等式を「条件付きの」予想として
//! 追加する(probe_and_expand_conjectures)。自由度を1つ落として何かを導くことになるので既定では無効。

use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};
use crate::logic_core::{ProverEngine, BlackboardEngine};
use crate::mcts::MCTSSearchEngine;
use crate::theorems;
use std::time::{Duration, Instant};

/// 🌟 --preset=all で順番に走らせる古典的な配置。単体検証用の test_* と重い bench_* を除いた名前付きの問題に、
/// triangle_centers(三角形+外心+垂心+重心+九点円中心)を加えたもの。
pub const CLASSIC_PRESETS: &[&str] = &[
    "triangle_centers", "cyclic_quad", "varignon", "tangent_orthic", "miquel",
    "nine_point", "nine_point_full", "miquel_quadrilateral", "simson",
    "orthocenter", "orthocenter_alt", "circumcenter", "thales",
    "two_circles_reim", "orthic_incenter",
];

/// 🌟 新設のプリセット。既存31問題はどれも「1つの特定の古典的命題」を
/// 狙って作られており、"複数の中心が同時に絡む一般的な遊び場"という
/// 種配置が無かった。三角形の外心・垂心・重心・九点円中心を最初から
/// 全部揃えておけば、MCTSが基礎的な足場作りに予算を使い切る前に、
/// 名前付きの中心同士の関係(オイラー線の共線性等)を自由に組み合わせる
/// 段階へすぐ到達できる。
fn setup_triangle_centers(egraph: &mut EGraph) {
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let o = crate::problems::geo_helpers::circumcenter(egraph, a, b, c, "O");

    let bc = egraph.create_entity("BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let ca = egraph.create_entity("CA".to_string(), Definition::new_line(c, a), EntityType::Line);
    let alt_a = egraph.create_entity("Alt_A".to_string(), Definition::PerpendicularLine(bc, a), EntityType::Line);
    let alt_b = egraph.create_entity("Alt_B".to_string(), Definition::PerpendicularLine(ca, b), EntityType::Line);
    let h = egraph.create_entity("H".to_string(), Definition::Intersection(alt_a, alt_b), EntityType::Point);

    let mid_bc = egraph.create_entity("Mid_BC".to_string(), Definition::Midpoint(b, c), EntityType::Point);
    let mid_ca = egraph.create_entity("Mid_CA".to_string(), Definition::Midpoint(c, a), EntityType::Point);
    let med_a = egraph.create_entity("Med_A".to_string(), Definition::new_line(a, mid_bc), EntityType::Line);
    let med_b = egraph.create_entity("Med_B".to_string(), Definition::new_line(b, mid_ca), EntityType::Line);
    let g = egraph.create_entity("G".to_string(), Definition::Intersection(med_a, med_b), EntityType::Point);

    // 九点円中心 = 外心と垂心の中点(古典的な事実として構成に組み込む――
    // これ自体を"発見"させたいわけではなく、この点を足場にした先の
    // 探索を豊かにするのが狙い)。
    egraph.create_entity("N".to_string(), Definition::Midpoint(o, h), EntityType::Point);
    let _ = g;
}

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
    // 🌟 仮説駆動プロービングは「自由度を1つ強制的に落として何が従うか見る」仕組みで、無関係な2自由点の一致のような
    // 見せかけの発見を生みやすいので、--probe を付けたときだけ有効にする。
    let use_probe = args.iter().any(|a| a == "--probe");
    let probe_dfs_budget: usize = args.iter()
        .find_map(|a| a.strip_prefix("--probe-dfs-budget="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(3000);
    let probe_rounds: usize = args.iter()
        .find_map(|a| a.strip_prefix("--probe-rounds="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(5);
    // 🌟 --preset=<問題名>: 問題ファイルの配置(initial_facts)を種として再利用する(target_fact は使わない)。
    // 裸の自由点から始めると予算の大半が基礎的な足場作りに消えるため。--preset=all で CLASSIC_PRESETS をまとめて、
    // --preset=名前1,名前2 で任意の組み合わせを試せる。
    // 🌟 総当たり検出(report_sweep_discoveries)の候補数の上限。探索が進むと実体が増えるので、小さいと肝心の
    // 古典的な点(外心・垂心・重心など)が候補から押し出される。
    let sweep_pts: usize = args.iter()
        .find_map(|a| a.strip_prefix("--sweep-points="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(48);
    let sweep_lines: usize = args.iter()
        .find_map(|a| a.strip_prefix("--sweep-lines="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(36);
    let preset: Option<&str> = args.iter()
        .find_map(|a| a.strip_prefix("--preset="));
    let seed_names: Vec<String> = match preset {
        Some("all") => CLASSIC_PRESETS.iter().map(|s| s.to_string()).collect(),
        Some(list) => list.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect(),
        None => Vec::new(),
    };

    println!("🔭 自由作図による「綺麗な問題」発見モードを開始します (種配置: {}, ステップ上限: {}, 時間予算(種配置ごと): {}秒, 1ステップあたりのMCTSシミュレーション: {}回, 仮説駆動プロービング: {})",
        if seed_names.is_empty() { format!("自由点{}個", seed_points) } else { format!("{}個のプリセット [{}]", seed_names.len(), seed_names.join(", ")) },
        max_steps, time_budget_secs, sims_per_step, if use_probe { "有効" } else { "無効" });

    let mut all_sections: Vec<String> = Vec::new();
    if seed_names.is_empty() {
        let mut egraph = EGraph::new();
        let names = ["A", "B", "C", "D", "E", "F", "G", "H"];
        for i in 0..seed_points {
            let name = names.get(i).map(|s| s.to_string()).unwrap_or_else(|| format!("P{}", i));
            egraph.create_entity(name, Definition::FreePoint, EntityType::Point);
        }
        egraph.apply_congruence_closure();
        let label = format!("自由点{}個", seed_points);
        let sections = run_one_seed(&label, egraph, sweep_pts, sweep_lines, max_steps, sims_per_step, time_budget_secs,
            use_probe, probe_dfs_budget, probe_rounds, top_n, try_prove, prove_time_secs);
        all_sections.extend(sections);
    } else {
        for name in &seed_names {
            println!("\n########## 種配置: {} ##########", name);
            let mut egraph = EGraph::new();
            if name == "triangle_centers" {
                setup_triangle_centers(&mut egraph);
            } else {
                let problem = crate::problems::load_problem(name, &mut egraph);
                for fact in &problem.initial_facts {
                    match fact {
                        crate::mmp_core::Fact::Identical(id1, id2) => {
                            egraph.merge_entities_justified(*id1, *id2, crate::mmp_core::Justification::Given);
                        }
                        crate::mmp_core::Fact::Connected(c, p) => {
                            egraph.link_logical_incidence_justified(*c, *p, crate::mmp_core::Justification::Given);
                        }
                    }
                }
            }
            egraph.apply_congruence_closure();
            let sections = run_one_seed(name, egraph, sweep_pts, sweep_lines, max_steps, sims_per_step, time_budget_secs,
                use_probe, probe_dfs_budget, probe_rounds, top_n, try_prove, prove_time_secs);
            all_sections.extend(sections);
        }
    }
    write_discover_report_html(&all_sections);
}

/// 🌟 1つの種配置(自由点N個、または--presetで読み込んだ配置)について、
/// 自由構築→(任意で)仮説駆動プロービング→報告、までの一連の流れを行う。
/// --preset=allのように複数の種配置を1回の実行でまとめて試せるように
/// run()から切り出した。戻り値はHTML報告の断片(seed_labelの見出し付き)。
#[allow(clippy::too_many_arguments)]
fn run_one_seed(
    seed_label: &str,
    mut egraph: EGraph,
    sweep_pts: usize,
    sweep_lines: usize,
    max_steps: usize,
    sims_per_step: usize,
    time_budget_secs: u64,
    use_probe: bool,
    probe_dfs_budget: usize,
    probe_rounds: usize,
    top_n: usize,
    try_prove: bool,
    prove_time_secs: u64,
) -> Vec<String> {
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
    // 🌟 誤マージの原因調査用(--audit)。毎ステップ後に e-graph が主張している接続が数値評価と整合しているかを確かめ、
    // 最初に壊れたステップ・該当する接続・その根拠・関係する全マージの理由をまとめて出力する。
    let audit = crate::cli::audit();
    // 🌟 --systematic: MCTSの代わりに決定的な幅優先の作図閉包を使う
    // (systematic_closureのドキュメント参照)。
    if let Some(spec) = crate::cli::systematic() {
        let mut it = spec.split(',').filter_map(|v| v.trim().parse::<usize>().ok());
        let rounds = it.next().unwrap_or(2);
        let cap = it.next().unwrap_or(220);
        let per_kind = it.next().unwrap_or(9);
        systematic_closure(&mut egraph, rounds, cap, per_kind);
        steps_done = rounds;
    }
    while crate::cli::systematic().is_none()
        && start.elapsed() < Duration::from_secs(time_budget_secs) && steps_done < max_steps {
        let found = mcts.run_step(&mut egraph, &None, sims_per_step);
        steps_done += 1;
        if audit
            && let Some((bad_p, bad_l)) = crate::padic_eval::find_incidence_inconsistency(&egraph, 0xC0FFEE) {
                let mut namer = PrettyNamer::new();
                println!("\n🔬 [監査] ステップ{}でe-graphが幾何と矛盾しました: 「{} は {} 上にある」が数値的に成り立ちません。",
                    steps_done, namer.label(&egraph, bad_p), namer.label(&egraph, bad_l));
                if let Some((op, ol, just)) = egraph.find_incidence_justification(bad_p, bad_l) {
                    println!("   接続の根拠: {} ∈ {} は {:?}", 
                        egraph.entities[op.0].original_name, egraph.entities[ol.0].original_name, just);
                } else {
                    println!("   接続の根拠: (incidence_provenanceに記録なし=作図由来の構造的リンク)");
                }
                for (label, target) in [("点", bad_p), ("直線", bad_l)] {
                    let rep = egraph.get_rep(target);
                    println!("   {}側の同値類に流れ込んだマージ:", label);
                    let mut n = 0;
                    for (&slot, edge) in &egraph.proof_edges {
                        if egraph.get_rep(ClassId(slot)) != rep { continue; }
                        println!("     {} ≡ {} (理由: {:?})",
                            egraph.entities[edge.from.0].original_name,
                            egraph.entities[edge.to.0].original_name, edge.justification);
                        n += 1;
                        if n >= 12 { println!("     ..."); break; }
                    }
                    if n == 0 { println!("     (なし)"); }
                }
                break;
            }
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
    println!("\n🔭 [{}] 探索終了 ({}ステップ、{:.1}秒経過)。アクティブな同値類数: {}",
        seed_label, steps_done, start.elapsed().as_secs_f64(), egraph.count_active_classes());

    // 🌟 ここから先は定理探索エンジン(schedule_full_sweep/dfs_match)を使うため、
    // egraphの所有権をBlackboardEngineへ渡す。
    let mut engine = build_full_engine(egraph);
    if use_probe {
        probe_and_expand_conjectures(&mut engine, probe_dfs_budget, probe_rounds);
    }

    // 🌟 新設: 全対比較による一致・共線性の総当たり検出(report_sweep_discoveries
    // のドキュメント参照)。従来のreport_conjecturesは「作図が退化した時」しか
    // 拾えなかったため、実測で報告0件が続いていた。
    report_sweep_discoveries(&mut engine.prover.egraph, top_n, sweep_pts, sweep_lines);

    let sections = report_conjectures(&mut engine.prover.egraph, top_n, try_prove, prove_time_secs);
    report_heat_ranking(&engine.prover.egraph, 10);
    if sections.is_empty() { return Vec::new(); }
    vec![format!("<h2 style=\"font:600 18px sans-serif;margin:32px 0 4px;\">🔭 種配置: {}</h2>\n{}",
        xml_escape_html(seed_label), sections.join("\n"))]
}

/// 🌟 仮説駆動プロービングと --prove の証明試行が使う、全定理を登録した BlackboardEngine を組み立てる
/// (solve.rs の既定と同じく get_all_theorems + get_projective_theorems)。
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

/// 🌟 蓄積された予想それぞれに BlackboardEngine::probe_conjecture を1回適用し、「その予想を仮定するとさらに導かれる」
/// 等式を条件付きの予想として同じ conjectures マップに追加する。連鎖は1段だけ(再帰的な深追いは組み合わせ爆発する)。
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
        // 🌟 report_conjectures と同じく、構造的に退化した祖先を持つ予想はプロービングしない(無駄なうえ、退化した前提は
        // 全体崩壊の火種になる)。
        if has_degenerate_ancestor(&engine.prover.egraph, a, b) { continue; }
        let name_a = engine.prover.egraph.entities[engine.prover.egraph.get_rep(a).0].name.clone();
        let name_b = engine.prover.egraph.entities[engine.prover.egraph.get_rep(b).0].name.clone();
        // 🐛 ある前提を仮定した結果、グラフの大部分が1つの同値類へ潰れる「全体崩壊」が起きたら、その前提からの伝播は
        // 丸ごと捨てる。崩壊は前提が破綻している兆候で、そこから出るペア(無関係な自由点どうしの一致など)は発見ではない。
        let classes_before = engine.prover.egraph.count_active_classes();
        let discovered = engine.probe_conjecture(a, b, dfs_budget, sweep_rounds);
        const COLLAPSE_SUSPECT_RATIO: f64 = 0.2;
        let collapse_ratio = if classes_before > 0 { discovered.len() as f64 / classes_before as f64 } else { 0.0 };
        if collapse_ratio >= COLLAPSE_SUSPECT_RATIO {
            println!("  🚨 {} ≡ {} を仮定すると、{}件(仮定前の同値類{}件中、比率{:.0}%)もの実体が一斉に統合される全体崩壊が起きました。前提自体が既に破綻している可能性が高いため、この連鎖からの個別の\"発見\"は報告しません。",
                name_a, name_b, discovered.len(), classes_before, collapse_ratio * 100.0);
            continue;
        }
        if !discovered.is_empty() {
            println!("  🧪 {} ≡ {} を仮定すると、定理の連鎖により{}件の別の等式が追加で導かれました。",
                name_a, name_b, discovered.len());
        }
        for (x, y) in discovered {
            if x == y { continue; }
            // 仮説のテキストに実体名は埋め込まない(自動生成名は数百文字になり、報告側で付け替え名を使っても読めないまま残る)。
            // 条件付きの発見であることと、親の仮説だけを残す。
            let hypothesis = format!("[定理連鎖] 他の予想(仮説: {})を仮定すると導かれる", parent_hypothesis);
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
    construction_steps: usize,
    beauty: f64,
}

/// 🌟 報告の表示専用に、自由点・定数以外の実体へ型ごとの短い付け替え名(P1, L1, D1, Ang1, S1, C1...)を割り当てる。
/// 自動生成名は親の名前を連結するので数段で数百文字になる。証明や union-find には使わない。
struct PrettyNamer {
    labels: rustc_hash::FxHashMap<ClassId, String>,
    // 🌟 有限点(P)と無限遠点(D)は型では分からないので、判定した接頭辞そのものをキーに数える。
    counters: rustc_hash::FxHashMap<&'static str, usize>,
}

impl PrettyNamer {
    fn new() -> Self {
        Self { labels: rustc_hash::FxHashMap::default(), counters: rustc_hash::FxHashMap::default() }
    }

    fn label(&mut self, egraph: &EGraph, id: ClassId) -> String {
        let rep = egraph.get_rep(id);
        if let Some(l) = self.labels.get(&rep) { return l.clone(); }
        let e = &egraph.entities[rep.0];
        // 名前が既に短い(自動生成のタグ "_(" を含まない)実体だけを素通りさせる。調和共役の作図の補助点のように、
        // 定義は FreePoint でも名前が長い実体があるので、定義の種類では判定しない。
        let label = if !e.name.contains("_(") {
            e.name.clone()
        } else {
            // 🌟 接頭辞は型ではなく構造で決める: 無限遠直線に乗る点は D、円周点 I,J を両方通る二次曲線は Cir、それ以外の
            // 二次曲線は Q、AnglePair で作られた Scalar は Ang(表示専用なので original_definition だけで判定する)。
            let prefix: &'static str = if e.entity_type == EntityType::Point
                && egraph.is_connected(rep, egraph.line_infinity) {
                "D"
            } else if e.entity_type == EntityType::Conic
                && egraph.is_connected(rep, egraph.circ_i) && egraph.is_connected(rep, egraph.circ_j) {
                "Cir"
            } else if e.entity_type == EntityType::Scalar
                && matches!(e.original_definition, Definition::AnglePair(_, _)) {
                "Ang"
            } else {
                match e.entity_type {
                    EntityType::Point => "P",
                    EntityType::Line => "L",
                    EntityType::Conic => "Q",
                    EntityType::Scalar => "S",
                }
            };
            let n = self.counters.entry(prefix).or_insert(0);
            *n += 1;
            format!("{}{}", prefix, n)
        };
        self.labels.insert(rep, label.clone());
        label
    }
}

/// 🌟 探索中に蓄積されたEGraph::conjectures(数値的な偶然の一致候補)を
/// 「美しさ」スコアで順位付けして表示する。
fn report_conjectures(egraph: &mut EGraph, top_n: usize, try_prove: bool, prove_time_secs: u64) -> Vec<String> {
    let entries: Vec<((usize, usize), String, u32)> = {
        let map = egraph.conjectures.borrow();
        map.iter().map(|(&k, e)| (k, e.hypothesis.clone(), e.occurrences)).collect()
    };
    if entries.is_empty() {
        println!("\n😶 探索中に数値的な偶然の一致は見つかりませんでした。この乱数試行・この配置では、まだ知られていない関係を検出できませんでした(ステップ数や1ステップあたりのシミュレーション回数を増やすと見つかりやすくなります)。");
        return Vec::new();
    }

    let total_entries = entries.len();
    // 🌟 「全体崩壊」除外ルール(probe_and_expand_conjecturesと同じ閾値・
    // 同じ理由)をここでも適用する。estimate_conjecture_value自体は合同
    // 閉包1回だけの浅い見積もりだが、その浅い見積もりだけでもグラフの
    // 大部分が一斉に統合されるようなら、前提(a≡b)自体が既に破綻している
    // 可能性が高く、report_conjecturesが直接受け取る(プロービングを
    // 経ていない)生の数値的偶然についても同じ扱いにする。
    let classes_now = egraph.count_active_classes();
    const COLLAPSE_SUSPECT_RATIO: f64 = 0.2;
    let mut ranked: Vec<RankedConjecture> = Vec::new();
    let mut degenerate_skipped = 0usize;
    let mut collapse_skipped = 0usize;
    for ((ai, bi), hypothesis, occurrences) in entries {
        let (a, b) = (egraph.get_rep(ClassId(ai)), egraph.get_rep(ClassId(bi)));
        if a == b { continue; } // 探索の続きで別経路により既に証明済みになっていた
        // 🌟 除外ルール: a, b の祖先に「同じ代表元を2回以上要求する退化した構成」(調和共役の入力に自分の結果を使い回す、
        // など)があれば除外する。そこから導かれる等式は図形が退化しているという事実の言い換えでしかない。
        if has_degenerate_ancestor(egraph, a, b) {
            degenerate_skipped += 1;
            continue;
        }
        let value = egraph.estimate_conjecture_value(a, b, &None);
        if classes_now > 0 && (value.additional_merges as f64 / classes_now as f64) >= COLLAPSE_SUSPECT_RATIO {
            collapse_skipped += 1;
            continue;
        }
        // 構成手順の長さは describe_construction が辿る依存関係のステップ数で測る(mcts_depth は MCTS の構成でしか
        // 増えないので、定理が作った実体では常に0になる)。
        let construction_steps = describe_construction(egraph, a, b).2.len();
        // 🌟 美しさスコア(v1、今後の調整対象として意図的に単純にしてある):
        // ・additional_merges(この等式1つを仮定するだけで合同閉包が連鎖的に
        //   引き起こす追加の統合の数)を主軸にする――これが大きいほど
        //   「単発の偶然」ではなく、図形全体を支配する中心的な関係である
        //   可能性が高い(方冪の定理・オイラー線のような"効く"定理は、まさに
        //   1つの等式から芋づる式に他の関係が従う)。
        // ・occurrences(観測回数)は単発でも既にSchwartz-Zippelにより
        //   確信度が極めて高いため、頭打ち(min 5)にして小さくしか効かせない。
        // ・construction_steps(構成手順の長さ)は大きいほど減点する――定規と
        //   コンパスで再現する手順が短いほど、1つの命題として提示しやすい
        //   "エレガントな問題"に近いという仮定に基づく。
        // ・仮説駆動プロービング(probe_and_expand_conjectures)由来の"条件付き"
        //   予想([定理連鎖]接頭辞で識別)は、既に一度「実際に名前付き定理を
        //   発火させて出てきた」という単なる数値的偶然より強い根拠を持つため、
        //   ボーナスを与えて優先的に上位へ来るようにする。
        let chain_bonus = if hypothesis.starts_with("[定理連鎖]") { 5.0 } else { 0.0 };
        let beauty = value.additional_merges as f64 * 3.0
            + (occurrences.min(5) as f64) * 0.5
            - construction_steps as f64 * 0.5
            + chain_bonus;
        ranked.push(RankedConjecture { a, b, hypothesis, occurrences, additional_merges: value.additional_merges, construction_steps, beauty });
    }
    ranked.sort_by(|x, y| y.beauty.partial_cmp(&x.beauty).unwrap_or(std::cmp::Ordering::Equal));

    // 🌟 検出された予想候補が(局所的な一意性判定propagate_line_uniqueness/
    // propagate_point_uniqueness等により)報告時点までに既に記号的に統合
    // 済みだった場合、ranked は空になり得る。これは「何も見つからなかった」
    // (total_entries==0)とは違う状態(何かは見つかったが、報告に値する
    // 未解決の関係としては残らなかった)なので、区別してメッセージを出す。
    if ranked.is_empty() {
        println!("\n😶 探索中に{}件の数値的な偶然の一致が検出されましたが、いずれも(局所的な一意性判定による自明化、退化した構成、または全体崩壊による除外)報告に値する未解決の関係としては残っていません(退化した構成による除外: {}件、全体崩壊による除外: {}件)。",
            total_entries, degenerate_skipped, collapse_skipped);
        return Vec::new();
    }

    println!("\n=== 🏛️  発見された「綺麗な」関係の候補 (美しさスコア降順、上位{}件 / 全{}件、退化した構成として除外{}件、全体崩壊として除外{}件) ===",
        top_n.min(ranked.len()), ranked.len(), degenerate_skipped, collapse_skipped);
    // 🌟 テキストの構成手順と同じ実体集合・同じ付け替え名で discover_viz::render_svg に図を描かせ、
    // result/discover_report.html にまとめて書き出す。
    let mut html_sections: Vec<String> = Vec::new();
    for (rank, c) in ranked.iter().take(top_n).enumerate() {
        let (name_a, name_b, steps, order, labels) = describe_construction(egraph, c.a, c.b);
        println!("\n{}. [美しさ {:.1}] {} ≡ {}  (仮説: {}, 追加的帰結{}件, 観測{}回, 構成手順{}段)",
            rank + 1, c.beauty, name_a, name_b, c.hypothesis, c.additional_merges, c.occurrences,
            c.construction_steps);
        println!("   構成手順:");
        for line in &steps {
            println!("     {}", line);
        }
        let svg = crate::discover_viz::render_svg(egraph, &order, &labels, c.a, c.b, 24);
        if svg.is_none() {
            println!("   (この配置はランダムな実数座標では図示できませんでした――平行線・共線等の退化が常に起きる構成の可能性があります)");
        }
        html_sections.push(render_html_section(rank + 1, c, &name_a, &name_b, &steps, svg.as_deref()));
    }

    if try_prove
        && let Some(top) = ranked.first() {
            attempt_proof(egraph, top.a, top.b, prove_time_secs);
        }
    html_sections
}

/// 🌟 発見された関係1件分を、見出し・SVG図(あれば)・構成手順を並べた
/// HTMLの断片として組み立てる。
fn render_html_section(rank: usize, c: &RankedConjecture, name_a: &str, name_b: &str, steps: &[String], svg: Option<&str>) -> String {
    let steps_html: String = steps.iter().map(|s| format!("<li>{}</li>", xml_escape_html(s))).collect();
    let svg_html = svg.map(|s| s.to_string()).unwrap_or_else(|| "<p style=\"color:#999;\">(図示できませんでした)</p>".to_string());
    format!(
        "<section style=\"margin-bottom:32px;padding-bottom:24px;border-bottom:1px solid #e3ddd0;\">\n\
         <h2 style=\"font:600 16px/1.4 sans-serif;margin:0 0 6px;\">{rank}. [美しさ {beauty:.1}] {a} ≡ {b}</h2>\n\
         <p style=\"font:13px monospace;color:#555;margin:0 0 12px;\">仮説: {hyp} / 追加的帰結{merges}件 / 観測{occ}回 / 構成手順{steps_n}段</p>\n\
         <div style=\"display:flex;gap:24px;flex-wrap:wrap;align-items:flex-start;\">\n{svg}\n\
         <ol style=\"font:13px monospace;margin:0;padding-left:20px;\">{steps_html}</ol>\n</div>\n</section>\n",
        rank = rank, beauty = c.beauty, a = xml_escape_html(name_a), b = xml_escape_html(name_b),
        hyp = xml_escape_html(&c.hypothesis), merges = c.additional_merges, occ = c.occurrences,
        steps_n = c.construction_steps, svg = svg_html, steps_html = steps_html,
    )
}

fn xml_escape_html(s: &str) -> String {
    s.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;")
}

/// 🌟 result/discover_report.htmlへ、今回の実行で発見された上位候補の
/// 図解付き報告をまとめて書き出す(main.rsのoutput_proof等と同じく、
/// 「コンソールには要点、ファイルには詳細」の方針)。
fn write_discover_report_html(sections: &[String]) {
    if sections.is_empty() { return; }
    let body = sections.join("\n");
    let html = format!(
        "<!doctype html>\n<html lang=\"ja\"><head><meta charset=\"utf-8\">\n\
         <title>discover report</title></head>\n\
         <body style=\"font-family:sans-serif;max-width:960px;margin:24px auto;padding:0 16px;color:#1f2733;background:#fff;\">\n\
         <h1 style=\"font-size:20px;\">🏛️ discover: 発見された「綺麗な」関係</h1>\n{body}\n</body></html>\n",
        body = body
    );
    let dir = "result";
    if std::fs::create_dir_all(dir).is_ok() {
        let path = format!("{}/discover_report.html", dir);
        match std::fs::write(&path, &html) {
            Ok(_) => println!("\n📄 図解付き報告を '{}' に保存しました(ブラウザで開いて確認できます)。", path),
            Err(e) => println!("\n⚠️ discover報告ファイルの書き込みに失敗しました ({}): {}", path, e),
        }
    }
}

/// 🌟 report_conjecturesの除外ルールのドキュメント参照。a, bの祖先
/// (依存関係の閉包、original_definition.get_parents()を再帰的に辿る)の
/// 中に、「2つ以上の異なる役割の親を要求する構成なのに、実際には同じ
/// 代表元を2回以上渡している(=退化している)」ものが1つでもあれば true。
/// get_parents()はDefinitionの種類を問わず親のClassIdを平坦に返すため、
/// この判定はHarmonicConjugateOf/LineThroughPoints/Midpoint/Intersection/
/// Circumcircle/AnglePair等、異なる親を要求する定義全般に汎用的に効く
/// (PerpendicularLine(line, point)のように型が異なる2引数は、そもそも
/// 同じClassIdになり得ないため誤検出しない)。
/// 作図の祖先に「同じ実体を2回引数に取る」定義があるか(円の第2交点のような
/// 正しい対合性による閉路は退化とみなさない版。has_degenerate_ancestor参照)。
pub(crate) fn has_duplicated_parent(egraph: &EGraph, id: ClassId) -> bool {
    let mut seen: rustc_hash::FxHashSet<ClassId> = rustc_hash::FxHashSet::default();
    let mut stack = vec![egraph.get_rep(id)];
    while let Some(rep) = stack.pop() {
        if !seen.insert(rep) { continue; }
        let def = egraph.entities[rep.0].original_definition.clone();
        let parents = def.get_parents();
        for i in 0..parents.len() {
            for j in (i + 1)..parents.len() {
                if egraph.get_rep(parents[i]) == egraph.get_rep(parents[j]) { return true; }
            }
        }
        for p in parents { stack.push(egraph.get_rep(p)); }
    }
    false
}

pub(crate) fn has_degenerate_ancestor(egraph: &EGraph, a: ClassId, b: ClassId) -> bool {
    fn is_degenerate_def(egraph: &EGraph, def: &Definition) -> bool {
        let parents = def.get_parents();
        for i in 0..parents.len() {
            for j in (i + 1)..parents.len() {
                if egraph.get_rep(parents[i]) == egraph.get_rep(parents[j]) { return true; }
            }
        }
        false
    }
    // 🐛 依存関係は本来 DAG だが、マージ後(get_rep 後)に見ると循環することがある。白/灰/黒の3色 DFS にして、
    // 灰色のノードに再び到達したら閉路(構成手順として書き下せない退化した状態)として検出する。
    fn visit(egraph: &EGraph, id: ClassId, gray: &mut rustc_hash::FxHashSet<ClassId>, black: &mut rustc_hash::FxHashSet<ClassId>) -> bool {
        let rep = egraph.get_rep(id);
        if black.contains(&rep) { return false; }
        if gray.contains(&rep) { return true; } // 閉路検出
        gray.insert(rep);
        let def = &egraph.entities[rep.0].original_definition;
        let degenerate = is_degenerate_def(egraph, def)
            || def.get_parents().iter().any(|&p| visit(egraph, p, gray, black));
        gray.remove(&rep);
        black.insert(rep);
        degenerate
    }
    let mut gray = rustc_hash::FxHashSet::default();
    let mut black = rustc_hash::FxHashSet::default();
    visit(egraph, a, &mut gray, &mut black) || visit(egraph, b, &mut gray, &mut black)
}

/// 🌟 実体 a, b にたどり着くまでに使われた作図を、依存関係の順(親が先)に列挙する。original_definition を辿るので、
/// 後から名前が上書きされても何から作られたかを正確に復元できる。表示は PrettyNamer の付け替え名を使う。
/// 戻り値は(aの付け替え名, bの付け替え名, 構成手順の行一覧, 依存関係順の ClassId 列, 付け替え名の対応表)。
/// 最後の2つは discover_viz::render_svg がテキストと同じ実体・同じラベルで図を描くのに使う。
fn describe_construction(egraph: &EGraph, a: ClassId, b: ClassId) -> (String, String, Vec<String>, Vec<ClassId>, rustc_hash::FxHashMap<ClassId, String>) {
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

    let mut namer = PrettyNamer::new();
    // 🌟 依存順(親が先)に付け替え名を確定させてから表示文字列を組み立てる。
    // 先に全てのラベルを確定しておかないと、後方参照(まだ訪れていない親を
    // 先に参照する行)でラベルが振られる順序が構成順と食い違ってしまう。
    for &id in &order {
        namer.label(egraph, id);
    }
    let lines = order.iter().map(|&id| {
        let e = &egraph.entities[id.0];
        let label = namer.label(egraph, id);
        match &e.original_definition {
            Definition::FreePoint | Definition::GivenPoint => format!("{} := 自由点", label),
            def => {
                let body = egraph.format_definition_with(def, |pid| namer_lookup(egraph, &namer, pid));
                format!("{} := {}", label, body)
            }
        }
    }).collect();
    let name_a = namer.label(egraph, a);
    let name_b = namer.label(egraph, b);
    (name_a, name_b, lines, order, namer.labels)
}

/// 🌟 format_definition_withへ渡すための、既に確定済みのPrettyNamerを
/// 参照だけする読み取りヘルパー(labelは&mut selfを要求するが、
/// format_definition_with呼び出し中は既に全ラベルが確定済みなので
/// 新規採番は起きない――未登録のIDが来た場合のみ安全側としてその場の
/// 実際の名前にフォールバックする)。
fn namer_lookup(egraph: &EGraph, namer: &PrettyNamer, id: ClassId) -> String {
    let rep = egraph.get_rep(id);
    namer.labels.get(&rep).cloned().unwrap_or_else(|| egraph.entities[rep.0].name.clone())
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

/// 🌟 自由探索で組み上がった e-graph 全体を独立な乱数座標で複数回評価し、
///   (a) 同型の全ペアのうち射影的に一致するもの(独立に作った2つの図形が実は同一。3直線の共点性は交点どうしの一致になる)
///   (b) 熱量上位の点の3つ組のうち共線なもの(オイラー線型)
/// を総当たりで検出する。まだ記号的に統合されていない・構造的に共線と分かっていないものだけに絞るので、
/// 報告されるのは今の定理群では導けていない関係だけになる。
fn report_sweep_discoveries(egraph: &mut EGraph, top_n: usize, sweep_pts: usize, sweep_lines: usize) -> usize {
    const SEEDS: [u64; 3] = [0xC0FFEE, 0xBEEF77, 0x1234ABCD];
    let mut namer = PrettyNamer::new();

    // 🌟 崩壊検出: e-graph が構造的に主張している接続(点Pは直線L上)が数値評価と1件でも矛盾したら、この配置の報告を
    // 打ち切る。潰れた e-graph から出る一致・共円は崩壊の言い換えで、発見ではない。
    if let Some((bad_p, bad_l)) = crate::padic_eval::find_incidence_inconsistency(egraph, SEEDS[0]) {
        println!("\n⚠️  [崩壊検出] e-graphは「{} は {} 上にある」と主張していますが、数値評価では成り立ちません。自由探索中の誤ったマージでe-graphが実際の幾何と矛盾した状態に陥っているため、この種配置の発見報告は信頼できないものとして打ち切ります。",
            namer.label(egraph, bad_p), namer.label(egraph, bad_l));
        return 0;
    }

    let pairs = crate::padic_eval::find_generic_coincidences(egraph, &SEEDS);
    let mut kept: Vec<(ClassId, ClassId, usize)> = Vec::new();
    let mut degenerate_skipped = 0usize;
    for (a, b) in pairs {
        if has_degenerate_ancestor(egraph, a, b) { degenerate_skipped += 1; continue; }
        let steps = describe_construction(egraph, a, b).2.len();
        kept.push((a, b, steps));
    }
    // 構成手順が短い(=命題として提示しやすい)ものを上位にする。
    kept.sort_by_key(|&(_, _, steps)| steps);

    println!("\n=== 🔬 全対比較による一致の検出 (独立な乱数{}回すべてで一致、退化した構成として除外{}件) ===", SEEDS.len(), degenerate_skipped);
    if kept.is_empty() {
        println!("  (まだ記号的に統合されていない一致は見つかりませんでした)");
    }
    for (rank, &(a, b, steps)) in kept.iter().take(top_n).enumerate() {
        let na = namer.label(egraph, a);
        let nb = namer.label(egraph, b);
        let ty = egraph.entities[egraph.get_rep(a).0].entity_type;
        println!("\n{}. [{:?}] {} ≡ {}  (構成手順{}段)", rank + 1, ty, na, nb, steps);
        let (_, _, lines, _, _) = describe_construction(egraph, a, b);
        for line in lines.iter().take(14) { println!("     {}", line); }
    }

    // 共線性(3点)の検出。構造的に既に共線と分かっている組は「既知」なので除外する。
    let triples = crate::padic_eval::find_generic_collinear_triples(egraph, &SEEDS, sweep_pts);
    let mut fresh: Vec<(ClassId, ClassId, ClassId)> = Vec::new();
    let raw_triples = triples.len();
    let (mut rej_known, mut rej_degen) = (0usize, 0usize);
    for (a, b, c) in triples {
        let reps = [egraph.get_rep(a), egraph.get_rep(b), egraph.get_rep(c)];
        if egraph.find_common_line(&reps).is_some() { rej_known += 1; continue; } // 構造的に既知
        if has_degenerate_ancestor(egraph, a, b) || has_degenerate_ancestor(egraph, a, c) { rej_degen += 1; continue; }
        fresh.push((a, b, c));
    }
    if crate::cli::sweep_debug() {
        eprintln!("  [sweep-debug] 共線: 生検出{}件 -> 既知として除外{}件 / 退化として除外{}件 / 報告{}件",
            raw_triples, rej_known, rej_degen, fresh.len());
    }
    println!("\n=== 📐 未知の共線性の検出 (独立な乱数{}回すべてで共線) ===", SEEDS.len());
    if fresh.is_empty() {
        println!("  (構造的にまだ知られていない共線性は見つかりませんでした)");
    }
    for (rank, set) in maximal_verified_sets(egraph, &SEEDS, fresh.iter().map(|&(a, b, c)| vec![a, b, c]).collect(), crate::padic_eval::PropertyKind::Collinear).into_iter().take(top_n).enumerate() {
        let labels: Vec<String> = set.iter().map(|&id| namer.label(egraph, id)).collect();
        println!("  {}. {} は共線", rank + 1, labels.join(" , "));
        for line in explain_entities(egraph, &mut namer, &set) { println!("       {}", line); }
    }

    // 🌟 3直線の共点性。交点が実体として作られていなくても検出できる
    // (「3本の高さは1点で交わる」型の結論はまさにこの形)。既に構造的に
    // 共有点が分かっている3本組は「既知」として除外する。
    let conc = crate::padic_eval::find_generic_concurrent_lines(egraph, &SEEDS, sweep_lines);
    let mut fresh_conc: Vec<(ClassId, ClassId, ClassId)> = Vec::new();
    for (a, b, c) in conc {
        if shares_known_point(egraph, a, b, c) { continue; }
        // 🌟 3直線がどれも定義上同じ点Pを通るように作られた直線なら、Pで交わるのは作図の言い換えなので除く。
        if is_trivial_pencil(egraph, &[a, b, c]) { continue; }
        // 🌟 3本のうち2本が既に構造的な共有点Pを持つなら、この共点性の中身は「Pが3本目の直線の上にある」という1本の
        // 接続で、接続の検出(find_generic_point_on_curve)が正準な形で報告するので、共点性からは外す。
        if pairwise_shared_point(egraph, a, b).is_some()
            || pairwise_shared_point(egraph, b, c).is_some()
            || pairwise_shared_point(egraph, a, c).is_some() { continue; }
        fresh_conc.push((a, b, c));
    }
    println!("\n=== ✳️  未知の共点性の検出 (3直線が1点で交わる) ===");
    if fresh_conc.is_empty() { println!("  (構造的にまだ知られていない共点性は見つかりませんでした)"); }
    for (rank, set) in maximal_verified_sets(egraph, &SEEDS, fresh_conc.iter().map(|&(a, b, c)| vec![a, b, c]).collect(), crate::padic_eval::PropertyKind::Concurrent).into_iter().take(top_n).enumerate() {
        let labels: Vec<String> = set.iter().map(|&id| namer.label(egraph, id)).collect();
        println!("  {}. {} は1点で交わる", rank + 1, labels.join(" , "));
        for line in explain_entities(egraph, &mut namer, &set) { println!("       {}", line); }
    }

    // 🌟 3円が1点を共有する(ミケル点・根心型)の検出。
    let cc = crate::padic_eval::find_generic_concurrent_circles(egraph, &SEEDS, sweep_lines);
    let mut fresh_cc: Vec<(ClassId, ClassId, ClassId)> = Vec::new();
    for (a, b, c) in cc {
        // 3円が既に構造的に共有点を持つなら既知。
        if shares_known_point(egraph, a, b, c) { continue; }
        if has_degenerate_ancestor(egraph, a, b) || has_degenerate_ancestor(egraph, a, c) { continue; }
        fresh_cc.push((a, b, c));
    }
    println!("
=== 🔵 未知の3円共点の検出 (3つの円が1点を共有する) ===");
    if fresh_cc.is_empty() { println!("  (構造的にまだ知られていない3円共点は見つかりませんでした)"); }
    for (rank, &(a, b, c)) in fresh_cc.iter().take(top_n).enumerate() {
        println!("  {}. 円 {} , {} , {} は1点を共有する",
            rank + 1, namer.label(egraph, a), namer.label(egraph, b), namer.label(egraph, c));
        for line in explain_entities(egraph, &mut namer, &[a, b, c]) { println!("       {}", line); }
    }

    // 🌟 点が直線・円の上にあるという接続そのものの検出。
    // 「垂心のBCに関する対称点が外接円上にある」のように、意味のある名前を
    // 持つ曲線の上に由来の違う点が乗る、という形の結論はここでしか拾えない。
    let inc = crate::padic_eval::find_generic_point_on_curve(egraph, &SEEDS, sweep_pts, sweep_lines);
    let mut fresh_inc: Vec<(ClassId, ClassId)> = Vec::new();
    let raw_inc = inc.len();
    let (mut rej_nat, mut rej_deg) = (0usize, 0usize);
    for (p, c) in inc {
        // 「その点自身から作られた曲線」への接続は作図の言い換えなので除く。
        if egraph.is_natural_incidence(egraph.get_rep(p), egraph.get_rep(c)) { rej_nat += 1; continue; }
        // 🐛 has_degenerate_ancestor はここでは使えない: 第2交点は「2回取ると元に戻る」対合性を持つので、円がらみの作図では
        // 依存関係に必ず閉路が現れる。弾くのは「同じ実体を2回引数に取る」退化した作図だけにする。
        if has_duplicated_parent(egraph, p) || has_duplicated_parent(egraph, c) { rej_deg += 1; continue; }
        fresh_inc.push((p, c));
    }
    if crate::cli::sweep_debug() {
        eprintln!("  [sweep-debug] 接続: 生検出{}件 -> 自然な接続として除外{}件 / 退化として除外{}件",
            raw_inc, rej_nat, rej_deg);
    }
    if crate::cli::sweep_debug() {
        eprintln!("  [sweep-debug] 接続: 報告{}件", fresh_inc.len());
    }
    println!("
=== 🎯 未知の接続の検出 (点が直線・円の上にある) ===");
    if fresh_inc.is_empty() { println!("  (構造的にまだ知られていない接続は見つかりませんでした)"); }
    for (rank, &(p, c)) in fresh_inc.iter().take(top_n).enumerate() {
        let kind = if egraph.entities[egraph.get_rep(c).0].entity_type == EntityType::Conic { "円" } else { "直線" };
        println!("  {}. 点 {} は{} {} の上にある", rank + 1, namer.label(egraph, p), kind, namer.label(egraph, c));
        for line in explain_entities(egraph, &mut namer, &[p, c]) { println!("       {}", line); }
    }

    // 🌟 4点の共円性(九点円のような「由来の異なる点が実は同じ円に乗る」発見)。
    let quads = crate::padic_eval::find_generic_concyclic_quadruples(egraph, &SEEDS, sweep_pts);
    let mut fresh_quads: Vec<[ClassId; 4]> = Vec::new();
    for q in quads {
        if shares_known_conic(egraph, &q) { continue; }
        // 4点のうち3点が既に共線なら、共円は「退化した円=直線」の言い換えに過ぎない。
        let mut degenerate = false;
        for i in 0..4 { for j in (i+1)..4 { for k in (j+1)..4 {
            if egraph.find_common_line(&[egraph.get_rep(q[i]), egraph.get_rep(q[j]), egraph.get_rep(q[k])]).is_some() { degenerate = true; }
        }}}
        if degenerate { continue; }
        fresh_quads.push(q);
    }
    println!("\n=== ⭕ 未知の共円性の検出 (4点が同一円周上) ===");
    if fresh_quads.is_empty() { println!("  (構造的にまだ知られていない共円性は見つかりませんでした)"); }
    for (rank, set) in maximal_verified_sets(egraph, &SEEDS, fresh_quads.iter().map(|q| q.to_vec()).collect(), crate::padic_eval::PropertyKind::Concyclic).into_iter().take(top_n).enumerate() {
        // 既知の円が集合の3点以上を含むなら、主張の中身は「まだ載ると分かっていない点がその円に載る」ことなので、そう言い換える
        // (「8点が共円」の中身が「残り1点がこの円に乗る」だけ、という報告を避ける)。
        if let Some((circle, extra)) = known_circle_through_most(egraph, &set)
            && !extra.is_empty() {
                let ex: Vec<String> = extra.iter().map(|&id| namer.label(egraph, id)).collect();
                println!("  {}. 点 {} は 円 {} の上にある", rank + 1, ex.join(" , "), namer.label(egraph, circle));
                let mut show = extra.clone();
                show.push(circle);
                for line in explain_entities(egraph, &mut namer, &show) { println!("       {}", line); }
                continue;
            }
        let labels: Vec<String> = set.iter().map(|&id| namer.label(egraph, id)).collect();
        println!("  {}. {}点 {} は共円", rank + 1, set.len(), labels.join(" , "));
        for line in explain_entities(egraph, &mut namer, &set) { println!("       {}", line); }
    }

    kept.len() + fresh.len() + fresh_conc.len() + fresh_cc.len() + fresh_inc.len() + fresh_quads.len()
}

/// 2直線が構造的に共有すると分かっている点(あれば1つ)。
/// 無限遠点(平行性)は「共点」の根拠にしないので除く。
pub(crate) fn pairwise_shared_point(egraph: &EGraph, a: ClassId, b: ClassId) -> Option<ClassId> {
    let ra = egraph.get_rep(a);
    let pts: Vec<ClassId> = egraph.entities[ra.0].components.first()
        .map(|comp| comp.subobjects.iter().map(|&s| egraph.get_rep(s))
            .filter(|&s| egraph.entities[s.0].entity_type == EntityType::Point)
            .filter(|&s| !egraph.is_connected(s, egraph.line_infinity))
            .collect())
        .unwrap_or_default();
    pts.into_iter().find(|&p| egraph.is_connected(p, b))
}

/// 3直線が「構造的に既に共有点を持つと分かっている」か(=共点性が既知か)。
pub(crate) fn shares_known_point(egraph: &EGraph, a: ClassId, b: ClassId, c: ClassId) -> bool {
    let ra = egraph.get_rep(a);
    let pts: Vec<ClassId> = egraph.entities[ra.0].components.first()
        .map(|comp| comp.subobjects.iter().map(|&s| egraph.get_rep(s))
            .filter(|&s| egraph.entities[s.0].entity_type == EntityType::Point)
            .collect())
        .unwrap_or_default();
    pts.iter().any(|&p| egraph.is_connected(p, b) && egraph.is_connected(p, c))
}

/// 4点が「構造的に既に同じ二次曲線に乗ると分かっている」か(=共円性が既知か)。
/// 集合の3点以上を「構造的に既に通ると分かっている」円のうち、最も多くの点を
/// 覆うものと、その円にまだ載ると分かっていない残りの点を返す。
/// 共円の報告を「N点が共円」ではなく「この点はこの円の上にある」という、
/// 情報量がそのまま見える形に言い換えるために使う。
pub(crate) fn known_circle_through_most(egraph: &EGraph, set: &[ClassId]) -> Option<(ClassId, Vec<ClassId>)> {
    let mut best: Option<(ClassId, usize)> = None;
    let mut candidates: Vec<ClassId> = Vec::new();
    for &p in set {
        let rep = egraph.get_rep(p);
        if let Some(comp) = egraph.entities[rep.0].components.first() {
            for &sub in &comp.subobjects {
                let c = egraph.get_rep(sub);
                if egraph.entities[c.0].entity_type == EntityType::Conic && !candidates.contains(&c) {
                    candidates.push(c);
                }
            }
        }
    }
    for c in candidates {
        let n = set.iter().filter(|&&p| egraph.is_connected(p, c)).count();
        if n >= 3 && best.map_or(true, |(_, m)| n > m) { best = Some((c, n)); }
    }
    let (c, _) = best?;
    let extra: Vec<ClassId> = set.iter().copied().filter(|&p| !egraph.is_connected(p, c)).collect();
    Some((c, extra))
}

pub(crate) fn shares_known_conic(egraph: &EGraph, q: &[ClassId]) -> bool {
    if q.is_empty() { return false; }
    let r0 = egraph.get_rep(q[0]);
    let conics: Vec<ClassId> = egraph.entities[r0.0].components.first()
        .map(|comp| comp.subobjects.iter().map(|&s| egraph.get_rep(s))
            .filter(|&s| egraph.entities[s.0].entity_type == EntityType::Conic)
            .collect())
        .unwrap_or_default();
    conics.iter().any(|&c| q[1..].iter().all(|&p| egraph.is_connected(p, c)))
}


/// 🌟 報告の可読性のための集約(検証つき)。検出結果は3点組・4点組の部分集合として大量に出るが、共有要素が多い集合を
/// 無条件に併合すると偽の大集合ができる(平行な直線の族が連鎖的に併合される、など)。そこで各組を種に、他の組の要素を
/// 1つずつ足しては verify_property で集合全体で性質が成り立つかを数値的に確かめ、成り立つときだけ採用する(貪欲な極大化)。
pub(crate) fn maximal_verified_sets(
    egraph: &EGraph,
    seeds: &[u64],
    detected: Vec<Vec<ClassId>>,
    kind: crate::padic_eval::PropertyKind,
) -> Vec<Vec<ClassId>> {
    // 成長候補のプール: 検出結果に登場した全要素。
    let mut pool: Vec<ClassId> = Vec::new();
    for set in detected.iter().take(MAX_SEEDS_TO_GROW) {
        for &x in set { if !pool.contains(&x) { pool.push(x); } }
    }

    // 🌟 成長の1試行ごとにverify_property(=毎回まっさらな評価器でグラフを
    // 評価し直す)を呼ぶので、コストは 種の数 × プールの大きさ × seed数 に
    // 比例する。検出がまとめて数千件出ると探索が実質止まってしまうため、
    // 種とプールの両方に上限を掛ける(検出結果は既に熱量順に近い並びなので、
    // 先頭を採るだけで実用上は足りる)。
    const MAX_SEEDS_TO_GROW: usize = 120;
    const MAX_POOL: usize = 60;
    pool.truncate(MAX_POOL);

    // 🌟 検証は同じ実体を何度も評価するので、座標をseedごとに一度だけ
    // 前計算しておく(padic_eval::precompute_shapesのドキュメント参照)。
    let mut all_ids: Vec<ClassId> = pool.clone();
    for set in detected.iter().take(MAX_SEEDS_TO_GROW) {
        for &x in set { if !all_ids.contains(&x) { all_ids.push(x); } }
    }
    let tables = crate::padic_eval::precompute_shapes(egraph, seeds, &all_ids);

    let mut out: Vec<Vec<ClassId>> = Vec::new();
    let mut seen: Vec<Vec<usize>> = Vec::new();
    for base in detected.into_iter().take(MAX_SEEDS_TO_GROW) {
        // 既に採用済みの極大集合に完全に含まれている種は飛ばす。
        if out.iter().any(|g| base.iter().all(|x| g.contains(x))) { continue; }
        let mut set = base;
        for &c in &pool {
            if set.contains(&c) { continue; }
            let mut trial = set.clone();
            trial.push(c);
            // 共点性は「定義上その点を通る直線」を足しても情報が増えない
            // (is_trivial_pencil参照)ので、自明な束に育てない。
            if kind == crate::padic_eval::PropertyKind::Concurrent && is_trivial_pencil(egraph, &trial) { continue; }
            // 種の三つ組と同じく、成長させるときも「2本が既に構造的な共有点を持つ」直線は足さない(同じ中点を通るだけの直線の束を
            // 共点として報告しない)。
            if kind == crate::padic_eval::PropertyKind::Concurrent
                && set.iter().any(|&x| pairwise_shared_point(egraph, x, c).is_some()) { continue; }
            // 共円も同様に、既に同じ円に乗ると分かっている点を足しても
            // 新しい主張にはならない。
            if kind == crate::padic_eval::PropertyKind::Concyclic {
                let mut probe = set.clone(); probe.push(c);
                if shares_known_conic(egraph, &probe) { continue; }
            }
            if crate::padic_eval::verify_property_cached(&tables, &trial, kind) { set = trial; }
        }
        let mut key: Vec<usize> = set.iter().map(|x| x.0).collect();
        key.sort_unstable();
        if seen.contains(&key) { continue; }
        seen.push(key);
        out.push(set);
    }
    // 🌟 新規性による並べ替え。有名な定理(中線・垂心・外心)は3本とも同じ形の構成を頂点で巡回させただけの強い対称性を
    // 持ち、教科書に載りにくい結果は構成の形が混ざっている。各要素の「定義の形の署名」の異なる個数が多い集合を上に出す。
    out.sort_by_key(|g| (std::cmp::Reverse(shape_diversity(egraph, g)), std::cmp::Reverse(g.len())));
    out
}

/// 集合に含まれる実体の「作図の形」が何種類あるか。同じ形ばかりなら
/// (頂点を入れ替えただけの)対称的で有名な構図である可能性が高い。
fn shape_diversity(egraph: &EGraph, ids: &[ClassId]) -> usize {
    let kind_of = |id: ClassId| -> String {
        let rep = egraph.get_rep(id);
        egraph.entities[rep.0].original_definition.get_type_name().to_string()
    };
    let mut sigs: Vec<String> = ids.iter().map(|&id| {
        let rep = egraph.get_rep(id);
        let def = &egraph.entities[rep.0].original_definition;
        let args: Vec<String> = def.get_parents().iter().map(|&p| kind_of(p)).collect();
        format!("{}({})", def.get_type_name(), args.join(","))
    }).collect();
    sigs.sort();
    sigs.dedup();
    sigs.len()
}

/// 報告に出てくるラベルが実際に何なのか(どう作図された図形か)を
/// 1段だけ展開して示す。PrettyNamerのラベルは短くて読みやすい代わりに
/// それ自体では中身が分からないため。
fn explain_entities(egraph: &EGraph, namer: &mut PrettyNamer, ids: &[ClassId]) -> Vec<String> {
    let mut out = Vec::new();
    for &id in ids {
        let rep = egraph.get_rep(id);
        let def = egraph.entities[rep.0].original_definition.clone();
        let me = namer.label(egraph, id);
        let mut parent_labels: rustc_hash::FxHashMap<ClassId, String> = rustc_hash::FxHashMap::default();
        for pid in def.get_parents() {
            let l = namer.label(egraph, pid);
            parent_labels.insert(egraph.get_rep(pid), l);
        }
        let body = egraph.format_definition_with(&def, |q| {
            parent_labels.get(&egraph.get_rep(q)).cloned()
                .unwrap_or_else(|| egraph.entities[egraph.get_rep(q).0].name.chars().take(60).collect())
        });
        // 🌟 系統的作図の実体は作図そのものが名前なので、多くの場合この行は
        // 「X = X」にしかならない。その場合は出しても情報が無いので省く。
        if body == me { continue; }
        out.push(format!("{} = {}", me, body));
    }
    out
}

/// 共点性の「自明さ」判定。
/// LineThrough(P,Q) なら P,Q が、Perpendicular(l ⟂ P)/Parallel(l ∥ P)/TangentLine(c,P) なら P が、その直線上にあることは
/// 作図の定義から自明。ある点Pについて定義上Pを通る直線が3本以上あれば、それらがPで交わるのは作図の言い換えでしかない
/// (2直線は必ずどこかで交わるので、内容があるのは3本目以降)。
pub(crate) fn is_trivial_pencil(egraph: &EGraph, lines: &[ClassId]) -> bool {
    let pts_on = |l: ClassId| -> Vec<ClassId> {
        let rep = egraph.get_rep(l);
        let mut acc: Vec<ClassId> = Vec::new();
        let defs: Vec<crate::mmp_core::Definition> = egraph.entities[rep.0].components.first()
            .map(|c| c.definitions.clone()).unwrap_or_default();
        for def in defs.iter().chain(std::iter::once(&egraph.entities[rep.0].original_definition)) {
            match def {
                Definition::LineThroughPoints(a, b) => { acc.push(egraph.get_rep(*a)); acc.push(egraph.get_rep(*b)); }
                Definition::PerpendicularLine(_, p)
                | Definition::ParallelLine(_, p)
                | Definition::TangentLine(_, p) => acc.push(egraph.get_rep(*p)),
                _ => {}
            }
        }
        acc.sort_unstable_by_key(|x| x.0);
        acc.dedup();
        acc
    };
    let per_line: Vec<Vec<ClassId>> = lines.iter().map(|&l| pts_on(l)).collect();
    let mut all: Vec<ClassId> = per_line.concat();
    all.sort_unstable_by_key(|x| x.0);
    all.dedup();
    all.iter().any(|&p| per_line.iter().filter(|v| v.contains(&p)).count() >= 3)
}
/// 🌟 既存の点・直線から機械的に作れる作図を幅優先で閉包していく決定的なモード。MCTS の1手ずつの確率的な探索は、
/// 構造の薄い種配置では意味のある作図が噛み合わず何の一致にも届かない。プリセットに依存しないので、出てくる関係も
/// 有名な定理に偏りにくい。
/// 各ラウンドで作るもの: 点×点 -> 直線・中点 / 直線×直線 -> 交点 / 点×直線 -> 垂線 / 点×点×点 -> 外接円。
/// 実体数が cap を超えたら打ち切り、候補は熱量(heat_with_degree)の降順に絞る。
pub(crate) fn systematic_closure(egraph: &mut EGraph, rounds: usize, cap: usize, per_kind: usize) {
    systematic_closure_until(egraph, rounds, cap, per_kind, None)
}

/// 🌟 時間の上限つき。ブラウザから探索を起動する場合(serve.rs)、ラウンド数と
/// 実体数の上限だけでは「どれくらい待たされるか」が読めないので、
/// 壁時計の締切も渡せるようにした。締切を過ぎたら、そのラウンドの作図を
/// 打ち切って(合同閉包だけは必ず走らせて整合を保ってから)終わる。
pub(crate) fn systematic_closure_until(
    egraph: &mut EGraph, rounds: usize, cap: usize, per_kind: usize,
    deadline: Option<std::time::Instant>,
) {
    let expired = |d: Option<std::time::Instant>| d.is_some_and(|t| std::time::Instant::now() >= t);
    for round in 0..rounds {
        if expired(deadline) {
            println!("  ⏱️  [系統的作図] 時間の上限に達したのでラウンド{}の手前で打ち切ります。", round + 1);
            break;
        }
        let hot = |eg: &EGraph, ty: EntityType, n: usize| -> Vec<ClassId> {
            let mut v: Vec<(ClassId, f64)> = (0..eg.entities.len()).map(ClassId)
                .filter(|&id| eg.get_rep(id) == id
                    && eg.entities[id.0].entity_type == ty
                    && eg.entities[id.0].is_active()
                    && id != eg.line_infinity
                    && !(ty == EntityType::Point && eg.is_connected(id, eg.line_infinity)))
                .map(|id| (id, eg.entities[id.0].heat_with_degree()))
                .collect();
            v.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
            v.truncate(n);
            v.into_iter().map(|(id, _)| id).collect()
        };
        let pts = hot(egraph, EntityType::Point, per_kind);
        let lines = hot(egraph, EntityType::Line, per_kind);
        // 🌟 「数値的には同じ点/共線なのに、まだ記号的に統合されていない」
        // 組み合わせから退化した作図を作らないためのふるい
        // (padic_eval::NumericSieveのドキュメント参照)。
        let sieve = crate::padic_eval::numeric_sieve(egraph, 0xD1F7 + round as u64, &pts);

        let mut new_defs: Vec<(Definition, EntityType)> = Vec::new();
        // 中点どうしの中点は作らない(アフィンな細分にすぎず、「線分の1/8点」の共線・共円が報告を埋める)。
        // 中点を端点とする直線や中点への垂線は作るので、中点連結線などは失われない。
        let is_midpoint = |eg: &EGraph, id: ClassId| -> bool {
            let rep = eg.get_rep(id);
            eg.entities[rep.0].components.first()
                .map(|c| c.definitions.iter().any(|d| matches!(d, Definition::Midpoint(_, _))))
                .unwrap_or(false)
                || matches!(eg.entities[rep.0].original_definition, Definition::Midpoint(_, _))
        };
        for i in 0..pts.len() {
            for j in (i + 1)..pts.len() {
                if sieve.same_point(pts[i], pts[j]) { continue; }
                new_defs.push((Definition::new_line(pts[i], pts[j]), EntityType::Line));
                if !is_midpoint(egraph, pts[i]) && !is_midpoint(egraph, pts[j]) {
                    new_defs.push((Definition::Midpoint(pts[i], pts[j]), EntityType::Point));
                }
            }
        }
        for i in 0..lines.len() {
            for j in (i + 1)..lines.len() {
                new_defs.push((Definition::Intersection(lines[i], lines[j]), EntityType::Point));
            }
        }
        for &p in &pts {
            for &l in &lines {
                new_defs.push((Definition::PerpendicularLine(l, p), EntityType::Line));
            }
        }
        // 🌟 外接円は毎ラウンド、熱量上位の点だけに絞って作る(最初のラウンドだけだと円が1つしか無く、根軸も2円の第2交点も
        // 作れない)。
        let circle_pts = &pts[..pts.len().min(6)];
        for i in 0..circle_pts.len() {
            for j in (i + 1)..circle_pts.len() {
                for k in (j + 1)..circle_pts.len() {
                    let tri = [circle_pts[i], circle_pts[j], circle_pts[k]];
                    // 既に共線と分かっている3点の「外接円」は退化した二次曲線で、円の一意性伝播を暴走させて e-graph を潰すので作らない。
                    if egraph.find_common_line(&tri).is_some() { continue; }
                    if sieve.degenerate_triple(tri[0], tri[1], tri[2]) { continue; }
                    new_defs.push((Definition::Circumcircle(tri[0], tri[1], tri[2]), EntityType::Conic));
                }
            }
        }

        // 🌟 円を経由する作図(根軸・第2交点)も作る。直線と中点だけの閉包は一次的な関係しか生まないが、円は方冪・共円・角度と
        // いう別の層の関係を持ち込む。
        let conics = hot(egraph, EntityType::Conic, per_kind.min(6));
        let on_curve = |eg: &EGraph, curve: ClassId| -> Vec<ClassId> {
            eg.entities[eg.get_rep(curve).0].components.first()
                .map(|comp| comp.subobjects.iter().map(|&s| eg.get_rep(s))
                    .filter(|&s| eg.entities[s.0].entity_type == EntityType::Point)
                    .filter(|&s| !eg.is_connected(s, eg.line_infinity))
                    .collect::<Vec<_>>())
                .unwrap_or_default()
        };
        for (ci, &c) in conics.iter().enumerate() {
            let on_c = on_curve(egraph, c);
            // (1) 円周上の既知点での接線。
            for &p in &on_c {
                new_defs.push((Definition::TangentLine(c, p), EntityType::Line));
            }
            // (2) 円と直線の第2交点。「その直線と円の交点が1つ既に分かって
            // いる」場合だけ有理的に作図できる(平方根が不要)ので、円周上の
            // 点pを通る直線に限る。
            for &p in &on_c {
                for &l in &lines {
                    if !egraph.is_connected(p, l) { continue; }
                    new_defs.push((Definition::SecondIntersectionOfLineAndConic(p, l, c), EntityType::Point));
                }
            }
            // (3) 2円の根軸(共有点が無くても定義できる)と、共有点が1つ
            // 分かっている場合の第2交点。
            for &c2 in conics.iter().skip(ci + 1) {
                let shared: Vec<ClassId> = on_c.iter().copied().filter(|&p| egraph.is_connected(p, c2)).collect();
                // 共有点が2つ以上既に分かっているなら、根軸はその2点を結ぶ
                // 直線そのもので新しい対象ではなく、第2交点も既知。
                // (3つ以上ならそもそも同じ円なので、根軸は定まらない。)
                if shared.len() >= 2 { continue; }
                new_defs.push((Definition::RadicalAxis(c, c2), EntityType::Line));
                for &p in shared.iter() {
                    new_defs.push((Definition::SecondIntersectionOfCircles(p, c, c2), EntityType::Point));
                }
            }
        }

        let mut added = 0usize;
        for (def, ty) in new_defs {
            if egraph.count_active_classes() >= cap { break; }
            if added % 16 == 0 && expired(deadline) { break; }
            let norm = egraph.normalize_definition(&def);
            if egraph.memo.contains_key(&norm) { continue; }
            // 作図そのものを名前にする(通し番号だと報告が読めない)。ラウンド数は高々数回なので親の名前をそのまま埋め込み、
            // 切り詰めるのは最後の保険としてだけ(途中で切ると括弧の途中で切れて読めなくなる)。
            let raw = egraph.format_definition_with(&norm, |id| {
                let n = egraph.entities[egraph.get_rep(id).0].name.clone();
                if n.chars().count() > 90 { n.chars().take(90).collect::<String>() + "…" } else { n }
            });
            egraph.create_entity(raw, norm, ty);
            added += 1;
        }
        let before_closure = egraph.count_active_classes();
        egraph.apply_congruence_closure();
        let after = egraph.count_active_classes();
        println!("  🏗️  [系統的作図] ラウンド{}: {}件を追加、アクティブな同値類数 {}",
            round + 1, added, after);
        // 🌟 崩壊の早期検出と原因の特定。系統的作図は決定的なので、
        // 「合同閉包の前後で同値類が激減した」= 誤ったマージが連鎖した、
        // という状況をその場で捕まえて、原因になったマージの根拠を出せる。
        // 🌟 系統的作図でも、ラウンドごとに「構造的な主張と数値評価の整合性」を
        // 監査できるようにする(DISCOVER_AUDIT=1)。崩壊が"激減"として現れない
        // タイプ(少数の誤マージ)は同値類数では捕まらないため。
        if crate::cli::audit()
            && let Some((bad_p, bad_l)) = crate::padic_eval::find_incidence_inconsistency(egraph, 0xC0FFEE) {
                println!("  🔬 [監査] ラウンド{}終了時点で矛盾: 「{} は {} 上にある」が数値的に成り立ちません。",
                    round + 1,
                    egraph.entities[egraph.get_rep(bad_p).0].name.chars().take(70).collect::<String>(),
                    egraph.entities[egraph.get_rep(bad_l).0].name.chars().take(70).collect::<String>());
                let rep_p = egraph.get_rep(bad_p);
                let rep_l = egraph.get_rep(bad_l);
                for (label, target) in [("点", rep_p), ("直線", rep_l)] {
                    println!("     {}側の同値類に流れ込んだマージ:", label);
                    let mut n = 0;
                    for (&slot, edge) in &egraph.proof_edges {
                        if egraph.get_rep(ClassId(slot)) != target { continue; }
                        println!("       {} ≡ {} (理由: {})",
                            egraph.entities[edge.from.0].name.chars().take(55).collect::<String>(),
                            egraph.entities[edge.to.0].name.chars().take(55).collect::<String>(),
                            format!("{:?}", edge.justification).chars().take(100).collect::<String>());
                        n += 1;
                        if n >= 10 { println!("       ..."); break; }
                    }
                    if n == 0 { println!("       (なし)"); }
                }
                return;
            }
        if after * 3 < before_closure {
            println!("  🚨 [崩壊] 合同閉包で同値類が{}→{}に激減しました。原因になったマージの根拠を表示します:", before_closure, after);
            let mut reasons: rustc_hash::FxHashMap<String, usize> = rustc_hash::FxHashMap::default();
            let mut samples: Vec<String> = Vec::new();
            for (&slot, edge) in &egraph.proof_edges {
                let _ = slot;
                let key = format!("{:?}", edge.justification);
                let key = key.chars().take(90).collect::<String>();
                *reasons.entry(key.clone()).or_insert(0) += 1;
                if samples.len() < 8 {
                    samples.push(format!("     {} ≡ {} (理由: {})",
                        egraph.entities[edge.from.0].name.chars().take(60).collect::<String>(),
                        egraph.entities[edge.to.0].name.chars().take(60).collect::<String>(), key));
                }
            }
            let mut rv: Vec<(String, usize)> = reasons.into_iter().collect();
            rv.sort_by_key(|&(_, n)| std::cmp::Reverse(n));
            for (r, n) in rv.into_iter().take(6) { println!("     {}件: {}", n, r); }
            for l in samples { println!("{}", l); }
        }
        if egraph.count_active_classes() >= cap { break; }
    }
}

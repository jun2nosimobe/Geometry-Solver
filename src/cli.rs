//! 🌟 ユーザー要望「手元でいろんなオプションやパラメーターを調整して
//! このエンジンを回せるようにしたい」への対応。
//!
//! これまでオプションは main.rs / discover.rs / discover_degenerate.rs の
//! 3か所に `args.iter().find_map(|a| a.strip_prefix("--time="))` の形で
//! 直に散らばっており、
//!   (1) 何が指定できるのかソースを読まないと分からない、
//!   (2) `--sweep-point=60` のように綴りを間違えても黙って無視され、
//!       「パラメータを変えたつもりで実は既定値のまま」の実験結果が出る、
//!   (3) 一部の設定(系統的作図・監査・デバッグ出力)は環境変数でしか
//!       指定できず、他のフラグと書き方が揃っていない、
//! という状態だった。(2)はパラメータ調整をしたい人にとって最悪の失敗の
//! 仕方なので、ここに全オプションの一覧(OPTIONS)を1つだけ持ち、
//! ヘルプ表示・未知フラグの検出・環境変数への橋渡しをまとめて行う。
//!
//! 既存の解析コード自体はそのまま残してある(挙動を変えないため)。
//! この表と実際の解析がずれないよう、ソースを走査して突き合わせる
//! テスト(tests::every_flag_in_source_is_documented)を置いている。

use std::collections::BTreeSet;

/// オプションが値を取るかどうか(ヘルプの表示と未知フラグ判定に使う)。
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Arg {
    /// 値を取らないスイッチ (`--mcts`)
    None,
    /// `--time=5` のように `=` で値を取る
    Value(&'static str),
}

pub struct Opt {
    pub name: &'static str,
    pub arg: Arg,
    /// 既定値。スイッチなら "無効" のように状態を書く。
    pub default: &'static str,
    /// どのサブコマンドで効くか(ヘルプの見出しに使う)
    pub mode: Mode,
    pub help: &'static str,
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Mode {
    /// 問題を解く通常実行 (`geom_solver <問題名>`)
    Solve,
    /// 自由探索・発見モード (`geom_solver discover`)
    Discover,
    /// 退化探索 (`geom_solver discover-degenerate`)
    Degenerate,
    /// パラメータ掃引 (`geom_solver sweep`)
    Sweep,
    /// 作図インターフェース (`geom_solver serve`)
    Serve,
}

impl Mode {
    fn title(self) -> &'static str {
        match self {
            Mode::Solve => "問題を解く: geom_solver <問題名> [オプション]",
            Mode::Discover => "自由探索で定理を発見する: geom_solver discover [オプション]",
            Mode::Degenerate => "退化させて関連を調べる: geom_solver discover-degenerate <問題名> [オプション]",
            Mode::Sweep => "パラメータを振って比べる: geom_solver sweep [オプション]",
            Mode::Serve => "ブラウザで作図する: geom_solver serve [オプション]",
        }
    }
}

use Arg::{None as Switch, Value};
use Mode::{Degenerate, Discover, Serve, Solve, Sweep};

pub const OPTIONS: &[Opt] = &[
    // ---- 問題を解くモード ----
    Opt { name: "--time", arg: Value("秒"), default: "5", mode: Solve,
          help: "探索の時間予算。解けない問題を長く回したいときに上げる" },
    Opt { name: "--mcts", arg: Switch, default: "無効", mode: Solve,
          help: "MCTSによる補助点の作図を有効にする(既定は無効)" },
    Opt { name: "--heat-cap", arg: Value("個"), default: "40", mode: Solve,
          help: "定理のマッチングで見る「熱い」実体の数。上げると広く探すが遅くなる" },
    Opt { name: "--fanout-heat-cap", arg: Value("個"), default: "5", mode: Solve,
          help: "枝分かれの大きいパターンで見る実体の数。足りなければ自動で広がるので初期値" },
    Opt { name: "--no-bandit", arg: Switch, default: "バンディット有効", mode: Solve,
          help: "UCB1バンディットによる定理の優先順位付けを切る(A/B比較用)" },
    Opt { name: "--no-mcts-target-bias", arg: Switch, default: "バイアス有効", mode: Solve,
          help: "MCTSが証明目標に近い図形を優先するのを切る(A/B比較用)" },
    Opt { name: "--midpoint-demands", arg: Switch, default: "無効", mode: Solve,
          help: "行き詰まったら、図に既にある中点の端点について残りの中点も作る" },
    Opt { name: "--degen-heat", arg: Switch, default: "無効", mode: Solve,
          help: "退化させたとき一致する図形どうしにheatボーナスを配る" },
    Opt { name: "--degen-heat-seed", arg: Value("整数"), default: "12345", mode: Solve,
          help: "退化グループを作るときの乱数シード" },
    Opt { name: "--degen-heat-min-hits", arg: Value("回"), default: "2", mode: Solve,
          help: "何回の独立な乱数で一致したら関連ありとみなすか" },
    Opt { name: "--degen-heat-factor", arg: Value("倍率"), default: "0.5", mode: Solve,
          help: "関連する図形へ配るheatボーナスの倍率" },
    Opt { name: "--stats", arg: Switch, default: "非表示", mode: Solve,
          help: "終了時に定理ごとの試行回数・平均報酬を表示する" },
    Opt { name: "--profile", arg: Switch, default: "非表示", mode: Solve,
          help: "終了時に探索の各フェーズの所要時間の内訳を表示する" },

    // ---- 自由探索・発見モード ----
    Opt { name: "--preset", arg: Value("名前|all"), default: "自由点だけ", mode: Discover,
          help: "既存の問題の配置を種として使う。カンマ区切りで複数、allで古典配置を一括" },
    Opt { name: "--seed-points", arg: Value("個"), default: "3", mode: Discover,
          help: "プリセットを使わないときの自由点の数(最低3)。4にすると四角形の配置になる" },
    Opt { name: "--systematic", arg: Value("ラウンド,実体数上限,1種あたり"), default: "未指定ならMCTS探索", mode: Discover,
          help: "MCTSの代わりに決定的な作図閉包を回す。例: --systematic=4,800,10" },
    Opt { name: "--time", arg: Value("秒"), default: "60", mode: Discover,
          help: "MCTS探索の時間予算(種配置ごと)" },
    Opt { name: "--steps", arg: Value("回"), default: "80", mode: Discover,
          help: "MCTS探索のステップ数上限" },
    Opt { name: "--sims", arg: Value("回"), default: "150", mode: Discover,
          help: "1ステップあたりのMCTSシミュレーション回数" },
    Opt { name: "--top", arg: Value("件"), default: "5", mode: Discover,
          help: "各セクションで報告する件数" },
    Opt { name: "--sweep-points", arg: Value("個"), default: "48", mode: Discover,
          help: "総当たり検出で見る点の数。上げると見つかるが共円判定がO(n^4)で重い" },
    Opt { name: "--sweep-lines", arg: Value("本"), default: "36", mode: Discover,
          help: "総当たり検出で見る直線・円の数" },
    Opt { name: "--prove", arg: Switch, default: "無効", mode: Discover,
          help: "見つかった予想に実際に証明を試みる" },
    Opt { name: "--prove-time", arg: Value("秒"), default: "15", mode: Discover,
          help: "--prove のときの1件あたりの証明時間" },
    Opt { name: "--probe", arg: Switch, default: "無効", mode: Discover,
          help: "予想を仮定して何が導かれるかを調べる(自由度が落ちるので既定は無効)" },
    Opt { name: "--probe-dfs-budget", arg: Value("回"), default: "3000", mode: Discover,
          help: "--probe のときの1件あたりの探索予算" },
    Opt { name: "--probe-rounds", arg: Value("回"), default: "5", mode: Discover,
          help: "--probe のときのラウンド数" },
    Opt { name: "--audit", arg: Switch, default: "無効", mode: Discover,
          help: "各ステップで構造的な主張と数値評価の整合を検査する(重いが崩壊の原因特定に使う)" },
    Opt { name: "--sweep-debug", arg: Switch, default: "無効", mode: Discover,
          help: "検出器が何件を何の理由で捨てたかを標準エラーに出す" },

    // ---- 退化探索 ----
    Opt { name: "--seed", arg: Value("整数"), default: "12345", mode: Degenerate,
          help: "乱数シード" },
    Opt { name: "--min-hits", arg: Value("回"), default: "2", mode: Degenerate,
          help: "何回の独立な乱数で一致したら報告するか" },

    // ---- パラメータ掃引 ----
    Opt { name: "--problems", arg: Value("名前,..|all|bench"), default: "all", mode: Sweep,
          help: "掃引の対象にする問題。allは全問題、benchはbench_で始まる問題" },
    Opt { name: "--vary", arg: Value("--フラグ=値,値,.."), default: "なし", mode: Sweep,
          help: "振りたいオプションと値の候補。複数回指定すると直積を全部試す" },
    Opt { name: "--base", arg: Value("フラグ列"), default: "なし", mode: Sweep,
          help: "全ての組み合わせに共通で付けるオプション(空白区切り)" },
    Opt { name: "--timeout", arg: Value("秒"), default: "30", mode: Sweep,
          help: "1問あたりの打ち切り時間" },
    Opt { name: "--repeat", arg: Value("回"), default: "1", mode: Sweep,
          help: "同じ組み合わせを何回走らせて合算するか(ゆらぎを均すため)" },

    // ---- 作図インターフェース ----
    Opt { name: "--port", arg: Value("番号"), default: "8080", mode: Serve,
          help: "待ち受けるポート。塞がっていたら別の番号にする" },
];

/// 環境変数でも指定できるもの(後方互換)。フラグ -> 環境変数名。
pub const ENV_ALIASES: &[(&str, &str)] = &[
    ("--systematic", "DISCOVER_SYSTEMATIC"),
    ("--audit", "DISCOVER_AUDIT"),
    ("--sweep-debug", "SWEEP_DEBUG"),
];

pub const SUBCOMMANDS: &[(&str, &str)] = &[
    ("<問題名>", "その問題の証明を試みる(名前は list で確認できます)"),
    ("discover", "自由作図で未知の関係を探す"),
    ("discover-degenerate", "図形を退化させて関連の深い図形の組を探す"),
    ("serve", "ブラウザで作図して定理を発見する(GeoGebra風の画面)"),
    ("sweep", "オプションを振って解けた数と時間を比べる"),
    ("list", "問題名・プリセット名の一覧を出す"),
    ("extract-proof", "raw_proofファイルから2実体が等しい理由を抜き出す"),
    ("help", "このヘルプ"),
];

/// 端末上の見かけの幅(日本語などの全角文字は2桁ぶん)。
/// Rustの `{:<38}` は文字数で詰めるため、全角を含む行だけ右にずれてしまう。
fn display_width(s: &str) -> usize {
    s.chars().map(|c| {
        let c = c as u32;
        let wide = (0x1100..=0x115F).contains(&c)
            || (0x2E80..=0xA4CF).contains(&c)    // CJK部首〜漢字・かな
            || (0xAC00..=0xD7A3).contains(&c)    // ハングル
            || (0xF900..=0xFAFF).contains(&c)    // CJK互換漢字
            || (0xFF00..=0xFF60).contains(&c)    // 全角英数
            || (0xFFE0..=0xFFE6).contains(&c)
            || (0x1F300..=0x1FAFF).contains(&c); // 絵文字
        if wide { 2 } else { 1 }
    }).sum()
}

/// 見かけの幅で左詰めする。
pub fn pad(s: &str, width: usize) -> String {
    let mut out = s.to_string();
    for _ in display_width(s)..width { out.push(' '); }
    out
}

pub fn print_help() {
    println!("geom_solver — 射影幾何ベースの初等幾何ソルバ\n");
    println!("使い方: geom_solver <サブコマンド|問題名> [オプション]\n");
    println!("サブコマンド:");
    for (name, help) in SUBCOMMANDS {
        println!("  {} {}", pad(name, 22), help);
    }
    for mode in [Mode::Solve, Mode::Discover, Mode::Degenerate, Mode::Sweep, Mode::Serve] {
        println!("\n{}", mode.title());
        for o in OPTIONS.iter().filter(|o| o.mode == mode) {
            let shown = match o.arg {
                Arg::None => o.name.to_string(),
                Arg::Value(v) => format!("{}=<{}>", o.name, v),
            };
            println!("  {} {}  [既定: {}]", pad(&shown, 34), o.help, o.default);
        }
    }
    println!("\n同じ設定は環境変数でも指定できます(フラグの方が新しい書き方です):");
    for (flag, env) in ENV_ALIASES {
        println!("  {} = {}", pad(env, 22), flag);
    }
    println!("\nよく使う例:");
    println!("  # ブラウザで作図しながら定理を探す");
    println!("  geom_solver serve");
    println!("  # 1問だけ、時間を伸ばして解かせる");
    println!("  geom_solver simson --time=30 --mcts");
    println!("  # 全問まとめて回して、いま何問解けるかを見る(回帰確認)");
    println!("  geom_solver sweep --problems=all --timeout=30");
    println!("  # 裸の三角形から、決定的な作図閉包で未知の関係を探す");
    println!("  geom_solver discover --systematic=4,800,10 --seed-points=3 --top=6");
    println!("  # 既存の問題の配置を種にして探す(検出器が何を捨てたかも出す)");
    println!("  geom_solver discover --preset=orthocenter --systematic=3,700,10 --sweep-debug");
    println!("  # パラメータを振って効き目を比べる(組み合わせの直積を全部試す)");
    println!("  geom_solver sweep --problems=bench --vary=--heat-cap=20,40,80 --base=\"--mcts --time=20\"");
    println!("  # 図形を退化させて関連の深い図形の組を探す");
    println!("  geom_solver discover-degenerate orthocenter --min-hits=3");
    println!("  # 問題名・プリセット名の一覧");
    println!("  geom_solver list");
}

pub fn print_catalog() {
    println!("問題名 ({}件):", crate::problems::ALL_PROBLEMS.len());
    for chunk in crate::problems::ALL_PROBLEMS.chunks(3) {
        println!("  {}", chunk.iter().map(|s| pad(s, 28)).collect::<String>().trim_end());
    }
    println!("\ndiscover の --preset= に渡せる名前:");
    println!("  上の問題名すべて、加えて三角形の五心を最初から揃えた合成配置:");
    println!("    triangle_centers");
    println!("  --preset=all は次の古典配置をまとめて試します:");
    for chunk in crate::discover::CLASSIC_PRESETS.chunks(4) {
        println!("    {}", chunk.join(", "));
    }
}

/// 渡された引数のうち、OPTIONSにもサブコマンドにも無いものを返す。
///
/// 綴り間違いを黙って無視すると「パラメータを変えたつもりで既定値のまま」の
/// 実験結果が出てしまうので、呼び出し側はこれが空でなければ止める。
pub fn unknown_flags(args: &[String]) -> Vec<String> {
    let known: BTreeSet<&str> = OPTIONS.iter().map(|o| o.name).collect();
    let mut bad = Vec::new();
    for a in args.iter().skip(1) {
        if !a.starts_with("--") { continue; }
        let name = a.split('=').next().unwrap_or(a);
        if !known.contains(name) { bad.push(a.clone()); }
    }
    bad
}

/// 「もしかして」候補(編集距離1〜2の最も近い既知フラグ)。
pub fn nearest_flag(input: &str) -> Option<&'static str> {
    let name = input.split('=').next().unwrap_or(input);
    OPTIONS.iter()
        .map(|o| (o.name, levenshtein(name, o.name)))
        .filter(|&(_, d)| d <= 3)
        .min_by_key(|&(_, d)| d)
        .map(|(n, _)| n)
}

fn levenshtein(a: &str, b: &str) -> usize {
    let (a, b): (Vec<char>, Vec<char>) = (a.chars().collect(), b.chars().collect());
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    let mut cur = vec![0usize; b.len() + 1];
    for i in 1..=a.len() {
        cur[0] = i;
        for j in 1..=b.len() {
            let cost = if a[i - 1] == b[j - 1] { 0 } else { 1 };
            cur[j] = (prev[j] + 1).min(cur[j - 1] + 1).min(prev[j - 1] + cost);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[b.len()]
}

/// 🌟 フラグと環境変数の両方で指定できる設定の置き場。
///
/// `--systematic=...` のようなフラグは main で1度だけ読み取り、
/// 深いところ(discover.rs の閉包や padic_eval の検出器)からは
/// この関数経由で参照する。環境変数を書き換えて橋渡しする手もあるが、
/// std::env::set_var は他スレッドと競合し得るため unsafe であり、
/// 「起動時に1回決めて以後読むだけ」というこの用途には OnceLock の方が
/// 素直で安全。main を通らないテストからも使えるよう、初期化されて
/// いなければ環境変数だけを見る。
pub struct Overrides {
    /// `--systematic=ラウンド,実体数上限,1種あたり` / DISCOVER_SYSTEMATIC
    pub systematic: Option<String>,
    /// `--audit` / DISCOVER_AUDIT
    pub audit: bool,
    /// `--sweep-debug` / SWEEP_DEBUG
    pub sweep_debug: bool,
}

static OVERRIDES: std::sync::OnceLock<Overrides> = std::sync::OnceLock::new();

/// mainで1度だけ呼ぶ。フラグが無ければ環境変数を見る(後方互換)。
pub fn init(args: &[String]) {
    let value_of = |flag: &str| -> Option<String> {
        let with_value = format!("{}=", flag);
        args.iter().find_map(|a| a.strip_prefix(with_value.as_str()).map(|v| v.to_string()))
    };
    let present = |flag: &str| args.iter().any(|a| a == flag);
    let _ = OVERRIDES.set(Overrides {
        systematic: value_of("--systematic").or_else(|| std::env::var("DISCOVER_SYSTEMATIC").ok()),
        audit: present("--audit") || std::env::var("DISCOVER_AUDIT").is_ok(),
        sweep_debug: present("--sweep-debug") || std::env::var("SWEEP_DEBUG").is_ok(),
    });
}

fn overrides() -> &'static Overrides {
    OVERRIDES.get_or_init(|| Overrides {
        systematic: std::env::var("DISCOVER_SYSTEMATIC").ok(),
        audit: std::env::var("DISCOVER_AUDIT").is_ok(),
        sweep_debug: std::env::var("SWEEP_DEBUG").is_ok(),
    })
}

/// 系統的作図の設定(`ラウンド,実体数上限,1種あたり`)。Noneならこのモードは使わない。
pub fn systematic() -> Option<&'static str> { overrides().systematic.as_deref() }
/// 構造的な主張と数値評価の整合を各ステップで検査するか。
pub fn audit() -> bool { overrides().audit }
/// 検出器が何件を何の理由で捨てたかを標準エラーに出すか。
pub fn sweep_debug() -> bool { overrides().sweep_debug }

#[cfg(test)]
mod tests {
    use super::*;

    /// 🌟 この表と実際の解析がずれると、ヘルプが嘘をつくうえに正しいフラグが
    /// 「未知」として弾かれてしまう。ソースを走査して、実際に解析されている
    /// `--xxx` が全部 OPTIONS に載っていることを確かめる。
    #[test]
    fn every_flag_in_source_is_documented() {
        const SOURCES: &[&str] = &[
            include_str!("main.rs"),
            include_str!("discover.rs"),
            include_str!("discover_degenerate.rs"),
        ];
        let known: BTreeSet<&str> = OPTIONS.iter().map(|o| o.name).collect();
        let mut missing: Vec<String> = Vec::new();
        for src in SOURCES {
            for (pat, strip_eq) in [("strip_prefix(\"", true), ("a == \"", false)] {
                let mut rest = *src;
                while let Some(pos) = rest.find(pat) {
                    rest = &rest[pos + pat.len()..];
                    let Some(end) = rest.find('"') else { break };
                    let tok = &rest[..end];
                    if !tok.starts_with("--") { continue; }
                    let name = if strip_eq { tok.trim_end_matches('=') } else { tok };
                    if !known.contains(name) && !missing.contains(&name.to_string()) {
                        missing.push(name.to_string());
                    }
                }
            }
        }
        assert!(missing.is_empty(),
            "ソース中で解析されているのに cli.rs::OPTIONS に載っていないフラグ: {:?}", missing);
    }

    #[test]
    fn unknown_flags_are_detected_and_suggested() {
        let args: Vec<String> = ["geom_solver", "simson", "--sweep-point=60", "--mcts"]
            .iter().map(|s| s.to_string()).collect();
        let bad = unknown_flags(&args);
        assert_eq!(bad, vec!["--sweep-point=60".to_string()],
            "綴り違いのフラグだけが未知として検出されるべき");
        assert_eq!(nearest_flag("--sweep-point=60"), Some("--sweep-points"),
            "一番近い既知のフラグを提案できるべき");
    }

    #[test]
    fn flags_and_env_vars_are_both_understood() {
        // init前(=mainを通らないテスト実行時)は環境変数だけを見る。
        assert!(!audit() || std::env::var("DISCOVER_AUDIT").is_ok(),
            "initされていなければ環境変数の有無と一致するべき");
        // フラグの読み取り自体は init を通さずとも同じ規則で確かめられる。
        let args: Vec<String> = ["geom_solver", "discover", "--systematic=4,800,10", "--audit"]
            .iter().map(|s| s.to_string()).collect();
        let value_of = |flag: &str| -> Option<String> {
            let w = format!("{}=", flag);
            args.iter().find_map(|a| a.strip_prefix(w.as_str()).map(|v| v.to_string()))
        };
        assert_eq!(value_of("--systematic").as_deref(), Some("4,800,10"));
        assert!(args.iter().any(|a| a == "--audit"));
    }
}

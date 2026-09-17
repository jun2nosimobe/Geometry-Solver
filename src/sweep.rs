//! 🌟 パラメータを振って比べる掃引実行器(sweep)。自分自身を子プロセスとして起動し、`--vary` に与えた候補の直積を
//! 全部試して「解けた数」と「所要時間」を表にする(シェルスクリプトを書き換えずに済み、シェルにも依存しない)。
//!
//! 例:
//!   geom_solver sweep --problems=bench --vary=--heat-cap=20,40,80
//!   geom_solver sweep --vary=--fanout-heat-cap=5,10 --vary=--mcts=on,off --repeat=3
//!
//! `--vary=--フラグ=on,off` のように on/off を並べると、値を取らないスイッチの有無を振れる(onならフラグを付ける、offなら付けない)。

use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// 成功判定に使う文字列(main.rsが証明成功時に必ず出す)。
const SUCCESS_MARK: &str = "🎉 証明完了";

pub fn run(args: &[String]) {
    let problems = match resolve_problems(args) {
        Some(p) => p,
        None => return,
    };
    let varies = parse_varies(args);
    let base: Vec<String> = args.iter()
        .find_map(|a| a.strip_prefix("--base="))
        .map(|s| s.split_whitespace().map(|t| t.to_string()).collect())
        .unwrap_or_default();
    let timeout_secs: u64 = args.iter()
        // 🌟 探索の予算は --steps(仕事量)で決まるので、ここは「暴走を
        // 止める」ためだけの安全弁。短くすると machine の混み具合で結果が
        // 変わってしまい、仕事量で測る意味が無くなるので既定を長く取る。
        .find_map(|a| a.strip_prefix("--timeout="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(600);
    let repeat: u32 = args.iter()
        .find_map(|a| a.strip_prefix("--repeat="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(1)
        .max(1);

    let combos = cartesian(&varies);
    let exe = match std::env::current_exe() {
        Ok(p) => p,
        Err(e) => { println!("⚠️ 自分自身の実行ファイルの場所が分かりませんでした: {}", e); return; }
    };

    println!("🔧 パラメータ掃引: 問題{}件 × 組み合わせ{}通り × {}回 (1問あたり最大{}秒)",
        problems.len(), combos.len(), repeat, timeout_secs);
    if !base.is_empty() { println!("   共通オプション: {}", base.join(" ")); }
    println!();

    let mut rows: Vec<(String, usize, usize, f64, Vec<String>)> = Vec::new();
    for combo in &combos {
        let label = if combo.is_empty() { "(既定のまま)".to_string() } else { combo.join(" ") };
        let mut solved = 0usize;
        let mut total = 0usize;
        let mut elapsed = 0.0f64;
        let mut failed: Vec<String> = Vec::new();
        for problem in &problems {
            let mut ok_count = 0u32;
            for _ in 0..repeat {
                let mut argv: Vec<String> = vec![problem.clone()];
                argv.extend(base.iter().cloned());
                argv.extend(combo.iter().cloned());
                let (ok, secs) = run_once(&exe, &argv, timeout_secs);
                elapsed += secs;
                total += 1;
                if ok { solved += 1; ok_count += 1; }
            }
            if ok_count == 0 { failed.push(problem.clone()); }
        }
        println!("  {} {:>4}/{:<4} ({:>5.1}%)  {:>7.1}秒",
            crate::cli::pad(&truncate(&label, 44), 44), solved, total,
            100.0 * solved as f64 / total.max(1) as f64, elapsed);
        rows.push((label, solved, total, elapsed, failed));
    }

    // 解けた数の多い順、同数なら速い順。
    rows.sort_by(|a, b| b.1.cmp(&a.1)
        .then(a.3.partial_cmp(&b.3).unwrap_or(std::cmp::Ordering::Equal)));
    println!("\n=== 解けた数の多い順 ===");
    for (rank, (label, solved, total, elapsed, failed)) in rows.iter().enumerate() {
        println!("{:>2}. {} {}/{}  {:.1}秒", rank + 1,
            crate::cli::pad(&truncate(label, 44), 44), solved, total, elapsed);
        if !failed.is_empty() {
            println!("     解けなかった問題: {}", failed.join(", "));
        }
    }
}

/// 子プロセスを1回走らせて (成功したか, 所要秒) を返す。
///
/// Rustの標準ライブラリにはプロセスのタイムアウトが無いので、
/// try_waitで様子を見ながら待ち、超過したらkillする。
fn run_once(exe: &std::path::Path, argv: &[String], timeout_secs: u64) -> (bool, f64) {
    let (solved, secs, _) = run_capture(exe, argv, timeout_secs);
    (solved, secs)
}

/// run_once と同じだが、子プロセスの標準出力も返す(sketch::diagnose が
/// 筋書きの各手順の到達状況を拾うのに使う)。
pub(crate) fn run_capture(exe: &std::path::Path, argv: &[String], timeout_secs: u64) -> (bool, f64, String) {
    let start = Instant::now();
    let child = Command::new(exe)
        .args(argv)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn();
    let mut child = match child {
        Ok(c) => c,
        Err(e) => { println!("⚠️ 子プロセスを起動できませんでした: {}", e); return (false, 0.0, String::new()); }
    };
    // 子の stdout は別スレッドで待っている間ずっと吸い出す(wait し終えてから読むと、パイプのバッファが埋まった子が
    // 書き込みでブロックし、親はタイムアウトまで待って「解けなかった」と誤判定する)。
    let mut stdout = child.stdout.take();
    let reader = std::thread::spawn(move || {
        let mut out = String::new();
        if let Some(pipe) = stdout.as_mut() {
            use std::io::Read;
            let _ = pipe.read_to_string(&mut out);
        }
        out
    });
    let limit = Duration::from_secs(timeout_secs);
    let mut timed_out = false;
    loop {
        match child.try_wait() {
            Ok(Some(_)) => break,
            Ok(None) => {
                if start.elapsed() > limit {
                    let _ = child.kill();
                    let _ = child.wait();
                    timed_out = true;
                    break;
                }
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(_) => break,
        }
    }
    // killするとパイプが閉じるので、読み取りスレッドはここで必ず終わる。
    let out = reader.join().unwrap_or_default();
    let solved = !timed_out && out.contains(SUCCESS_MARK);
    (solved, start.elapsed().as_secs_f64(), out)
}

fn resolve_problems(args: &[String]) -> Option<Vec<String>> {
    let spec = args.iter()
        .find_map(|a| a.strip_prefix("--problems="))
        .unwrap_or("all");
    let all = crate::problems::ALL_PROBLEMS;
    let picked: Vec<String> = match spec {
        "all" => all.iter().map(|s| s.to_string()).collect(),
        "bench" => all.iter().filter(|s| s.starts_with("bench_")).map(|s| s.to_string()).collect(),
        other => other.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect(),
    };
    let unknown: Vec<&String> = picked.iter().filter(|p| !all.contains(&p.as_str())).collect();
    if !unknown.is_empty() {
        println!("⚠️ そんな名前の問題はありません: {:?}", unknown);
        println!("   `geom_solver list` で一覧が出ます。");
        return None;
    }
    if picked.is_empty() {
        println!("⚠️ 対象の問題が空です。");
        return None;
    }
    Some(picked)
}

/// `--vary=--heat-cap=20,40,80` を「そのフラグが取り得る引数列」に変換する。
/// 値を取らないスイッチは `--vary=--mcts=on,off` と書く。
fn parse_varies(args: &[String]) -> Vec<Vec<Vec<String>>> {
    let mut out = Vec::new();
    for spec in args.iter().filter_map(|a| a.strip_prefix("--vary=")) {
        let Some(eq) = spec.find('=') else {
            println!("⚠️ --vary は --vary=--フラグ=値,値,.. の形で書いてください: {}", spec);
            continue;
        };
        let flag = &spec[..eq];
        let values = &spec[eq + 1..];
        let mut choices: Vec<Vec<String>> = Vec::new();
        for v in values.split(',').map(|s| s.trim()).filter(|s| !s.is_empty()) {
            match v {
                "on" => choices.push(vec![flag.to_string()]),
                "off" => choices.push(Vec::new()),
                _ => choices.push(vec![format!("{}={}", flag, v)]),
            }
        }
        if !choices.is_empty() { out.push(choices); }
    }
    out
}

fn cartesian(varies: &[Vec<Vec<String>>]) -> Vec<Vec<String>> {
    let mut acc: Vec<Vec<String>> = vec![Vec::new()];
    for choices in varies {
        let mut next = Vec::new();
        for base in &acc {
            for c in choices {
                let mut v = base.clone();
                v.extend(c.iter().cloned());
                next.push(v);
            }
        }
        acc = next;
    }
    acc
}

fn truncate(s: &str, n: usize) -> String {
    if s.chars().count() <= n { s.to_string() } else { s.chars().take(n - 1).collect::<String>() + "…" }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn a(v: &[&str]) -> Vec<String> { v.iter().map(|s| s.to_string()).collect() }

    #[test]
    fn vary_expands_values_and_switches() {
        let args = a(&["geom_solver", "sweep", "--vary=--heat-cap=20,40", "--vary=--mcts=on,off"]);
        let varies = parse_varies(&args);
        let combos = cartesian(&varies);
        assert_eq!(combos.len(), 4, "2値 × 2状態 = 4通りの直積になるべき: {:?}", combos);
        assert!(combos.contains(&a(&["--heat-cap=20", "--mcts"])));
        assert!(combos.contains(&a(&["--heat-cap=40"])), "offはフラグを付けない組み合わせになるべき");
    }

    #[test]
    fn no_vary_means_one_run_with_defaults() {
        let combos = cartesian(&parse_varies(&a(&["geom_solver", "sweep"])));
        assert_eq!(combos, vec![Vec::<String>::new()],
            "--varyが無ければ「既定のまま1通り」になるべき");
    }

    #[test]
    fn problem_selection_understands_all_and_bench() {
        let all = resolve_problems(&a(&["geom_solver", "sweep", "--problems=all"])).unwrap();
        assert_eq!(all.len(), crate::problems::ALL_PROBLEMS.len());
        let bench = resolve_problems(&a(&["geom_solver", "sweep", "--problems=bench"])).unwrap();
        assert!(bench.iter().all(|p| p.starts_with("bench_")) && !bench.is_empty());
        assert!(resolve_problems(&a(&["geom_solver", "sweep", "--problems=nope"])).is_none(),
            "存在しない問題名は弾かれるべき");
    }
}

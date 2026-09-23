mod mmp_math;
mod mmp_core;
mod noise;
mod logic_core;
mod mmp_calculators;
mod theorems;
mod action_space;
mod mcts;
mod problems;
mod cli;
mod discover;
mod serve;
mod solve;
mod sweep;
mod discover_viz;
mod padic;
mod padic_eval;
mod discover_degenerate;
mod trace;
mod sketch;

use std::env;
use std::fs;

use mmp_core::RawProof;

/// `geom_solver extract-proof <raw_proofファイル> <名前A> <名前B>`:
/// 保存済みのマージ履歴から、2つの実体が名前付き定理の連鎖だけで(定理の前提も再帰的に)
/// 合流しているかを、ソルバーを再実行せずに監査する。
fn run_extract_proof(args: &[String]) {
    if args.len() < 5 {
        println!("使い方: geom_solver extract-proof <raw_proofファイル> <名前A> <名前B>");
        return;
    }
    let path = &args[2];
    let text = match fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => { println!("⚠️ '{}' を読み込めませんでした: {}", path, e); return; }
    };
    let raw = RawProof::parse(&text);
    let (Some(a), Some(b)) = (raw.id_of(&args[3]), raw.id_of(&args[4])) else {
        println!("⚠️ '{}' または '{}' という名前の実体がraw_proof中に見つかりませんでした。", args[3], args[4]);
        return;
    };
    let report = raw.verify_identical(a, b);
    // result/raw_proof_<問題名>.txt から問題名を取り出して、同じ命名規則で保存する。
    let stem = std::path::Path::new(path).file_stem().and_then(|s| s.to_str()).unwrap_or(path);
    let problem_name = stem.strip_prefix("raw_proof_").unwrap_or(stem);
    solve::output_extract_report(&report, problem_name);
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() <= 1 || args[1] == "help" || args[1] == "--help" || args[1] == "-h" {
        cli::print_help();
        return;
    }
    if args[1] == "list" {
        cli::print_catalog();
        return;
    }
    // 綴り間違いを黙って無視すると、パラメータを変えたつもりで既定値のまま走ってしまう。
    let bad = cli::unknown_flags(&args);
    if !bad.is_empty() {
        for b in &bad {
            match cli::nearest_flag(b) {
                Some(near) => println!("⚠️ 知らないオプションです: {}  (もしかして {} ?)", b, near),
                None => println!("⚠️ 知らないオプションです: {}", b),
            }
        }
        println!("   `geom_solver help` で指定できるオプションの一覧が出ます。");
        println!("   (黙って無視すると、パラメータを変えたつもりで既定値のまま走ってしまうので止めます)");
        return;
    }
    cli::init(&args);

    match args[1].as_str() {
        "sweep" => sweep::run(&args),
        "serve" => serve::run(&args),
        "diagnose" => sketch::diagnose(&args),
        "extract-proof" => run_extract_proof(&args),
        "discover" => discover::run(&args),
        "discover-degenerate" => discover_degenerate::run(&args),
        problem_name => match solve::SolveOptions::parse(&args) {
            Ok(opts) => solve::run(problem_name, &opts),
            Err(e) => println!("⚠️ {}", e),
        },
    }
}

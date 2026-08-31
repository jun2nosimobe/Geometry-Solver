mod mmp_math;
mod mmp_core;
mod logic_core;
mod mmp_calculators;
mod mmp_tester;
mod theorems;
mod action_space;
mod mcts;
mod problems; // 🌟 問題モジュール

use mmp_core::EGraph;
use logic_core::{ProverEngine, BlackboardEngine, Event};
use mmp_tester::MMPTester;
use mcts::MCTSSearchEngine;
use std::time::Instant;

fn main() {
    let mut egraph = EGraph::new();
    let tester = MMPTester::new();

    // 🌟 問題を動的にロード
    let problem = problems::load_problem("tangent_orthic", &mut egraph);

    let mut prover = ProverEngine::new(egraph);
    prover.theorems = theorems::get_all_theorems();
    let mut engine = BlackboardEngine::new(prover);
    let mut mcts = MCTSSearchEngine::new();

    let start_time = Instant::now();
    engine.schedule_full_sweep();

    while start_time.elapsed() < std::time::Duration::from_secs(1) {
        let applied_logic = engine.run_step(10000);

        // ゴール判定
        if let Some((_, ref target_args)) = problem.target_fact {
            let r1 = engine.prover.egraph.get_rep(target_args[0]);
            let r2 = engine.prover.egraph.get_rep(target_args[1]);
            if r1 == r2 {
                println!("🎉 証明完了！ (Time: {:.2?}s)", start_time.elapsed().as_secs_f64());
                break;
            }
        }

        if !applied_logic {
            println!("⏳ ロジックがStallしました。リカバリーフェーズに移行します...");
            
            // 1. オンデマンド作図
            let mut recovered = engine.resolve_demands();
            
            // 2. 角の自動生成 (スマート補完)
            if engine.resolve_angle_demands() {
                recovered = true;
            }

            // 3. MCTS (どちらも空振りした場合)
            if !recovered {
                println!("  -> 要求がないため、MCTSでランダムな補助線を探索中...");
                mcts.run_step(&mut engine.prover.egraph, &tester, 100);
                engine.schedule_full_sweep();
            }
        }
    }
}
mod mmp_math;
mod mmp_core;
mod logic_core;
mod mmp_calculators;
mod mmp_tester;
mod theorems;
mod action_space;
mod mcts;

use mmp_core::{EGraph, Definition, EntityType};
use logic_core::{ProverEngine, BlackboardEngine};
use mmp_tester::MMPTester;
use mcts::MCTSSearchEngine;
use std::time::Instant;

fn main() {
    println!("=== 幾何ソルバー 完全Rust移行版 起動 ===");

    // 1. 環境とモジュールの初期化
    let mut egraph = EGraph::new();
    let tester = MMPTester::new();
    
    // (デバッグ用: シムソンの定理の初期点をセットアップ)
    // let pA = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    // let pB = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);

    let mut prover = ProverEngine::new(egraph);
    prover.theorems = theorems::get_all_theorems(); // 定理集をロード

    let mut engine = BlackboardEngine::new(prover);
    let mut mcts = MCTSSearchEngine::new();

    // 2. メインループ実行
    let start_time = Instant::now();
    let time_limit = std::time::Duration::from_secs(30);

    println!("🔄 推論を開始...");
    engine.schedule_full_sweep();

    while start_time.elapsed() < time_limit {
        let applied_logic = engine.run_step(1000);

        if engine.check_target_reached() {
            println!("🎉 証明完了！ (Time: {:.2?}s)", start_time.elapsed().as_secs_f64());
            break;
        }

        if !applied_logic {
            println!("⏳ ロジックがStallしました。MCTSで補助線を探索中...");
            // 論理で行き詰まったらMCTSを呼び出し、グラフに変化を与える
            mcts.run_step(&mut engine.prover.egraph, &tester, 100);
            engine.schedule_full_sweep(); // グラフが変わったので再探索
        }
    }
}
mod mmp_math;
mod mmp_core;
mod logic_core;
mod mmp_calculators;
mod mmp_tester;
mod theorems;
mod action_space;
mod mcts;

use mmp_core::{EGraph, Definition, EntityType};
use logic_core::{ProverEngine, BlackboardEngine, Event};
use mmp_tester::MMPTester;
use mcts::MCTSSearchEngine;
use std::time::Instant;

fn main() {
    println!("=== 幾何ソルバー 完全Rust移行版 (ハイブリッドエンジン) 起動 ===");

    // 1. 環境とモジュールの初期化
    let mut egraph = EGraph::new();
    let tester = MMPTester::new();

    // 初期図形のセットアップ (中点連結定理のテスト)
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let m1 = egraph.create_entity("M1".to_string(), Definition::Midpoint(a, b), EntityType::Point);
    let m2 = egraph.create_entity("M2".to_string(), Definition::Midpoint(a, c), EntityType::Point);

    let l_bc = egraph.create_entity("L_BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let l_m1m2 = egraph.create_entity("L_M1M2".to_string(), Definition::new_line(m1, m2), EntityType::Line);

    let dir_bc = egraph.create_entity("Dir_BC".to_string(), Definition::DirectionOf(l_bc), EntityType::Direction);
    let dir_m1m2 = egraph.create_entity("Dir_M1M2".to_string(), Definition::DirectionOf(l_m1m2), EntityType::Direction);

    // 初期状態の安定化（自己マージとTrivial Relationsの反映）
    egraph.apply_congruence_closure();

    println!("推論前: Dir_BC(ID: {}) ≡ Dir_M1M2(ID: {}) ? -> {}", 
        egraph.get_rep(dir_bc).0, egraph.get_rep(dir_m1m2).0, 
        egraph.get_rep(dir_bc) == egraph.get_rep(dir_m1m2));

    // 2. MMPTesterによる発見フェーズ (数値計算ベースの予想抽出)
    println!("▶ 初期状態のMMP大発見を実行中 (全有効図形を爆速テスト)...");
    let vars = vec![
        "A_x".to_string(), "A_y".to_string(),
        "B_x".to_string(), "B_y".to_string(),
        "C_x".to_string(), "C_y".to_string(),
    ];
    let conjectures = tester.discover_relations(&egraph, &vars);

    // 3. 推論エンジンの初期化
    let mut prover = ProverEngine::new(egraph);
    prover.theorems = theorems::get_all_theorems();
    let mut engine = BlackboardEngine::new(prover);
    let mut mcts = MCTSSearchEngine::new();

    // MMPテストで発見した予想をイベントキューに積む
    for conj in conjectures {
        engine.emit(Event::FactProven(conj));
    }

    // 4. メインループ実行
    let start_time = Instant::now();
    let time_limit = std::time::Duration::from_secs(10);

    println!("🔄 並行ブラックボード推論を開始...");
    engine.schedule_full_sweep();

    while start_time.elapsed() < time_limit {
        let applied_logic = engine.run_step(10000);

        // 終了判定
        let rep_bc = engine.prover.egraph.get_rep(dir_bc);
        let rep_m1m2 = engine.prover.egraph.get_rep(dir_m1m2);
        
        if rep_bc == rep_m1m2 {
            println!("🎉 証明完了！ (Time: {:.2?}s)", start_time.elapsed().as_secs_f64());
            println!("🟢 結論: Dir_BC ≡ Dir_M1M2");
            break;
        }

        if !applied_logic {
            println!("⏳ ロジックがStallしました。MCTSで補助線を探索中...");
            
            // 論理で行き詰まったらMCTSを呼び出し、グラフに変化を与える
            mcts.run_step(&mut engine.prover.egraph, &tester, 100);
            
            // グラフに新しい作図が追加されたため再探索
            engine.schedule_full_sweep();
        }
    }

    let final_rep_bc = engine.prover.egraph.get_rep(dir_bc);
    let final_rep_m1m2 = engine.prover.egraph.get_rep(dir_m1m2);
    
    println!("推論後: Dir_BC(ID: {}) ≡ Dir_M1M2(ID: {}) ? -> {}", 
        final_rep_bc.0, final_rep_m1m2.0, 
        final_rep_bc == final_rep_m1m2);
}
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

fn main() {
    println!("=== 幾何ソルバー 中点連結定理 テスト開始 ===");

    let mut egraph = EGraph::new();

    // 1. 点 A, B, C を作図
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    // 2. 中点 M1(AB), M2(AC) を作図
    let m1 = egraph.create_entity("M1".to_string(), Definition::Midpoint(a, b), EntityType::Point);
    let m2 = egraph.create_entity("M2".to_string(), Definition::Midpoint(a, c), EntityType::Point);

    // 3. 直線 BC, M1M2 と、その方向（Direction）を作図
    let l_bc = egraph.create_entity("L_BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let l_m1m2 = egraph.create_entity("L_M1M2".to_string(), Definition::new_line(m1, m2), EntityType::Line);
    
    let dir_bc = egraph.create_entity("Dir_BC".to_string(), Definition::DirectionOf(l_bc), EntityType::Direction);
    let dir_m1m2 = egraph.create_entity("Dir_M1M2".to_string(), Definition::DirectionOf(l_m1m2), EntityType::Direction);

    // 実行前の確認（別々のノードIDを持っているはず）
    println!("推論前: Dir_BC(ID: {}) ≡ Dir_M1M2(ID: {}) ? -> {}", 
        egraph.get_rep(dir_bc).0, egraph.get_rep(dir_m1m2).0, 
        egraph.get_rep(dir_bc) == egraph.get_rep(dir_m1m2));

    // 推論エンジンのセットアップ
    let mut prover = ProverEngine::new(egraph);
    prover.theorems = theorems::get_all_theorems();
    let mut engine = BlackboardEngine::new(prover);

    // 探索キューに全定理をセットして推論開始
    engine.schedule_full_sweep();
    engine.run_step(10000);

    // 実行後の確認（中点連結定理が発火し、同じ代表元IDにマージされているはず）
    println!("推論後: Dir_BC(ID: {}) ≡ Dir_M1M2(ID: {}) ? -> {}", 
        engine.prover.egraph.get_rep(dir_bc).0, 
        engine.prover.egraph.get_rep(dir_m1m2).0, 
        engine.prover.egraph.get_rep(dir_bc) == engine.prover.egraph.get_rep(dir_m1m2));
}
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

fn main() {
    let args: Vec<String> = env::args().collect();
    let problem_name = if args.len() > 1 {
        &args[1]
    } else {
        "cyclic_quad" // 引数がない場合のデフォルト
    };

    println!("🚀 幾何ソルバーを起動します (対象問題: {})", problem_name);

    let mut egraph = EGraph::new();
    let _tester = MMPTester::new();

    // コマンドライン引数で問題を動的にロード
    let problem = problems::load_problem(problem_name, &mut egraph);

    let mut prover = ProverEngine::new(egraph);
    prover.theorems = theorems::get_all_theorems();
    let mut engine = BlackboardEngine::new(prover);
    let mut mcts = MCTSSearchEngine::new();
    
    for fact in &problem.initial_facts {
        match fact {
            crate::mmp_core::Fact::Identical(id1, id2) => {
                engine.prover.egraph.merge_entities(*id1, *id2);
                engine.emit(logic_core::Event::NodeMerged);
            },
            crate::mmp_core::Fact::Connected(c, p) => {
                engine.prover.egraph.link_logical_incidence(*c, *p);
            },
            _ => {}
        }
        engine.emit(logic_core::Event::FactProven(fact.clone()));
    }
    let start_time = Instant::now();

    engine.schedule_full_sweep();

    while start_time.elapsed() < std::time::Duration::from_secs(5) {
        let applied_logic = engine.run_step(10000);

        // 🌟 FIX: & をつけて参照としてパターンマッチし、所有権の移動（move）を防ぐ
        if let Some((fact_type, target_args)) = &problem.target_fact {
            if fact_type == "Identical" {
                let r1 = engine.prover.egraph.get_rep(target_args[0]);
                let r2 = engine.prover.egraph.get_rep(target_args[1]);
                if r1 == r2 {
                    println!("🎉 証明完了！ (Time: {:.2?}s)", start_time.elapsed().as_secs_f64());
                    break;
                }
            } else if fact_type == "Concyclic" {
                let r1 = engine.prover.egraph.get_rep(target_args[0]);
                let r2 = engine.prover.egraph.get_rep(target_args[1]);
                let r3 = engine.prover.egraph.get_rep(target_args[2]);
                let r4 = engine.prover.egraph.get_rep(target_args[3]);
                let fact = crate::mmp_core::Fact::new_concyclic(r1, r2, r3, r4);
                if engine.prover.facts.contains(&fact) {
                    println!("🎉 証明完了！ (Time: {:.2?}s)", start_time.elapsed().as_secs_f64());
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
                println!("  -> 要求がないため、MCTSでランダムな補助線を探索中...");
                mcts.run_step(&mut engine.prover.egraph, &_tester, 100);
                engine.schedule_full_sweep();
            }
        }
    }
    engine.prover.egraph.dump_state();
}
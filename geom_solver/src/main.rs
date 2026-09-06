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
    // 🌟 Rc化: theorems は Vec<Rc<TheoremDef>>。定理は実行中不変なので、
    // ここで一度だけ Rc に包めば、以降の参照はすべてポインタ共有になる。
    prover.theorems = theorems::get_all_theorems().into_iter().map(std::rc::Rc::new).collect();
    let mut engine = BlackboardEngine::new(prover);
    // 🌟 MCTSは現状ほぼ使われておらず、しかもe-graph全体を毎回cloneするだけで
    // 実際のロールアウト評価をしていない(スコア固定)ため、性能検証のあいだ一旦無効化する。
    // TODO: e-graphをcloneしないクローンフリーな実装に書き換えてから再有効化する。
    let mut _mcts = MCTSSearchEngine::new();
    
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
                // 🌟 Concyclicは専用Factをやめたので、target_argsの全点が
                // 共通の円にConnectedかどうかで判定する。
                let reps: Vec<_> = target_args.iter().map(|&id| engine.prover.egraph.get_rep(id)).collect();
                if engine.prover.egraph.points_share_a_circle(&reps) {
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
                // 🌟 MCTSは一旦スキップ(理由は上記コメント参照)。
                // 需要による作図もMCTSによる補助線もどちらも打てない = これ以上進めないので、
                // 残り時間を無駄なスピンで消費せずここで打ち切る。
                println!("  -> 要求がなく、MCTSも無効化中のため探索を打ち切ります。");
                break;
            }
        }
    }
    engine.prover.egraph.dump_state();
}
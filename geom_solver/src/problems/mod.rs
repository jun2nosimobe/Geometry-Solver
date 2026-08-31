pub mod cyclic_quad;
pub mod varignon;
pub mod tangent_orthic;
pub mod miquel;
pub mod nine_point;
pub mod simson;
pub mod test_parallel;
pub mod test_right_midpoint;

use crate::mmp_core::{ClassId, EGraph, Fact}; // Factを追加

pub struct ProblemSetup {
    pub target_fact: Option<(String, Vec<ClassId>)>,
    pub initial_facts: Vec<Fact>, // 🌟 追加
}

pub fn load_problem(name: &str, egraph: &mut EGraph) -> ProblemSetup {
    match name {
        "cyclic_quad" => cyclic_quad::setup(egraph),
        "varignon" => varignon::setup(egraph),
        "tangent_orthic" => tangent_orthic::setup(egraph),
        "miquel" => miquel::setup(egraph),
        "nine_point" => nine_point::setup(egraph),
        "simson" => simson::setup(egraph),
        "test_parallel" => test_parallel::setup(egraph),
        "test_right_midpoint" => test_right_midpoint::setup(egraph),
        _ => panic!("未知の問題名です: {}", name),
    }
}
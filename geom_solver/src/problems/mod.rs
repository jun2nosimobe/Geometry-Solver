pub mod cyclic_quad;
pub mod varignon;
pub mod tangent_orthic;

use crate::mmp_core::{ClassId, EGraph};

pub struct ProblemSetup {
    pub target_fact: Option<(String, Vec<ClassId>)>,
}

pub fn load_problem(name: &str, egraph: &mut EGraph) -> ProblemSetup {
    match name {
        "cyclic_quad" => cyclic_quad::setup(egraph),
        "varignon" => varignon::setup(egraph),
        "tangent_orthic" => tangent_orthic::setup(egraph),
        _ => panic!("未知の問題名です: {}", name),
    }
}
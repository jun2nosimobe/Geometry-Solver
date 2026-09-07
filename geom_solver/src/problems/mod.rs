pub mod cyclic_quad;
pub mod varignon;
pub mod tangent_orthic;
pub mod miquel;
pub mod nine_point;
pub mod nine_point_full;
pub mod miquel_quadrilateral;
pub mod simson;
pub mod test_parallel;
pub mod test_right_midpoint;
pub mod orthocenter;
pub mod orthocenter_alt;
pub mod circumcenter;
pub mod thales;
pub mod two_circles_reim;
pub mod orthic_incenter;
pub mod test_cross_ratio;
pub mod test_steiner;
pub mod test_involution;
pub mod test_isosceles_converse;
pub mod test_power_of_point;
pub mod test_steiner_converse;
pub mod geo_helpers;
pub mod bench_2012egmop1;
pub mod bench_2018silkroadp1;
pub mod bench_2011armog10p6;
pub mod bench_2010g1;
pub mod bench_2018chnwesternmop5;
pub mod bench_2005ctstp1;
pub mod bench_2005usamop3;
pub mod bench_2011balkanmop1;

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
        "nine_point_full" => nine_point_full::setup(egraph),
        "miquel_quadrilateral" => miquel_quadrilateral::setup(egraph),
        "simson" => simson::setup(egraph),
        "test_parallel" => test_parallel::setup(egraph),
        "test_right_midpoint" => test_right_midpoint::setup(egraph),
        "orthocenter" => orthocenter::setup(egraph),
        "orthocenter_alt" => orthocenter_alt::setup(egraph),
        "circumcenter" => circumcenter::setup(egraph),
        "thales" => thales::setup(egraph),
        "two_circles_reim" => two_circles_reim::setup(egraph),
        "orthic_incenter" => orthic_incenter::setup(egraph),
        "test_cross_ratio" => test_cross_ratio::setup(egraph),
        "test_steiner" => test_steiner::setup(egraph),
        "test_involution" => test_involution::setup(egraph),
        "test_isosceles_converse" => test_isosceles_converse::setup(egraph),
        "test_power_of_point" => test_power_of_point::setup(egraph),
        "test_steiner_converse" => test_steiner_converse::setup(egraph),
        "bench_2012egmop1" => bench_2012egmop1::setup(egraph),
        "bench_2018silkroadp1" => bench_2018silkroadp1::setup(egraph),
        "bench_2011armog10p6" => bench_2011armog10p6::setup(egraph),
        "bench_2010g1" => bench_2010g1::setup(egraph),
        "bench_2018chnwesternmop5" => bench_2018chnwesternmop5::setup(egraph),
        "bench_2005ctstp1" => bench_2005ctstp1::setup(egraph),
        "bench_2005usamop3" => bench_2005usamop3::setup(egraph),
        "bench_2011balkanmop1" => bench_2011balkanmop1::setup(egraph),
        _ => panic!("未知の問題名です: {}", name),
    }
}
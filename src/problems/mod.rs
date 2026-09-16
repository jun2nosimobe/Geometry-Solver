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
pub mod test_steiner_tangent;
pub mod test_involution;
pub mod test_isosceles_converse;
pub mod test_power_of_point;
pub mod test_steiner_converse;
pub mod geo_helpers;
pub mod bench_2012egmop1;
pub mod bench_2019g1;
pub mod bench_2015apmop1;
pub mod bench_2018silkroadp1;
pub mod bench_2011armog10p6;
pub mod bench_2010g1;
pub mod bench_2018chnwesternmop5;
pub mod bench_2005ctstp1;
pub mod bench_2005usamop3;
pub mod bench_2011balkanmop1;
pub mod test_spiral_similarity;
pub mod centroid;
pub mod pappus;
pub mod pascal;
pub mod desargues;
pub mod newton_gauss;

use crate::mmp_core::{ClassId, EGraph, Fact}; // Factを追加

pub struct ProblemSetup {
    pub target_fact: Option<(String, Vec<ClassId>)>,
    pub initial_facts: Vec<Fact>, // 🌟 追加
}

/// 🌟 load_problemが受け付ける問題名の一覧。`geom_solver list` の表示と、
/// `geom_solver sweep --problems=all` の対象、およびCLIの入力検証に使う。
/// load_problemのmatch腕と手で同期させる必要があるため、全部が実際に
/// 読み込めることをテスト(tests::all_listed_problems_load)で担保する。
pub const ALL_PROBLEMS: &[&str] = &[
    "cyclic_quad",
    "varignon",
    "tangent_orthic",
    "miquel",
    "nine_point",
    "nine_point_full",
    "miquel_quadrilateral",
    "simson",
    "test_parallel",
    "test_right_midpoint",
    "orthocenter",
    "orthocenter_alt",
    "circumcenter",
    "thales",
    "two_circles_reim",
    "orthic_incenter",
    "test_cross_ratio",
    "test_steiner",
    "test_steiner_tangent",
    "test_involution",
    "test_isosceles_converse",
    "test_power_of_point",
    "test_steiner_converse",
    "bench_2012egmop1",
    "bench_2019g1",
    "bench_2015apmop1",
    "bench_2018silkroadp1",
    "bench_2011armog10p6",
    "bench_2010g1",
    "bench_2018chnwesternmop5",
    "bench_2005ctstp1",
    "bench_2005usamop3",
    "bench_2011balkanmop1",
    "test_spiral_similarity",
    "centroid",
    "pappus",
    "pascal",
    "desargues",
    "newton_gauss",
];

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
        "test_steiner_tangent" => test_steiner_tangent::setup(egraph),
        "test_involution" => test_involution::setup(egraph),
        "test_isosceles_converse" => test_isosceles_converse::setup(egraph),
        "test_power_of_point" => test_power_of_point::setup(egraph),
        "test_steiner_converse" => test_steiner_converse::setup(egraph),
        "bench_2012egmop1" => bench_2012egmop1::setup(egraph),
        "bench_2019g1" => bench_2019g1::setup(egraph),
        "bench_2015apmop1" => bench_2015apmop1::setup(egraph),
        "bench_2018silkroadp1" => bench_2018silkroadp1::setup(egraph),
        "bench_2011armog10p6" => bench_2011armog10p6::setup(egraph),
        "bench_2010g1" => bench_2010g1::setup(egraph),
        "bench_2018chnwesternmop5" => bench_2018chnwesternmop5::setup(egraph),
        "bench_2005ctstp1" => bench_2005ctstp1::setup(egraph),
        "bench_2005usamop3" => bench_2005usamop3::setup(egraph),
        "bench_2011balkanmop1" => bench_2011balkanmop1::setup(egraph),
        "test_spiral_similarity" => test_spiral_similarity::setup(egraph),
        "centroid" => centroid::setup(egraph),
        "pappus" => pappus::setup(egraph),
        "pascal" => pascal::setup(egraph),
        "desargues" => desargues::setup(egraph),
        "newton_gauss" => newton_gauss::setup(egraph),
        _ => panic!("未知の問題名です: {}", name),
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    /// ALL_PROBLEMSに載っている名前が全部 load_problem で読み込めること
    /// (load_problemは未知の名前でpanicするので、載せ間違いはここで落ちる)。
    /// 目標が「前提の下でだけ成り立つ」ため、乱数座標では検算できない問題。
    ///
    /// initial_facts ではなく setup の中で直接 merge_entities して前提を
    /// 与えている問題がここに入る。例えば thales は「OP = OA」(Pが円周上)を
    /// LengthSq どうしの統合として与えるが、これは自由点Pの座標への制約で
    /// あって、乱数で置いた座標は当然それを満たさない(e-graph上でスカラーを
    /// 統合しても点の座標は動かない)。問題が間違っているのではなく、
    /// 検算の手法が適用できないだけ。
    const ASSUMES_A_HYPOTHESIS: &[&str] = &["thales", "bench_2010g1"];

    /// 🌟 ベンチマークの主張そのものが正しいことを、乱数座標で確かめる。
    ///
    /// 解けない問題は「エンジンがまだ弱い」のか「問題の書き方を間違えて
    /// いて、そもそも成り立たない主張になっている」のか区別がつかない。
    /// 後者は前者より遥かに悪い(いつまでも解けない偽のベンチマークとして
    /// 残り続ける)ので、目標が Identical の問題については、実際に乱数座標を
    /// 入れて両辺が一致するかをここで検算する。
    #[test]
    fn identical_targets_actually_hold_numerically() {
        let mut checked = 0;
        for name in ALL_PROBLEMS {
            let mut egraph = EGraph::new();
            let setup = load_problem(name, &mut egraph);
            // 🌟 前提(initial_facts)を持つ問題は対象外。例えば test_parallel は
            // 「2つの有向角が等しい」を前提に与えるが、これは自由点の座標への
            // 制約であって、乱数で置いた座標は当然それを満たさない
            // (e-graph上でスカラーを統合しても、点の座標は動かない)。
            // そういう問題をここで「偽」と判定してしまうのは検算の側の誤り。
            // 前提が作図そのものに織り込まれている問題だけを見る。
            if !setup.initial_facts.is_empty() { continue; }
            if ASSUMES_A_HYPOTHESIS.contains(name) { continue; }
            let Some((kind, args)) = setup.target_fact else { continue };
            if kind != "Identical" || args.len() < 2 { continue; }
            checked += 1;
            assert_ne!(egraph.numeric_plausibility_check(args[0], args[1], 4), Some(false),
                "問題「{}」の目標は乱数座標で成り立たない。作図の書き方が間違っていて、                 そもそも成り立たない主張になっている可能性が高い。", name);
        }
        assert!(checked >= 20, "検算できた問題が少なすぎる({}件)。除外リストが増えすぎていないか。", checked);
    }

    #[test]
    fn all_listed_problems_load() {
        for name in ALL_PROBLEMS {
            let mut egraph = EGraph::new();
            let _ = load_problem(name, &mut egraph);
        }
    }
}

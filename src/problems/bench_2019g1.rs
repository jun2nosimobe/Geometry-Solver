use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::geo_helpers::direction_of;
use crate::problems::ProblemSetup;

/// 🌟 HAGeo-409ベンチマーク: 2019 IMO Shortlist G1 (difficulty 1.2)
///
/// 三角形ABCについて、Aを通る円Γが辺AB, ACと再びD, Eで交わり、辺BCとは
/// F, Gで交わる(FはBとGの間)。円BDFのFにおける接線と、円CEGのGにおける
/// 接線がTで交わる。このときATがBCに平行であることを示す。
///
/// 🌟 方冪の定理を主題とする問題としてHAGeo-409から採った。人間の標準解も
/// 方冪(BF·BG = BD·BA、CG·CF = CE·CA)と接弦定理を使う。このエンジンには
/// 「共点二弦の相似(方冪の定理の基礎)」と接弦定理が既にあるので、
/// 定理の追加ではなくマッチング/スケジューリングの側の課題になる。
///
/// 作図の写し取り方: 原題の「Aを通る円Γ」は中心が自由な円だが、このエンジンの
/// Definitionには「中心と1点で決まる円」が無い。代わりに、Γ上の点のうち
/// 図に現れるもの2つ(D: AB上、F: BC上)を自由点として置き、
/// Γ = Circumcircle(A, D, F) と書くことで同じ自由度の図形になる
/// (A,D,Fの3点で円は一意に決まり、DとFはそれぞれ直線上を自由に動く)。
/// 残りのE, GはΓと直線AC, BCの「もう一方の交点」として決まる。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): 2019 ISL G1 (方冪) ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let line_ab = egraph.create_entity("Line_AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let line_ac = egraph.create_entity("Line_AC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let line_bc = egraph.create_entity("Line_BC".to_string(), Definition::new_line(b, c), EntityType::Line);

    // D: AB上の自由点、F: BC上の自由点。この2点とAでΓが決まる。
    let d = egraph.create_entity("D".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(d, line_ab);
    let f = egraph.create_entity("F".to_string(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(f, line_bc);

    let gamma = egraph.create_entity("Gamma".to_string(), Definition::Circumcircle(a, d, f), EntityType::Conic);

    // E: ΓとACのもう一方の交点(Aが既知の交点)。G: ΓとBCのもう一方の交点(Fが既知)。
    let e = egraph.create_entity("E".to_string(),
        Definition::SecondIntersectionOfLineAndConic(a, line_ac, gamma), EntityType::Point);
    let g = egraph.create_entity("G".to_string(),
        Definition::SecondIntersectionOfLineAndConic(f, line_bc, gamma), EntityType::Point);

    // 円BDFのFにおける接線と、円CEGのGにおける接線。
    let circ_bdf = egraph.create_entity("Circ_BDF".to_string(), Definition::Circumcircle(b, d, f), EntityType::Conic);
    let tan_f = egraph.create_entity("Tan_F".to_string(), Definition::TangentLine(circ_bdf, f), EntityType::Line);
    let circ_ceg = egraph.create_entity("Circ_CEG".to_string(), Definition::Circumcircle(c, e, g), EntityType::Conic);
    let tan_g = egraph.create_entity("Tan_G".to_string(), Definition::TangentLine(circ_ceg, g), EntityType::Line);

    let t = egraph.create_entity("T".to_string(), Definition::Intersection(tan_f, tan_g), EntityType::Point);

    let line_at = egraph.create_entity("Line_AT".to_string(), Definition::new_line(a, t), EntityType::Line);

    egraph.apply_congruence_closure();

    // 目標: AT ∥ BC。このエンジンでは平行を「2直線が同じ無限遠点を通る」=
    // 方向が一致する、として表すので、2つのDirectionOfのIdenticalになる。
    let dir_at = direction_of(egraph, line_at, "AT");
    let dir_bc = direction_of(egraph, line_bc, "BC");

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![dir_at, dir_bc])),
        initial_facts: vec![],
    }
}

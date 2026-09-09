use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

// 🌟 垂足三角形と内心 (角度の追跡)
// 鋭角三角形ABCの垂心をHとし、A,B,Cから対辺に下ろした垂線の足を
// それぞれD,E,Fとする。このときHは三角形DEFの内心である。
//
// 証明の骨格はシムソンの定理と同じ「直角2つ→共円」の角度追跡を
// 3組の垂線の足に対して使うもの。ここでは内心であることの一部分、
// すなわち「DHが角FDEを二等分する(∠HDF=∠HDE)」だけを目標にする。
// 残り2頂点(E,F)についても全く対称な議論で同様に示せるはずなので、
// 1つを代表として検証する。
//
// 垂心の存在(3本の垂線が1点で交わること)自体は別問題として一旦
// 保留しているので、ここではHを2本の垂線の交点として作図し、
// 3本目の垂線Alt_Cにも乗っているという前提を与件として明示する
// (鋭角三角形の垂心が存在することは既知の前提として使ってよい)。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 垂足三角形と内心 (角度の追跡) ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let line_bc = egraph.create_entity("Line_BC".to_string(), Definition::new_line(b, c), EntityType::Line);
    let line_ca = egraph.create_entity("Line_CA".to_string(), Definition::new_line(c, a), EntityType::Line);
    let line_ab = egraph.create_entity("Line_AB".to_string(), Definition::new_line(a, b), EntityType::Line);

    let alt_a = egraph.create_entity("Alt_A".to_string(), Definition::PerpendicularLine(line_bc, a), EntityType::Line);
    let alt_b = egraph.create_entity("Alt_B".to_string(), Definition::PerpendicularLine(line_ca, b), EntityType::Line);
    let alt_c = egraph.create_entity("Alt_C".to_string(), Definition::PerpendicularLine(line_ab, c), EntityType::Line);

    // 🌟 垂心Hの存在(3本の垂線の共点性)は既知の前提として与える
    let h = egraph.create_entity("H".to_string(), Definition::Intersection(alt_a, alt_b), EntityType::Point);
    egraph.link_logical_incidence(h, alt_c);

    // 垂線の足 D, E, F
    let d = egraph.create_entity("D".to_string(), Definition::Intersection(alt_a, line_bc), EntityType::Point);
    let e = egraph.create_entity("E".to_string(), Definition::Intersection(alt_b, line_ca), EntityType::Point);
    let f = egraph.create_entity("F".to_string(), Definition::Intersection(alt_c, line_ab), EntityType::Point);

    // DH は Alt_A そのもの(D, H はともにAlt_A上の点)なので、Dir(Alt_A)を
    // DHの方向としてそのまま使う。
    let dir_dh = egraph.create_entity("Dir_Alt_A".to_string(), Definition::DirectionOf(alt_a), EntityType::Point);

    let line_df = egraph.create_entity("Line_DF".to_string(), Definition::new_line(d, f), EntityType::Line);
    let line_de = egraph.create_entity("Line_DE".to_string(), Definition::new_line(d, e), EntityType::Line);
    let dir_df = egraph.create_entity("Dir_DF".to_string(), Definition::DirectionOf(line_df), EntityType::Point);
    let dir_de = egraph.create_entity("Dir_DE".to_string(), Definition::DirectionOf(line_de), EntityType::Point);

    // 目標: ∠(DH, DF) = ∠(DE, DH) すなわちDHが∠FDEを二等分する
    let ang_hdf = egraph.create_entity("Ang_HDF".to_string(), Definition::AnglePair(dir_dh, dir_df), EntityType::Scalar);
    let ang_edh = egraph.create_entity("Ang_EDH".to_string(), Definition::AnglePair(dir_de, dir_dh), EntityType::Scalar);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![ang_hdf, ang_edh])),
        initial_facts: vec![],
    }
}

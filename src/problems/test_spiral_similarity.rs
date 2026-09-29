use crate::mmp_core::{Definition, EGraph, EntityType, Fact};
use crate::problems::ProblemSetup;

/// 🌟 「スパイラル相似の中点対応」定理の単体検証。
/// E,A,B,D,Cを自由点とし、「△EABと△EDCが同じ向きに相似」という前提を
/// (test_isosceles_converse.rs等と同じ確立された流儀で)直接
/// Fact::new_identicalとして与える: E での角の一致 ∠(EA,EB)=∠(ED,EC) と、
/// A・D での角の一致 ∠(AE,AB)=∠(DE,DC)(有向角の2組の一致は同じ向きの相似と同値)。
/// このときM=Midpoint(A,B), N=Midpoint(D,C)について∠AEM=∠DENと
/// なることを示す(定理の結論)。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: スパイラル相似の中点対応(単体検証) ===");
    let e = egraph.create_entity("E".to_string(), Definition::FreePoint, EntityType::Point);
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let d = egraph.create_entity("D".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let line_ea = egraph.create_entity("LineEA".to_string(), Definition::new_line(e, a), EntityType::Line);
    let line_eb = egraph.create_entity("LineEB".to_string(), Definition::new_line(e, b), EntityType::Line);
    let line_ed = egraph.create_entity("LineED".to_string(), Definition::new_line(e, d), EntityType::Line);
    let line_ec = egraph.create_entity("LineEC".to_string(), Definition::new_line(e, c), EntityType::Line);

    let dir_ea = egraph.create_entity("DirEA".to_string(), Definition::DirectionOf(line_ea), EntityType::Point);
    let dir_eb = egraph.create_entity("DirEB".to_string(), Definition::DirectionOf(line_eb), EntityType::Point);
    let dir_ed = egraph.create_entity("DirED".to_string(), Definition::DirectionOf(line_ed), EntityType::Point);
    let dir_ec = egraph.create_entity("DirEC".to_string(), Definition::DirectionOf(line_ec), EntityType::Point);

    let ang_e_ab = egraph.create_entity("AngE_AB".to_string(), Definition::AnglePair(dir_ea, dir_eb), EntityType::Scalar);
    let ang_e_dc = egraph.create_entity("AngE_DC".to_string(), Definition::AnglePair(dir_ed, dir_ec), EntityType::Scalar);

    let line_ab = egraph.create_entity("LineAB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let line_dc = egraph.create_entity("LineDC".to_string(), Definition::new_line(d, c), EntityType::Line);
    let dir_ab = egraph.create_entity("DirAB".to_string(), Definition::DirectionOf(line_ab), EntityType::Point);
    let dir_dc = egraph.create_entity("DirDC".to_string(), Definition::DirectionOf(line_dc), EntityType::Point);
    let ang_a = egraph.create_entity("AngA".to_string(), Definition::AnglePair(dir_ea, dir_ab), EntityType::Scalar);
    let ang_d = egraph.create_entity("AngD".to_string(), Definition::AnglePair(dir_ed, dir_dc), EntityType::Scalar);

    // 目標を構成するM,N側も先に組み立てておく
    let m = egraph.create_entity("M".to_string(), Definition::Midpoint(a, b), EntityType::Point);
    let n = egraph.create_entity("N".to_string(), Definition::Midpoint(d, c), EntityType::Point);
    let line_em = egraph.create_entity("LineEM".to_string(), Definition::new_line(e, m), EntityType::Line);
    let line_en = egraph.create_entity("LineEN".to_string(), Definition::new_line(e, n), EntityType::Line);
    let dir_em = egraph.create_entity("DirEM".to_string(), Definition::DirectionOf(line_em), EntityType::Point);
    let dir_en = egraph.create_entity("DirEN".to_string(), Definition::DirectionOf(line_en), EntityType::Point);
    let ang_e_am = egraph.create_entity("AngE_AM".to_string(), Definition::AnglePair(dir_ea, dir_em), EntityType::Scalar);
    let ang_e_dn = egraph.create_entity("AngE_DN".to_string(), Definition::AnglePair(dir_ed, dir_en), EntityType::Scalar);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![ang_e_am, ang_e_dn])),
        initial_facts: vec![
            Fact::new_identical(ang_e_ab, ang_e_dc),
            Fact::new_identical(ang_a, ang_d),
        ],
    }
}

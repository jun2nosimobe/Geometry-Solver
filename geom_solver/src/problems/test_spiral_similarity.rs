use crate::mmp_core::{Definition, EGraph, EntityType, Fact};
use crate::problems::ProblemSetup;

/// 🌟 「スパイラル相似の中点対応」定理の単体検証。
/// E,A,B,D,Cを自由点とし、「△EABと△EDCが直接相似」という前提を
/// (test_isosceles_converse.rs等と同じ確立された流儀で)直接
/// Fact::new_identicalとして与える: 角度の一致(∠AEB=∠DEC)と
/// 比の一致(EA・EC=EB・ED、LengthSqの積として)の2つ。
/// このときM=Midpoint(A,B), N=Midpoint(D,C)について∠AEM=∠DENと
/// なることを示す(定理の結論の一方)。
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

    let ang_e_ab = egraph.create_entity("AngE_AB".to_string(), Definition::AnglePair(dir_ea, dir_eb), EntityType::Angle);
    let ang_e_dc = egraph.create_entity("AngE_DC".to_string(), Definition::AnglePair(dir_ed, dir_ec), EntityType::Angle);

    let lensq_ea = egraph.create_entity("LenSqEA".to_string(), Definition::LengthSq(e, a), EntityType::Scalar);
    let lensq_eb = egraph.create_entity("LenSqEB".to_string(), Definition::LengthSq(e, b), EntityType::Scalar);
    let lensq_ed = egraph.create_entity("LenSqED".to_string(), Definition::LengthSq(e, d), EntityType::Scalar);
    let lensq_ec = egraph.create_entity("LenSqEC".to_string(), Definition::LengthSq(e, c), EntityType::Scalar);
    let prod_eaec = egraph.create_entity("ProdEAEC".to_string(), Definition::Product(lensq_ea, lensq_ec), EntityType::Scalar);
    let prod_ebed = egraph.create_entity("ProdEBED".to_string(), Definition::Product(lensq_eb, lensq_ed), EntityType::Scalar);

    // 目標を構成するM,N側も先に組み立てておく
    let m = egraph.create_entity("M".to_string(), Definition::Midpoint(a, b), EntityType::Point);
    let n = egraph.create_entity("N".to_string(), Definition::Midpoint(d, c), EntityType::Point);
    let line_em = egraph.create_entity("LineEM".to_string(), Definition::new_line(e, m), EntityType::Line);
    let line_en = egraph.create_entity("LineEN".to_string(), Definition::new_line(e, n), EntityType::Line);
    let dir_em = egraph.create_entity("DirEM".to_string(), Definition::DirectionOf(line_em), EntityType::Point);
    let dir_en = egraph.create_entity("DirEN".to_string(), Definition::DirectionOf(line_en), EntityType::Point);
    let ang_e_am = egraph.create_entity("AngE_AM".to_string(), Definition::AnglePair(dir_ea, dir_em), EntityType::Angle);
    let ang_e_dn = egraph.create_entity("AngE_DN".to_string(), Definition::AnglePair(dir_ed, dir_en), EntityType::Angle);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![ang_e_am, ang_e_dn])),
        initial_facts: vec![
            Fact::new_identical(ang_e_ab, ang_e_dc),
            Fact::new_identical(prod_eaec, prod_ebed),
        ],
    }
}

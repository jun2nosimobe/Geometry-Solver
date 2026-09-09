use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 円に内接する四角形 (円周角の連鎖) ===");

    let o = egraph.create_entity("O".to_string(), Definition::FreePoint, EntityType::Point);
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    let d = egraph.create_entity("D".to_string(), Definition::FreePoint, EntityType::Point);

    // 円を作図し、点A,B,C,Dが同一円周上にあるとする
    let circ = egraph.create_entity("Circ".to_string(), Definition::Circumcircle(a, b, c), EntityType::Conic);
    egraph.link_logical_incidence(d, circ); // Dも同じ円に乗せる
    // 🌟 「円周角の定理」はConnected(点,円)の4連続で共円を判定するので、
    // A,B,C(Circumcircleの定義から自動リンク)とD(ここでリンク)が
    // 同じ円に乗っているという構造的な接続だけで発火するようになった。

    // 対角線 AC, BD を引く
    let l_ac = egraph.create_entity("L_AC".to_string(), Definition::new_line(a, c), EntityType::Line);
    let l_bd = egraph.create_entity("L_BD".to_string(), Definition::new_line(b, d), EntityType::Line);

    // 辺 AB, CD を引く
    let l_ab = egraph.create_entity("L_AB".to_string(), Definition::new_line(a, b), EntityType::Line);
    let l_cd = egraph.create_entity("L_CD".to_string(), Definition::new_line(c, d), EntityType::Line);

    let dir_ac = egraph.create_entity("Dir_AC".to_string(), Definition::DirectionOf(l_ac), EntityType::Point);
    let dir_bd = egraph.create_entity("Dir_BD".to_string(), Definition::DirectionOf(l_bd), EntityType::Point);
    let dir_ab = egraph.create_entity("Dir_AB".to_string(), Definition::DirectionOf(l_ab), EntityType::Point);
    let dir_cd = egraph.create_entity("Dir_CD".to_string(), Definition::DirectionOf(l_cd), EntityType::Point);

    // 目標: 円周角 ∠(AB, AC) ≡ ∠(DB, DC) が証明できるか
    let ang1 = egraph.create_entity("Ang_BAC".to_string(), Definition::AnglePair(dir_ab, dir_ac), EntityType::Scalar);
    let ang2 = egraph.create_entity("Ang_BDC".to_string(), Definition::AnglePair(dir_bd, dir_cd), EntityType::Scalar);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![ang1, ang2])),
        initial_facts: vec![],
    }
}
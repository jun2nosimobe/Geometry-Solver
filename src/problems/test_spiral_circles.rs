use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::geo_helpers::{angle_pair, direction_of};
use crate::problems::ProblemSetup;

/// 🌟 スパイラル相似が作図から生じる古典的な配置(前提を事実として与えない版)。
/// 2円 ω1・ω2 が E と P で交わる。P を通る直線が ω1・ω2 と再び A・D で交わり、P を通る別の直線が B・C で交わる。
/// このとき E は A→D, B→C に写すスパイラル相似の中心で(△EAB ∽ △EDC、同じ向き)、
/// AB の中点 M・DC の中点 N について ∠(EA,EM) = ∠(ED,EN)。
/// 角の2組の一致(E での角と A・D での角)は、どちらも円周角の定理から出る。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 2円の交点を中心とするスパイラル相似 ===");
    let e = egraph.create_entity("E".to_string(), Definition::FreePoint, EntityType::Point);
    let p = egraph.create_entity("P".to_string(), Definition::FreePoint, EntityType::Point);
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let x = egraph.create_entity("X".to_string(), Definition::FreePoint, EntityType::Point);
    let q = egraph.create_entity("Q".to_string(), Definition::FreePoint, EntityType::Point);

    let w1 = egraph.create_entity("Omega1".to_string(), Definition::Circumcircle(e, p, a), EntityType::Conic);
    let w2 = egraph.create_entity("Omega2".to_string(), Definition::Circumcircle(e, p, x), EntityType::Conic);

    let line_pa = egraph.create_entity("Line_PA".to_string(), Definition::new_line(p, a), EntityType::Line);
    let d = egraph.create_entity("D".to_string(), Definition::SecondIntersectionOfLineAndConic(p, line_pa, w2), EntityType::Point);
    let line_pq = egraph.create_entity("Line_PQ".to_string(), Definition::new_line(p, q), EntityType::Line);
    let b = egraph.create_entity("B".to_string(), Definition::SecondIntersectionOfLineAndConic(p, line_pq, w1), EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::SecondIntersectionOfLineAndConic(p, line_pq, w2), EntityType::Point);

    let m = egraph.create_entity("M".to_string(), Definition::Midpoint(a, b), EntityType::Point);
    let n = egraph.create_entity("N".to_string(), Definition::Midpoint(d, c), EntityType::Point);
    let line_ea = egraph.create_entity("LineEA".to_string(), Definition::new_line(e, a), EntityType::Line);
    let line_ed = egraph.create_entity("LineED".to_string(), Definition::new_line(e, d), EntityType::Line);
    let line_em = egraph.create_entity("LineEM".to_string(), Definition::new_line(e, m), EntityType::Line);
    let line_en = egraph.create_entity("LineEN".to_string(), Definition::new_line(e, n), EntityType::Line);
    let d_ea = direction_of(egraph, line_ea, "EA");
    let d_ed = direction_of(egraph, line_ed, "ED");
    let d_em = direction_of(egraph, line_em, "EM");
    let d_en = direction_of(egraph, line_en, "EN");
    let ang_am = angle_pair(egraph, d_ea, d_em, "E_AM");
    let ang_dn = angle_pair(egraph, d_ed, d_en, "E_DN");

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![ang_am, ang_dn])),
        initial_facts: vec![],
    }
}

use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

// 🌟 交わる2円と直線 (Reimの定理の一種)
// 2つの円 Γ1, Γ2 が2点 A, B で交わっている。Aを通る直線がΓ1, Γ2とそれぞれ
// 点C, Dで交わり、Bを通る直線がΓ1, Γ2とそれぞれ点E, Fで交わっているとする。
// このとき直線CEと直線DFは平行になる。
//
// 「線がΓ1と交わる」という操作(円と直線の交点)自体は今のエンジンには
// 無いので、C,Eなどは自由点として作り、円の定義(Circumcircle)または
// link_logical_incidenceで「その円の上にある」という前提を直接与え、
// 別々に「共線である」という前提もlink_logical_incidenceで直接与える形
// (前提を構造的な接続として明示する)にした。これはsimson.rs等で
// 「Pが外接円上にある」という前提を与えたのと同じ考え方。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 交わる2円と直線 (Reimの定理) ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);
    let d = egraph.create_entity("D".to_string(), Definition::FreePoint, EntityType::Point);
    let e = egraph.create_entity("E".to_string(), Definition::FreePoint, EntityType::Point);
    let f = egraph.create_entity("F".to_string(), Definition::FreePoint, EntityType::Point);

    // Γ1 = Circumcircle(A,B,C) (Cはこの定義そのものでΓ1上にある)。Eも
    // 別ルートでΓ1上にあることを与える(Bを通る直線がΓ1と交わる点)。
    let gamma1 = egraph.create_entity("Gamma1".to_string(), Definition::Circumcircle(a, b, c), EntityType::Circle);
    egraph.link_logical_incidence(e, gamma1);

    // Γ2 = Circumcircle(A,B,D) (Dはこの定義そのものでΓ2上にある)。Fも
    // 別ルートでΓ2上にあることを与える(Bを通る直線がΓ2と交わる点)。
    let gamma2 = egraph.create_entity("Gamma2".to_string(), Definition::Circumcircle(a, b, d), EntityType::Circle);
    egraph.link_logical_incidence(f, gamma2);

    // C, A, D はこの順に一直線上 (Aを通る1本の直線)
    let line_cad = egraph.create_entity("Line_CAD".to_string(), Definition::new_line(c, a), EntityType::Line);
    egraph.link_logical_incidence(d, line_cad);

    // E, B, F はこの順に一直線上 (Bを通る1本の直線)
    let line_ebf = egraph.create_entity("Line_EBF".to_string(), Definition::new_line(e, b), EntityType::Line);
    egraph.link_logical_incidence(f, line_ebf);

    // 目標: 直線CEと直線DFが平行 (方向が一致)
    let line_ce = egraph.create_entity("Line_CE".to_string(), Definition::new_line(c, e), EntityType::Line);
    let line_df = egraph.create_entity("Line_DF".to_string(), Definition::new_line(d, f), EntityType::Line);
    let dir_ce = egraph.create_entity("Dir_CE".to_string(), Definition::DirectionOf(line_ce), EntityType::Point);
    let dir_df = egraph.create_entity("Dir_DF".to_string(), Definition::DirectionOf(line_df), EntityType::Point);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![dir_ce, dir_df])),
        initial_facts: vec![],
    }
}

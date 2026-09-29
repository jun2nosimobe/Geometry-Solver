use crate::mmp_core::{Definition, EGraph, EntityType};
use crate::problems::ProblemSetup;

/// 🌟 重心の存在定理: 三角形の3本の中線は1点で交わる。
///
/// ユーザー提案「重心の存在定理が良いベンチマークになりそう」。
/// 目標は「中線Aと中線Bの交点」と「中線Aと中線Cの交点」が同じ点であること
/// ――これは自由作図の探索が出す「3直線が1点で交わる」をそのまま証明の
/// 目標に翻訳した形と全く同じなので、その経路の実戦テストになる。
///
/// 内容としては比についての主張(中線は互いを2:1に分ける)で、古典的には
/// チェバの定理そのもの。射影的には「共線4点の複比」で書けるので、
/// 複比の透視射影不変性とその逆(propagate_cross_ratio_uniqueness)が
/// 噛み合うかを見る問題でもある。
pub fn setup(egraph: &mut EGraph) -> ProblemSetup {
    println!("=== 問題: 重心の存在定理 (3中線の共点性) ===");
    let a = egraph.create_entity("A".to_string(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".to_string(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".to_string(), Definition::FreePoint, EntityType::Point);

    let ma = egraph.create_entity("Ma".to_string(), Definition::Midpoint(b, c), EntityType::Point);
    let mb = egraph.create_entity("Mb".to_string(), Definition::Midpoint(c, a), EntityType::Point);
    let mc = egraph.create_entity("Mc".to_string(), Definition::Midpoint(a, b), EntityType::Point);

    let med_a = egraph.create_entity("Med_A".to_string(), Definition::new_line(a, ma), EntityType::Line);
    let med_b = egraph.create_entity("Med_B".to_string(), Definition::new_line(b, mb), EntityType::Line);
    let med_c = egraph.create_entity("Med_C".to_string(), Definition::new_line(c, mc), EntityType::Line);

    let g1 = egraph.create_entity("G1".to_string(), Definition::Intersection(med_a, med_b), EntityType::Point);
    let g2 = egraph.create_entity("G2".to_string(), Definition::Intersection(med_a, med_c), EntityType::Point);

    egraph.apply_congruence_closure();

    ProblemSetup {
        target_fact: Some(("Identical".to_string(), vec![g1, g2])),
        initial_facts: vec![],
    }
}

/// 🌟 証明の筋書き(sketch.rs)。G = Med_B ∩ Med_C とし、BG・CG の中点を X・Y とする。McMbYX が平行四辺形になり、
/// 対角線 XMb・McY の交点が G なので BG = 2 GMb。同じ比の点は中線上で一意だから、中線 A も G を通る。
pub const SKETCH: &str = r#"
aux point G inter Med_B Med_C
aux point X mid B G
aux point Y mid C G
step parallel X Y B C              | △GBC の中点連結: XY ∥ BC
step equal_length Mc Mb X Y        | 中点連結: McMb = BC/2 = XY
step parallel Mc X Mb Y            | どちらも AG に平行(△ABG, △ACG の中点連結)
step equal_length G X G Mb         | 平行四辺形 McMbYX の対角線 XMb は G で二等分される(BG = 2 GMb)
step coincide G1 G                 | Med_B 上で B から 2:1 の点は一意 ⇒ 中線 A も G を通る
"#;

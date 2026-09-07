use super::*;
use crate::mmp_math::ModInt;
use crate::mmp_calculators;
use rustc_hash::FxHashMap;

#[test]
fn test_line_merge_by_two_points() {
    let mut egraph = EGraph::new();
    let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);

    let l1 = egraph.create_entity("L1".into(), Definition::new_line(p_a, p_b), EntityType::Line);
    let l2 = egraph.create_entity("L2".into(), Definition::new_line(p_b, p_a), EntityType::Line);

    egraph.apply_congruence_closure();
    assert_eq!(egraph.get_rep(l1), egraph.get_rep(l2), "2点を共有する直線はマージされるべき");
}

#[test]
fn test_incidence_preservation_after_merge() {
    let mut egraph = EGraph::new();
    let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let p_c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);

    let l1 = egraph.create_entity("L1".into(), Definition::new_line(p_a, p_b), EntityType::Line);
    let l2 = egraph.create_entity("L2".into(), Definition::FreePoint, EntityType::Line); // 仮の独立した直線

    // CをL2上に乗せる (論理リンク)
    egraph.link_logical_incidence(p_c, l2);
    assert!(egraph.is_connected(p_c, l2), "リンク直後は接続されている");

    // L1とL2を強制的にマージ
    egraph.merge_entities(l1, l2);
    egraph.apply_congruence_closure();

    // L2の代表元はL1になっているはずなので、CはL1に乗っていると判定されるべき
    assert!(egraph.is_connected(p_c, l1), "マージ後、所属関係(Incidence)が代表元に引き継がれるべき");
}

#[test]
fn test_line_merge_by_point_and_direction() {
    // 🐛 FIX: 以前はA,B,Cを完全に独立な自由点にした上で
    // merge_entities(dir_ab, dir_ac) により方向の一致を「強制的に(検証なしで)」
    // 仮定していた。これは健全性チェック(numeric_plausibility_check)導入後は
    // 矛盾する(ランダムなA,B,Cの座標では、無関係な方向を強制一致させても
    // 実際の直線の式までは一致しないため、数値的には「別の直線」に見えて
    // しまい、正しく却下されてテストが失敗する)。
    // 代わりに、Aを通りL_ABに平行な直線(ParallelLine)を作る、という
    // 現実的かつ数値的にも常に真になるシナリオに置き換えた: Aは既にL_AB上に
    // あるので、「Aを通りL_ABに平行な直線」は幾何学的に必ずL_AB自身になる。
    let mut egraph = EGraph::new();
    let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);

    let l_ab = egraph.create_entity("L_AB".into(), Definition::new_line(p_a, p_b), EntityType::Line);
    let l_para = egraph.create_entity("L_para".into(), Definition::ParallelLine(l_ab, p_a), EntityType::Line);
    egraph.apply_congruence_closure(); // ここで直線の自動マージが走るはず

    // Aという1点を共有し、かつ平行線の定義により方向も一致するので、
    // L_AB と L_para は同一の直線になるべき
    assert_eq!(egraph.get_rep(l_ab), egraph.get_rep(l_para), "1点を共有し、平行線の定義で方向も一致する直線はマージされるべき");
}

#[test]
fn test_perpendicular_creates_ang90() {
    let mut egraph = EGraph::new();
    let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let p_c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);

    let l_ab = egraph.create_entity("L_AB".into(), Definition::new_line(p_a, p_b), EntityType::Line);

    // CからABへ垂線を下ろす
    let perp = egraph.create_entity("Perp_C_AB".into(), Definition::PerpendicularLine(l_ab, p_c), EntityType::Line);
    egraph.apply_congruence_closure();

    // 垂線と元の直線の方向からなる有向角を取得
    let dir_ab = egraph.memo.get(&Definition::DirectionOf(l_ab)).unwrap();
    let dir_perp = egraph.memo.get(&Definition::DirectionOf(perp)).unwrap();

    let ang = egraph.memo.get(&Definition::AnglePair(*dir_ab, *dir_perp)).unwrap();

    // 自動的にAng90とマージされているはず
    assert_eq!(egraph.get_rep(*ang), egraph.get_rep(egraph.ang90), "垂線から作られた有向角は自動的にAng90にマージされるべき");
}

#[test]
fn test_parallel_merges_directions() {
    let mut egraph = EGraph::new();
    let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let p_c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);

    let l_ab = egraph.create_entity("L_AB".into(), Definition::new_line(p_a, p_b), EntityType::Line);
    let para = egraph.create_entity("Para_C_AB".into(), Definition::ParallelLine(l_ab, p_c), EntityType::Line);
    egraph.apply_congruence_closure();

    let dir_ab = egraph.memo.get(&Definition::DirectionOf(l_ab)).unwrap();
    let dir_para = egraph.memo.get(&Definition::DirectionOf(para)).unwrap();

    assert_eq!(egraph.get_rep(*dir_ab), egraph.get_rep(*dir_para), "平行線として作図された直線の方向はマージされるべき");
}

#[test]
fn test_midpoint_symmetry_and_incidence() {
    let mut egraph = EGraph::new();
    let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);

    let m1 = egraph.create_entity("M1".into(), Definition::Midpoint(p_a, p_b), EntityType::Point);
    let m2 = egraph.create_entity("M2".into(), Definition::Midpoint(p_b, p_a), EntityType::Point);
    egraph.apply_congruence_closure();

    assert_eq!(egraph.get_rep(m1), egraph.get_rep(m2), "引数の順序が逆の中点はマージされるべき");

    // 中点を作図すると自動的にその2点を結ぶ直線が作られ、中点がその上に乗る
    let l_ab = egraph.memo.get(&Definition::LineThroughPoints(p_a, p_b)).expect("ABを結ぶ直線が自動生成されているべき");
    assert!(egraph.is_connected(m1, *l_ab), "中点は元の2点を結ぶ直線上にあるべき");
}
#[test]
fn test_angle_pair_symmetry_and_normalization() {
    let mut egraph = EGraph::new();
    let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let p_c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);

    let l1 = egraph.create_entity("L1".into(), Definition::new_line(p_a, p_b), EntityType::Line);
    let l2 = egraph.create_entity("L2".into(), Definition::new_line(p_b, p_c), EntityType::Line);

    // 🌟 FIX: `*` でデリファレンスして値(ClassId)としてコピーし、借用を即座に終わらせる
    let d1 = *egraph.memo.get(&Definition::DirectionOf(l1)).unwrap();
    let d2 = *egraph.memo.get(&Definition::DirectionOf(l2)).unwrap();

    // 異なる順序で有向角を作成
    let ang1 = egraph.create_entity("Ang1".into(), Definition::AnglePair(d1, d2), EntityType::Angle);
    let ang2 = egraph.create_entity("Ang2".into(), Definition::AnglePair(d1, d2), EntityType::Angle);

    egraph.apply_congruence_closure();
    assert_eq!(egraph.get_rep(ang1), egraph.get_rep(ang2), "同一の方向ペアから作られた有向角は一意にマージされるべき");
}

#[test]
fn test_ang90_constant_propagation() {
    let mut egraph = EGraph::new();
    let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let p_c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);

    let l_ab = egraph.create_entity("L_AB".into(), Definition::new_line(p_a, p_b), EntityType::Line);

    let perp = egraph.create_entity("Perp".into(), Definition::PerpendicularLine(l_ab, p_c), EntityType::Line);
    egraph.apply_congruence_closure();

    // 🌟 FIX: 同様に値としてコピー
    let dir_ab = *egraph.memo.get(&Definition::DirectionOf(l_ab)).unwrap();
    let dir_perp = *egraph.memo.get(&Definition::DirectionOf(perp)).unwrap();

    let ang_test = egraph.create_entity("AngTest".into(), Definition::AnglePair(dir_ab, dir_perp), EntityType::Angle);
    egraph.apply_congruence_closure();

    assert_eq!(egraph.get_rep(ang_test), egraph.get_rep(egraph.ang90), "垂直な2直線の有向角はグローバルなang90と一致するべき");
}

#[test]
fn test_parallel_direction_angle_zero() {
    let mut egraph = EGraph::new();
    let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let p_c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);

    let l1 = egraph.create_entity("L1".into(), Definition::new_line(p_a, p_b), EntityType::Line);
    let l2 = egraph.create_entity("L2".into(), Definition::ParallelLine(l1, p_c), EntityType::Line);
    egraph.apply_congruence_closure();

    // 🌟 FIX: 同様に値としてコピー
    let d1 = *egraph.memo.get(&Definition::DirectionOf(l1)).unwrap();
    let d2 = *egraph.memo.get(&Definition::DirectionOf(l2)).unwrap();

    assert_eq!(egraph.get_rep(d1), egraph.get_rep(d2), "平行線作図により方向ベクトルがマージされるべき");
}

#[test]
fn test_perpendiculars_to_same_line_are_parallel() {
    // 🌟 垂線の射影的表現(PerpDirectionOf)の検証:
    // 同じ直線 L に対する2本の垂線(異なる点 B, C からそれぞれ下ろした)は、
    // 「有向角の加法性」等の角度チェイス定理を一切使わずとも、
    // PerpDirectionOf(Dir(L)) という同じ値への合同閉包だけで
    // 自動的に平行(同じ方向)だと判定されるべき。
    let mut egraph = EGraph::new();
    let p_a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let p_b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let p_c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);

    let l = egraph.create_entity("L".into(), Definition::new_line(p_a, p_b), EntityType::Line);
    let perp_from_b = egraph.create_entity("Perp_B".into(), Definition::PerpendicularLine(l, p_b), EntityType::Line);
    let perp_from_c = egraph.create_entity("Perp_C".into(), Definition::PerpendicularLine(l, p_c), EntityType::Line);
    egraph.apply_congruence_closure();

    let dir_perp_b = *egraph.memo.get(&Definition::DirectionOf(egraph.get_rep(perp_from_b))).unwrap();
    let dir_perp_c = *egraph.memo.get(&Definition::DirectionOf(egraph.get_rep(perp_from_c))).unwrap();

    assert_eq!(
        egraph.get_rep(dir_perp_b), egraph.get_rep(dir_perp_c),
        "同じ直線への2本の垂線は、角度チェイス定理を使わずとも合同閉包だけで方向が一致するべき"
    );
}

#[test]
fn test_harmonic_conjugate_construction_is_numerically_correct() {
    // 🌟 完全四辺形(直線と交点だけ)による調和共役点の作図が、実際に
    // 交叉比 -1 を満たす点を計算していることを、独立した閉じた式
    // (calc_harmonic_conjugate)との数値一致で検証する。
    // A=(0,0), B=(4,0), C=(1,0) のとき、古典的な計算から
    // 調和共役点 D は (-2, 0) になる。
    let mut egraph = EGraph::new();
    let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);

    let d = egraph.construct_harmonic_conjugate(a, b, c);

    // 補助点 P, Q の名前は construct_harmonic_conjugate の命名規則に従う
    let mut vars: FxHashMap<String, ModInt> = FxHashMap::default();
    vars.insert("A_x".into(), ModInt::new(0));
    vars.insert("A_y".into(), ModInt::new(0));
    vars.insert("B_x".into(), ModInt::new(4));
    vars.insert("B_y".into(), ModInt::new(0));
    vars.insert("C_x".into(), ModInt::new(1));
    vars.insert("C_y".into(), ModInt::new(0));
    vars.insert("P_Harm_A_B_C_(Aux)_x".into(), ModInt::new(2));
    vars.insert("P_Harm_A_B_C_(Aux)_y".into(), ModInt::new(5));
    vars.insert("Q_Harm_A_B_C_(Aux)_x".into(), ModInt::new(0));
    vars.insert("Q_Harm_A_B_C_(Aux)_y".into(), ModInt::new(-5));

    let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
    let vd = egraph.evaluate_node(d, &vars, &mut cache).expect("Dが数値的に計算できるべき");
    let vd = mmp_calculators::normalize(&vd);

    // 期待値 D=(-2, 0, 1) (斉次座標)
    let x = vd[0] / vd[2];
    let y = vd[1] / vd[2];
    assert_eq!(x, ModInt::new(-2), "作図されたDのx座標は-2であるべき");
    assert_eq!(y, ModInt::new(0), "作図されたDのy座標は0であるべき");

    // 独立した閉じた式(calc_harmonic_conjugate)とも一致するはず
    let va = egraph.evaluate_node(a, &vars, &mut cache).unwrap();
    let vb = egraph.evaluate_node(b, &vars, &mut cache).unwrap();
    let vc = egraph.evaluate_node(c, &vars, &mut cache).unwrap();
    let vd_formula = mmp_calculators::normalize(&mmp_calculators::calc_harmonic_conjugate(&va, &vb, &vc));
    assert_eq!(vd, vd_formula, "完全四辺形による作図と閉じた式による計算が一致するべき");
}

#[test]
fn test_harmonic_conjugate_is_an_involution() {
    // 🌟 対合性: H(A,B,D) は、Dを求めるための2回目の作図をやり直さずとも
    // 合同閉包だけで自動的にCへ一致するべき(construct_harmonic_conjugateの
    // 内部で登録される)。
    let mut egraph = EGraph::new();
    let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
    let d = egraph.construct_harmonic_conjugate(a, b, c);

    // 新規に作図せず、既存の合同閉包だけでH(A,B,D)=Cが引ける
    let inv_def = egraph.normalize_definition(&Definition::HarmonicConjugateOf(a, b, d));
    let &inv_id = egraph.memo.get(&inv_def).expect("対合の逆像は既にmemoに登録済みのはず");
    assert_eq!(egraph.get_rep(inv_id), egraph.get_rep(c), "H(A,B,H(A,B,C)) は C に一致するべき(対合性)");

    // 交叉比のペア交換対称性: H(C,D,A) は B に一致するべき
    let swap_def = egraph.normalize_definition(&Definition::HarmonicConjugateOf(c, d, a));
    let &swap_id = egraph.memo.get(&swap_def).expect("ペア交換の像も既にmemoに登録済みのはず");
    assert_eq!(egraph.get_rep(swap_id), egraph.get_rep(b), "(A,B;C,D)=-1 ⟹ (C,D;A,B)=-1 つまり H(C,D,A)=B であるべき");
}

/// 🌟 numeric_plausibility_checkが、直線への構造的前提(link_logical_incidenceだけ
/// による接続、自身のDefinitionからは自然に従わないもの)を持つ自由点についても、
/// 以前のように問答無用でNone(判定不能)に倒すのではなく、実際にその前提を
/// 満たす座標をサンプリングして検証を続けられることを確認する。
#[test]
fn test_numeric_check_samples_consistent_point_on_line() {
    let mut egraph = EGraph::new();
    let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let line_ab = egraph.create_entity("L_AB".into(), Definition::new_line(a, b), EntityType::Line);

    // QはFreePointのまま(定義上はL_ABと無関係)だが、「L_AB上にある」という
    // 前提だけをlink_logical_incidenceで直接与える(simson.rs等と同じパターン)。
    let q = egraph.create_entity("Q".into(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(q, line_ab);

    // AとQを通る直線は、Qが本当にL_AB上にあるなら幾何学的に必ずL_ABそのものになる。
    let line_aq = egraph.create_entity("L_AQ".into(), Definition::new_line(a, q), EntityType::Line);

    // 🐛 以前の実装: has_extraneous_incidence(q) が真になるため、この比較は
    // 問答無用でNone(判定不能)を返していた。現在はQに「L_AB上にある」という
    // 前提を満たす座標を実際にサンプリングして検証できるので、Some(true)が返るべき。
    assert_eq!(
        egraph.numeric_plausibility_check(line_ab, line_aq, 5),
        Some(true),
        "Qが構造的にL_AB上にあるなら、L_AQはL_ABと数値的に一致するべき"
    );

    // 対照実験: 何の前提も無い(単なる自由点)Rを使うと、AとRを通る直線は
    // 一般にL_ABとは別の直線になるはず(こちらは以前から動いていた既存の経路)。
    let r = egraph.create_entity("R".into(), Definition::FreePoint, EntityType::Point);
    let line_ar = egraph.create_entity("L_AR".into(), Definition::new_line(a, r), EntityType::Line);
    assert_eq!(
        egraph.numeric_plausibility_check(line_ab, line_ar, 5),
        Some(false),
        "何の前提も無い自由点Rを通る直線は、一般にL_ABとは数値的に別の直線であるべき"
    );
}

/// 🌟 同様に、円への構造的前提を持つ自由点についても座標をサンプリングして
/// 検証を続けられることを確認する(sample_point_on_circle)。
#[test]
fn test_numeric_check_samples_consistent_point_on_circle() {
    let mut egraph = EGraph::new();
    let p1 = egraph.create_entity("P1".into(), Definition::FreePoint, EntityType::Point);
    let p2 = egraph.create_entity("P2".into(), Definition::FreePoint, EntityType::Point);
    let p3 = egraph.create_entity("P3".into(), Definition::FreePoint, EntityType::Point);
    let circ = egraph.create_entity("Circ".into(), Definition::Circumcircle(p1, p2, p3), EntityType::Circle);

    // QはFreePointのまま(定義上はCircと無関係)だが、「Circ上にある」という
    // 前提だけをlink_logical_incidenceで直接与える(simson.rs/cyclic_quad.rs等と同じ)。
    let q = egraph.create_entity("Q".into(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(q, circ);

    // P1,P2,Qを通る外接円は、Qが本当にCirc上にあるなら幾何学的に必ずCircそのものになる
    // (円は同一直線上にない3点で一意に決まるため)。
    let circ2 = egraph.create_entity("Circ2".into(), Definition::Circumcircle(p1, p2, q), EntityType::Circle);

    assert_eq!(
        egraph.numeric_plausibility_check(circ, circ2, 5),
        Some(true),
        "QがCirc上にあるなら、P1,P2,Qを通る外接円はCircと数値的に一致するべき"
    );

    // 対照実験: 何の前提も無い自由点Rでは、P1,P2,Rを通る外接円は一般にCircとは別の円になる。
    let r = egraph.create_entity("R".into(), Definition::FreePoint, EntityType::Point);
    let circ3 = egraph.create_entity("Circ3".into(), Definition::Circumcircle(p1, p2, r), EntityType::Circle);
    assert_eq!(
        egraph.numeric_plausibility_check(circ, circ3, 5),
        Some(false),
        "何の前提も無い自由点Rを使った外接円は、一般にCircとは数値的に別の円であるべき"
    );
}

/// 🌟 raw_proof::RawProof::verify_identicalの回帰テスト(ユーザー指摘への対応):
/// 「2直線が2点を共有」によるLineUniqueness自体は、共有点それぞれの直線への
/// 接続が定義から機械的に従う基底事実(このテストのA, Bのように)である限り、
/// 数値サンプリングにしか頼らない「ギャップ」ではなく、共有点の由来まで
/// 遡って検証済みの「resolved_shortcuts」として扱われるべきことを確認する
/// (circumcenter/orthocenter_altの調査で実際にこの区別が必要だと判明した)。
#[test]
fn test_raw_proof_resolves_shared_point_shortcut() {
    let mut egraph = EGraph::new();
    let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let l1 = egraph.create_entity("L1".into(), Definition::new_line(a, b), EntityType::Line);
    // L2はL1とは別定義(素朴なFreePointプレースホルダ)として独立に作り、A, Bを
    // 後から手動でリンクする(test_incidence_preservation_after_mergeと同じ手法)。
    // これでpropagate_line_uniquenessが「2点共有」経由でL1, L2をマージする状況を
    // 意図的に作れる(new_line同士だと正規化されたDefinitionのhash consingで
    // 最初から同一実体になってしまい、LineUniqueness経路を通らない)。
    let l2 = egraph.create_entity("L2".into(), Definition::FreePoint, EntityType::Line);
    egraph.link_logical_incidence(a, l2);
    egraph.link_logical_incidence(b, l2);
    egraph.apply_congruence_closure();
    assert_eq!(egraph.get_rep(l1), egraph.get_rep(l2), "前提: 2点共有でL1, L2がマージされているはず");

    let raw_text = egraph.dump_raw_proof();
    let raw = RawProof::parse(&raw_text);
    let report = raw.verify_identical(l1.0, l2.0);
    assert!(report.is_rigorous(),
        "A, Bへの接続はどちらも定義から機械的に従う基底事実なので、LineUniqueness自体はギャップにならないはず: {}",
        report.format_deep());
    assert!(report.resolved_shortcuts() >= 1,
        "LineUniquenessショートカットが少なくとも1件、由来検証済みとして解決されているはず");
}

/// 🌟 raw_proof::RawProof::verify_identicalの回帰テスト: そもそも合流していない
/// (raw_proof中に一切マージ経路が無い)2つの実体を尋ねた場合は、当然ギャップ
/// (未証明)として報告されるべきことを確認する。
#[test]
fn test_raw_proof_reports_gap_for_unmerged_entities() {
    let mut egraph = EGraph::new();
    let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    egraph.apply_congruence_closure();

    let raw_text = egraph.dump_raw_proof();
    let raw = RawProof::parse(&raw_text);
    let report = raw.verify_identical(a.0, b.0);
    assert!(!report.is_rigorous(), "無関係などうしはマージされていないので、ギャップとして報告されるべき");
}

/// 🌟 複比(A,B;C,D)のV4正規化: 値を厳密に保つ4元クライン群
/// {id, (AB)(CD), (AC)(BD), (AD)(BC)} の4通りの引数順は、全て同じ
/// エンティティに畳み込まれるべき(Circumcircleが3点の6順列を1つに
/// 畳み込むのと同じ発想)。一方、この4通りに含まれない置換
/// (例: (A,C,B,D))は値そのものが変わる(一般に1-kになる)ため、
/// 別エンティティのままであるべき(過剰な同一視をしていないことの確認)。
#[test]
fn test_cross_ratio_v4_normalization() {
    let mut egraph = EGraph::new();
    let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
    let d = egraph.create_entity("D".into(), Definition::FreePoint, EntityType::Point);

    let base = egraph.create_entity("CR1".into(), Definition::CrossRatio(a, b, c, d), EntityType::Scalar);
    let swap_pairs = egraph.create_entity("CR2".into(), Definition::CrossRatio(b, a, d, c), EntityType::Scalar);
    let swap_halves = egraph.create_entity("CR3".into(), Definition::CrossRatio(c, d, a, b), EntityType::Scalar);
    let swap_both = egraph.create_entity("CR4".into(), Definition::CrossRatio(d, c, b, a), EntityType::Scalar);

    assert_eq!(base, swap_pairs, "(B,A;D,C)は(A,B;C,D)と同じ値になるはずなので、同一エンティティであるべき");
    assert_eq!(base, swap_halves, "(C,D;A,B)は(A,B;C,D)と同じ値になるはずなので、同一エンティティであるべき");
    assert_eq!(base, swap_both, "(D,C;B,A)は(A,B;C,D)と同じ値になるはずなので、同一エンティティであるべき");

    let different_value = egraph.create_entity("CR5".into(), Definition::CrossRatio(a, c, b, d), EntityType::Scalar);
    assert_ne!(base, different_value, "(A,C;B,D)は一般に異なる値(1-k)になるはずなので、別エンティティであるべき");
}

/// 🌟 calc_cross_ratioの正しさを、既に検証済みのcalc_harmonic_conjugateとの
/// 整合性で確認する: 定義上、調和共役点D=H(A,B,C)に対しては
/// (A,B;C,D)がちょうど-1になるはず。
#[test]
fn test_cross_ratio_matches_harmonic_conjugate_value() {
    let a = vec![ModInt::new(0), ModInt::new(0), ModInt::new(1)];
    let b = vec![ModInt::new(4), ModInt::new(0), ModInt::new(1)];
    let c = vec![ModInt::new(1), ModInt::new(0), ModInt::new(1)];

    let d = mmp_calculators::calc_harmonic_conjugate(&a, &b, &c);
    let k = mmp_calculators::calc_cross_ratio(&a, &b, &c, &d).expect("非退化な配置なので複比は計算できるはず");
    assert_eq!(k, ModInt::new(-1), "調和共役点との複比はちょうど-1になるべき");
}

/// 🌟 calc_cross_ratioがA,B自身に対しては退化(定義不能)を正しく検出することを確認する
/// (C=BやD=Aは複比の定義域外)。
#[test]
fn test_cross_ratio_degenerate_cases_return_none() {
    let a = vec![ModInt::new(0), ModInt::new(0), ModInt::new(1)];
    let b = vec![ModInt::new(4), ModInt::new(0), ModInt::new(1)];
    let c = vec![ModInt::new(1), ModInt::new(0), ModInt::new(1)];

    // C=B (第3引数がBそのもの)
    assert!(mmp_calculators::calc_cross_ratio(&a, &b, &b, &c).is_none());
    // D=A (第4引数がAそのもの)
    assert!(mmp_calculators::calc_cross_ratio(&a, &b, &c, &a).is_none());
}

/// 🌟 Method of Moving Points(動点法)の次数測定(measure_numerical_degree)の
/// 検証: ユーザーが指摘した通り、中点の作図を何段重ねても次数は1のまま
/// 留まるべきである(中点は自由点1つが直線的に動く時、常に直線的にしか
/// 動かないため)。
#[test]
fn test_numerical_degree_stays_low_for_repeated_midpoints() {
    let mut egraph = EGraph::new();
    let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let mut e = egraph.create_entity("E0".into(), Definition::FreePoint, EntityType::Point);

    let mut current = a;
    for i in 1..=3 {
        e = egraph.create_entity(format!("E{}", i).into(), Definition::FreePoint, EntityType::Point);
        current = egraph.create_entity(format!("M{}", i).into(), Definition::Midpoint(current, e), EntityType::Point);
        let deg = egraph.measure_numerical_degree(current, 6).expect("次数が測定できるはず");
        assert_eq!(deg, 1, "中点をM{}段重ねても次数は1のまま留まるべき", i);
    }
    let _ = e; // 未使用警告よけ
}

/// 🌟 対照実験: 無関係な2直線の交点を取ると、中点とは対照的に次数が
/// 明確に増加する(1段取っただけでmover自身の次数1から2へ上がる)。これに
/// より「次数の低い補助点(中点等)は積極的に採用し、次数が上がる補助点
/// (無関係な交点)は警戒する」というフィルタが実際に意味のある判定に
/// なることを確認する。
/// 🌟 注記: 2段目以降は交点の取り方によって偶然の代数的な相殺が起こり
/// 次数が上がりきらないことがある(実測で確認済み――これ自体はMMPの
/// 次数評価が「常に最良の上界を単純に足し算できるとは限らない」ことの
/// 実例で、上界の予測にはPDFが述べる通り数個の図での実測が必要になる
/// 理由でもある)。ここでは「中点は増えない・交点は増える」という
/// 最小限の対照だけを固く検証する。
#[test]
fn test_numerical_degree_grows_with_arbitrary_intersection() {
    let mut egraph = EGraph::new();
    let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
    let d = egraph.create_entity("D".into(), Definition::FreePoint, EntityType::Point);
    let e = egraph.create_entity("E".into(), Definition::FreePoint, EntityType::Point);

    let deg_a = egraph.measure_numerical_degree(a, 6).expect("次数が測定できるはず");
    assert_eq!(deg_a, 1, "mover自身の次数は1のはず");

    let l1 = egraph.create_entity("L1".into(), Definition::new_line(a, c), EntityType::Line);
    let m = egraph.create_entity("Mid".into(), Definition::Midpoint(a, e), EntityType::Point);
    let l2 = egraph.create_entity("L2".into(), Definition::new_line(m, d), EntityType::Line);
    let p = egraph.create_entity("P".into(), Definition::Intersection(l1, l2), EntityType::Point);

    let deg_p = egraph.measure_numerical_degree(p, 6).expect("次数が測定できるはず");
    assert!(deg_p > deg_a, "無関係な2直線の交点は、moverそのものより次数が高くなるべき(1 -> {})", deg_p);
}

/// 🌟 ユーザー提案の検証: 「点の組A,Bについて、線分ABの次数がdeg(A)+deg(B)
/// という素朴な上界より退化して小さい組は、隠れた定理・偶然の一致(この
/// テストでは「B=Midpoint(A,F)なのでA,B,Fは常に共線」という自明な幾何的
/// 事実)が効いている兆候として『相性が良い』とみなせる」を実測で確認する。
/// A(mover, 次数1)とB=Midpoint(A,F)(次数1、Fは固定点)は素朴には
/// deg(A)+deg(B)=2の直線を作りそうに見えるが、実際にはA,B,Fが常に
/// 一直線上にある(=Line(A,B)は実質的にLine(A,F)、次数1)ため、
/// measure_line_affinityはこの退化(2ではなく1)を検出できるはず。
#[test]
fn test_line_affinity_detects_collinear_degeneracy() {
    let mut egraph = EGraph::new();
    let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let f = egraph.create_entity("F".into(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".into(), Definition::Midpoint(a, f), EntityType::Point);

    let (deg_a, deg_b, deg_line) = egraph.measure_line_affinity(a, b, 6).expect("次数が測定できるはず");
    assert_eq!(deg_a, 1, "mover自身の次数は1のはず");
    assert_eq!(deg_b, 1, "中点(Midpoint)は次数を上げないはず");
    assert!(
        deg_line < deg_a + deg_b,
        "A,B=Midpoint(A,F),Fは常に共線なので、Line(A,B)の次数は素朴な和({})より小さいはず(実測: {})",
        deg_a + deg_b, deg_line
    );
}

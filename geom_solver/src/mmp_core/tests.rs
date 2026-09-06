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

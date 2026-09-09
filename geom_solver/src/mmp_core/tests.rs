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
fn test_tangent_line_to_circle_is_numerically_correct() {
    // 🌟 経緯: eval.rs::sample_point_on_circleのコメントで「calc_circumcircleが
    // 実際に返す係数の並びは[A,D,E,F](0番目がx²+y²の係数)だが、
    // calc_tangent_line側のコメント/実装は[D,E,F,A](Aが最後)を前提にしており、
    // この不一致がtangent_orthic.rs等では症状として顕在化していなかった
    // (証明が純粋に記号的な定理適用だけで届き、接線の数値そのものを
    // 検算する経路を通っていなかったため)」という既知の疑いがあった。
    // 円 x²+y²-4x-3y=0 (原点(0,0),(4,0),(0,3)を通る、中心(2,1.5)・半径2.5)
    // 上の(4,0)における接線を計算すると、古典的な公式
    // x*x0+y*y0+D(x+x0)/2+E(y+y0)/2+F=0 から 4x-3y-16=0 になるはずである。
    // 最初のバージョンはA=(1,0),B=(0,1),C=(-1,0)という単位円だったが、
    // これはD=E=0になる対称な配置で、係数の並び順の取り違えを検出できない
    // (0と0を入れ替えても違いが出ない)ことが後で判明したため、D,E,Fが
    // すべて非自明な値を持つこの非対称な配置に変更した。
    let mut egraph = EGraph::new();
    let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
    let circ = egraph.create_entity("Circ".into(), Definition::Circumcircle(a, b, c), EntityType::Circle);
    let tan = egraph.create_entity("Tan".into(), Definition::TangentLine(circ, b), EntityType::Line);

    let mut vars: FxHashMap<String, ModInt> = FxHashMap::default();
    vars.insert("A_x".into(), ModInt::new(0));
    vars.insert("A_y".into(), ModInt::new(0));
    vars.insert("B_x".into(), ModInt::new(4));
    vars.insert("B_y".into(), ModInt::new(0));
    vars.insert("C_x".into(), ModInt::new(0));
    vars.insert("C_y".into(), ModInt::new(3));

    let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
    let vtan = egraph.evaluate_node(tan, &vars, &mut cache).expect("接線が数値的に計算できるべき");
    let vtan = mmp_calculators::normalize(&vtan);

    let expected = mmp_calculators::normalize(&[ModInt::new(4), ModInt::new(-3), ModInt::new(-16)]);
    assert_eq!(vtan, expected,
        "円x²+y²-4x-3y=0上の(4,0)における接線は4x-3y-16=0であるべき");
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

/// 🌟 ユーザー提案「多点での評価を導入する。円も係数を射影空間の点だと
/// 思えばOK」の検証: 3点版(measure_circle_affinity)でも同じ退化検出が
/// 働くことを確認する。A(mover), B(固定点), D=Midpoint(A,B)は常に一直線上
/// (Dが線分AB上にある)にあるため、本来「外接円」であるはずの
/// Circumcircle(A,B,D)は退化して実質的にLine(A,B)そのものになる。
/// deg(A)+deg(B)+deg(D)という素朴な和より、実際のCircumcircle(A,B,D)の
/// (係数ベクトルを4成分の同次座標とみなした)次数の方が小さくなるはず。
#[test]
fn test_circle_affinity_detects_collinear_degeneracy() {
    let mut egraph = EGraph::new();
    let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let d = egraph.create_entity("D".into(), Definition::Midpoint(a, b), EntityType::Point);

    let (deg_a, deg_b, deg_d, deg_circle) = egraph.measure_circle_affinity(a, b, d, 6).expect("次数が測定できるはず");
    assert_eq!(deg_a, 1, "mover自身の次数は1のはず");
    assert_eq!(deg_b, 0, "Bは固定点なので次数0のはず");
    assert_eq!(deg_d, 1, "中点(Midpoint)は次数を上げないはず");
    assert!(
        deg_circle < deg_a + deg_b + deg_d,
        "A,B,D=Midpoint(A,B)は常に共線なので、Circumcircle(A,B,D)(実質的にLine(A,B))の次数は素朴な和({})より小さいはず(実測: {})",
        deg_a + deg_b + deg_d, deg_circle
    );
}

/// 🌟 A,B,M1=Midpoint(A,B),M2=Midpoint(A,M1)の4点を作る共通ヘルパー。
/// M1,M2はどちらもA,Bの固定係数によるアフィン結合(M1=(A+B)/2、
/// M2=(3A+B)/4)なので、A,Bの実際の位置に関わらずCrossRatio(A,B,M1,M2)は
/// 常に同じ定数値になる(調和共役と違い"点が無限遠に飛ぶ"退化が起きない
/// ぶん扱いやすい)――かつ、A,B,M1,M2はMidpointの構成上常に一直線上に
/// あるので、calc_cross_ratio(decompose)の前提(直線上の4点)も満たす。
fn make_double_midpoint_quad(egraph: &mut EGraph, a_name: &str, b_name: &str) -> (ClassId, ClassId, ClassId, ClassId) {
    let a = egraph.create_entity(a_name.into(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity(b_name.into(), Definition::FreePoint, EntityType::Point);
    let m1 = egraph.create_entity(format!("Mid_{}", a_name), Definition::Midpoint(a, b), EntityType::Point);
    let m2 = egraph.create_entity(format!("Mid2_{}", a_name), Definition::Midpoint(a, m1), EntityType::Point);
    (a, b, m1, m2)
}

/// 🌟 ユーザー提案「複比同士の関係式からconjectureを発行する」の検証。
/// 完全に独立な2組の4点(A1,B1,M1_1,M2_1)と(A2,B2,M1_2,M2_2)は、どちらも
/// 「2重中点」という同じアフィン結合係数の構成なので複比が必ず同じ定数値に
/// なる(座標のランダムな取り方に依存しない数学的な恒等式)。構造的には
/// 何の関係もない(異なる自由点から作られた)2つの複比エンティティが、
/// detect_cross_ratio_coincidencesによって「値が一致する」予想として
/// 検出されることを確認する。
#[test]
fn test_detect_cross_ratio_coincidences_finds_matching_values() {
    let mut egraph = EGraph::new();

    let (a1, b1, m1_1, m2_1) = make_double_midpoint_quad(&mut egraph, "A1", "B1");
    let cr1_def = egraph.normalize_definition(&Definition::CrossRatio(a1, b1, m1_1, m2_1));
    let _cr1 = egraph.create_entity("CR1".into(), cr1_def, EntityType::Scalar);

    let (a2, b2, m1_2, m2_2) = make_double_midpoint_quad(&mut egraph, "A2", "B2");
    let cr2_def = egraph.normalize_definition(&Definition::CrossRatio(a2, b2, m1_2, m2_2));
    let cr2 = egraph.create_entity("CR2".into(), cr2_def, EntityType::Scalar);

    assert!(egraph.conjectures.borrow().is_empty(), "検出前は予想が無いはず");
    egraph.detect_cross_ratio_coincidences(cr2);
    assert!(
        !egraph.conjectures.borrow().is_empty(),
        "独立した2つの2重中点配置はどちらも同じ複比定数になるはずなので、予想として検出されるべき"
    );
}

/// 🌟 ユーザー提案「複比自体を次数を用いて生成に制限をかけて」の土台となる
/// measure_cross_ratio_affinityの検証。A(mover),B(固定点),M1=Midpoint(A,B),
/// M2=Midpoint(A,M1)は、A,Bの実際の位置に関わらず常に同じ定数の複比を
/// 持つ(make_double_midpoint_quadのコメント参照)ので、複比自体の次数は
/// ちょうど0(定数)になるはず――たとえ入力の4点が次数1のmoverを含んでいても、
/// 複比という「組み合わせ結果」の次数は個々の点の次数と独立に(このケースでは
/// 0まで)変わり得ることを示す。
#[test]
fn test_cross_ratio_affinity_is_zero_for_affine_invariant_configuration() {
    let mut egraph = EGraph::new();
    let (a, _b, m1, m2) = make_double_midpoint_quad(&mut egraph, "A", "B");

    let (deg_a, _deg_b, _deg_m1, _deg_m2, deg_cr) = egraph.measure_cross_ratio_affinity(a, _b, m1, m2, 6)
        .expect("次数が測定できるはず");
    assert_eq!(deg_a, 1, "mover自身の次数は1のはず");
    assert_eq!(deg_cr, 0, "2重中点の複比は常に同じ定数なので次数0のはず(実測: {})", deg_cr);
}

/// 🌟 ユーザー提案「有向角を複比として扱う」の検証: AnglePairの評価式を
/// calc_cross_ratio(CircI,CircJ,D1,D2)ベースに変更した後も、既存の
/// 「有向角の加法性」「有向角の交替律」定理がそのまま前提とする代数法則
/// (a/b=c/d ⟹ a/c=b/d、およびτ13=τ12*τ23の乗法性)が数値的に成り立つことを
/// 直接確認する。これらの定理は元々AnglePairの値をIdenticalで比較するだけの
/// 純粋に構造的な定理(値の計算式に依存しない)なので、eval式を差し替えても
/// 定理側は無傷のはずだが、その前提となる「値が本当にこの法則を満たす」こと
/// 自体は評価式の実装に依存するため、ここで直接検証しておく。
#[test]
fn test_angle_pair_value_satisfies_cross_ratio_multiplicativity() {
    let mut egraph = EGraph::new();
    let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
    let d = egraph.create_entity("D".into(), Definition::FreePoint, EntityType::Point);

    let l_ab = egraph.create_entity("L_AB".into(), Definition::new_line(a, b), EntityType::Line);
    let l_ac = egraph.create_entity("L_AC".into(), Definition::new_line(a, c), EntityType::Line);
    let l_ad = egraph.create_entity("L_AD".into(), Definition::new_line(a, d), EntityType::Line);

    let dir_ab = egraph.create_entity("Dir_AB".into(), Definition::DirectionOf(l_ab), EntityType::Point);
    let dir_ac = egraph.create_entity("Dir_AC".into(), Definition::DirectionOf(l_ac), EntityType::Point);
    let dir_ad = egraph.create_entity("Dir_AD".into(), Definition::DirectionOf(l_ad), EntityType::Point);

    let ang_ab_ac = egraph.create_entity("Ang_AB_AC".into(), Definition::AnglePair(dir_ab, dir_ac), EntityType::Angle);
    let ang_ac_ad = egraph.create_entity("Ang_AC_AD".into(), Definition::AnglePair(dir_ac, dir_ad), EntityType::Angle);
    let ang_ab_ad = egraph.create_entity("Ang_AB_AD".into(), Definition::AnglePair(dir_ab, dir_ad), EntityType::Angle);

    let mut vars: FxHashMap<String, ModInt> = FxHashMap::default();
    vars.insert("A_x".into(), ModInt::new(0)); vars.insert("A_y".into(), ModInt::new(0));
    vars.insert("B_x".into(), ModInt::new(3)); vars.insert("B_y".into(), ModInt::new(1));
    vars.insert("C_x".into(), ModInt::new(1)); vars.insert("C_y".into(), ModInt::new(4));
    vars.insert("D_x".into(), ModInt::new(-2)); vars.insert("D_y".into(), ModInt::new(5));

    let mut cache = FxHashMap::default();
    let v12 = egraph.evaluate_node(ang_ab_ac, &vars, &mut cache).expect("計算できるはず")[0];
    let v23 = egraph.evaluate_node(ang_ac_ad, &vars, &mut cache).expect("計算できるはず")[0];
    let v13 = egraph.evaluate_node(ang_ab_ad, &vars, &mut cache).expect("計算できるはず")[0];

    // 加法性: (I,J;D1,D2)*(I,J;D2,D3) = (I,J;D1,D3) (本文コメント参照、
    // φ(D)=τ_Dとおいた時のφ(D1)/φ(D2)*φ(D2)/φ(D3)=φ(D1)/φ(D3)という
    // Möbius変換の比の連鎖則そのもの)。
    assert_eq!(v12 * v23, v13, "有向角の加法性はτ13=τ12*τ23という複比の乗法則として成り立つべき");
}

/// 🌟 二次曲線(5点)の係数復元(calc_conic_through_5_points)の正しさを、
/// 既知の円(x²+y²=25、有理点(5,0),(0,5),(-5,0),(0,-5),(3,4)はいずれも
/// この円周上にある)から復元させることで検証する。円は
/// 「xy項が無くx²とy²の係数が等しい」特殊な二次曲線なので、復元結果は
/// [1,0,1,0,0,-25](= x²+y²-25=0)にnormalizeされるはず。
#[test]
fn test_calc_conic_through_5_points_reconstructs_known_circle() {
    let pts = vec![
        vec![ModInt::new(5), ModInt::new(0), ModInt::new(1)],
        vec![ModInt::new(0), ModInt::new(5), ModInt::new(1)],
        vec![ModInt::new(-5), ModInt::new(0), ModInt::new(1)],
        vec![ModInt::new(0), ModInt::new(-5), ModInt::new(1)],
        vec![ModInt::new(3), ModInt::new(4), ModInt::new(1)],
    ];
    let coeffs = mmp_calculators::calc_conic_through_5_points(&pts);
    assert_eq!(
        coeffs,
        vec![ModInt::new(1), ModInt::new(0), ModInt::new(1), ModInt::new(0), ModInt::new(0), ModInt::new(-25)],
        "x²+y²-25=0 (半径5の円)が復元されるべき"
    );
}

/// 🌟 5点のうち4点が同一直線上にある(=5×6行列のランクが5未満の)退化配置では、
/// 二次曲線が(一意には)定まらないのでNone相当(空Vec)を返すことを確認する。
#[test]
fn test_calc_conic_through_5_points_degenerate_returns_empty() {
    let pts = vec![
        vec![ModInt::new(0), ModInt::new(0), ModInt::new(1)],
        vec![ModInt::new(1), ModInt::new(0), ModInt::new(1)],
        vec![ModInt::new(2), ModInt::new(0), ModInt::new(1)],
        vec![ModInt::new(3), ModInt::new(0), ModInt::new(1)],
        vec![ModInt::new(4), ModInt::new(0), ModInt::new(1)],
    ];
    assert!(mmp_calculators::calc_conic_through_5_points(&pts).is_empty(), "4点以上が同一直線上にある退化配置は空Vecを返すべき");
}

/// 🌟 ユーザー提案「二次曲線の導入」の検証: Circumcircleと同じ要領で、
/// ConicThrough5Pointsの生成元5点が構造的にConnected(この二次曲線に乗って
/// いる)と判定されることを確認する(apply_trivial_relations経由)。
#[test]
fn test_conic_through_5_points_links_generator_points_structurally() {
    let mut egraph = EGraph::new();
    let pts: Vec<ClassId> = (0..5)
        .map(|i| egraph.create_entity(format!("P{}", i), Definition::FreePoint, EntityType::Point))
        .collect();
    let conic = egraph.create_entity(
        "Conic".into(),
        Definition::ConicThrough5Points(pts[0], pts[1], pts[2], pts[3], pts[4]),
        EntityType::Conic,
    );
    for &p in &pts {
        assert!(egraph.is_connected(p, conic), "生成元の点は二次曲線にConnectedであるべき");
    }
}

/// 🌟 sample_point_on_conic(円のsample_point_on_circleの二次曲線版)の検証。
/// test_numeric_check_samples_consistent_point_on_circleと全く同じ発想:
/// 「QはこのConic上にある」という前提をlink_logical_incidenceだけで与えた
/// (座標としては裏付けの無い)自由点Qについて、P1,P2,P3,P4,Qを通る二次曲線が
/// 元のConicと数値的に一致するはず(二次曲線は5点で一意に決まるため)。
/// これが成り立つには、numeric_plausibility_checkの土台となる
/// assign_free_point_coordsがQの座標をsample_point_on_conic経由で正しく
/// 「本当にConic上にある」ように制約付きサンプリングできている必要がある。
#[test]
fn test_numeric_check_samples_consistent_point_on_conic() {
    let mut egraph = EGraph::new();
    let pts: Vec<ClassId> = (0..5)
        .map(|i| egraph.create_entity(format!("P{}", i), Definition::FreePoint, EntityType::Point))
        .collect();
    let conic = egraph.create_entity(
        "Conic".into(),
        Definition::ConicThrough5Points(pts[0], pts[1], pts[2], pts[3], pts[4]),
        EntityType::Conic,
    );

    let q = egraph.create_entity("Q".into(), Definition::FreePoint, EntityType::Point);
    egraph.link_logical_incidence(q, conic);

    let conic2 = egraph.create_entity(
        "Conic2".into(),
        Definition::ConicThrough5Points(pts[0], pts[1], pts[2], pts[3], q),
        EntityType::Conic,
    );
    assert_eq!(
        egraph.numeric_plausibility_check(conic, conic2, 5),
        Some(true),
        "QがConic上にあるなら、P0..P3,Qを通る二次曲線は元のConicと数値的に一致するべき"
    );

    // 対照実験: 何の前提も無い自由点Rでは、P0..P3,Rを通る二次曲線は一般に別物になる。
    let r = egraph.create_entity("R".into(), Definition::FreePoint, EntityType::Point);
    let conic3 = egraph.create_entity(
        "Conic3".into(),
        Definition::ConicThrough5Points(pts[0], pts[1], pts[2], pts[3], r),
        EntityType::Conic,
    );
    assert_eq!(
        egraph.numeric_plausibility_check(conic, conic3, 5),
        Some(false),
        "何の前提も無いRでは、P0..P3,Rを通る二次曲線は一般にConicとは別物になるべき"
    );
}

/// 🌟 ユーザー提案の検証: 「△EABと△EDCが直接相似(Eを中心とするスパイラル
/// 相似でA→D,B→C)」は、(E,A,B,I,J)と(E,D,C,I,J)という2つの5点配置が
/// 射影変換で移り合うことと同値であり、それは2つの独立な複比――
/// (a) Eを中心とする線束の複比(角度の情報だけを運ぶ)
/// (b) 虚円点Iを中心とする線束の複比(距離を含む計量的な情報を運ぶ)
/// ――が両方一致することと同値なはず、という仮説を数値的に検証する。
///
/// 複素数z=x+iy(iはこの体内のsqrt(-1)、circ_i/circ_jと全く同じもの)を使い、
/// D=E+k(A-E), C=E+k(B-E)というスパイラル相似(比k=kx+i*ky)で具体的にD,Cを
/// 構成し、(a)(b)の複比が確かにEABの配置とEDCの配置で一致することを確認する。
/// 対照実験として、Cだけ別の比k'で作った(=△EABと△EDCがもはや相似ではない)
/// 配置では、(b)(距離の情報を運ぶ方)が一致しなくなることも確認し、この複比が
/// 「常に一致してしまう自明な恒等式」ではなく実際に相似性を検出する非自明な
/// 不変量であることを確かめる。
#[test]
fn test_spiral_similarity_characterized_by_two_pencil_cross_ratios() {
    let mut egraph = EGraph::new();
    let e = egraph.create_entity("E".into(), Definition::FreePoint, EntityType::Point);
    let a = egraph.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
    let b = egraph.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
    let d = egraph.create_entity("D".into(), Definition::FreePoint, EntityType::Point);
    let c = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);

    let circ_i = egraph.circ_i;
    let circ_j = egraph.circ_j;

    // (a) Eを中心とする線束: EA,EB,EI,EJ ↔ ED,EC,EI,EJ
    let l_ea = egraph.create_entity("L_EA".into(), Definition::new_line(e, a), EntityType::Line);
    let l_eb = egraph.create_entity("L_EB".into(), Definition::new_line(e, b), EntityType::Line);
    let l_ed = egraph.create_entity("L_ED".into(), Definition::new_line(e, d), EntityType::Line);
    let l_ec = egraph.create_entity("L_EC".into(), Definition::new_line(e, c), EntityType::Line);
    let l_ei = egraph.create_entity("L_EI".into(), Definition::new_line(e, circ_i), EntityType::Line);
    let l_ej = egraph.create_entity("L_EJ".into(), Definition::new_line(e, circ_j), EntityType::Line);
    let cr_e_ab = egraph.create_entity("CR_E_AB".into(), Definition::CrossRatioOfLines(l_ea, l_eb, l_ei, l_ej), EntityType::Scalar);
    let cr_e_dc = egraph.create_entity("CR_E_DC".into(), Definition::CrossRatioOfLines(l_ed, l_ec, l_ei, l_ej), EntityType::Scalar);

    // (b) 虚円点Iを中心とする線束: IE,IA,IB,IJ ↔ IE,ID,IC,IJ
    let l_ie = egraph.create_entity("L_IE".into(), Definition::new_line(circ_i, e), EntityType::Line);
    let l_ia = egraph.create_entity("L_IA".into(), Definition::new_line(circ_i, a), EntityType::Line);
    let l_ib = egraph.create_entity("L_IB".into(), Definition::new_line(circ_i, b), EntityType::Line);
    let l_id = egraph.create_entity("L_ID".into(), Definition::new_line(circ_i, d), EntityType::Line);
    let l_ic = egraph.create_entity("L_IC".into(), Definition::new_line(circ_i, c), EntityType::Line);
    let l_ij = egraph.create_entity("L_IJ".into(), Definition::new_line(circ_i, circ_j), EntityType::Line);
    let cr_i_ab = egraph.create_entity("CR_I_AB".into(), Definition::CrossRatioOfLines(l_ie, l_ia, l_ib, l_ij), EntityType::Scalar);
    let cr_i_dc = egraph.create_entity("CR_I_DC".into(), Definition::CrossRatioOfLines(l_ie, l_id, l_ic, l_ij), EntityType::Scalar);

    // E,A,Bへ具体的な座標を与え、D,Cは複素数演算 D=E+k(A-E), C=E+k(B-E) で
    // 「本物のスパイラル相似」になるよう構成する(k=5+2i、単なる回転ではなく
    // 拡大率も伴う値を選ぶことで、角度だけでなく距離の情報も試験対象にする)。
    let i_val = ModInt::new(3).pow((crate::mmp_math::PRIME - 1) / 4);
    let cmul = |ax: ModInt, ay: ModInt, bx: ModInt, by: ModInt| -> (ModInt, ModInt) {
        (ax * bx - ay * by, ax * by + ay * bx)
    };
    let (kx, ky) = (ModInt::new(5), ModInt::new(2));

    let mut vars: FxHashMap<String, ModInt> = FxHashMap::default();
    let (ex, ey) = (ModInt::new(1), ModInt::new(7));
    let (ax, ay) = (ModInt::new(4), ModInt::new(2));
    let (bx, by) = (ModInt::new(-3), ModInt::new(6));
    vars.insert("E_x".into(), ex); vars.insert("E_y".into(), ey);
    vars.insert("A_x".into(), ax); vars.insert("A_y".into(), ay);
    vars.insert("B_x".into(), bx); vars.insert("B_y".into(), by);

    let (dax, day) = cmul(kx, ky, ax - ex, ay - ey);
    vars.insert("D_x".into(), ex + dax); vars.insert("D_y".into(), ey + day);
    let (dbx, dby) = cmul(kx, ky, bx - ex, by - ey);
    vars.insert("C_x".into(), ex + dbx); vars.insert("C_y".into(), ey + dby);

    let mut cache = FxHashMap::default();
    let v_e_ab = egraph.evaluate_node(cr_e_ab, &vars, &mut cache).expect("計算できるはず")[0];
    let v_e_dc = egraph.evaluate_node(cr_e_dc, &vars, &mut cache).expect("計算できるはず")[0];
    let v_i_ab = egraph.evaluate_node(cr_i_ab, &vars, &mut cache).expect("計算できるはず")[0];
    let v_i_dc = egraph.evaluate_node(cr_i_dc, &vars, &mut cache).expect("計算できるはず")[0];

    assert_eq!(v_e_ab, v_e_dc, "本物のスパイラル相似では、Eを中心とする線束の複比が一致するはず(角度の一致)");
    assert_eq!(v_i_ab, v_i_dc, "本物のスパイラル相似では、Iを中心とする線束の複比も一致するはず(距離を含む一致)");
    let _ = i_val; // i自体は複素数演算の定義に暗黙に埋め込まれているだけで直接は使わないが、記録として残す

    // 対照実験: Cだけ全く別の比k'=(2,9)で作り直す(△EABと△EDCはもはや
    // 相似ではない)。角度の複比(Eからの線束)はEA,ED間の関係だけで決まる
    // ので依然として一致し得るが(EA,EBの間の角度がたまたま保たれる保証は
    // 一般には無いのでこちらも通常は崩れる)、距離を運ぶIからの線束の複比は
    // 確実に崩れるはずである。
    let (kx2, ky2) = (ModInt::new(2), ModInt::new(9));
    let (dbx2, dby2) = cmul(kx2, ky2, bx - ex, by - ey);
    vars.insert("C_x".into(), ex + dbx2); vars.insert("C_y".into(), ey + dby2);
    let mut cache2 = FxHashMap::default();
    let v_i_dc_broken = egraph.evaluate_node(cr_i_dc, &vars, &mut cache2).expect("計算できるはず")[0];
    assert_ne!(v_i_ab, v_i_dc_broken, "比kが△EABと△EDCで食い違えば、距離を運ぶIからの線束の複比は一致しないはず(この不変量が非自明であることの確認)");
}

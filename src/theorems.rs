use crate::mmp_core::{DefKind, EntityType};
use crate::logic_core::{Conclusion, Construction, Flip, Pattern, Refinement, SelfBindPool, TheoremDef};
use rustc_hash::FxHashMap;

// --- 定理を書くための補助 ---
// 変数名は定理の中だけで通じる名前。型は entities で宣言する。

fn entities(list: &[(&str, EntityType)]) -> FxHashMap<String, EntityType> {
    list.iter().map(|(k, v)| (k.to_string(), *v)).collect()
}

fn strings(xs: &[&str]) -> Vec<String> {
    xs.iter().map(|s| s.to_string()).collect()
}

fn connected(child: &str, parent: &str, child_ref: Refinement, parent_ref: Refinement) -> Pattern {
    Pattern::Connected { child: child.to_string(), parent: parent.to_string(), child_ref, parent_ref }
}

/// child が parent に乗っている(点なら有限点、二次曲線なら円でないもの)。
fn on(child: &str, parent: &str) -> Pattern {
    connected(child, parent, Refinement::Default, Refinement::Default)
}

/// 直線 line の方向(L∞上の点)が dir。
fn has_direction(line: &str, dir: &str) -> Pattern {
    connected(line, dir, Refinement::Default, Refinement::Direction)
}

/// 点 point が円 circle に乗っている。
fn on_circle(point: &str, circle: &str) -> Pattern {
    connected(point, circle, Refinement::Default, Refinement::Circle)
}

fn identical(a: &str, b: &str, pool: SelfBindPool) -> Pattern {
    Pattern::Identical { a: a.to_string(), b: b.to_string(), pool }
}

fn same(a: &str, b: &str) -> Pattern { identical(a, b, SelfBindPool::Any) }
fn same_angle(a: &str, b: &str) -> Pattern { identical(a, b, SelfBindPool::Angle) }
fn same_cross_ratio_of_lines(a: &str, b: &str) -> Pattern { identical(a, b, SelfBindPool::CrossRatioOfLines) }

fn defined_by(kind: DefKind, args: &[&str], flip: Flip) -> Pattern {
    let (result, parents) = args.split_last().expect("DefinedBy には結果の変数が要る");
    Pattern::DefinedBy { kind, parents: strings(parents), result: result.to_string(), flip }
}

/// args の最後が結果、それより前が親。
fn def_by(kind: DefKind, args: &[&str]) -> Pattern { defined_by(kind, args, Flip::Fixed) }

/// 有向角 [D1, D2, Ang] を両方の向きで読む。
fn angle_free(args: &[&str]) -> Pattern { defined_by(DefKind::AnglePair, args, Flip::Free) }

/// 有向角 [D1, D2, Ang] を両方の向きで読むが、同じ group の角とは向きをそろえる。
fn angle_grouped(args: &[&str], group: &str) -> Pattern {
    defined_by(DefKind::AnglePair, args, Flip::Grouped(group.to_string()))
}

fn distinct(args: &[&str]) -> Pattern {
    Pattern::Distinct(strings(args))
}

/// 代表元IDの厳密な昇順。同じ候補プールから選ぶ変数の並べ替えを1通りに絞る。
/// 変数の割り当て順序が結論の成否に影響しない場合にだけ使うこと。
fn order(args: &[&str]) -> Pattern {
    Pattern::Order(strings(args))
}

/// 代表元IDの非厳密な昇順。2組の役割を丸ごと入れ替えても同じ結論になる対称性を間引く。
fn order_le(args: &[&str]) -> Pattern {
    Pattern::OrderNonStrict(strings(args))
}

/// 作図: parents から kind で作った図形を bind_to に束縛する。
fn build(kind: DefKind, parents: &[&str], bind_to: &str) -> Construction {
    Construction { kind, args: strings(parents), bind_to: bind_to.to_string() }
}

fn concl_same(a: &str, b: &str) -> Conclusion { Conclusion::Identical(a.to_string(), b.to_string()) }
fn concl_on(child: &str, parent: &str) -> Conclusion { Conclusion::Connected(child.to_string(), parent.to_string()) }

// --- 定理集合 ---

/// 基本の定理(get_all_theorems)に足す定理群。
pub struct TheoremSetOptions {
    /// 射影の定理(複比の透視射影不変性・シュタイナーの定理)。既定で入る。
    pub projective: bool,
    /// 長さを橋渡しする定理(--length-theorems)。
    pub length_bridge: bool,
    /// 中心角の定理(--central-angle)。
    pub central_angle: bool,
}

impl Default for TheoremSetOptions {
    fn default() -> Self {
        Self { projective: true, length_bridge: false, central_angle: false }
    }
}

/// 証明に使う定理集合。solve・serve・discover の証明試行は全てここから取る。
/// 同じ優先度のタスクは定理の登録順に取り出されるので、並び(基本 → 長さ → 中心角 → 射影)を変えると探索も変わる。
pub fn theorem_set(opts: &TheoremSetOptions) -> Vec<TheoremDef> {
    let mut all = get_all_theorems();
    if opts.length_bridge {
        all.extend(get_length_bridge_theorems());
    }
    if opts.central_angle {
        all.extend(get_central_angle_theorem());
    }
    if opts.projective {
        all.extend(get_projective_theorems());
    }
    all
}

// --- 定理の定義 ---

pub fn get_all_theorems() -> Vec<TheoremDef> {
    vec![
        // 1. 円周角の定理
        TheoremDef {
            name: "円周角の定理".to_string(),
            entities: entities(&[
                ("Apex1", EntityType::Point), ("Apex2", EntityType::Point),
                ("Base1", EntityType::Point), ("Base2", EntityType::Point),
                ("Circ", EntityType::Conic),
                ("L_A1_B1", EntityType::Line), ("L_A1_B2", EntityType::Line),
                ("L_A2_B1", EntityType::Line), ("L_A2_B2", EntityType::Line),
                ("Dir_A1_B1", EntityType::Point), ("Dir_A1_B2", EntityType::Point),
                ("Dir_A2_B1", EntityType::Point), ("Dir_A2_B2", EntityType::Point),
                ("Ang1", EntityType::Scalar), ("Ang2", EntityType::Scalar),
            ]),
            patterns: vec![
                // 🌟 「4点が同じ円に乗っている」は専用の Fact ではなく Connected の4連続で表す。on_circle は
                // I,J を両方通る Conic(本物の円)だけを候補にする(シュタイナーの定理用の一般の二次曲線を混ぜない)。
                on_circle("Apex1", "Circ"),
                on_circle("Apex2", "Circ"),
                on_circle("Base1", "Circ"),
                on_circle("Base2", "Circ"),
                distinct(&["Apex1", "Apex2", "Base1", "Base2"]),
                
                // 🌟 FIX: Connected から DefinedBy に変更し、作図需要(Demand)を発生させる
                def_by(DefKind::LineThroughPoints, &["Apex1", "Base1", "L_A1_B1"]),
                def_by(DefKind::LineThroughPoints, &["Apex1", "Base2", "L_A1_B2"]),
                distinct(&["L_A1_B1", "L_A1_B2"]),
                
                def_by(DefKind::LineThroughPoints, &["Apex2", "Base1", "L_A2_B1"]),
                def_by(DefKind::LineThroughPoints, &["Apex2", "Base2", "L_A2_B2"]),
                
                on("Apex2", "L_A2_B1"),
                on("Base1", "L_A2_B1"),
                on("Apex2", "L_A2_B2"),
                on("Base2", "L_A2_B2"),
                distinct(&["L_A2_B1", "L_A2_B2"]),
                
                def_by(DefKind::DirectionOf, &["L_A1_B1", "Dir_A1_B1"]),
                def_by(DefKind::DirectionOf, &["L_A1_B2", "Dir_A1_B2"]),
                def_by(DefKind::DirectionOf, &["L_A2_B1", "Dir_A2_B1"]),
                def_by(DefKind::DirectionOf, &["L_A2_B2", "Dir_A2_B2"]),
                
                angle_grouped(&["Dir_A1_B1", "Dir_A1_B2", "Ang1"], "Cyclic"),
                angle_grouped(&["Dir_A2_B1", "Dir_A2_B2", "Ang2"], "Cyclic"),
                distinct(&["Ang1", "Ang2"]),
            ],
            constructions: vec![],
            conclusions: vec![concl_same("Ang1", "Ang2")],
        },


        // ==========================================
        // 🌟 垂直二等分線の距離の等価性 (順方向)
        // ==========================================
        // 線分BCの垂直二等分線上の点Pは、B,Cから等距離にある。
        // 外心(3辺の垂直二等分線の共点性)の証明で使う。
        TheoremDef {
            name: "垂直二等分線の距離の等価性".to_string(),
            entities: entities(&[
                ("B", EntityType::Point), ("C", EntityType::Point), ("Mid_BC", EntityType::Point),
                ("LineBC", EntityType::Line), ("PerpMid", EntityType::Line), ("P", EntityType::Point),
            ]),
            patterns: vec![
                def_by(DefKind::Midpoint, &["B", "C", "Mid_BC"]),
                def_by(DefKind::LineThroughPoints, &["B", "C", "LineBC"]),
                def_by(DefKind::PerpendicularLine, &["LineBC", "Mid_BC", "PerpMid"]),
                on("P", "PerpMid"),
                distinct(&["B", "C", "P"]),
            ],
            constructions: vec![
                build(DefKind::LengthSq, &["P", "B"], "Dist_PB"),
                build(DefKind::LengthSq, &["P", "C"], "Dist_PC"),
            ],
            conclusions: vec![
                concl_same("Dist_PB", "Dist_PC")
            ],
        },

        // ==========================================
        // 🌟 垂直二等分線の距離の等価性の逆
        // ==========================================
        // B,Cから等距離にある点Pは、線分BCの垂直二等分線上にある(Connected)。
        // 中点と垂直二等分線は前提で要求せず、結論側で作る(要求すると、垂直二等分線がまだ無い線分では
        // 等距離が示されても発火しない)。2点が同じ垂直二等分線に乗れば、直線の一意性で2点を結ぶ直線が
        // その垂直二等分線そのものになる(「等距離な2点を結ぶ直線 ⊥ 線分」)。
        TheoremDef {
            name: "垂直二等分線の距離の等価性の逆".to_string(),
            entities: entities(&[
                ("B", EntityType::Point), ("C", EntityType::Point), ("Mid_BC", EntityType::Point),
                ("LineBC", EntityType::Line), ("PerpMid", EntityType::Line), ("P", EntityType::Point),
                ("Dist_PB", EntityType::Scalar), ("Dist_PC", EntityType::Scalar),
            ]),
            patterns: vec![
                def_by(DefKind::LengthSq, &["P", "B", "Dist_PB"]),
                def_by(DefKind::LengthSq, &["P", "C", "Dist_PC"]),
                same("Dist_PB", "Dist_PC"),
                distinct(&["B", "C", "P"]),
            ],
            constructions: vec![
                build(DefKind::Midpoint, &["B", "C"], "Mid_BC"),
                build(DefKind::LineThroughPoints, &["B", "C"], "LineBC"),
                build(DefKind::PerpendicularLine, &["LineBC", "Mid_BC"], "PerpMid"),
            ],
            conclusions: vec![
                concl_on("P", "PerpMid")
            ],
        },

        // 3. 中点連結定理
        TheoremDef {
            name: "中点連結定理".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point),
                ("M1", EntityType::Point), ("M2", EntityType::Point),
                ("LineBC", EntityType::Line), ("LineM1M2", EntityType::Line),
                ("DirBC", EntityType::Point), ("DirM1M2", EntityType::Point),
            ]),
            patterns: vec![
                def_by(DefKind::Midpoint, &["A", "B", "M1"]),
                def_by(DefKind::Midpoint, &["A", "C", "M2"]),
                distinct(&["A", "B", "C", "M1", "M2"]),
                
                def_by(DefKind::LineThroughPoints, &["B", "C", "LineBC"]),
                def_by(DefKind::LineThroughPoints, &["M1", "M2", "LineM1M2"]),
                def_by(DefKind::DirectionOf, &["LineBC", "DirBC"]),
                def_by(DefKind::DirectionOf, &["LineM1M2", "DirM1M2"]),
            ],
            constructions: vec![],
            conclusions: vec![
                concl_same("DirBC", "DirM1M2")
            ],
        },


        TheoremDef {
            name: "二等辺三角形の底角".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point),
                ("Dist_AB", EntityType::Scalar), ("Dist_AC", EntityType::Scalar),
                ("LineAB", EntityType::Line), ("LineAC", EntityType::Line), ("LineBC", EntityType::Line),
                ("DirAB", EntityType::Point), ("DirAC", EntityType::Point), ("DirBC", EntityType::Point),
                ("Ang_B", EntityType::Scalar), ("Ang_C", EntityType::Scalar),
            ]),
            patterns: vec![
                same("Dist_AB", "Dist_AC"),
                def_by(DefKind::LengthSq, &["A", "B", "Dist_AB"]),
                def_by(DefKind::LengthSq, &["A", "C", "Dist_AC"]),
                distinct(&["A", "B", "C"]),
                
                def_by(DefKind::LineThroughPoints, &["A", "B", "LineAB"]),
                def_by(DefKind::LineThroughPoints, &["A", "C", "LineAC"]),
                def_by(DefKind::LineThroughPoints, &["B", "C", "LineBC"]),
                
                def_by(DefKind::DirectionOf, &["LineAB", "DirAB"]),
                def_by(DefKind::DirectionOf, &["LineAC", "DirAC"]),
                def_by(DefKind::DirectionOf, &["LineBC", "DirBC"]),
                distinct(&["DirAB", "DirAC", "DirBC"]),
                
                // 🌟 フリップ同期グループ "Isosceles" を適用
                angle_grouped(&["DirAB", "DirBC", "Ang_B"], "Isosceles"),
                angle_grouped(&["DirBC", "DirAC", "Ang_C"], "Isosceles"),
            ],
            constructions: vec![],
            conclusions: vec![
                concl_same("Ang_B", "Ang_C")
            ],
        },

        // ==========================================
        // 🌟 二等辺三角形の底角の逆(底角が等しい ⟹ 二辺が等しい)
        // ==========================================
        // 自己相似(△ABC ∽ △ACB、相似比1)による古典的な証明に対応する。上の「二等辺三角形の底角」と同じ足場で
        // 前提と結論を入れ替えた形だが、逆は自動では従わないので独立に定式化する。
        TheoremDef {
            name: "二等辺三角形の底角の逆".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point),
                ("Dist_AB", EntityType::Scalar), ("Dist_AC", EntityType::Scalar),
                ("LineAB", EntityType::Line), ("LineAC", EntityType::Line), ("LineBC", EntityType::Line),
                ("DirAB", EntityType::Point), ("DirAC", EntityType::Point), ("DirBC", EntityType::Point),
                ("Ang_B", EntityType::Scalar), ("Ang_C", EntityType::Scalar),
            ]),
            patterns: vec![
                // 🌟 シード: Identical(Ang_B,Ang_C)(底角が等しいという前提)から
                // 始めて、それぞれの定義からDirAB,DirBC,DirACを直接束縛する
                // (全件スキャン不要。「二等辺三角形の底角」の逆順)。
                same_angle("Ang_B", "Ang_C"),
                angle_grouped(&["DirAB", "DirBC", "Ang_B"], "IsoscelesConv"),
                angle_grouped(&["DirBC", "DirAC", "Ang_C"], "IsoscelesConv"),
                distinct(&["DirAB", "DirAC", "DirBC"]),

                has_direction("LineAB", "DirAB"),
                has_direction("LineBC", "DirBC"),
                has_direction("LineAC", "DirAC"),
                distinct(&["LineAB", "LineBC", "LineAC"]),

                // A = LineAB ∩ LineAC, B = LineAB ∩ LineBC, C = LineBC ∩ LineAC
                on("A", "LineAB"),
                on("A", "LineAC"),
                on("B", "LineAB"),
                on("B", "LineBC"),
                on("C", "LineBC"),
                on("C", "LineAC"),
                distinct(&["A", "B", "C"]),
            ],
            constructions: vec![
                build(DefKind::LengthSq, &["A", "B"], "Dist_AB"),
                build(DefKind::LengthSq, &["A", "C"], "Dist_AC"),
            ],
            conclusions: vec![
                concl_same("Dist_AB", "Dist_AC")
            ],
        },

        // ==========================================
        // 🌟 共点二弦の相似(方冪の定理の基礎)
        // ==========================================
        // 方冪の定理を専用定理にせず、AA相似の最小部品として書く。
        // 主張: 2直線AB,CDがPで交わり、弦BDを見込む角が ∠(AB,AD) = ∠(CB,CD) なら、△PAD∽△PCB から
        // PA・PB = PC・PD(Pにおける角は直線の方向だけで決まるので、共通角の前提は構造的に満たされる)。
        // 円周角の定理が共円の4点にこの角の一致を与えるので、鎖状につながって方冪の定理になる
        // (test_power_of_point)。
        TheoremDef {
            name: "共点二弦の相似(方冪の定理の基礎)".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point), ("D", EntityType::Point), ("P", EntityType::Point),
                ("LineAB", EntityType::Line), ("LineCD", EntityType::Line), ("LineAD", EntityType::Line), ("LineCB", EntityType::Line),
                ("DirAB", EntityType::Point), ("DirCD", EntityType::Point), ("DirAD", EntityType::Point), ("DirCB", EntityType::Point),
                ("AngA", EntityType::Scalar), ("AngC", EntityType::Scalar),
                ("LenPA", EntityType::Scalar), ("LenPB", EntityType::Scalar), ("LenPC", EntityType::Scalar), ("LenPD", EntityType::Scalar),
                ("ProdAB", EntityType::Scalar), ("ProdCD", EntityType::Scalar),
            ]),
            patterns: vec![
                // Identical(AngA,AngC) から始めて、それぞれの定義から4方向を直接束縛する。
                // 前提は弦 BD を見込む円周角の一致 ∠(AB,AD) = ∠(CB,CD)(円周角の定理と同じ形)。
                // 2つの角は同じ向きで読む(グループ PowSim)。以前は2つ目を ∠(CD,CB) と逆向きに
                // 書いたうえで向きを独立に読ませていたので、共円でない配置でもマッチして
                // 数値的に偽のマージを作っていた。
                same_angle("AngA", "AngC"),
                angle_grouped(&["DirAB", "DirAD", "AngA"], "PowSim"),
                angle_grouped(&["DirCB", "DirCD", "AngC"], "PowSim"),
                distinct(&["DirAB", "DirAD"]),
                distinct(&["DirCD", "DirCB"]),

                // distinct は4直線が揃うまで待たず、束縛されるたびに挟んで、誤った組み合わせを早く打ち切る。
                has_direction("LineAB", "DirAB"),
                has_direction("LineAD", "DirAD"),
                has_direction("LineCD", "DirCD"),
                has_direction("LineCB", "DirCB"),
                distinct(&["LineAB", "LineAD", "LineCD", "LineCB"]),

                // A = LineAB ∩ LineAD (∠Aの頂点)
                on("A", "LineAB"),
                on("A", "LineAD"),
                // C = LineCD ∩ LineCB (∠Cの頂点)
                on("C", "LineCD"),
                on("C", "LineCB"),
                // P = LineAB ∩ LineCD (2弦の交点)。A,Cが確定した直後に見つけて
                // すぐdistinctで弾くことで、「PがAやCに化けた」まま後段の
                // B,D探索まで持ち越してしまう無駄を防ぐ。
                on("P", "LineAB"),
                on("P", "LineCD"),
                distinct(&["A", "C", "P"]),
                // B = LineAB ∩ LineCB (弦ABのもう一端。LineCBの上にもある点として一意に特定)
                on("B", "LineAB"),
                on("B", "LineCB"),
                distinct(&["A", "P", "B"]),
                // D = LineCD ∩ LineAD (弦CDのもう一端)
                on("D", "LineCD"),
                distinct(&["C", "P", "D"]),
                on("D", "LineAD"),
                distinct(&["A", "B", "C", "D"]),
            ],
            constructions: vec![
                build(DefKind::LengthSq, &["P", "A"], "LenPA"),
                build(DefKind::LengthSq, &["P", "B"], "LenPB"),
                build(DefKind::LengthSq, &["P", "C"], "LenPC"),
                build(DefKind::LengthSq, &["P", "D"], "LenPD"),
                build(DefKind::Product, &["LenPA", "LenPB"], "ProdAB"),
                build(DefKind::Product, &["LenPC", "LenPD"], "ProdCD"),
            ],
            conclusions: vec![
                concl_same("ProdAB", "ProdCD")
            ],
        },

        // 🌟 スパイラル相似の中点対応
        // 前提: ∠AEB=∠DEC かつ EA・EC=EB・ED(Eを中心とするスパイラル相似でA→D, B→C)。
        // 結論: M=Midpoint(A,B), N=Midpoint(D,C) について ∠AEM=∠DEN かつ EA・EN=EM・ED
        // (同じスパイラル相似が A,B の中点を D,C の中点に写す、を角と比に分解したもの)。
        // 射影的には「E中心の線束の複比(角)と円周点I中心の線束の複比(比)が両方一致する」ことと同値
        // (mmp_core/tests.rs の test_spiral_similarity_characterized_by_two_pencil_cross_ratios)で、
        // これが既存の語彙 AnglePair / LengthSq / Product だけで足りる根拠になっている。
        TheoremDef {
            name: "スパイラル相似の中点対応".to_string(),
            entities: entities(&[
                ("E", EntityType::Point), ("A", EntityType::Point), ("B", EntityType::Point), ("D", EntityType::Point), ("C", EntityType::Point),
                ("M", EntityType::Point), ("N", EntityType::Point),
                ("LineEA", EntityType::Line), ("LineEB", EntityType::Line), ("LineED", EntityType::Line), ("LineEC", EntityType::Line),
                ("LineEM", EntityType::Line), ("LineEN", EntityType::Line),
                ("DirEA", EntityType::Point), ("DirEB", EntityType::Point), ("DirED", EntityType::Point), ("DirEC", EntityType::Point),
                ("DirEM", EntityType::Point), ("DirEN", EntityType::Point),
                ("AngE_AB", EntityType::Scalar), ("AngE_DC", EntityType::Scalar), ("AngE_AM", EntityType::Scalar), ("AngE_DN", EntityType::Scalar),
                ("LenSqEA", EntityType::Scalar), ("LenSqEB", EntityType::Scalar), ("LenSqEC", EntityType::Scalar), ("LenSqED", EntityType::Scalar),
                ("LenSqEM", EntityType::Scalar), ("LenSqEN", EntityType::Scalar),
                ("ProdEAEC", EntityType::Scalar), ("ProdEBED", EntityType::Scalar),
                ("ProdEAEN", EntityType::Scalar), ("ProdEMED", EntityType::Scalar),
            ]),
            patterns: vec![
                // 角度の一致 ∠AEB = ∠DEC(A→D, B→C の向きをそろえた相似)から4方向を束縛する。
                // 2つの角は同じ向きで読む(向きが食い違うと ∠AEB = -∠DEC になり、相似ではない)。
                same_angle("AngE_AB", "AngE_DC"),
                angle_grouped(&["DirEA", "DirEB", "AngE_AB"], "SpiralSim"),
                angle_grouped(&["DirED", "DirEC", "AngE_DC"], "SpiralSim"),
                distinct(&["DirEA", "DirEB"]),
                distinct(&["DirED", "DirEC"]),

                has_direction("LineEA", "DirEA"),
                has_direction("LineEB", "DirEB"),
                has_direction("LineED", "DirED"),
                has_direction("LineEC", "DirEC"),
                distinct(&["LineEA", "LineEB", "LineED", "LineEC"]),

                // E = LineEA ∩ LineEB (∠AEBの頂点)であり、かつLineED,LineEC
                // 両方の上にもある(=△EDCの頂点も同じE、というスパイラル
                // 相似の前提そのもの)。
                on("E", "LineEA"),
                on("E", "LineEB"),
                on("E", "LineED"),
                on("E", "LineEC"),

                // A,B,D,C = それぞれの直線上のEでない方の点
                on("A", "LineEA"),
                on("B", "LineEB"),
                on("D", "LineED"),
                on("C", "LineEC"),
                distinct(&["E", "A", "B", "D", "C"]),

                // 前提2: 比の一致 EA・EC=EB・ED (共点二弦の相似と同じ形)。
                // E,A,B,D,Cはここまでで既に確定しているので、これは新規探索
                // ではなく「本当にこの比が成り立っているか」の確認になる。
                def_by(DefKind::LengthSq, &["E", "A", "LenSqEA"]),
                def_by(DefKind::LengthSq, &["E", "C", "LenSqEC"]),
                def_by(DefKind::Product, &["LenSqEA", "LenSqEC", "ProdEAEC"]),
                def_by(DefKind::LengthSq, &["E", "B", "LenSqEB"]),
                def_by(DefKind::LengthSq, &["E", "D", "LenSqED"]),
                def_by(DefKind::Product, &["LenSqEB", "LenSqED", "ProdEBED"]),
                same("ProdEAEC", "ProdEBED"),
            ],
            constructions: vec![
                build(DefKind::Midpoint, &["A", "B"], "M"),
                build(DefKind::Midpoint, &["D", "C"], "N"),
                build(DefKind::LineThroughPoints, &["E", "M"], "LineEM"),
                build(DefKind::LineThroughPoints, &["E", "N"], "LineEN"),
                build(DefKind::DirectionOf, &["LineEM"], "DirEM"),
                build(DefKind::DirectionOf, &["LineEN"], "DirEN"),
                build(DefKind::AnglePair, &["DirEA", "DirEM"], "AngE_AM"),
                build(DefKind::AnglePair, &["DirED", "DirEN"], "AngE_DN"),
                build(DefKind::LengthSq, &["E", "M"], "LenSqEM"),
                build(DefKind::LengthSq, &["E", "N"], "LenSqEN"),
                build(DefKind::Product, &["LenSqEA", "LenSqEN"], "ProdEAEN"),
                build(DefKind::Product, &["LenSqEM", "LenSqED"], "ProdEMED"),
            ],
            conclusions: vec![
                concl_same("AngE_AM", "AngE_DN"),
                concl_same("ProdEAEN", "ProdEMED"),
            ],
        },

        TheoremDef {
            name: "接弦定理".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point),
                ("Circ", EntityType::Conic), ("TanA", EntityType::Line),
                ("LineAB", EntityType::Line), ("LineAC", EntityType::Line), ("LineBC", EntityType::Line),
                ("DirTan", EntityType::Point), ("DirAB", EntityType::Point), ("DirAC", EntityType::Point), ("DirBC", EntityType::Point),
                ("AngTan", EntityType::Scalar), ("AngBCA", EntityType::Scalar),
            ]),
            patterns: vec![
                def_by(DefKind::Circumcircle, &["A", "B", "C", "Circ"]),
                def_by(DefKind::TangentLine, &["Circ", "A", "TanA"]),
                distinct(&["A", "B", "C"]),
                
                def_by(DefKind::LineThroughPoints, &["A", "B", "LineAB"]),
                def_by(DefKind::LineThroughPoints, &["A", "C", "LineAC"]),
                def_by(DefKind::LineThroughPoints, &["B", "C", "LineBC"]),
                
                def_by(DefKind::DirectionOf, &["TanA", "DirTan"]),
                def_by(DefKind::DirectionOf, &["LineAB", "DirAB"]),
                def_by(DefKind::DirectionOf, &["LineAC", "DirAC"]),
                def_by(DefKind::DirectionOf, &["LineBC", "DirBC"]),
                
                // 接線とABのなす角 ≡ 弧ABに対する円周角(C)
                angle_grouped(&["DirTan", "DirAB", "AngTan"], "TanGrp"),
                angle_grouped(&["DirAC", "DirBC", "AngBCA"], "TanGrp"),
            ],
            constructions: vec![],
            conclusions: vec![
                concl_same("AngTan", "AngBCA")
            ],
        },// ==========================================
        // 円周角の定理の逆[cite: 6]
        // ==========================================
        TheoremDef {
            name: "円周角の定理の逆".to_string(),
            entities: entities(&[
                ("Ang1", EntityType::Scalar), ("Ang2", EntityType::Scalar),
                ("Dir_L1", EntityType::Point), ("Dir_L2", EntityType::Point),
                ("Dir_L3", EntityType::Point), ("Dir_L4", EntityType::Point),
                ("L1", EntityType::Line), ("L2", EntityType::Line), ("L3", EntityType::Line), ("L4", EntityType::Line),
                ("P_Apex1", EntityType::Point), ("P_Apex2", EntityType::Point),
                ("P_Base1", EntityType::Point), ("P_Base2", EntityType::Point),
                ("Circ_New", EntityType::Conic),
            ]),
            patterns: vec![
                same_angle("Ang1", "Ang2"),
                angle_grouped(&["Dir_L1", "Dir_L2", "Ang1"], "ConvCyc"),
                angle_grouped(&["Dir_L3", "Dir_L4", "Ang2"], "ConvCyc"),
                
                has_direction("L1", "Dir_L1"),
                has_direction("L2", "Dir_L2"),
                has_direction("L3", "Dir_L3"),
                has_direction("L4", "Dir_L4"),
                distinct(&["L1", "L2", "L3", "L4"]),
                
                on("P_Apex1", "L1"),
                on("P_Apex1", "L2"),
                on("P_Apex2", "L3"),
                on("P_Apex2", "L4"),
                on("P_Base1", "L1"),
                on("P_Base1", "L3"),
                on("P_Base2", "L2"),
                on("P_Base2", "L4"),
                distinct(&["P_Apex1", "P_Apex2", "P_Base1", "P_Base2"]),
            ],
            // 🌟 Concyclicという専用Factで結論するのをやめ、P_Apex1,P_Base1,P_Base2
            // を通る円を作図し、P_Apex2もその円にConnectedである、という形で結論する。
            // (4点は対称な関係なので、どの3点を作図に使っても良い)
            constructions: vec![
                build(DefKind::Circumcircle, &["P_Apex1", "P_Base1", "P_Base2"], "Circ_New"),
            ],
            conclusions: vec![concl_on("P_Apex2", "Circ_New")],
        },
        // ==========================================
        // 同位角による平行判定 (右共通 / 左共通)[cite: 6]
        // ==========================================
        TheoremDef {
            name: "同位角による平行判定(右共通)".to_string(),
            entities: entities(&[
                ("D1", EntityType::Point), ("D2", EntityType::Point), ("D3", EntityType::Point),
                ("Ang1", EntityType::Scalar), ("Ang2", EntityType::Scalar),
            ]),
            patterns: vec![
                same_angle("Ang1", "Ang2"),
                angle_grouped(&["D1", "D3", "Ang1"], "P1"),
                angle_grouped(&["D2", "D3", "Ang2"], "P1"),
                distinct(&["D1", "D2", "D3"]),
            ],
            constructions: vec![],
            conclusions: vec![
                concl_same("D1", "D2")
            ],
        },
        TheoremDef {
            name: "同位角による平行判定(左共通)".to_string(),
            entities: entities(&[
                ("D1", EntityType::Point), ("D2", EntityType::Point), ("D3", EntityType::Point),
                ("Ang1", EntityType::Scalar), ("Ang2", EntityType::Scalar),
            ]),
            patterns: vec![
                same_angle("Ang1", "Ang2"),
                angle_grouped(&["D3", "D1", "Ang1"], "P2"),
                angle_grouped(&["D3", "D2", "Ang2"], "P2"),
                distinct(&["D1", "D2", "D3"]),
            ],
            constructions: vec![],
            conclusions: vec![
                concl_same("D1", "D2")
            ],
        },
        // ==========================================
        // 🌟 有向角の加法性
        // ==========================================
        TheoremDef {
            name: "有向角の加法性".to_string(),
            entities: entities(&[
                ("D1", EntityType::Point), ("D2", EntityType::Point), ("D3", EntityType::Point),
                ("D4", EntityType::Point), ("D5", EntityType::Point), ("D6", EntityType::Point),
                ("Ang12", EntityType::Scalar), ("Ang45", EntityType::Scalar),
                ("Ang23", EntityType::Scalar), ("Ang56", EntityType::Scalar),
                ("Ang13", EntityType::Scalar), ("Ang46", EntityType::Scalar),
            ]),
            patterns: vec![
                same_angle("Ang12", "Ang45"),
                angle_grouped(&["D1", "D2", "Ang12"], "Add1"),
                angle_grouped(&["D4", "D5", "Ang45"], "Add1"),
                
                // 爆速化: 一致した方向(D2, D5)を起点にピンポイント検索
                angle_grouped(&["D2", "D3", "Ang23"], "Add2"),
                angle_grouped(&["D5", "D6", "Ang56"], "Add2"),
                same_angle("Ang23", "Ang56"),
                
                distinct(&["D1", "D2", "D3"]),
                distinct(&["D4", "D5", "D6"]),

                // 🌟 [D1,D2,D3] と [D4,D5,D6] を丸ごと入れ替えても同じ結論になるので、order_le(D1,D4) で片方だけ残す。
                // D1==D4(方向を共有する角度チェイスの本来の使い方)は通す(OrderNonStrict 参照)。
                order_le(&["D1", "D4"]),

                angle_grouped(&["D1", "D3", "Ang13"], "Add3"),
                angle_grouped(&["D4", "D6", "Ang46"], "Add3"),
            ],
            constructions: vec![],
            conclusions: vec![
                concl_same("Ang13", "Ang46")
            ],
        },

        // ==========================================
        // 🌟 有向角の交替律 (Angle Permutation)
        // ==========================================
        TheoremDef {
            name: "有向角の交替律".to_string(),
            entities: entities(&[
                ("D1", EntityType::Point), ("D2", EntityType::Point), 
                ("D3", EntityType::Point), ("D4", EntityType::Point),
                ("Ang12", EntityType::Scalar), ("Ang34", EntityType::Scalar),
                ("Ang13", EntityType::Scalar), ("Ang24", EntityType::Scalar),
            ]),
            patterns: vec![
                same_angle("Ang12", "Ang34"),
                angle_grouped(&["D1", "D2", "Ang12"], "Perm1"),
                angle_grouped(&["D3", "D4", "Ang34"], "Perm1"),
                distinct(&["D1", "D2", "D3", "D4"]),
                
                angle_grouped(&["D1", "D3", "Ang13"], "Perm2"),
                angle_grouped(&["D2", "D4", "Ang24"], "Perm2"),
            ],
            constructions: vec![],
            conclusions: vec![
                concl_same("Ang13", "Ang24")
            ],
        },
        // ==========================================
        // 🌟 定理: 直角三角形の斜辺の中線 (角度版)
        // ==========================================
        TheoremDef {
            name: "直角三角形の斜辺の中線".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("C", EntityType::Point), ("H", EntityType::Point), ("M", EntityType::Point),
                ("L_AH", EntityType::Line), ("L_CH", EntityType::Line), ("L_MH", EntityType::Line), ("L_CA", EntityType::Line),
                ("Dir_AH", EntityType::Point), ("Dir_CH", EntityType::Point), ("Dir_MH", EntityType::Point), ("Dir_CA", EntityType::Point),
                ("Ang90", EntityType::Scalar), ("Ang_AH_CH", EntityType::Scalar), ("Ang_MH_CH", EntityType::Scalar), ("Ang_CH_CA", EntityType::Scalar),
            ]),
            patterns: vec![
                // 爆速化: まず中点を探す
                def_by(DefKind::Midpoint, &["A", "C", "M"]),
                
                same_angle("Ang_AH_CH", "Ang90"),
                def_by(DefKind::AnglePair, &["Dir_AH", "Dir_CH", "Ang_AH_CH"]),
                
                def_by(DefKind::DirectionOf, &["L_AH", "Dir_AH"]),
                def_by(DefKind::DirectionOf, &["L_CH", "Dir_CH"]),
                
                // CommonEntity の代用: Hが両方の直線に乗っていること
                on("H", "L_AH"),
                on("H", "L_CH"),
                
                on("A", "L_AH"),
                on("C", "L_CH"),
                
                distinct(&["A", "C", "H", "M"]),
                distinct(&["L_AH", "L_CH"]),
            ],
            constructions: vec![
                build(DefKind::LineThroughPoints, &["M", "H"], "L_MH"),
                build(DefKind::LineThroughPoints, &["C", "A"], "L_CA"),
                build(DefKind::DirectionOf, &["L_MH"], "Dir_MH"),
                build(DefKind::DirectionOf, &["L_CA"], "Dir_CA"),
                build(DefKind::AnglePair, &["Dir_MH", "Dir_CH"], "Ang_MH_CH"),
                build(DefKind::AnglePair, &["Dir_CH", "Dir_CA"], "Ang_CH_CA"),
            ],
            conclusions: vec![
                concl_same("Ang_MH_CH", "Ang_CH_CA")
            ],
        },

        // ==========================================
        // 🌟 定理: 直角三角形の斜辺の中線 (直線と距離の完全作図版)
        // ==========================================
        TheoremDef {
            name: "直角三角形の斜辺の中線 (距離版)".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point), ("Mid_BC", EntityType::Point),
                ("L1", EntityType::Line), ("L2", EntityType::Line),
                ("Dir1", EntityType::Point), ("Dir2", EntityType::Point),
                ("Ang_A", EntityType::Scalar), ("Ang90", EntityType::Scalar),
                ("Line_Median", EntityType::Line), ("Dir_Median", EntityType::Point), // 🌟 復活
                ("Dist_MB", EntityType::Scalar), ("Dist_MA", EntityType::Scalar),
            ]),
            patterns: vec![
                def_by(DefKind::Midpoint, &["B", "C", "Mid_BC"]),
                same_angle("Ang_A", "Ang90"),
                // 🌟 allow_flip = true
                angle_free(&["Dir1", "Dir2", "Ang_A"]),
                
                def_by(DefKind::DirectionOf, &["L1", "Dir1"]),
                def_by(DefKind::DirectionOf, &["L2", "Dir2"]),
                on("A", "L1"),
                on("A", "L2"),
                on("B", "L1"),
                on("C", "L2"),
                distinct(&["A", "B", "C"]),
            ],
            constructions: vec![
                // 🌟 FIX: 直線と方向をE-Graphに物理的に作図し、他の定理への架け橋を作る
                build(DefKind::LineThroughPoints, &["Mid_BC", "A"], "Line_Median"),
                build(DefKind::DirectionOf, &["Line_Median"], "Dir_Median"),
                
                build(DefKind::LengthSq, &["Mid_BC", "B"], "Dist_MB"),
                build(DefKind::LengthSq, &["Mid_BC", "A"], "Dist_MA"),
            ],
            conclusions: vec![
                concl_same("Dist_MB", "Dist_MA")
            ],
        },

        // ==========================================
        // 🌟 定理: 直角三角形の斜辺の中線の逆
        // ==========================================
        // 「直角三角形の斜辺の中線(距離版)」の逆。BCの中点MからAまでの距離が
        // Mから B までの距離(=BC/2)と等しいならば、角Aは直角である。
        // タレスの定理(半円の弧に立つ角は直角)の証明で使う: 直径の両端をB,C、
        // 円の中心(=BCの中点)をM、円周上の点をAとすれば、MA=MB(=半径)は
        // 「Aが円上にある」という仮定そのものなので、この定理だけで
        // ∠BAC=90°が導ける。
        TheoremDef {
            name: "直角三角形の斜辺の中線の逆".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point), ("Mid_BC", EntityType::Point),
                ("L1", EntityType::Line), ("L2", EntityType::Line),
                ("Dir1", EntityType::Point), ("Dir2", EntityType::Point),
                ("Ang_A", EntityType::Scalar), ("Ang90", EntityType::Scalar),
                ("Dist_MB", EntityType::Scalar), ("Dist_MA", EntityType::Scalar),
            ]),
            patterns: vec![
                def_by(DefKind::Midpoint, &["B", "C", "Mid_BC"]),
                def_by(DefKind::LengthSq, &["Mid_BC", "B", "Dist_MB"]),
                def_by(DefKind::LengthSq, &["Mid_BC", "A", "Dist_MA"]),
                same("Dist_MB", "Dist_MA"),
                distinct(&["A", "B", "C"]),
            ],
            constructions: vec![
                build(DefKind::LineThroughPoints, &["A", "B"], "L1"),
                build(DefKind::LineThroughPoints, &["A", "C"], "L2"),
                build(DefKind::DirectionOf, &["L1"], "Dir1"),
                build(DefKind::DirectionOf, &["L2"], "Dir2"),
                build(DefKind::AnglePair, &["Dir1", "Dir2"], "Ang_A"),
            ],
            conclusions: vec![
                concl_same("Ang_A", "Ang90")
            ],
        },
    ]
}

/// 🌟 長さを橋渡しする定理(既定の定理集合には入れていない。--length-theorems で入る)。
/// 未解決問題の詰まり所の手順は自力で出せるようになったが、既定に入れると解ける問題は増えずに他の問題の
/// 仕事量が大きく増える(増えた長さの事実に探索が引っ張られる)。問題ごとの opt-in は新しい問題に効かない
/// ので持たず、課税をスケジューラ側で自動的に抑えられるようになるまでは全問題一律のスイッチにしておく。
pub fn get_length_bridge_theorems() -> Vec<TheoremDef> {
    vec![
        // ==========================================
        // 🌟 中点連結定理(長さ版)
        // ==========================================
        // 三角形ABCの3辺の中点 Mab, Mac, Mbc について、Mab–Mac の長さは BC の半分、つまり B–Mbc(= Mbc–C)に
        // 等しい。上の「中点連結定理」は平行しか結論しない。
        // 3つの中点が既に図にあることを要求する(作らない)。中点は数が少ないのでマッチングは安く、無関係な問題に
        // 中点を撒くこともない。長さは平方のまま比べる。1回の発火で1辺ぶんを結論し、残りの2辺は A,B,C の取り方の
        // 違いとして別の発火が出す。
        TheoremDef {
            name: "中点連結定理(長さ)".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point),
                ("Mab", EntityType::Point), ("Mac", EntityType::Point), ("Mbc", EntityType::Point),
                ("LenMid", EntityType::Scalar), ("LenHalf", EntityType::Scalar),
            ]),
            patterns: vec![
                def_by(DefKind::Midpoint, &["A", "B", "Mab"]),
                def_by(DefKind::Midpoint, &["A", "C", "Mac"]),
                def_by(DefKind::Midpoint, &["B", "C", "Mbc"]),
                distinct(&["A", "B", "C", "Mab", "Mac", "Mbc"]),
            ],
            constructions: vec![
                build(DefKind::LengthSq, &["Mab", "Mac"], "LenMid"),
                build(DefKind::LengthSq, &["B", "Mbc"], "LenHalf"),
            ],
            conclusions: vec![
                concl_same("LenMid", "LenHalf")
            ],
        },
    ]
}

/// 🌟 中心角の定理: OがA,B,Cから等距離(=外接円の中心)であるとき、中心角∠BOCは円周角∠BACの2倍。
/// 有向角(mod π)は円周点との複比 k=e^{2iθ} として評価されるので、角の2倍は k² になる。つまり「2倍」は
/// 既存の Product(AngBAC と自分自身の積)で表せ、新しい計算プリミティブは要らない。
/// 既定の定理集合には入れていない: 外心を持つ問題では前提がほぼ常に満たされるので、無関係な問題にも
/// 試行のコストが乗り、既定に入れると他の問題が解けなくなった。現状は solve.rs の CENTRAL_ANGLE_PROBLEMS
/// (暫定の問題名リスト)と --central-angle で入る。
pub fn get_central_angle_theorem() -> Vec<TheoremDef> {
    vec![
        TheoremDef {
            name: "中心角の定理".to_string(),
            entities: entities(&[
                ("O", EntityType::Point), ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point),
                ("LenOA", EntityType::Scalar), ("LenOB", EntityType::Scalar), ("LenOC", EntityType::Scalar),
                ("L_AB", EntityType::Line), ("L_AC", EntityType::Line), ("L_OB", EntityType::Line), ("L_OC", EntityType::Line),
                ("Dir_AB", EntityType::Point), ("Dir_AC", EntityType::Point), ("Dir_OB", EntityType::Point), ("Dir_OC", EntityType::Point),
                ("AngBAC", EntityType::Scalar), ("AngBOC", EntityType::Scalar), ("AngBAC_Sq", EntityType::Scalar),
            ]),
            patterns: vec![
                // 前提: OA=OB=OC (Oは外心)
                def_by(DefKind::LengthSq, &["O", "A", "LenOA"]),
                def_by(DefKind::LengthSq, &["O", "B", "LenOB"]),
                same("LenOA", "LenOB"),
                def_by(DefKind::LengthSq, &["O", "C", "LenOC"]),
                same("LenOA", "LenOC"),
                distinct(&["O", "A", "B", "C"]),

                // 円周角∠BAC(A→B, A→C)と中心角∠BOC(O→B, O→C)を同じ
                // 向き(B側→C側)で構成する。
                def_by(DefKind::LineThroughPoints, &["A", "B", "L_AB"]),
                def_by(DefKind::LineThroughPoints, &["A", "C", "L_AC"]),
                distinct(&["L_AB", "L_AC"]),
                def_by(DefKind::LineThroughPoints, &["O", "B", "L_OB"]),
                def_by(DefKind::LineThroughPoints, &["O", "C", "L_OC"]),
                distinct(&["L_OB", "L_OC"]),

                def_by(DefKind::DirectionOf, &["L_AB", "Dir_AB"]),
                def_by(DefKind::DirectionOf, &["L_AC", "Dir_AC"]),
                def_by(DefKind::DirectionOf, &["L_OB", "Dir_OB"]),
                def_by(DefKind::DirectionOf, &["L_OC", "Dir_OC"]),

                def_by(DefKind::AnglePair, &["Dir_AB", "Dir_AC", "AngBAC"]),
                def_by(DefKind::AnglePair, &["Dir_OB", "Dir_OC", "AngBOC"]),
            ],
            constructions: vec![
                build(DefKind::Product, &["AngBAC", "AngBAC"], "AngBAC_Sq"),
            ],
            conclusions: vec![
                concl_same("AngBOC", "AngBAC_Sq")
            ],
        },
    ]
}

/// 射影の定理: 複比の透視射影不変性(点→線束・線束→点)とシュタイナーの定理(順・接線版・逆)。
///
/// 全問題で既定で使う(--no-projective で外せる)。射影を主題にしない問題にも仕事量を上乗せするが、
/// 問題名で入れる問題を選ぶ方式は新しい問題に効かないのでやめた。
pub fn get_projective_theorems() -> Vec<TheoremDef> {
    vec![
        // 🌟 複比の透視射影不変性は、9変数を同時に束縛する1つの定理ではなく、線束の複比 CrossRatioOfLines を
        // 中継点にした2つの小さな定理に分けて書く:
        //   点→線束: 直線L上のA,B,C,Dの複比 = Oを通る4直線(LOA..LOD)の複比
        //   線束→点: 共点な4直線(L1..L4)の複比 = 横断線T上のAp..Dpの複比
        // 合同閉包が CrossRatioOfLines を介して両者をつなぎ、CrossRatio(A,B,C,D) ≡ CrossRatio(Ap,Bp,Cp,Dp) に届く。
        // 変数は Connected の局所スキャンで芋づる式に見つかり、線束→点の L1..L4 は点→線束が作った DefinedBy
        // 事実からシードされるので、どちらも全件スキャンが要らない。
        // 点→線束は対合定理(共点4直線を横断線が切る配置)の最小形でもあるので、別の定理として複製しない
        // (同じ線束を2本の横断線で切る「対合」は、この定理2回 + 推移律で得られる。test_involution)。
        TheoremDef {
            name: "複比の透視射影不変性(点→線束)/対合定理(共点4直線+横断線)".to_string(),
            entities: entities(&[
                ("O", EntityType::Point),
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point), ("D", EntityType::Point),
                ("L", EntityType::Line),
                ("LOA", EntityType::Line), ("LOB", EntityType::Line), ("LOC", EntityType::Line), ("LOD", EntityType::Line),
                ("CR1", EntityType::Scalar), ("CRL", EntityType::Scalar),
            ]),
            patterns: vec![
                // A,B,C,Dが共通の直線L上にある(複比が意味を持つための前提)。
                // Aから局所スキャンでLを見つけ、B,C,Dも同じL上にあるか確認する。制約は最後に1回ではなく、各点が
                // 束縛された直後に挟む(Distinct/Order は全変数が束縛されるまで INFINITY なので、最後にまとめると
                // A=B のような無駄な組み合わせを掘り下げてから弾くことになる)。
                on("A", "L"),
                on("B", "L"),
                // 🌟 同じ4点集合の並べ替えを全部試さないよう、代表元ID昇順の1通りだけを通す。複比は V4 でしか値が
                // 保たれない(6通りの値がある)ので、そのうち1つしか作られない ― 目標の複比が別の値だと届かないという
                // 既知の制約がある。緩め方は試したがどれも採用できなかった(経緯: docs/notes/theorems.md
                // 「複比の透視射影不変性」)。直すならパターンの評価順と cap の側で、定理を増やす話ではない。
                order(&["A", "B"]),
                on("C", "L"),
                order(&["B", "C"]),
                on("D", "L"),
                order(&["C", "D"]),
                // A,B,C,Dそれぞれについて「Lとは別の、Oを通る直線」を局所
                // スキャンで見つける(A自身の既知の直線のうち、Lではない方)。
                on("A", "LOA"),
                on("O", "LOA"),
                on("B", "LOB"),
                on("O", "LOB"),
                on("C", "LOC"),
                on("O", "LOC"),
                on("D", "LOD"),
                on("O", "LOD"),
                distinct(&["LOA", "LOB", "LOC", "LOD"]),
            ],
            constructions: vec![
                build(DefKind::CrossRatio, &["A", "B", "C", "D"], "CR1"),
                build(DefKind::CrossRatioOfLines, &["LOA", "LOB", "LOC", "LOD"], "CRL"),
            ],
            conclusions: vec![
                concl_same("CR1", "CRL")
            ],
        },
        TheoremDef {
            name: "複比の透視射影不変性(線束→点)".to_string(),
            entities: entities(&[
                ("L1", EntityType::Line), ("L2", EntityType::Line), ("L3", EntityType::Line), ("L4", EntityType::Line),
                ("O", EntityType::Point), ("T", EntityType::Line),
                ("Ap", EntityType::Point), ("Bp", EntityType::Point), ("Cp", EntityType::Point), ("Dp", EntityType::Point),
                ("CRL", EntityType::Scalar), ("CR2", EntityType::Scalar),
            ]),
            patterns: vec![
                // 前提は2つ: L1..L4 が1点 O で交わる(線束である)こと、Ap..Dp が同じ直線 T の上で
                // それぞれ L1..L4 と交わること。どちらが欠けても線束の複比と点の複比は一致しない
                // (DefinedBy は線束の複比を任意の4直線に対してその場で作るので、共点は明示が要る)。
                def_by(DefKind::CrossRatioOfLines, &["L1", "L2", "L3", "L4", "CRL"]),
                distinct(&["L1", "L2", "L3", "L4"]),
                on("O", "L1"),
                on("O", "L2"),
                on("O", "L3"),
                on("O", "L4"),
                on("Ap", "L1"),
                on("Ap", "T"),
                on("Bp", "L2"),
                on("Bp", "T"),
                on("Cp", "L3"),
                on("Cp", "T"),
                on("Dp", "L4"),
                on("Dp", "T"),
                // 交点が中心 O そのものなら T は O を通っていて、複比は定まらない。
                distinct(&["O", "Ap", "Bp", "Cp", "Dp"]),
            ],
            constructions: vec![
                build(DefKind::CrossRatio, &["Ap", "Bp", "Cp", "Dp"], "CR2"),
            ],
            conclusions: vec![
                concl_same("CRL", "CR2")
            ],
        },
        // ==========================================
        // 🌟 シュタイナーの定理(二次曲線上の6点による複比の不変性)
        // ==========================================
        // 円周角の定理の一般の二次曲線への拡張。二次曲線上の2点P,Qから見た、同じ二次曲線上の他の4点への直線束は
        // 常に同じ複比を持つ。
        // マッチングを軽くするため、6点を全件スキャンで探さず、二次曲線の定義の生成元5点 P1..P5 を DefinedBy から
        // 直接束縛し、新たにスキャンするのは「二次曲線上のもう1点Q」だけにする。視点は P1,P5、見る先は P2,P3,P4,Q
        // に固定した特殊形で、別の視点が要るなら問題側でその点を生成元に含めて二次曲線を作る。
        TheoremDef {
            name: "シュタイナーの定理(二次曲線上の6点の複比不変性)".to_string(),
            entities: entities(&[
                ("P1", EntityType::Point), ("P2", EntityType::Point), ("P3", EntityType::Point),
                ("P4", EntityType::Point), ("P5", EntityType::Point), ("Q", EntityType::Point),
                ("Conic", EntityType::Conic),
                ("L1_P2", EntityType::Line), ("L1_P3", EntityType::Line), ("L1_P4", EntityType::Line), ("L1_Q", EntityType::Line),
                ("L5_P2", EntityType::Line), ("L5_P3", EntityType::Line), ("L5_P4", EntityType::Line), ("L5_Q", EntityType::Line),
                ("CR_P1", EntityType::Scalar), ("CR_P5", EntityType::Scalar),
            ]),
            patterns: vec![
                // 🌟 シード: 既存の二次曲線自身の定義からP1..P5とConicを直接
                // 束縛する(「複比の透視射影不変性(線束→点)」がCrossRatioOfLines
                // からL1..L4を直接束縛するのと全く同じ発想)。
                def_by(DefKind::ConicThrough5Points, &["P1", "P2", "P3", "P4", "P5", "Conic"]),
                // 二次曲線上のもう1点Qを局所スキャンで見つける(唯一の
                // 「新規に探す」変数)。
                on("Q", "Conic"),
                distinct(&["P1", "P2", "P3", "P4", "P5", "Q"]),
                // P1から見たP2,P3,P4,Qへの4直線(既存のものが無ければ
                // 円周角の定理のL_A1_B1等と同じ「DefinedBy+作図需要」で作る)。
                def_by(DefKind::LineThroughPoints, &["P1", "P2", "L1_P2"]),
                def_by(DefKind::LineThroughPoints, &["P1", "P3", "L1_P3"]),
                def_by(DefKind::LineThroughPoints, &["P1", "P4", "L1_P4"]),
                def_by(DefKind::LineThroughPoints, &["P1", "Q", "L1_Q"]),
                distinct(&["L1_P2", "L1_P3", "L1_P4", "L1_Q"]),
                // P5から見た同じP2,P3,P4,Qへの4直線。
                def_by(DefKind::LineThroughPoints, &["P5", "P2", "L5_P2"]),
                def_by(DefKind::LineThroughPoints, &["P5", "P3", "L5_P3"]),
                def_by(DefKind::LineThroughPoints, &["P5", "P4", "L5_P4"]),
                def_by(DefKind::LineThroughPoints, &["P5", "Q", "L5_Q"]),
                distinct(&["L5_P2", "L5_P3", "L5_P4", "L5_Q"]),
            ],
            constructions: vec![
                build(DefKind::CrossRatioOfLines, &["L1_P2", "L1_P3", "L1_P4", "L1_Q"], "CR_P1"),
                build(DefKind::CrossRatioOfLines, &["L5_P2", "L5_P3", "L5_P4", "L5_Q"], "CR_P5"),
            ],
            conclusions: vec![
                concl_same("CR_P1", "CR_P5")
            ],
        },
        // ==========================================
        // 🌟 シュタイナーの定理(接線版)/接弦定理の射影版
        // ==========================================
        // 上のシュタイナーの定理で Q→P1 とした極限(弦 P1Q が P1 における接線に退化する)。接弦定理が円周角の定理の
        // 極限であるのと同じ関係。生成元5点だけで完結するので Q のスキャンが要らない: P1 における接線 T1 と
        // P1 から見た P2,P3,P4 への3直線の複比が、P5 から見た P2,P3,P4,P1 への4直線の複比と一致する。
        TheoremDef {
            name: "シュタイナーの定理(接線版)/接弦定理(射影版)".to_string(),
            entities: entities(&[
                ("P1", EntityType::Point), ("P2", EntityType::Point), ("P3", EntityType::Point),
                ("P4", EntityType::Point), ("P5", EntityType::Point),
                ("Conic", EntityType::Conic),
                ("T1", EntityType::Line),
                ("L1_P2", EntityType::Line), ("L1_P3", EntityType::Line), ("L1_P4", EntityType::Line),
                ("L5_P2", EntityType::Line), ("L5_P3", EntityType::Line), ("L5_P4", EntityType::Line), ("L5_P1", EntityType::Line),
                ("CR_P1", EntityType::Scalar), ("CR_P5", EntityType::Scalar),
            ]),
            patterns: vec![
                // 🌟 シード: シュタイナーの定理と全く同じ発想で、二次曲線自身の
                // 定義からP1..P5とConicを直接束縛する(全件スキャン不要)。
                def_by(DefKind::ConicThrough5Points, &["P1", "P2", "P3", "P4", "P5", "Conic"]),
                distinct(&["P1", "P2", "P3", "P4", "P5"]),

                // P1における接線T1(円周角の定理の逆の"TanA"と同じ発想の
                // DefinedBy+作図需要)。
                def_by(DefKind::TangentLine, &["Conic", "P1", "T1"]),

                // P1から見たP2,P3,P4への3直線。
                def_by(DefKind::LineThroughPoints, &["P1", "P2", "L1_P2"]),
                def_by(DefKind::LineThroughPoints, &["P1", "P3", "L1_P3"]),
                def_by(DefKind::LineThroughPoints, &["P1", "P4", "L1_P4"]),
                distinct(&["L1_P2", "L1_P3", "L1_P4"]),

                // P5から見たP2,P3,P4,P1への4直線(P1は接点ではなく"ただの弦"
                // として、シュタイナーの定理のQと同じ役割で扱う)。
                def_by(DefKind::LineThroughPoints, &["P5", "P2", "L5_P2"]),
                def_by(DefKind::LineThroughPoints, &["P5", "P3", "L5_P3"]),
                def_by(DefKind::LineThroughPoints, &["P5", "P4", "L5_P4"]),
                def_by(DefKind::LineThroughPoints, &["P5", "P1", "L5_P1"]),
                distinct(&["L5_P2", "L5_P3", "L5_P4", "L5_P1"]),
            ],
            constructions: vec![
                build(DefKind::CrossRatioOfLines, &["L1_P2", "L1_P3", "L1_P4", "T1"], "CR_P1"),
                build(DefKind::CrossRatioOfLines, &["L5_P2", "L5_P3", "L5_P4", "L5_P1"], "CR_P5"),
            ],
            conclusions: vec![
                concl_same("CR_P1", "CR_P5")
            ],
        },
        // ==========================================
        // 🌟 シュタイナーの定理の逆(射影版・円周角の定理の逆)
        // ==========================================
        // P1,P5から見た同じ4点(P2,P3,P4,Q)への直線束の複比が等しいなら、6点は共通の二次曲線に乗る。
        // 二次曲線はこれから作るので、CrossRatioOfLines の定義から4直線を直接束縛する(円周角の定理の逆が
        // AnglePair の定義から2方向を束縛するのと同じ)。
        TheoremDef {
            name: "シュタイナーの定理の逆(射影版・円周角の定理の逆)".to_string(),
            entities: entities(&[
                ("CR_P1", EntityType::Scalar), ("CR_P5", EntityType::Scalar),
                ("L1_P2", EntityType::Line), ("L1_P3", EntityType::Line), ("L1_P4", EntityType::Line), ("L1_Q", EntityType::Line),
                ("L5_P2", EntityType::Line), ("L5_P3", EntityType::Line), ("L5_P4", EntityType::Line), ("L5_Q", EntityType::Line),
                ("P1", EntityType::Point), ("P5", EntityType::Point),
                ("P2", EntityType::Point), ("P3", EntityType::Point), ("P4", EntityType::Point), ("Q", EntityType::Point),
                ("Conic_New", EntityType::Conic),
            ]),
            patterns: vec![
                // 🌟 シード: Identical(CR_P1,CR_P5) から始めて、それぞれの定義から4直線を直接束縛する。
                // same_cross_ratio_of_lines は自己束縛の候補を CrossRatioOfLines 由来の Scalar だけに絞る
                // (長さ・積・点の複比まで含むプールから無関係な値を試さない)。
                same_cross_ratio_of_lines("CR_P1", "CR_P5"),
                def_by(DefKind::CrossRatioOfLines, &["L1_P2", "L1_P3", "L1_P4", "L1_Q", "CR_P1"]),
                def_by(DefKind::CrossRatioOfLines, &["L5_P2", "L5_P3", "L5_P4", "L5_Q", "CR_P5"]),
                distinct(&["L1_P2", "L1_P3", "L1_P4", "L1_Q"]),
                distinct(&["L5_P2", "L5_P3", "L5_P4", "L5_Q"]),

                // P1 = L1側4直線に共通の点(視点)。P5も同様。
                on("P1", "L1_P2"),
                on("P1", "L1_P3"),
                on("P1", "L1_P4"),
                on("P1", "L1_Q"),
                on("P5", "L5_P2"),
                on("P5", "L5_P3"),
                on("P5", "L5_P4"),
                on("P5", "L5_Q"),

                // P2 = L1_P2とL5_P2に共通の点(視点P1,P5以外)。P3,P4,Qも同様。
                on("P2", "L1_P2"),
                on("P2", "L5_P2"),
                on("P3", "L1_P3"),
                on("P3", "L5_P3"),
                on("P4", "L1_P4"),
                on("P4", "L5_P4"),
                on("Q", "L1_Q"),
                on("Q", "L5_Q"),
                distinct(&["P1", "P5", "P2", "P3", "P4", "Q"]),
            ],
            constructions: vec![
                build(DefKind::ConicThrough5Points, &["P1", "P2", "P3", "P4", "P5"], "Conic_New"),
            ],
            conclusions: vec![
                concl_on("Q", "Conic_New")
            ],
        },
    ]
}
#[cfg(test)]
mod tests {
    use super::*;

    fn every_theorem() -> Vec<TheoremDef> {
        let mut all = get_all_theorems();
        all.extend(get_projective_theorems());
        all.extend(get_central_angle_theorem());
        all.extend(get_length_bridge_theorems());
        all
    }

    /// Order / Distinct / Not に出てくる変数が、(Not の外の)事実パターンのどれかにも出てくること。
    ///
    /// dfs_match は一番安いパターンを消費するが、制約と Not は「全変数が束縛されるまで INFINITY」。
    /// 生きているパターンが全部 INFINITY なら一番若い添字が消費されるので、事実パターンで
    /// 束縛されない変数があると、その変数についての制約は検査されないまま捨てられる。
    #[test]
    fn every_constrained_variable_is_also_bound_by_a_fact() {
        fn vars_of(pat: &Pattern, out: &mut Vec<String>) {
            match pat {
                Pattern::Order(v) | Pattern::OrderNonStrict(v) | Pattern::Distinct(v) => out.extend(v.iter().cloned()),
                Pattern::Not(inner) => vars_of(inner, out),
                _ => out.extend(pat.fact_args().into_iter().flatten().cloned()),
            }
        }
        let mut bad: Vec<String> = Vec::new();
        for t in &every_theorem() {
            let mut fact_vars: Vec<String> = Vec::new();
            let mut constrained: Vec<String> = Vec::new();
            for p in &t.patterns {
                match p {
                    Pattern::Order(_) | Pattern::OrderNonStrict(_) | Pattern::Distinct(_) | Pattern::Not(_) => vars_of(p, &mut constrained),
                    _ => vars_of(p, &mut fact_vars),
                }
            }
            for v in constrained {
                if !fact_vars.contains(&v) {
                    bad.push(format!("定理「{}」の変数 {}", t.name, v));
                }
            }
        }
        assert!(bad.is_empty(), "Order/Distinct にしか出てこない変数がある:\n{}", bad.join("\n"));
    }

    /// 作図・DefinedBy の親の数が種類と合っていること。合わないと build_definition が
    /// None を返し、その作図やパターンは黙って成立しなくなる。
    #[test]
    fn every_definition_has_the_right_number_of_parents() {
        let mut bad: Vec<String> = Vec::new();
        for t in &every_theorem() {
            for p in &t.patterns {
                let p = match p { Pattern::Not(inner) => &**inner, other => other };
                if let Pattern::DefinedBy { kind, parents, .. } = p {
                    if parents.len() != kind.arity() {
                        bad.push(format!("定理「{}」の DefinedBy {:?}({})", t.name, kind, parents.join(",")));
                    }
                }
            }
            for c in &t.constructions {
                if c.args.len() != c.kind.arity() {
                    bad.push(format!("定理「{}」の作図 {:?}({})", t.name, c.kind, c.args.join(",")));
                }
            }
        }
        assert!(bad.is_empty(), "親の数が種類と合わない:\n{}", bad.join("\n"));
    }

    /// dfs_match は「まだ消費していないパターン」を u64 のビットマスクで持つので、
    /// 定理1つあたりのパターンは64本まで。
    #[test]
    fn every_theorem_fits_the_pattern_bitmask() {
        let all = every_theorem();
        for t in &all {
            assert!(t.patterns.len() <= 64,
                "定理「{}」のパターンが{}本あり、u64のビットマスクに入らない。\
                 dfs_matchのactiveをu128等に広げる必要がある。", t.name, t.patterns.len());
        }
        let widest = all.iter().map(|t| t.patterns.len()).max().unwrap_or(0);
        assert!(widest > 0, "定理が1つも読めていない");
    }
}

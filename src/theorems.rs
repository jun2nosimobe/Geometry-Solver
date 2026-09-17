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
                // 🌟 Concyclicという専用Factをやめ、「4点が同じ円Circに乗っている」を
                // Connectedの4連続で表す。link_logical_incidenceによる構造的な接続
                // だけで十分になり、専用Factの登録忘れバグが起きなくなる。
                // 🌟 EntityType::Circle撤廃(mmp_core/mod.rs::EntityTypeの
                // ドキュメント参照)により、Circは今やEntityType::Conic(一般の
                // 二次曲線と同じ型)なので、target_type="Circle"マーカーで
                // 「I,Jを両方通る=本物の円」だけに絞る(マーカー無しだと
                // シュタイナーの定理用の非円な二次曲線まで候補に混ざってしまう)。
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

        // 🌟 「直線の一致条件」(2直線が2点を共有、または1点+同方向を共有するなら
        // 同一直線)と「2直線の交点の一意性」(2直線の交点として既知の点と、同じ
        // 2直線にConnectedな別の点があれば同一点)は、以前はここに専用の
        // TheoremDefとして存在していたが、e-graphの合同閉包(mmp_core.rsの
        // propagate_line_uniqueness / propagate_point_uniqueness)に局所伝播
        // として統合済み。dfs_matchによる全探索より遥かに軽く、Direction
        // (無限遠直線上の点として扱う)も同じ経路で扱えるようになったため、
        // このBlackboard定理としての実装は不要になり削除した。
        // 実装は commit ea75ca3 (追加) / a66efdb (伝播への統合) を参照。

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
        //
        // 🌟 中点と垂直二等分線は前提ではなく結論側で作る。以前は Mid_BC・LineBC・
        // PerpMid を DefinedBy で「既に図にあること」として要求していたので、
        // 垂直二等分線がまだ無い線分では等距離が示されても一度も発火しなかった。
        // diagnose(sketch.rs)で、bench_2016armog10p2 の「OaとObがDXの両端から
        // 等距離 ⟹ OaOb ⊥ DX」と bench_2000usatstp2 の「MとNがEFの両端から
        // 等距離 ⟹ MN ⊥ EF」が、まさにこの制約で止まっていると分かった。
        // 2点が同じ垂直二等分線に乗れば、あとは直線の一意性で2点を結ぶ直線が
        // その垂直二等分線そのものになる。
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
        // 古典的には「三角形ABCと三角形ACB(B,Cを入れ替えたもの)は、角Bと角Cが
        // 等しく角Aが共通なのでAA相似。相似比はBC/CB=1なので、対応する
        // AB/AC = CA/BA = 1、すなわちAB=AC」という自己相似による証明に対応する。
        // 上の「二等辺三角形の底角」と全く同じ足場(A,B,C・3直線・3方向)を使い、
        // 前提と結論を入れ替えただけの構造だが、これは「底角が等しい⟺二辺が
        // 等しい」という古典的な必要十分性の、逆方向を独立に定式化したもの
        // (対称なパターンを持つからといって自動的に逆が成り立つわけではない
        // ―― フリップ機構は有向角の符号の曖昧さを吸収するだけの、双方向の
        // 論理的主張のどちらにも中立なパターンマッチ上の道具立てである)。
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
        // 方冪の定理(PA・PB=PC・PD)を、それ自体を専用定理として作らず、
        // 「AA相似」の最小構成部品として実装する。円周角の定理(既存)と
        // 組み合わせるだけで方冪の定理そのものが得られる(ユーザー要望通り
        // 「難しい定理を簡単な定理の組み合わせに分割する」の実践 ――
        // 「対合定理」を独自定理として複製せず既存定理の組み合わせで得た
        // のと全く同じ発想)。
        //
        // 主張: 2直線AB,CDがPで交わるとき、∠(AB方向,AD方向)=∠(CD方向,CB方向)
        // (Pにおける角は直線の方向だけで決まるので、A,Bどちらを基準にしても
        // 同じ角になり、"共通角"の前提は構造的に自動で満たされる)ならば、
        // 三角形PAD∽三角形PCB(2角相等)から PA・PB = PC・PD。
        // 円周角の定理が「A,D,B,Cが共円なら∠DAB=∠DCB」を与えるので、
        // 4点が共円のときはこの定理と鎖状に繋がって方冪の定理そのものになる
        // (test_power_of_point.rsで実際に新定理を1つも増やさず検証済み)。
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

                // 🐛 実測に基づくFIX(セッション既知の教訓の再適用): distinctを
                // 4直線が全部揃うまで1回だけにまとめず、束縛されるたびに
                // 挟むことで、間違った(=有向角のフリップや無関係な複比クラスに
                // 由来する)直線の組み合わせを早期に打ち切る(「複比の透視射影
                // 不変性」定理群のバグ修正と全く同じ理由)。
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
        //
        // ユーザー提案の経緯: 「△EABと△EDCが直接相似(Eを中心とするスパイラル
        // 相似でA→D,B→C)」は、古典的に「(E,A,B,I,J)と(E,D,C,I,J)という2つの
        // 5点配置が射影変換で移り合う」こと(I,Jは虚円点。相似変換=射影変換の
        // うちI,Jを固定するものという古典的特徴づけ)と同値であり、これは
        // (a)Eを中心とする線束の複比(角度だけを運ぶ)と(b)虚円点Iを中心とする
        // 線束の複比(距離を含む計量的な情報を運ぶ)の両方が一致することと
        // 同値、という指摘に基づく。実際にtest_spiral_similarity_characterized_by_two_pencil_cross_ratios
        // (mmp_core/tests.rs)で数値的に検証した。
        //
        // (a)は既存のAnglePair等式と、(b)は既存のLengthSq/Product(方冪の
        // 定理と同じ形)と、それぞれ既に完全に同値であることが分かった
        // (射影的な言い回しはあくまで「なぜこの2つの条件だけで十分か」を
        // 裏付ける理論的根拠であって、実装そのものはI,J/CrossRatioOfLinesを
        // 新たに持ち出さなくても、既存の語彙(AnglePair, LengthSq, Product)
        // だけで完結する)。
        //
        // 前提: ∠AEB=∠DEC(角度の一致)かつ EA・EC=EB・ED(比の一致、
        // LengthSqの積として表現。共点二弦の相似と全く同じ形)。
        // 結論: M=Midpoint(A,B), N=Midpoint(D,C) について、
        //   ∠AEM=∠DEN(同じ回転角で対応する)
        //   EA・EN=EM・ED(同じ比で対応する)
        // これは「△EAM ∽ △EDN が同じスパイラル相似で結ばれている」ことを
        // 意味し、特に「Eを中心とするスパイラル相似はA,Bの中点をD,Cの中点に
        // 写す」という事実の(比と角度に分解した)言い換えになっている。
        //
        // 🌟 ProductをDefinedByパターンの前提として直接参照できるように
        // logic_core.rs::defined_by_valid_nodesにProduct用の正規化分岐と
        // 自動生成の許可を追加した(以前は共点二弦の相似がconstructionsで
        // しか使っておらず、前提として要求されたことが無かったため未対応だった)。
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

                // 🌟 高速化(Simson級を1秒未満にする目標への対応): [D1,D2,D3]と
                // [D4,D5,D6]という2組の方向トリプルは丸ごと入れ替えても同じ
                // 結論(Ang13≡Ang46、Identicalは順序を問わない)になる対称性が
                // あり、この定理はまさにこの対称な重複探索(組×組の直積)が
                // simsonでdfs_call消費量トップ(平均19,317回/試行)の主因だった。
                // order_le(D1,D4)で「入れ替えて片方だけ残す」を行い、正当な解を
                // 一切失わずに(D1==D4という方向共有ケース――角度チェイスの
                // 本来のユースケース――も証明可能なOrderNonStrictのドキュメント
                // 参照)対称な重複だけを間引く。
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
///
/// diagnose(sketch.rs)で、未解決の2問(bench_2012chnwesternmop5 / bench_2000usatstp2)の
/// 詰まり所が「中点連結の長さ」だと分かり、実際にこの定理でその手順は自力で出るように
/// なった。ただし44問では解けた問題が1問も増えず、解けた31問の仕事量が +66.1%
/// (bench_2012egmop1 +513%、nine_point_full +98%)になった。定理そのものは数回しか
/// 発火しない問題でも、増えた長さの事実に探索が引っ張られる。
///
/// 「無関係な問題への課税」を問題ごとの opt-in で逃がすのは方針に反する(新しい問題では
/// 効かない)ので、問題名のリストは持たない。既定に入れるかどうかは、課税をスケジューラ側で
/// 自動的に抑えられるようになってから決める。それまでは全問題一律のスイッチで試せるようにする。
pub fn get_length_bridge_theorems() -> Vec<TheoremDef> {
    vec![
        // ==========================================
        // 🌟 中点連結定理(長さ版)
        // ==========================================
        // 三角形ABCの3辺の中点 Mab, Mac, Mbc について、Mab–Mac の長さは BC の半分、
        // つまり B–Mbc(= Mbc–C)に等しい。上の「中点連結定理」は平行しか結論しない。
        //
        // diagnose(sketch.rs)で、長さを橋渡しする手順が2問の詰まり所として出た:
        //   bench_2012chnwesternmop5 の NK = AF(三角形HAOの中点 K, N, F)
        //   bench_2000usatstp2 の MX = YP、MY = XP(三角形PADの中点 X, Y, M)
        // どちらも3辺の中点がそろった三角形で、この形そのもの。
        //
        // 3つの中点が既に図にあることを要求する(作らない)。中点は数が少ないので
        // マッチングは安く、無関係な問題に中点を撒くこともない(中点を補う需要は
        // bench_2012egmop1 を落とすので既定では使っていない)。長さは平方のまま
        // 比べる(このエンジンの計量の語彙)。1回の発火で1辺ぶんを結論し、残りの
        // 2辺は A,B,C の取り方の違いとして別の発火が出す。
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

/// 🌟 中心角の定理: OがA,B,Cから等距離(=外接円の中心)であるとき、
/// 中心角∠BOCは円周角∠BACの2倍になる。
///
/// 有向角(mod π)は「方向2つと円周点I,Jとの複比」k=e^{2iθ}として評価
/// されている(AnglePairのeval参照)ので、θを2倍した角の値は単純にk²に
/// なる: A=(1,0),B=(cosβ,sinβ),C=(cosγ,sinγ)という単位円+中心Oの
/// 具体例で確認すると、円周角∠BAC(Aから見た向き)の値はk=e^{i(γ-β)}、
/// 中心角∠BOC(Oから見た向き、B→Cの順で対応)の値はk²=e^{2i(γ-β)}に
/// 一致する。つまり「2倍」は既存のProduct(2つのScalarの積、方冪の定理で
/// 使っているのと同じ構成要素)をAngBACに対して自分自身との積として
/// 使うだけで表現でき、新しい計算プリミティブは一切要らない。
///
/// トリガーとなる「OがA,B,Cから等距離」は、外心を2本の垂直二等分線の
/// 交点として作図した場合、「垂直二等分線の距離の等価性」が自動的に
/// 示してくれる(problems/geo_helpers.rs::circumcenterを使う限り、
/// この定理はいつでも発火可能な状態になる)。
///
/// ユーザー指摘: bench_2012egmop1(2012 EGMO P1)の本質はこの定理
/// (∠FKE=2∠FAE、KはAEFの外心)であり、これが無いと同じ中間結論に
/// 到達できない。
///
/// 🐛 get_all_theoremsに含めなかった理由(get_projective_theoremsと同じ
/// opt-in方式にした理由): この定理自体のdfs_call消費は軽量(実測で平均
/// 9~16回、cap到達0回)だが、外心を持つ問題では大抵いつでも前提
/// (OA=OB=OC)が満たされているため、定理を1つ追加しただけでUCB1
/// バンディットの試行対象が1つ増え、無関係な問題も「一度は試す」固定
/// コストを全問題が払うことになる(backlog#5で既知の構造的コスト)。
/// 実測でorthocenter/orthocenter_altがデフォルト設定(5秒・MCTS無効)で
/// 安定して失敗するようになる退行を引き起こしたため、get_all_theorems
/// への統合は見送り、必要な問題(bench_2012egmop1)側でmain.rsが明示的に
/// 追加するopt-in方式にした。
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
        // 🌟 ユーザー提案:「複比の透視射影不変性は、4点複比(A,B;C,D)→4直線の
        // 複比(PA,PB;PC,PD)→4点複比(A',B';C',D')として扱えばマッチングが
        // 楽になりそう」への対応。旧版(このコメント直下の履歴参照)は
        // O,A,B,C,D,Ap,Bp,Cp,Dpの9自由変数を同時に束縛する必要があり、
        // 天然のシードが無いためdfs_capを食い潰す問題があった(次数
        // ヒューリスティックで「壊れる」→「遅いが正しい」までは改善したが、
        // デフォルト採用に足る速さには届かなかった)。
        //
        // ここでは「点の複比」と「線束(共点な4直線)の複比」を、直線の同次
        // 係数(a,b,c)を射影平面の"点"とみなす(Definition::CrossRatioOfLines
        // 参照)ことで橋渡しし、1つの巨大な定理を2つの小さな定理に分解した:
        //   定理A: 直線L上のA,B,C,D の複比 = Oを通る4直線(LOA,LOB,LOC,LOD)の複比
        //   定理B: 共点な4直線(L1,L2,L3,L4)の複比 = 別の直線上のAp,Bp,Cp,Dpの複比
        // CrossRatioOfLines(LOA,LOB,LOC,LOD)という共通の"ハブ"を経由して
        // 合同閉包が両者を繋げることで、結局は元の定理と同じ
        // CrossRatio(A,B,C,D) ≡ CrossRatio(Ap,Bp,Cp,Dp) に到達する。
        //
        // 🌟 この分解のシードが軽い理由: 各定理の変数は「Aと同じ直線に乗って
        // いる別の点」「Aを通る(Lとは別の)直線」というConnected(_, _)の
        // 局所スキャン(その点/直線が実際に繋がっている少数の候補だけを見る)
        // だけで芋づる式に見つかる。定理Bの起点(L1..L4)は、定理Aの
        // construction(CrossRatioOfLines生成)が新しく証明するDefinedBy事実
        // そのものからシードされる(schedule_matcher_task由来の「発見済みの
        // 事実から変数を具体的に束縛する」経路)ため、こちらも全件スキャン
        // 不要。O自身は定理Bのどの変数にも登場しない(線束の複比を計算する
        // のに"誰が中心か"は不要)ので、定理Bの自由変数はl1..l4とAp..Dpの
        // 8個で済む。
        //
        // 🌟 検証結果: この分解により、既存12問題+orthocenter+orthocenter_alt
        // 全てで実行時間に有意な劣化が無いことを確認できたため(旧版は
        // nine_point/orthic_incenter/miquel_quadrilateralを実際に壊していた)、
        // main.rsでopt-in(問題名にcross_ratioを含む場合のみ)にしていたのを
        // やめ、get_all_theoremsと同様デフォルトの定理集合に含めるように
        // 変更した。
        // 🌟 ユーザー提案「対合定理」への最小構成での対応: 共点4直線L1..L4を
        // 横断線Lが切る4点A,B,C,DについてCrossRatio(A,B,C,D)=CrossRatioOfLines
        // (L1..L4)、というのがDesargues Involution Theoremの最小・最も基本的な
        // 形(退化した「2直線の対」を二次曲線とみなした場合の対合定理)。
        // これは実は下の「複比の透視射影不変性(点→線束)」定理と全く同じ主張
        // (共点4直線を横断線が切る配置)なので、新たに別定理としては複製せず
        // (同じDFSパターンを2つ持っても探索が重複するだけで得るものが無い)、
        // 下の定理名に「対合定理」の別名を追記するだけに留めた。実際に
        // 「対合」らしい使い方(同じ線束を2本の横断線で切って複比が一致する
        // ことを示す)は、この定理を2回適用+推移律で自動的に得られる
        // (test_involution.rsで実際に検証済み)。
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
                // Aから局所スキャンでLを見つけ、B,C,Dも同じL上にあるか確認する。
                //
                // 🐛 実測に基づくFIX: A,B,C,DはすべてLの(少数とはいえ複数の)
                // 既知の点から同じ候補プールを引くため、distinctを最後に
                // 1回だけ置くと(Pattern::Distinctはコスト計算上「全変数が
                // 束縛されるまではINFINITY」なので)A,B,C,Dが全部揃うまで
                // 一切の枝刈りが効かず、A=Bのような明らかに無駄な組み合わせを
                // 何十通りも掘り下げてから初めて弾かれる、という組み合わせ
                // 爆発を実際に観測した(次数ヒューリスティックとは別種の問題)。
                // 各点が新しく束縛された直後にdistinctを挟むことで、
                // (Distinctは「必要な変数が全て束縛済みならコスト0」という
                // 既存の見積もりに従い)estimate_costが最短経路でそれを選び、
                // 無駄な組み合わせを即座に打ち切れるようにする。
                on("A", "L"),
                on("B", "L"),
                // 🐛 実験的変更(要検証): distinct(&["A","B"]) 等だったのを
                // order(&["A","B"]) 等に変更した。同じ直線L上のN点から
                // A,B,C,Dを選ぶ際、distinctだけだと同じ4点集合のN!通りの
                // 並べ替えを全て試してしまう(実測でsimsonのdfs_call消費量
                // トップの主因だった)。order()は代表元ID昇順という1つの
                // 正準形だけを通すため無駄な並べ替えを削れるが、複比は
                // 完全対称ではなくクライン4群の下でしか値が保存されない
                // (順列によって1-x, 1/x等の異なる値になる)ため、この定理の
                // 結論(CR1≡CRL、同じ割り当てに対する内部無矛盾性)は常に
                // 真だが、外部の目標複比と数値一致させる必要がある問題
                // (test_cross_ratio/test_involution)では「必要な特定の値」を
                // 正準順序が排除してしまい壊れるリスクがある。
                //
                // 🌟 実測結果(このリスクは本物だった、ただし直すのは簡単では
                // ない)。4点の複比は完全対称ではなく、値を保つのはクライン4群
                // V4(4通り)だけなので 24/4 = 6通りの異なる値がある。昇順1通りに
                // 固定すると、そのうち1つしか作られない。
                //
                //   - order を「Aが4点の最小」だけに緩める(= 3! = 6通り、V4の
                //     各剰余類をちょうど1回ずつ通る最小の完全集合)と、重心の
                //     存在定理 centroid でこの定理が0回→27回発火するように
                //     なった。「平行は出るのに比へ渡れない」という行き詰まりは
                //     定理不足ではなくマッチングの問題だった、という
                //     ユーザー指摘の裏付け。
                //   - ただしベンチマークは悪化する: 37問で30→29
                //     (bench_2018chnwesternmop5を落とす)、全体で約4倍遅い。
                //     マッチングの分岐を6倍にする代償が大きすぎる。
                //     しかも centroid 自体は27回発火しても証明には至らない。
                //   - 「マッチは昇順1通りのまま constructions で6通り作る」
                //     という安い案も試したが、これでは駄目だった。昇順の
                //     ままだとこの定理は centroid で**そもそも1回もマッチ
                //     しない**(必要な割り当てに探索が到達しない)ため、
                //     構成を増やしても実行されない。つまり問題は「作る値の
                //     数」ではなく「探索がその割り当てに辿り着けるか」の方に
                //     ある――order の緩め方でマッチ自体の可否が変わるのは、
                //     Pattern::Order が全変数の束縛まで INFINITY を返す
                //     (estimate_cost参照)ため枝刈りの掛かる時点がずれ、
                //     dfs_cap 内で到達できる割り当てが変わるから。
                //
                // 次に手を入れるならここ(パターンの評価順と cap の側)で、
                // 定理を増やす話ではない。
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
                // 🐛 実測に基づくFIX: 当初は「OがL上にある退化を弾く」安全策
                // として not(Connected(O, L)) を末尾に置いていたが、Oがまだ
                // どこにも束縛されていない時点でこのnotが評価されると、
                // 「Oという特定の点がL上にあるか」ではなく「Lに繋がる点が
                // 何かしら存在するか」という無関係な問いになってしまい
                // (L上には元々A,B,C,D自身が乗っているので必ず真になる)、
                // 常にnotが失敗して全探索を潰していた。Oは他のConnected
                // パターン(Connected(O,LOA)等)で既に一意に発見されている
                // ので、この安全策自体は無くても健全性は変わらない
                // (退化したO=L上の点という束縛は、その後のConnected(O,LOA)
                // 等がL自身をLOAとして誤って選ばない限り実害が無く、万一
                // 選んだ場合もdistinct(LOA..LOD)やCrossRatioOfLinesの
                // 次数ゲートが弾く)ため、単純に削除した。
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
        // 円周角の定理(2定点から見た2定点への直線のなす角が一致)の、一般の
        // 二次曲線への拡張。円は「角度」で比較できたが、一般の二次曲線には
        // 角度に相当する不変量が無いため、複比(CrossRatioOfLines)で比較する:
        // 二次曲線上の2点P,Qから見た、同じ二次曲線上の他の4点への直線束は
        // 常に同じ複比を持つ。
        //
        // 🌟 マッチングを軽くする設計(ユーザー要望「マッチングしやすい
        // オブジェクトが少ないものを採用する」への対応):
        // 二次曲線上で自由に6点を全件スキャンで探す(6重ループ)のは
        // 明らかに高コストなので、代わりに二次曲線自身の定義(生成元5点
        // P1..P5)を「複比の透視射影不変性(線束→点)」と同じ要領で
        // DefinedByシードから直接束縛し(全件スキャン不要)、実際に新規
        // スキャンが必要なのは「二次曲線上のもう1点Q」(Connected(Q,Conic)の
        // 1変数だけ)に抑えている。したがって視点は生成元のうちP1,P5の2点、
        // 見る先はP2,P3,P4とQの4点に固定した特殊ケースだが、これは
        // シュタイナーの定理の本質(2視点からの直線束の複比が一致する)を
        // 正しく捉えた非自明な具体例であり、視点を他の2点に取り直したい
        // 場合は問題側でその2点を生成元に含めて二次曲線を作り直せばよい。
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
        // ユーザー提案「射影幾何への移植を進めたい(円周角は移植後の定理も
        // あるはず)」への対応。既存の"接弦定理"(theorems.rs先頭側、円+
        // AnglePairによるEuclid版)の射影一般化で、上の「シュタイナーの定理」
        // (二次曲線上の6点の複比不変性)からもう1点Qを消した極限
        // (Q→P1、すなわち"P1から見た弦P1Q"が"P1における接線"に退化する
        // 極限)にあたる。接弦定理(接線と弦のなす角=同じ弧に対する円周角)は
        // まさにこの極限そのもの: 円周角の定理が「2定点から見た2定点への
        // 角が一致」なら、接弦定理は「その2定点のうち片方が接点そのものに
        // 退化した」特別な場合であり、シュタイナーの定理とその接線版の
        // 関係も同じ極限操作で対応する。
        //
        // 二次曲線の生成元5点P1..P5だけで完結し(シュタイナーの定理が
        // 必要としていた「二次曲線上のもう1点Qを局所スキャンで探す」手順が
        // 丸ごと不要になる)、その分マッチングも軽い: P1における接線T1と、
        // P1から見たP2,P3,P4への3直線の複比(視点P1)が、P5から見た
        // P2,P3,P4,P1への4直線の複比(視点P5、P1は"ただの弦"として扱う)と
        // 一致する。
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
        // 「円周角の定理の逆」(2定点から見た2定点への角が等しいなら4点は
        // 共円)の一般二次曲線版。P1,P5から見た同じ4点(P2,P3,P4,Q)への
        // 直線束の複比が等しいなら、6点は共通の二次曲線に乗る。
        //
        // シュタイナーの定理と全く逆向きの構造(CR_P1,CR_P5の複比一致が前提、
        // 二次曲線の構築とQの接続が結論)だが、シードの取り方が異なる:
        // 二次曲線はまだ存在しない(むしろこれから作る)ので、CrossRatioOfLines
        // の側から4直線を直接束縛する(「円周角の定理の逆」がAnglePairの
        // 定義から2方向を直接束縛するのと同じ発想)。CrossRatioOfLinesの
        // V4クライン群展開はAnglePairのフリップ機構と違って共有状態(グループ)
        // を持たないので(各パターンが独立に4通りを試す)、"共点二弦の相似"で
        // 見つかった「共有flip_groupが噛み合わない」種類の不整合は起こらない。
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
                // 🌟 シード: Identical(CR_P1,CR_P5)から始めて、それぞれの定義
                // から4直線を直接束縛する(全件スキャン不要)。
                // 🌟 sub_type="CrossRatioOfLines"マーカー(logic_core.rs::
                // match_identical_factの(None,None)自己束縛分岐が消費する)を
                // 付与: CR_P1/CR_P5は次のDefinedByパターンでCrossRatioOfLines
                // としてしか使われないので、自己束縛の候補を最初から
                // CrossRatioOfLines由来のScalarだけに絞ってよい(長さ・積・
                // 点の複比まで無差別に含む自己束縛プールに埋もれて無関係な
                // 値ばかり試す性能問題への対処、miquel_quadrilateralで観測)。
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

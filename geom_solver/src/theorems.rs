use crate::mmp_core::EntityType;
use crate::logic_core::{
    ConstructTemplate, FactPatternDef, FactTemplate, Pattern, TheoremDef,
};
use rustc_hash::FxHashMap;

// --- 構文糖衣 (ヘルパー関数) ---
fn entities(list: &[(&str, EntityType)]) -> FxHashMap<String, EntityType> {
    list.iter().map(|(k, v)| (k.to_string(), *v)).collect()
}

fn fact(f_type: &str, args: &[&str]) -> Pattern {
    Pattern::Fact(FactPatternDef {
        fact_type: f_type.to_string(),
        args: args.iter().map(|s| s.to_string()).collect(),
        target_type: None, sub_type: None, allow_flip: false, flip_group: None,
    })
}

/// target_type/sub_typeは大半のfact_typeでは(記録目的だけの)未使用フィールド
/// だが、fact_type=="Connected"に限っては logic_core.rs::match_connected_fact が
/// 実際に読む: target_type=="Direction"ならparent側(args[1])、
/// sub_type=="Direction"ならchild側(args[0])を「L∞上の点(=方向)」に限定して
/// 列挙し、それ以外(既定)は逆に「L∞上に無い有限点」に限定する
/// (EntityType::Direction撤廃により、方向はもう独立した型ではなくL∞への
/// incidenceで判定するしかないため。以前は"Line"上の点を探すfact_ext呼び出しが
/// 別に"Direction"上の点を探すfact_ext呼び出しと型で自然に区別されていたが、
/// 今は両方ともEntityType::Pointなので、このマーカーで明示的に伝える必要がある)。
fn fact_ext(f_type: &str, args: &[&str], t_type: Option<&str>, s_type: Option<&str>, flip: bool, group: Option<&str>) -> Pattern {
    Pattern::Fact(FactPatternDef {
        fact_type: f_type.to_string(),
        args: args.iter().map(|s| s.to_string()).collect(),
        target_type: t_type.map(|s| s.to_string()),
        sub_type: s_type.map(|s| s.to_string()),
        allow_flip: flip,
        flip_group: group.map(|s| s.to_string()),
    })
}

fn distinct(args: &[&str]) -> Pattern {
    Pattern::Distinct(args.iter().map(|s| s.to_string()).collect())
}

// 🌟 厳密な順序("<")。distinct()と違い「代表元IDの昇順」という1つの
// 正準形しか通さないため、複数の変数が同じ候補プール(例: 同じ直線上の点)
// から選ばれる場合に、同じ集合の異なる並べ替え(4点ならN!通り)を
// distinct()のように全て試すのではなく1通りに絞れる。使えるのは
// 「変数の割り当て順序が結論の成立可否に影響しない」場合のみ
// (順序に意味がある定理では使ってはいけない)。
fn order(args: &[&str]) -> Pattern {
    Pattern::Order(args.iter().map(|s| s.to_string()).collect())
}

// 🌟 Pattern::OrderNonStrictのドキュメント参照(logic_core.rs)。「2つの役割
// (方向トリプルの組など)を丸ごと入れ替えても同じ結論になる」定理の
// 対称的な重複探索を、正当な解を一切失わずに約半分に間引くためのヘルパー。
fn order_le(args: &[&str]) -> Pattern {
    Pattern::OrderNonStrict(args.iter().map(|s| s.to_string()).collect())
}

fn not(pat: Pattern) -> Pattern {
    Pattern::Not(Box::new(pat))
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
                ("Circ", EntityType::Circle),
                ("L_A1_B1", EntityType::Line), ("L_A1_B2", EntityType::Line),
                ("L_A2_B1", EntityType::Line), ("L_A2_B2", EntityType::Line),
                ("Dir_A1_B1", EntityType::Point), ("Dir_A1_B2", EntityType::Point),
                ("Dir_A2_B1", EntityType::Point), ("Dir_A2_B2", EntityType::Point),
                ("Ang1", EntityType::Angle), ("Ang2", EntityType::Angle),
            ]),
            patterns: vec![
                // 🌟 Concyclicという専用Factをやめ、「4点が同じ円Circに乗っている」を
                // Connectedの4連続で表す。link_logical_incidenceによる構造的な接続
                // だけで十分になり、専用Factの登録忘れバグが起きなくなる。
                fact_ext("Connected", &["Apex1", "Circ"], None, None, false, None),
                fact_ext("Connected", &["Apex2", "Circ"], None, None, false, None),
                fact_ext("Connected", &["Base1", "Circ"], None, None, false, None),
                fact_ext("Connected", &["Base2", "Circ"], None, None, false, None),
                distinct(&["Apex1", "Apex2", "Base1", "Base2"]),
                
                // 🌟 FIX: Connected から DefinedBy に変更し、作図需要(Demand)を発生させる
                fact_ext("DefinedBy", &["Apex1", "Base1", "L_A1_B1"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["Apex1", "Base2", "L_A1_B2"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                distinct(&["L_A1_B1", "L_A1_B2"]),
                
                fact_ext("DefinedBy", &["Apex2", "Base1", "L_A2_B1"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["Apex2", "Base2", "L_A2_B2"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                distinct(&["L_A2_B1", "L_A2_B2"]),
                
                fact_ext("Connected", &["Apex2", "L_A2_B1"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["Base1", "L_A2_B1"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["Apex2", "L_A2_B2"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["Base2", "L_A2_B2"], Some("Line"), Some("Point"), false, None),
                distinct(&["L_A2_B1", "L_A2_B2"]),
                
                fact_ext("DefinedBy", &["L_A1_B1", "Dir_A1_B1"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["L_A1_B2", "Dir_A1_B2"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["L_A2_B1", "Dir_A2_B1"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["L_A2_B2", "Dir_A2_B2"], Some("DirectionOf"), None, false, None),
                
                fact_ext("DefinedBy", &["Dir_A1_B1", "Dir_A1_B2", "Ang1"], Some("AnglePair"), None, true, Some("Cyclic")),
                fact_ext("DefinedBy", &["Dir_A2_B1", "Dir_A2_B2", "Ang2"], Some("AnglePair"), None, true, Some("Cyclic")),
                distinct(&["Ang1", "Ang2"]),
            ],
            constructions: vec![],
            conclusions: vec![FactTemplate { fact_type: "Identical".to_string(), args: vec!["Ang1".to_string(), "Ang2".to_string()], target_type: Some("Angle".to_string()), sub_type: None }],
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
                fact_ext("DefinedBy", &["B", "C", "Mid_BC"], Some("Midpoint"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["B", "C", "LineBC"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["LineBC", "Mid_BC", "PerpMid"], Some("PerpendicularLine"), None, false, None),
                fact_ext("Connected", &["P", "PerpMid"], None, None, false, None),
                distinct(&["B", "C", "P"]),
            ],
            constructions: vec![
                ConstructTemplate { def_type: "LengthSq".to_string(), args: vec!["P".to_string(), "B".to_string()], target_type: "Scalar".to_string(), bind_to: "Dist_PB".to_string() },
                ConstructTemplate { def_type: "LengthSq".to_string(), args: vec!["P".to_string(), "C".to_string()], target_type: "Scalar".to_string(), bind_to: "Dist_PC".to_string() },
            ],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["Dist_PB".to_string(), "Dist_PC".to_string()], target_type: Some("Scalar".to_string()), sub_type: None }
            ],
        },

        // ==========================================
        // 🌟 垂直二等分線の距離の等価性の逆
        // ==========================================
        // B,Cから等距離にある点Pは、線分BCの垂直二等分線上にある(Connected)。
        TheoremDef {
            name: "垂直二等分線の距離の等価性の逆".to_string(),
            entities: entities(&[
                ("B", EntityType::Point), ("C", EntityType::Point), ("Mid_BC", EntityType::Point),
                ("LineBC", EntityType::Line), ("PerpMid", EntityType::Line), ("P", EntityType::Point),
                ("Dist_PB", EntityType::Scalar), ("Dist_PC", EntityType::Scalar),
            ]),
            patterns: vec![
                fact_ext("DefinedBy", &["B", "C", "Mid_BC"], Some("Midpoint"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["B", "C", "LineBC"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["LineBC", "Mid_BC", "PerpMid"], Some("PerpendicularLine"), None, false, None),
                fact_ext("DefinedBy", &["P", "B", "Dist_PB"], Some("LengthSq"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["P", "C", "Dist_PC"], Some("LengthSq"), Some("Unordered"), false, None),
                fact_ext("Identical", &["Dist_PB", "Dist_PC"], Some("Scalar"), None, false, None),
                distinct(&["B", "C", "P"]),
            ],
            constructions: vec![],
            conclusions: vec![
                FactTemplate { fact_type: "Connected".to_string(), args: vec!["P".to_string(), "PerpMid".to_string()], target_type: Some("Line".to_string()), sub_type: None }
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
                fact_ext("DefinedBy", &["A", "B", "M1"], Some("Midpoint"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["A", "C", "M2"], Some("Midpoint"), Some("Unordered"), false, None),
                distinct(&["A", "B", "C", "M1", "M2"]),
                
                fact_ext("DefinedBy", &["B", "C", "LineBC"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["M1", "M2", "LineM1M2"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["LineBC", "DirBC"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["LineM1M2", "DirM1M2"], Some("DirectionOf"), None, false, None),
            ],
            constructions: vec![],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["DirBC".to_string(), "DirM1M2".to_string()], target_type: Some("Point".to_string()), sub_type: None }
            ],
        },

        TheoremDef {
            name: "二等辺三角形の底角".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point),
                ("Dist_AB", EntityType::Scalar), ("Dist_AC", EntityType::Scalar),
                ("LineAB", EntityType::Line), ("LineAC", EntityType::Line), ("LineBC", EntityType::Line),
                ("DirAB", EntityType::Point), ("DirAC", EntityType::Point), ("DirBC", EntityType::Point),
                ("Ang_B", EntityType::Angle), ("Ang_C", EntityType::Angle),
            ]),
            patterns: vec![
                fact_ext("Identical", &["Dist_AB", "Dist_AC"], None, None, false, None),
                fact_ext("DefinedBy", &["A", "B", "Dist_AB"], Some("LengthSq"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["A", "C", "Dist_AC"], Some("LengthSq"), Some("Unordered"), false, None),
                distinct(&["A", "B", "C"]),
                
                fact_ext("DefinedBy", &["A", "B", "LineAB"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["A", "C", "LineAC"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["B", "C", "LineBC"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                
                fact_ext("DefinedBy", &["LineAB", "DirAB"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["LineAC", "DirAC"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["LineBC", "DirBC"], Some("DirectionOf"), None, false, None),
                distinct(&["DirAB", "DirAC", "DirBC"]),
                
                // 🌟 フリップ同期グループ "Isosceles" を適用
                fact_ext("DefinedBy", &["DirAB", "DirBC", "Ang_B"], Some("AnglePair"), None, true, Some("Isosceles")),
                fact_ext("DefinedBy", &["DirBC", "DirAC", "Ang_C"], Some("AnglePair"), None, true, Some("Isosceles")),
            ],
            constructions: vec![],
            conclusions: vec![
                FactTemplate {
                    fact_type: "Identical".to_string(),
                    args: vec!["Ang_B".to_string(), "Ang_C".to_string()],
                    target_type: Some("Angle".to_string()),
                    sub_type: None,
                }
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
                ("Ang_B", EntityType::Angle), ("Ang_C", EntityType::Angle),
            ]),
            patterns: vec![
                // 🌟 シード: Identical(Ang_B,Ang_C)(底角が等しいという前提)から
                // 始めて、それぞれの定義からDirAB,DirBC,DirACを直接束縛する
                // (全件スキャン不要。「二等辺三角形の底角」の逆順)。
                fact_ext("Identical", &["Ang_B", "Ang_C"], Some("Angle"), None, false, None),
                fact_ext("DefinedBy", &["DirAB", "DirBC", "Ang_B"], Some("AnglePair"), None, true, Some("IsoscelesConv")),
                fact_ext("DefinedBy", &["DirBC", "DirAC", "Ang_C"], Some("AnglePair"), None, true, Some("IsoscelesConv")),
                distinct(&["DirAB", "DirAC", "DirBC"]),

                fact_ext("Connected", &["LineAB", "DirAB"], Some("Direction"), Some("Line"), false, None),
                fact_ext("Connected", &["LineBC", "DirBC"], Some("Direction"), Some("Line"), false, None),
                fact_ext("Connected", &["LineAC", "DirAC"], Some("Direction"), Some("Line"), false, None),
                distinct(&["LineAB", "LineBC", "LineAC"]),

                // A = LineAB ∩ LineAC, B = LineAB ∩ LineBC, C = LineBC ∩ LineAC
                fact_ext("Connected", &["A", "LineAB"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["A", "LineAC"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["B", "LineAB"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["B", "LineBC"], Some("Line"), Some("Point"), false, None),
                distinct(&["A", "B"]),
                fact_ext("Connected", &["C", "LineBC"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["C", "LineAC"], Some("Line"), Some("Point"), false, None),
                distinct(&["A", "B", "C"]),
            ],
            constructions: vec![
                ConstructTemplate { def_type: "LengthSq".to_string(), args: vec!["A".to_string(), "B".to_string()], target_type: "Scalar".to_string(), bind_to: "Dist_AB".to_string() },
                ConstructTemplate { def_type: "LengthSq".to_string(), args: vec!["A".to_string(), "C".to_string()], target_type: "Scalar".to_string(), bind_to: "Dist_AC".to_string() },
            ],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["Dist_AB".to_string(), "Dist_AC".to_string()], target_type: Some("Scalar".to_string()), sub_type: None }
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
                ("AngA", EntityType::Angle), ("AngC", EntityType::Angle),
                ("LenPA", EntityType::Scalar), ("LenPB", EntityType::Scalar), ("LenPC", EntityType::Scalar), ("LenPD", EntityType::Scalar),
                ("ProdAB", EntityType::Scalar), ("ProdCD", EntityType::Scalar),
            ]),
            patterns: vec![
                // 🌟 シード: Identical(AngA,AngC)から始めて、それぞれの定義から
                // 4方向を直接束縛する(全件スキャン不要)。
                //
                // 🐛 実測に基づくFIX: 当初はAngA・AngCの2つのAnglePair抽出に
                // 共通のflip_group("ProdSim")を与えていたが、これは
                // 「二等辺三角形の底角」のように"同じ定理が今まさに新規作成する
                // 2つの角"を反射対称の一貫した向きで結びたい場合の道具立てで
                // あり、AngA・AngCは(別の定理=円周角の定理が、それ自身の
                // 独立したflip_group「Cyclic」で向きを決めて)既に作成済みの
                // 角を後から読み取るだけなので、両者の向きの選び方に一貫性が
                // 保証されている前提が成り立たない。共通グループにすると、
                // AngA側で選ばれた向きがAngC側の選択を強制してしまい、AngCの
                // 実際の格納形と噛み合わない(=常に不整合になる)組み合わせしか
                // 試せなくなっていた。flip_groupをNone(=各自が独立に両方の
                // 向きを試す)にすることで、2つの角が別々の定理由来でも
                // 正しく噛み合う組み合わせを見つけられるようにした。
                fact_ext("Identical", &["AngA", "AngC"], Some("Angle"), None, false, None),
                fact_ext("DefinedBy", &["DirAB", "DirAD", "AngA"], Some("AnglePair"), None, true, None),
                fact_ext("DefinedBy", &["DirCD", "DirCB", "AngC"], Some("AnglePair"), None, true, None),
                distinct(&["DirAB", "DirAD"]),
                distinct(&["DirCD", "DirCB"]),

                // 🐛 実測に基づくFIX(セッション既知の教訓の再適用): distinctを
                // 4直線が全部揃うまで1回だけにまとめず、束縛されるたびに
                // 挟むことで、間違った(=有向角のフリップや無関係な複比クラスに
                // 由来する)直線の組み合わせを早期に打ち切る(「複比の透視射影
                // 不変性」定理群のバグ修正と全く同じ理由)。
                fact_ext("Connected", &["LineAB", "DirAB"], Some("Direction"), Some("Line"), false, None),
                fact_ext("Connected", &["LineAD", "DirAD"], Some("Direction"), Some("Line"), false, None),
                distinct(&["LineAB", "LineAD"]),
                fact_ext("Connected", &["LineCD", "DirCD"], Some("Direction"), Some("Line"), false, None),
                distinct(&["LineAB", "LineAD", "LineCD"]),
                fact_ext("Connected", &["LineCB", "DirCB"], Some("Direction"), Some("Line"), false, None),
                distinct(&["LineAB", "LineAD", "LineCD", "LineCB"]),

                // A = LineAB ∩ LineAD (∠Aの頂点)
                fact_ext("Connected", &["A", "LineAB"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["A", "LineAD"], Some("Line"), Some("Point"), false, None),
                // C = LineCD ∩ LineCB (∠Cの頂点)
                fact_ext("Connected", &["C", "LineCD"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["C", "LineCB"], Some("Line"), Some("Point"), false, None),
                distinct(&["A", "C"]),
                // P = LineAB ∩ LineCD (2弦の交点)。A,Cが確定した直後に見つけて
                // すぐdistinctで弾くことで、「PがAやCに化けた」まま後段の
                // B,D探索まで持ち越してしまう無駄を防ぐ。
                fact_ext("Connected", &["P", "LineAB"], Some("Line"), Some("Point"), false, None),
                distinct(&["A", "C", "P"]),
                fact_ext("Connected", &["P", "LineCD"], Some("Line"), Some("Point"), false, None),
                distinct(&["A", "C", "P"]),
                // B = LineAB ∩ LineCB (弦ABのもう一端。LineCBの上にもある点として一意に特定)
                fact_ext("Connected", &["B", "LineAB"], Some("Line"), Some("Point"), false, None),
                distinct(&["A", "P", "B"]),
                fact_ext("Connected", &["B", "LineCB"], Some("Line"), Some("Point"), false, None),
                distinct(&["A", "P", "B"]),
                // D = LineCD ∩ LineAD (弦CDのもう一端)
                fact_ext("Connected", &["D", "LineCD"], Some("Line"), Some("Point"), false, None),
                distinct(&["C", "P", "D"]),
                fact_ext("Connected", &["D", "LineAD"], Some("Line"), Some("Point"), false, None),
                distinct(&["A", "B", "C", "D"]),
            ],
            constructions: vec![
                ConstructTemplate { def_type: "LengthSq".to_string(), args: vec!["P".to_string(), "A".to_string()], target_type: "Scalar".to_string(), bind_to: "LenPA".to_string() },
                ConstructTemplate { def_type: "LengthSq".to_string(), args: vec!["P".to_string(), "B".to_string()], target_type: "Scalar".to_string(), bind_to: "LenPB".to_string() },
                ConstructTemplate { def_type: "LengthSq".to_string(), args: vec!["P".to_string(), "C".to_string()], target_type: "Scalar".to_string(), bind_to: "LenPC".to_string() },
                ConstructTemplate { def_type: "LengthSq".to_string(), args: vec!["P".to_string(), "D".to_string()], target_type: "Scalar".to_string(), bind_to: "LenPD".to_string() },
                ConstructTemplate { def_type: "Product".to_string(), args: vec!["LenPA".to_string(), "LenPB".to_string()], target_type: "Scalar".to_string(), bind_to: "ProdAB".to_string() },
                ConstructTemplate { def_type: "Product".to_string(), args: vec!["LenPC".to_string(), "LenPD".to_string()], target_type: "Scalar".to_string(), bind_to: "ProdCD".to_string() },
            ],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["ProdAB".to_string(), "ProdCD".to_string()], target_type: Some("Scalar".to_string()), sub_type: None }
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
                ("AngE_AB", EntityType::Angle), ("AngE_DC", EntityType::Angle), ("AngE_AM", EntityType::Angle), ("AngE_DN", EntityType::Angle),
                ("LenSqEA", EntityType::Scalar), ("LenSqEB", EntityType::Scalar), ("LenSqEC", EntityType::Scalar), ("LenSqED", EntityType::Scalar),
                ("LenSqEM", EntityType::Scalar), ("LenSqEN", EntityType::Scalar),
                ("ProdEAEC", EntityType::Scalar), ("ProdEBED", EntityType::Scalar),
                ("ProdEAEN", EntityType::Scalar), ("ProdEMED", EntityType::Scalar),
            ]),
            patterns: vec![
                // シード: 角度の一致(∠AEB=∠DEC)から4方向を束縛する
                // (共点二弦の相似と同じ理由でflip_groupはNone: AngE_AB,AngE_DCは
                // 別々の定理(円周角の定理など)が独自の向きで作成済みの角を
                // 後から読み取るだけなので、共通flip_groupを使うと正しい
                // 組み合わせが噛み合わなくなる)。
                fact_ext("Identical", &["AngE_AB", "AngE_DC"], Some("Angle"), None, false, None),
                fact_ext("DefinedBy", &["DirEA", "DirEB", "AngE_AB"], Some("AnglePair"), None, true, None),
                fact_ext("DefinedBy", &["DirED", "DirEC", "AngE_DC"], Some("AnglePair"), None, true, None),
                distinct(&["DirEA", "DirEB"]),
                distinct(&["DirED", "DirEC"]),

                fact_ext("Connected", &["LineEA", "DirEA"], Some("Direction"), Some("Line"), false, None),
                fact_ext("Connected", &["LineEB", "DirEB"], Some("Direction"), Some("Line"), false, None),
                distinct(&["LineEA", "LineEB"]),
                fact_ext("Connected", &["LineED", "DirED"], Some("Direction"), Some("Line"), false, None),
                distinct(&["LineEA", "LineEB", "LineED"]),
                fact_ext("Connected", &["LineEC", "DirEC"], Some("Direction"), Some("Line"), false, None),
                distinct(&["LineEA", "LineEB", "LineED", "LineEC"]),

                // E = LineEA ∩ LineEB (∠AEBの頂点)であり、かつLineED,LineEC
                // 両方の上にもある(=△EDCの頂点も同じE、というスパイラル
                // 相似の前提そのもの)。
                fact_ext("Connected", &["E", "LineEA"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["E", "LineEB"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["E", "LineED"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["E", "LineEC"], Some("Line"), Some("Point"), false, None),

                // A,B,D,C = それぞれの直線上のEでない方の点
                fact_ext("Connected", &["A", "LineEA"], Some("Line"), Some("Point"), false, None),
                distinct(&["E", "A"]),
                fact_ext("Connected", &["B", "LineEB"], Some("Line"), Some("Point"), false, None),
                distinct(&["E", "A", "B"]),
                fact_ext("Connected", &["D", "LineED"], Some("Line"), Some("Point"), false, None),
                distinct(&["E", "A", "B", "D"]),
                fact_ext("Connected", &["C", "LineEC"], Some("Line"), Some("Point"), false, None),
                distinct(&["E", "A", "B", "D", "C"]),

                // 前提2: 比の一致 EA・EC=EB・ED (共点二弦の相似と同じ形)。
                // E,A,B,D,Cはここまでで既に確定しているので、これは新規探索
                // ではなく「本当にこの比が成り立っているか」の確認になる。
                fact_ext("DefinedBy", &["E", "A", "LenSqEA"], Some("LengthSq"), None, true, None),
                fact_ext("DefinedBy", &["E", "C", "LenSqEC"], Some("LengthSq"), None, true, None),
                fact_ext("DefinedBy", &["LenSqEA", "LenSqEC", "ProdEAEC"], Some("Product"), None, true, None),
                fact_ext("DefinedBy", &["E", "B", "LenSqEB"], Some("LengthSq"), None, true, None),
                fact_ext("DefinedBy", &["E", "D", "LenSqED"], Some("LengthSq"), None, true, None),
                fact_ext("DefinedBy", &["LenSqEB", "LenSqED", "ProdEBED"], Some("Product"), None, true, None),
                fact_ext("Identical", &["ProdEAEC", "ProdEBED"], Some("Scalar"), None, false, None),
            ],
            constructions: vec![
                ConstructTemplate { def_type: "Midpoint".to_string(), args: vec!["A".to_string(), "B".to_string()], target_type: "Point".to_string(), bind_to: "M".to_string() },
                ConstructTemplate { def_type: "Midpoint".to_string(), args: vec!["D".to_string(), "C".to_string()], target_type: "Point".to_string(), bind_to: "N".to_string() },
                ConstructTemplate { def_type: "LineThroughPoints".to_string(), args: vec!["E".to_string(), "M".to_string()], target_type: "Line".to_string(), bind_to: "LineEM".to_string() },
                ConstructTemplate { def_type: "LineThroughPoints".to_string(), args: vec!["E".to_string(), "N".to_string()], target_type: "Line".to_string(), bind_to: "LineEN".to_string() },
                ConstructTemplate { def_type: "DirectionOf".to_string(), args: vec!["LineEM".to_string()], target_type: "Point".to_string(), bind_to: "DirEM".to_string() },
                ConstructTemplate { def_type: "DirectionOf".to_string(), args: vec!["LineEN".to_string()], target_type: "Point".to_string(), bind_to: "DirEN".to_string() },
                ConstructTemplate { def_type: "AnglePair".to_string(), args: vec!["DirEA".to_string(), "DirEM".to_string()], target_type: "Angle".to_string(), bind_to: "AngE_AM".to_string() },
                ConstructTemplate { def_type: "AnglePair".to_string(), args: vec!["DirED".to_string(), "DirEN".to_string()], target_type: "Angle".to_string(), bind_to: "AngE_DN".to_string() },
                ConstructTemplate { def_type: "LengthSq".to_string(), args: vec!["E".to_string(), "M".to_string()], target_type: "Scalar".to_string(), bind_to: "LenSqEM".to_string() },
                ConstructTemplate { def_type: "LengthSq".to_string(), args: vec!["E".to_string(), "N".to_string()], target_type: "Scalar".to_string(), bind_to: "LenSqEN".to_string() },
                ConstructTemplate { def_type: "Product".to_string(), args: vec!["LenSqEA".to_string(), "LenSqEN".to_string()], target_type: "Scalar".to_string(), bind_to: "ProdEAEN".to_string() },
                ConstructTemplate { def_type: "Product".to_string(), args: vec!["LenSqEM".to_string(), "LenSqED".to_string()], target_type: "Scalar".to_string(), bind_to: "ProdEMED".to_string() },
            ],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["AngE_AM".to_string(), "AngE_DN".to_string()], target_type: Some("Angle".to_string()), sub_type: None },
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["ProdEAEN".to_string(), "ProdEMED".to_string()], target_type: Some("Scalar".to_string()), sub_type: None },
            ],
        },

        TheoremDef {
            name: "接弦定理".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point),
                ("Circ", EntityType::Circle), ("TanA", EntityType::Line),
                ("LineAB", EntityType::Line), ("LineAC", EntityType::Line), ("LineBC", EntityType::Line),
                ("DirTan", EntityType::Point), ("DirAB", EntityType::Point), ("DirAC", EntityType::Point), ("DirBC", EntityType::Point),
                ("AngTan", EntityType::Angle), ("AngBCA", EntityType::Angle),
            ]),
            patterns: vec![
                fact_ext("DefinedBy", &["A", "B", "C", "Circ"], Some("Circumcircle"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["Circ", "A", "TanA"], Some("TangentLine"), None, false, None),
                distinct(&["A", "B", "C"]),
                
                fact_ext("DefinedBy", &["A", "B", "LineAB"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["A", "C", "LineAC"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["B", "C", "LineBC"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                
                fact_ext("DefinedBy", &["TanA", "DirTan"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["LineAB", "DirAB"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["LineAC", "DirAC"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["LineBC", "DirBC"], Some("DirectionOf"), None, false, None),
                
                // 接線とABのなす角 ≡ 弧ABに対する円周角(C)
                fact_ext("DefinedBy", &["DirTan", "DirAB", "AngTan"], Some("AnglePair"), None, true, Some("TanGrp")),
                fact_ext("DefinedBy", &["DirAC", "DirBC", "AngBCA"], Some("AnglePair"), None, true, Some("TanGrp")),
            ],
            constructions: vec![],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["AngTan".to_string(), "AngBCA".to_string()], target_type: Some("Angle".to_string()), sub_type: None }
            ],
        },// ==========================================
        // 円周角の定理の逆[cite: 6]
        // ==========================================
        TheoremDef {
            name: "円周角の定理の逆".to_string(),
            entities: entities(&[
                ("Ang1", EntityType::Angle), ("Ang2", EntityType::Angle),
                ("Dir_L1", EntityType::Point), ("Dir_L2", EntityType::Point),
                ("Dir_L3", EntityType::Point), ("Dir_L4", EntityType::Point),
                ("L1", EntityType::Line), ("L2", EntityType::Line), ("L3", EntityType::Line), ("L4", EntityType::Line),
                ("P_Apex1", EntityType::Point), ("P_Apex2", EntityType::Point),
                ("P_Base1", EntityType::Point), ("P_Base2", EntityType::Point),
                ("Circ_New", EntityType::Circle),
            ]),
            patterns: vec![
                fact_ext("Identical", &["Ang1", "Ang2"], Some("Angle"), None, false, None),
                fact_ext("DefinedBy", &["Dir_L1", "Dir_L2", "Ang1"], Some("AnglePair"), None, true, Some("ConvCyc")),
                fact_ext("DefinedBy", &["Dir_L3", "Dir_L4", "Ang2"], Some("AnglePair"), None, true, Some("ConvCyc")),
                
                fact_ext("Connected", &["L1", "Dir_L1"], Some("Direction"), Some("Line"), false, None),
                fact_ext("Connected", &["L2", "Dir_L2"], Some("Direction"), Some("Line"), false, None),
                fact_ext("Connected", &["L3", "Dir_L3"], Some("Direction"), Some("Line"), false, None),
                fact_ext("Connected", &["L4", "Dir_L4"], Some("Direction"), Some("Line"), false, None),
                distinct(&["L1", "L2", "L3", "L4"]),
                
                fact_ext("Connected", &["P_Apex1", "L1"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P_Apex1", "L2"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P_Apex2", "L3"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P_Apex2", "L4"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P_Base1", "L1"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P_Base1", "L3"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P_Base2", "L2"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P_Base2", "L4"], Some("Line"), Some("Point"), false, None),
                distinct(&["P_Apex1", "P_Apex2", "P_Base1", "P_Base2"]),
            ],
            // 🌟 Concyclicという専用Factで結論するのをやめ、P_Apex1,P_Base1,P_Base2
            // を通る円を作図し、P_Apex2もその円にConnectedである、という形で結論する。
            // (4点は対称な関係なので、どの3点を作図に使っても良い)
            constructions: vec![
                ConstructTemplate { def_type: "Circumcircle".to_string(), args: vec!["P_Apex1".to_string(), "P_Base1".to_string(), "P_Base2".to_string()], target_type: "Circle".to_string(), bind_to: "Circ_New".to_string() },
            ],
            conclusions: vec![FactTemplate { fact_type: "Connected".to_string(), args: vec!["P_Apex2".to_string(), "Circ_New".to_string()], target_type: Some("Circle".to_string()), sub_type: None }],
        },
        // ==========================================
        // 同位角による平行判定 (右共通 / 左共通)[cite: 6]
        // ==========================================
        TheoremDef {
            name: "同位角による平行判定(右共通)".to_string(),
            entities: entities(&[
                ("D1", EntityType::Point), ("D2", EntityType::Point), ("D3", EntityType::Point),
                ("Ang1", EntityType::Angle), ("Ang2", EntityType::Angle),
            ]),
            patterns: vec![
                fact_ext("Identical", &["Ang1", "Ang2"], Some("Angle"), None, false, None),
                fact_ext("DefinedBy", &["D1", "D3", "Ang1"], Some("AnglePair"), None, true, Some("P1")),
                fact_ext("DefinedBy", &["D2", "D3", "Ang2"], Some("AnglePair"), None, true, Some("P1")),
                distinct(&["D1", "D2", "D3"]),
            ],
            constructions: vec![],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["D1".to_string(), "D2".to_string()], target_type: Some("Point".to_string()), sub_type: None }
            ],
        },
        TheoremDef {
            name: "同位角による平行判定(左共通)".to_string(),
            entities: entities(&[
                ("D1", EntityType::Point), ("D2", EntityType::Point), ("D3", EntityType::Point),
                ("Ang1", EntityType::Angle), ("Ang2", EntityType::Angle),
            ]),
            patterns: vec![
                fact_ext("Identical", &["Ang1", "Ang2"], Some("Angle"), None, false, None),
                fact_ext("DefinedBy", &["D3", "D1", "Ang1"], Some("AnglePair"), None, true, Some("P2")),
                fact_ext("DefinedBy", &["D3", "D2", "Ang2"], Some("AnglePair"), None, true, Some("P2")),
                distinct(&["D1", "D2", "D3"]),
            ],
            constructions: vec![],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["D1".to_string(), "D2".to_string()], target_type: Some("Point".to_string()), sub_type: None }
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
                ("Ang12", EntityType::Angle), ("Ang45", EntityType::Angle),
                ("Ang23", EntityType::Angle), ("Ang56", EntityType::Angle),
                ("Ang13", EntityType::Angle), ("Ang46", EntityType::Angle),
            ]),
            patterns: vec![
                fact_ext("Identical", &["Ang12", "Ang45"], Some("Angle"), None, false, None),
                fact_ext("DefinedBy", &["D1", "D2", "Ang12"], Some("AnglePair"), None, true, Some("Add1")),
                fact_ext("DefinedBy", &["D4", "D5", "Ang45"], Some("AnglePair"), None, true, Some("Add1")),
                
                // 爆速化: 一致した方向(D2, D5)を起点にピンポイント検索
                fact_ext("DefinedBy", &["D2", "D3", "Ang23"], Some("AnglePair"), None, true, Some("Add2")),
                fact_ext("DefinedBy", &["D5", "D6", "Ang56"], Some("AnglePair"), None, true, Some("Add2")),
                fact_ext("Identical", &["Ang23", "Ang56"], Some("Angle"), None, false, None),
                
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

                fact_ext("DefinedBy", &["D1", "D3", "Ang13"], Some("AnglePair"), None, true, Some("Add3")),
                fact_ext("DefinedBy", &["D4", "D6", "Ang46"], Some("AnglePair"), None, true, Some("Add3")),
            ],
            constructions: vec![],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["Ang13".to_string(), "Ang46".to_string()], target_type: Some("Angle".to_string()), sub_type: None }
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
                ("Ang12", EntityType::Angle), ("Ang34", EntityType::Angle),
                ("Ang13", EntityType::Angle), ("Ang24", EntityType::Angle),
            ]),
            patterns: vec![
                fact_ext("Identical", &["Ang12", "Ang34"], Some("Angle"), None, false, None),
                fact_ext("DefinedBy", &["D1", "D2", "Ang12"], Some("AnglePair"), None, true, Some("Perm1")),
                fact_ext("DefinedBy", &["D3", "D4", "Ang34"], Some("AnglePair"), None, true, Some("Perm1")),
                distinct(&["D1", "D2", "D3", "D4"]),
                
                fact_ext("DefinedBy", &["D1", "D3", "Ang13"], Some("AnglePair"), None, true, Some("Perm2")),
                fact_ext("DefinedBy", &["D2", "D4", "Ang24"], Some("AnglePair"), None, true, Some("Perm2")),
            ],
            constructions: vec![],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["Ang13".to_string(), "Ang24".to_string()], target_type: Some("Angle".to_string()), sub_type: None }
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
                ("Ang90", EntityType::Angle), ("Ang_AH_CH", EntityType::Angle), ("Ang_MH_CH", EntityType::Angle), ("Ang_CH_CA", EntityType::Angle),
            ]),
            patterns: vec![
                // 爆速化: まず中点を探す
                fact_ext("DefinedBy", &["A", "C", "M"], Some("Midpoint"), None, false, None),
                
                fact_ext("Identical", &["Ang_AH_CH", "Ang90"], Some("Angle"), None, false, None),
                fact_ext("DefinedBy", &["Dir_AH", "Dir_CH", "Ang_AH_CH"], Some("AnglePair"), None, false, None),
                
                fact_ext("DefinedBy", &["L_AH", "Dir_AH"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["L_CH", "Dir_CH"], Some("DirectionOf"), None, false, None),
                
                // CommonEntity の代用: Hが両方の直線に乗っていること
                fact_ext("Connected", &["H", "L_AH"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["H", "L_CH"], Some("Line"), Some("Point"), false, None),
                
                fact_ext("Connected", &["A", "L_AH"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["C", "L_CH"], Some("Line"), Some("Point"), false, None),
                
                distinct(&["A", "C", "H", "M"]),
                distinct(&["L_AH", "L_CH"]),
            ],
            constructions: vec![
                ConstructTemplate { def_type: "LineThroughPoints".to_string(), args: vec!["M".to_string(), "H".to_string()], target_type: "Line".to_string(), bind_to: "L_MH".to_string() },
                ConstructTemplate { def_type: "LineThroughPoints".to_string(), args: vec!["C".to_string(), "A".to_string()], target_type: "Line".to_string(), bind_to: "L_CA".to_string() },
                ConstructTemplate { def_type: "DirectionOf".to_string(), args: vec!["L_MH".to_string()], target_type: "Point".to_string(), bind_to: "Dir_MH".to_string() },
                ConstructTemplate { def_type: "DirectionOf".to_string(), args: vec!["L_CA".to_string()], target_type: "Point".to_string(), bind_to: "Dir_CA".to_string() },
                ConstructTemplate { def_type: "AnglePair".to_string(), args: vec!["Dir_MH".to_string(), "Dir_CH".to_string()], target_type: "Angle".to_string(), bind_to: "Ang_MH_CH".to_string() },
                ConstructTemplate { def_type: "AnglePair".to_string(), args: vec!["Dir_CH".to_string(), "Dir_CA".to_string()], target_type: "Angle".to_string(), bind_to: "Ang_CH_CA".to_string() },
            ],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["Ang_MH_CH".to_string(), "Ang_CH_CA".to_string()], target_type: Some("Angle".to_string()), sub_type: None }
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
                ("Ang_A", EntityType::Angle), ("Ang90", EntityType::Angle),
                ("Line_Median", EntityType::Line), ("Dir_Median", EntityType::Point), // 🌟 復活
                ("Dist_MB", EntityType::Scalar), ("Dist_MA", EntityType::Scalar),
            ]),
            patterns: vec![
                fact_ext("DefinedBy", &["B", "C", "Mid_BC"], Some("Midpoint"), None, false, None),
                fact_ext("Identical", &["Ang_A", "Ang90"], Some("Angle"), None, false, None),
                // 🌟 allow_flip = true
                fact_ext("DefinedBy", &["Dir1", "Dir2", "Ang_A"], Some("AnglePair"), None, true, None),
                
                fact_ext("DefinedBy", &["L1", "Dir1"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["L2", "Dir2"], Some("DirectionOf"), None, false, None),
                fact_ext("Connected", &["A", "L1"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["A", "L2"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["B", "L1"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["C", "L2"], Some("Line"), Some("Point"), false, None),
                distinct(&["A", "B", "C"]),
            ],
            constructions: vec![
                // 🌟 FIX: 直線と方向をE-Graphに物理的に作図し、他の定理への架け橋を作る
                ConstructTemplate { def_type: "LineThroughPoints".to_string(), args: vec!["Mid_BC".to_string(), "A".to_string()], target_type: "Line".to_string(), bind_to: "Line_Median".to_string() },
                ConstructTemplate { def_type: "DirectionOf".to_string(), args: vec!["Line_Median".to_string()], target_type: "Point".to_string(), bind_to: "Dir_Median".to_string() },
                
                ConstructTemplate { def_type: "LengthSq".to_string(), args: vec!["Mid_BC".to_string(), "B".to_string()], target_type: "Scalar".to_string(), bind_to: "Dist_MB".to_string() },
                ConstructTemplate { def_type: "LengthSq".to_string(), args: vec!["Mid_BC".to_string(), "A".to_string()], target_type: "Scalar".to_string(), bind_to: "Dist_MA".to_string() },
            ],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["Dist_MB".to_string(), "Dist_MA".to_string()], target_type: None, sub_type: None }
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
                ("Ang_A", EntityType::Angle), ("Ang90", EntityType::Angle),
                ("Dist_MB", EntityType::Scalar), ("Dist_MA", EntityType::Scalar),
            ]),
            patterns: vec![
                fact_ext("DefinedBy", &["B", "C", "Mid_BC"], Some("Midpoint"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["Mid_BC", "B", "Dist_MB"], Some("LengthSq"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["Mid_BC", "A", "Dist_MA"], Some("LengthSq"), Some("Unordered"), false, None),
                fact_ext("Identical", &["Dist_MB", "Dist_MA"], Some("Scalar"), None, false, None),
                distinct(&["A", "B", "C"]),
            ],
            constructions: vec![
                ConstructTemplate { def_type: "LineThroughPoints".to_string(), args: vec!["A".to_string(), "B".to_string()], target_type: "Line".to_string(), bind_to: "L1".to_string() },
                ConstructTemplate { def_type: "LineThroughPoints".to_string(), args: vec!["A".to_string(), "C".to_string()], target_type: "Line".to_string(), bind_to: "L2".to_string() },
                ConstructTemplate { def_type: "DirectionOf".to_string(), args: vec!["L1".to_string()], target_type: "Point".to_string(), bind_to: "Dir1".to_string() },
                ConstructTemplate { def_type: "DirectionOf".to_string(), args: vec!["L2".to_string()], target_type: "Point".to_string(), bind_to: "Dir2".to_string() },
                ConstructTemplate { def_type: "AnglePair".to_string(), args: vec!["Dir1".to_string(), "Dir2".to_string()], target_type: "Angle".to_string(), bind_to: "Ang_A".to_string() },
            ],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["Ang_A".to_string(), "Ang90".to_string()], target_type: Some("Angle".to_string()), sub_type: None }
            ],
        },
    ]
}

/// 🌟 複比の透視射影不変性 (Phase 2)。
///
/// 点Oから4組の対応点(A,A'),(B,B'),(C,C'),(D,D')への4本の直線がそれぞれ
/// Oを通るなら(=Oを中心とする透視図法で対応しているなら)、複比(A,B;C,D)と
/// (A',B';C',D')は等しい。射影幾何の最も基本的な定理の一つで、円周角の
/// 定理・接弦定理・トレミーの定理など多くの古典定理を将来的に統一的に
/// 導出する土台になる想定(Phase 2以降で個別に接続していく)。
///
/// 🐛 既知の制約: この定理はO,A,B,C,D,A',B',C',D'という9つの自由な点変数を
/// 持ち、Identical/Connectedのような「新しい事実が証明された」イベントに
/// よって自然にシード(一部の変数を安価に固定)されることが無い。そのため
/// schedule_full_sweepの(シードなし)全探索でこの定理を評価しようとすると、
/// 先頭のDefinedBy(LineThroughPoints)パターンが「直線を持つ全ペア」を
/// 総当たりで試すことになり、点や直線が多い問題(nine_point/orthic_incenter/
/// miquel_quadrilateral等)でdfs_capを食い潰してしまい、実際に回帰テストで
/// 検出した(これらの問題が解けなくなり、他の問題群でも実行時間が数倍に
/// 悪化した)。そのためget_all_theorems()には含めず、この定理を実際に使う
/// 問題(test_cross_ratio等)側がmain.rsで明示的に追加する、opt-in方式に
/// している。将来、より安価にシードできる定式化(あるいはtheorem単位の
/// コスト上限/専用のシード機構)が見つかれば、get_all_theoremsへの統合を
/// 再検討する。
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
                fact_ext("Connected", &["A", "L"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["B", "L"], Some("Line"), Some("Point"), false, None),
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
                // 正準順序が排除してしまい壊れるリスクがある。要:
                // test_cross_ratio/test_involutionで実際に解けることを確認。
                order(&["A", "B"]),
                fact_ext("Connected", &["C", "L"], Some("Line"), Some("Point"), false, None),
                order(&["B", "C"]),
                fact_ext("Connected", &["D", "L"], Some("Line"), Some("Point"), false, None),
                order(&["C", "D"]),
                // A,B,C,Dそれぞれについて「Lとは別の、Oを通る直線」を局所
                // スキャンで見つける(A自身の既知の直線のうち、Lではない方)。
                fact_ext("Connected", &["A", "LOA"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["O", "LOA"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["B", "LOB"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["O", "LOB"], Some("Line"), Some("Point"), false, None),
                distinct(&["LOA", "LOB"]),
                fact_ext("Connected", &["C", "LOC"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["O", "LOC"], Some("Line"), Some("Point"), false, None),
                distinct(&["LOA", "LOB", "LOC"]),
                fact_ext("Connected", &["D", "LOD"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["O", "LOD"], Some("Line"), Some("Point"), false, None),
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
                ConstructTemplate { def_type: "CrossRatio".to_string(), args: vec!["A".to_string(), "B".to_string(), "C".to_string(), "D".to_string()], target_type: "Scalar".to_string(), bind_to: "CR1".to_string() },
                ConstructTemplate { def_type: "CrossRatioOfLines".to_string(), args: vec!["LOA".to_string(), "LOB".to_string(), "LOC".to_string(), "LOD".to_string()], target_type: "Scalar".to_string(), bind_to: "CRL".to_string() },
            ],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["CR1".to_string(), "CRL".to_string()], target_type: Some("Scalar".to_string()), sub_type: None }
            ],
        },
        TheoremDef {
            name: "複比の透視射影不変性(線束→点)".to_string(),
            entities: entities(&[
                ("L1", EntityType::Line), ("L2", EntityType::Line), ("L3", EntityType::Line), ("L4", EntityType::Line),
                ("Ap", EntityType::Point), ("Bp", EntityType::Point), ("Cp", EntityType::Point), ("Dp", EntityType::Point),
                ("CRL", EntityType::Scalar), ("CR2", EntityType::Scalar),
            ]),
            patterns: vec![
                // 🌟 シード: 定理A(点→線束)がCrossRatioOfLines(L1..L4)を新しく
                // 証明した直後、その事実からL1..L4とCRLを直接束縛できる
                // (全件スキャン不要)。
                fact_ext("DefinedBy", &["L1", "L2", "L3", "L4", "CRL"], Some("CrossRatioOfLines"), None, false, None),
                // 各直線について「Lとは別の(=線束の中心Oではない)、その直線上の
                // 点」を局所スキャンで見つける。中心Oは4直線全てに繋がっている
                // 唯一の点なので、「他の1本には繋がっていない」ことで確実に除外できる。
                // 🌟 定理A側と同じ理由(実測に基づくFIX)で、各点が束縛される
                // たびにdistinctを挟み、早期に枝刈りする。
                fact_ext("Connected", &["Ap", "L1"], Some("Line"), Some("Point"), false, None),
                not(fact_ext("Connected", &["Ap", "L2"], Some("Line"), Some("Point"), false, None)),
                fact_ext("Connected", &["Bp", "L2"], Some("Line"), Some("Point"), false, None),
                not(fact_ext("Connected", &["Bp", "L1"], Some("Line"), Some("Point"), false, None)),
                distinct(&["Ap", "Bp"]),
                fact_ext("Connected", &["Cp", "L3"], Some("Line"), Some("Point"), false, None),
                not(fact_ext("Connected", &["Cp", "L1"], Some("Line"), Some("Point"), false, None)),
                distinct(&["Ap", "Bp", "Cp"]),
                fact_ext("Connected", &["Dp", "L4"], Some("Line"), Some("Point"), false, None),
                not(fact_ext("Connected", &["Dp", "L1"], Some("Line"), Some("Point"), false, None)),
                distinct(&["Ap", "Bp", "Cp", "Dp"]),
            ],
            constructions: vec![
                ConstructTemplate { def_type: "CrossRatio".to_string(), args: vec!["Ap".to_string(), "Bp".to_string(), "Cp".to_string(), "Dp".to_string()], target_type: "Scalar".to_string(), bind_to: "CR2".to_string() },
            ],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["CRL".to_string(), "CR2".to_string()], target_type: Some("Scalar".to_string()), sub_type: None }
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
                fact_ext("DefinedBy", &["P1", "P2", "P3", "P4", "P5", "Conic"], Some("ConicThrough5Points"), None, false, None),
                distinct(&["P1", "P2", "P3", "P4", "P5"]),
                // 二次曲線上のもう1点Qを局所スキャンで見つける(唯一の
                // 「新規に探す」変数)。
                fact_ext("Connected", &["Q", "Conic"], None, None, false, None),
                distinct(&["P1", "P2", "P3", "P4", "P5", "Q"]),
                // P1から見たP2,P3,P4,Qへの4直線(既存のものが無ければ
                // 円周角の定理のL_A1_B1等と同じ「DefinedBy+作図需要」で作る)。
                fact_ext("DefinedBy", &["P1", "P2", "L1_P2"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["P1", "P3", "L1_P3"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                distinct(&["L1_P2", "L1_P3"]),
                fact_ext("DefinedBy", &["P1", "P4", "L1_P4"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                distinct(&["L1_P2", "L1_P3", "L1_P4"]),
                fact_ext("DefinedBy", &["P1", "Q", "L1_Q"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                distinct(&["L1_P2", "L1_P3", "L1_P4", "L1_Q"]),
                // P5から見た同じP2,P3,P4,Qへの4直線。
                fact_ext("DefinedBy", &["P5", "P2", "L5_P2"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["P5", "P3", "L5_P3"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                distinct(&["L5_P2", "L5_P3"]),
                fact_ext("DefinedBy", &["P5", "P4", "L5_P4"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                distinct(&["L5_P2", "L5_P3", "L5_P4"]),
                fact_ext("DefinedBy", &["P5", "Q", "L5_Q"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                distinct(&["L5_P2", "L5_P3", "L5_P4", "L5_Q"]),
            ],
            constructions: vec![
                ConstructTemplate { def_type: "CrossRatioOfLines".to_string(), args: vec!["L1_P2".to_string(), "L1_P3".to_string(), "L1_P4".to_string(), "L1_Q".to_string()], target_type: "Scalar".to_string(), bind_to: "CR_P1".to_string() },
                ConstructTemplate { def_type: "CrossRatioOfLines".to_string(), args: vec!["L5_P2".to_string(), "L5_P3".to_string(), "L5_P4".to_string(), "L5_Q".to_string()], target_type: "Scalar".to_string(), bind_to: "CR_P5".to_string() },
            ],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["CR_P1".to_string(), "CR_P5".to_string()], target_type: Some("Scalar".to_string()), sub_type: None }
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
                fact_ext("DefinedBy", &["P1", "P2", "P3", "P4", "P5", "Conic"], Some("ConicThrough5Points"), None, false, None),
                distinct(&["P1", "P2", "P3", "P4", "P5"]),

                // P1における接線T1(円周角の定理の逆の"TanA"と同じ発想の
                // DefinedBy+作図需要)。
                fact_ext("DefinedBy", &["Conic", "P1", "T1"], Some("TangentLine"), None, false, None),

                // P1から見たP2,P3,P4への3直線。
                fact_ext("DefinedBy", &["P1", "P2", "L1_P2"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["P1", "P3", "L1_P3"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                distinct(&["L1_P2", "L1_P3"]),
                fact_ext("DefinedBy", &["P1", "P4", "L1_P4"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                distinct(&["L1_P2", "L1_P3", "L1_P4"]),

                // P5から見たP2,P3,P4,P1への4直線(P1は接点ではなく"ただの弦"
                // として、シュタイナーの定理のQと同じ役割で扱う)。
                fact_ext("DefinedBy", &["P5", "P2", "L5_P2"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["P5", "P3", "L5_P3"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                distinct(&["L5_P2", "L5_P3"]),
                fact_ext("DefinedBy", &["P5", "P4", "L5_P4"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                distinct(&["L5_P2", "L5_P3", "L5_P4"]),
                fact_ext("DefinedBy", &["P5", "P1", "L5_P1"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                distinct(&["L5_P2", "L5_P3", "L5_P4", "L5_P1"]),
            ],
            constructions: vec![
                ConstructTemplate { def_type: "CrossRatioOfLines".to_string(), args: vec!["L1_P2".to_string(), "L1_P3".to_string(), "L1_P4".to_string(), "T1".to_string()], target_type: "Scalar".to_string(), bind_to: "CR_P1".to_string() },
                ConstructTemplate { def_type: "CrossRatioOfLines".to_string(), args: vec!["L5_P2".to_string(), "L5_P3".to_string(), "L5_P4".to_string(), "L5_P1".to_string()], target_type: "Scalar".to_string(), bind_to: "CR_P5".to_string() },
            ],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["CR_P1".to_string(), "CR_P5".to_string()], target_type: Some("Scalar".to_string()), sub_type: None }
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
                fact_ext("Identical", &["CR_P1", "CR_P5"], Some("Scalar"), None, false, None),
                fact_ext("DefinedBy", &["L1_P2", "L1_P3", "L1_P4", "L1_Q", "CR_P1"], Some("CrossRatioOfLines"), None, false, None),
                fact_ext("DefinedBy", &["L5_P2", "L5_P3", "L5_P4", "L5_Q", "CR_P5"], Some("CrossRatioOfLines"), None, false, None),
                distinct(&["L1_P2", "L1_P3", "L1_P4", "L1_Q"]),
                distinct(&["L5_P2", "L5_P3", "L5_P4", "L5_Q"]),

                // P1 = L1側4直線に共通の点(視点)。P5も同様。
                fact_ext("Connected", &["P1", "L1_P2"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P1", "L1_P3"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P1", "L1_P4"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P1", "L1_Q"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P5", "L5_P2"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P5", "L5_P3"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P5", "L5_P4"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P5", "L5_Q"], Some("Line"), Some("Point"), false, None),
                distinct(&["P1", "P5"]),

                // P2 = L1_P2とL5_P2に共通の点(視点P1,P5以外)。P3,P4,Qも同様。
                fact_ext("Connected", &["P2", "L1_P2"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P2", "L5_P2"], Some("Line"), Some("Point"), false, None),
                distinct(&["P1", "P5", "P2"]),
                fact_ext("Connected", &["P3", "L1_P3"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P3", "L5_P3"], Some("Line"), Some("Point"), false, None),
                distinct(&["P1", "P5", "P2", "P3"]),
                fact_ext("Connected", &["P4", "L1_P4"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P4", "L5_P4"], Some("Line"), Some("Point"), false, None),
                distinct(&["P1", "P5", "P2", "P3", "P4"]),
                fact_ext("Connected", &["Q", "L1_Q"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["Q", "L5_Q"], Some("Line"), Some("Point"), false, None),
                distinct(&["P1", "P5", "P2", "P3", "P4", "Q"]),
            ],
            constructions: vec![
                ConstructTemplate { def_type: "ConicThrough5Points".to_string(), args: vec!["P1".to_string(), "P2".to_string(), "P3".to_string(), "P4".to_string(), "P5".to_string()], target_type: "Conic".to_string(), bind_to: "Conic_New".to_string() },
            ],
            conclusions: vec![
                FactTemplate { fact_type: "Connected".to_string(), args: vec!["Q".to_string(), "Conic_New".to_string()], target_type: Some("Conic".to_string()), sub_type: None }
            ],
        },
    ]
}
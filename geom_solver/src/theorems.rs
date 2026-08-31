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
                ("L_A1_B1", EntityType::Line), ("L_A1_B2", EntityType::Line),
                ("L_A2_B1", EntityType::Line), ("L_A2_B2", EntityType::Line),
                ("Dir_A1_B1", EntityType::Direction), ("Dir_A1_B2", EntityType::Direction),
                ("Dir_A2_B1", EntityType::Direction), ("Dir_A2_B2", EntityType::Direction),
                ("Ang1", EntityType::Angle), ("Ang2", EntityType::Angle),
            ]),
            patterns: vec![
                fact_ext("Concyclic", &["Apex1", "Apex2", "Base1", "Base2"], Some("Unordered"), None, false, None),
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

        // 2. 直線の一致条件
        TheoremDef {
            name: "直線の一致条件".to_string(),
            entities: entities(&[
                ("P", EntityType::Point),
                ("L1", EntityType::Line), ("L2", EntityType::Line),
                ("Dir1", EntityType::Direction), ("Dir2", EntityType::Direction)
            ]),
            patterns: vec![
                // 🌟 必須条件: 2つの直線が「共通の点P」を通っていること
                fact_ext("Connected", &["P", "L1"], None, None, false, None),
                fact_ext("Connected", &["P", "L2"], None, None, false, None),
                
                fact_ext("DefinedBy", &["L1", "Dir1"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["L2", "Dir2"], Some("DirectionOf"), None, false, None),
                fact_ext("Identical", &["Dir1", "Dir2"], None, None, false, None),
            ],
            constructions: vec![],
            conclusions: vec![
                FactTemplate { 
                    fact_type: "Identical".to_string(), 
                    args: vec!["L1".to_string(), "L2".to_string()], 
                    target_type: Some("Line".to_string()), 
                    sub_type: None 
                }
            ],
        },

        // 3. 中点連結定理
        TheoremDef {
            name: "中点連結定理".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point),
                ("M1", EntityType::Point), ("M2", EntityType::Point),
                ("LineBC", EntityType::Line), ("LineM1M2", EntityType::Line),
                ("DirBC", EntityType::Direction), ("DirM1M2", EntityType::Direction),
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
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["DirBC".to_string(), "DirM1M2".to_string()], target_type: Some("Direction".to_string()), sub_type: None }
            ],
        },

        TheoremDef {
            name: "二等辺三角形の底角".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point),
                ("Dist_AB", EntityType::Scalar), ("Dist_AC", EntityType::Scalar),
                ("LineAB", EntityType::Line), ("LineAC", EntityType::Line), ("LineBC", EntityType::Line),
                ("DirAB", EntityType::Direction), ("DirAC", EntityType::Direction), ("DirBC", EntityType::Direction),
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

        TheoremDef {
            name: "接弦定理".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point),
                ("Circ", EntityType::Circle), ("TanA", EntityType::Line),
                ("LineAB", EntityType::Line), ("LineAC", EntityType::Line), ("LineBC", EntityType::Line),
                ("DirTan", EntityType::Direction), ("DirAB", EntityType::Direction), ("DirAC", EntityType::Direction), ("DirBC", EntityType::Direction),
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
                ("Dir_L1", EntityType::Direction), ("Dir_L2", EntityType::Direction),
                ("Dir_L3", EntityType::Direction), ("Dir_L4", EntityType::Direction),
                ("L1", EntityType::Line), ("L2", EntityType::Line), ("L3", EntityType::Line), ("L4", EntityType::Line),
                ("P_Apex1", EntityType::Point), ("P_Apex2", EntityType::Point),
                ("P_Base1", EntityType::Point), ("P_Base2", EntityType::Point),
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
            constructions: vec![],
            conclusions: vec![FactTemplate { fact_type: "Concyclic".to_string(), args: vec!["P_Apex1".to_string(), "P_Apex2".to_string(), "P_Base1".to_string(), "P_Base2".to_string()], target_type: Some("Circle".to_string()), sub_type: None }],
        },
        // ==========================================
        // 同位角による平行判定 (右共通 / 左共通)[cite: 6]
        // ==========================================
        TheoremDef {
            name: "同位角による平行判定(右共通)".to_string(),
            entities: entities(&[
                ("Dir1", EntityType::Direction), ("Dir2", EntityType::Direction), ("DirM", EntityType::Direction),
                ("Ang1", EntityType::Angle), ("Ang2", EntityType::Angle),
            ]),
            patterns: vec![
                fact_ext("Identical", &["Ang1", "Ang2"], Some("Angle"), None, false, None),
                fact_ext("DefinedBy", &["Dir1", "DirM", "Ang1"], Some("AnglePair"), None, true, Some("DirR")),
                fact_ext("DefinedBy", &["Dir2", "DirM", "Ang2"], Some("AnglePair"), None, true, Some("DirR")),
                distinct(&["Dir1", "Dir2", "DirM"]),
            ],
            constructions: vec![],
            conclusions: vec![FactTemplate { fact_type: "Identical".to_string(), args: vec!["Dir1".to_string(), "Dir2".to_string()], target_type: Some("Direction".to_string()), sub_type: None }],
        },
        TheoremDef {
            name: "同位角による平行判定(左共通)".to_string(),
            entities: entities(&[
                ("Dir1", EntityType::Direction), ("Dir2", EntityType::Direction), ("DirM", EntityType::Direction),
                ("Ang1", EntityType::Angle), ("Ang2", EntityType::Angle),
            ]),
            patterns: vec![
                fact_ext("Identical", &["Ang1", "Ang2"], Some("Angle"), None, false, None),
                fact_ext("DefinedBy", &["DirM", "Dir1", "Ang1"], Some("AnglePair"), None, true, Some("DirL")),
                fact_ext("DefinedBy", &["DirM", "Dir2", "Ang2"], Some("AnglePair"), None, true, Some("DirL")),
                distinct(&["Dir1", "Dir2", "DirM"]),
            ],
            constructions: vec![],
            conclusions: vec![FactTemplate { fact_type: "Identical".to_string(), args: vec!["Dir1".to_string(), "Dir2".to_string()], target_type: Some("Direction".to_string()), sub_type: None }],
        },
        // ==========================================
        // 🌟 有向角の加法性
        // ==========================================
        TheoremDef {
            name: "有向角の加法性".to_string(),
            entities: entities(&[
                ("D1", EntityType::Direction), ("D2", EntityType::Direction), ("D3", EntityType::Direction),
                ("D4", EntityType::Direction), ("D5", EntityType::Direction), ("D6", EntityType::Direction),
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
                ("D1", EntityType::Direction), ("D2", EntityType::Direction), 
                ("D3", EntityType::Direction), ("D4", EntityType::Direction),
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
        TheoremDef {
            name: "直角三角形の斜辺の中線 (距離版)".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point), ("Mid_BC", EntityType::Point),
                ("L1", EntityType::Line), ("L2", EntityType::Line),
                ("Dir1", EntityType::Direction), ("Dir2", EntityType::Direction),
                ("Ang_A", EntityType::Angle), ("Ang90", EntityType::Angle),
                ("Dist_MB", EntityType::Scalar), ("Dist_MA", EntityType::Scalar),
            ]),
            patterns: vec![
                fact_ext("DefinedBy", &["B", "C", "Mid_BC"], Some("Midpoint"), Some("Unordered"), false, None),
                fact_ext("Identical", &["Ang_A", "Ang90"], Some("Angle"), None, false, None),
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
                ConstructTemplate { def_type: "LengthSq".to_string(), args: vec!["Mid_BC".to_string(), "B".to_string()], target_type: "Scalar".to_string(), bind_to: "Dist_MB".to_string() },
                ConstructTemplate { def_type: "LengthSq".to_string(), args: vec!["Mid_BC".to_string(), "A".to_string()], target_type: "Scalar".to_string(), bind_to: "Dist_MA".to_string() },
            ],
            conclusions: vec![
                FactTemplate { fact_type: "Identical".to_string(), args: vec!["Dist_MB".to_string(), "Dist_MA".to_string()], target_type: Some("Scalar".to_string()), sub_type: None }
            ],
        },
    ]
}
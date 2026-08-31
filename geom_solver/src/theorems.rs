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
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point), ("D", EntityType::Point),
                ("Circ", EntityType::Circle),
                ("LineAB", EntityType::Line), ("LineAC", EntityType::Line), ("LineDB", EntityType::Line), ("LineDC", EntityType::Line),
                ("DirAB", EntityType::Direction), ("DirAC", EntityType::Direction), ("DirDB", EntityType::Direction), ("DirDC", EntityType::Direction),
                ("Ang_BAC", EntityType::Angle), ("Ang_BDC", EntityType::Angle),
            ]),
            patterns: vec![
                // 🌟 A,B,Cを通る円(Circ)上に、点Dも乗っている(Connected)という条件
                fact_ext("DefinedBy", &["A", "B", "C", "Circ"], Some("Circumcircle"), Some("Unordered"), false, None),
                fact_ext("Connected", &["D", "Circ"], None, None, false, None),
                distinct(&["A", "B", "C", "D"]),
                
                fact_ext("DefinedBy", &["A", "B", "LineAB"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["A", "C", "LineAC"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["D", "B", "LineDB"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                fact_ext("DefinedBy", &["D", "C", "LineDC"], Some("LineThroughPoints"), Some("Unordered"), false, None),
                
                fact_ext("DefinedBy", &["LineAB", "DirAB"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["LineAC", "DirAC"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["LineDB", "DirDB"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["LineDC", "DirDC"], Some("DirectionOf"), None, false, None),
                
                // 🌟 角度のフリップ同期 ("CircGroup" として向きを揃える)
                fact_ext("DefinedBy", &["DirAB", "DirAC", "Ang_BAC"], Some("AnglePair"), None, true, Some("CircGroup")),
                fact_ext("DefinedBy", &["DirDB", "DirDC", "Ang_BDC"], Some("AnglePair"), None, true, Some("CircGroup")),
            ],
            constructions: vec![],
            conclusions: vec![
                FactTemplate {
                    fact_type: "Identical".to_string(),
                    args: vec!["Ang_BAC".to_string(), "Ang_BDC".to_string()],
                    target_type: Some("Angle".to_string()),
                    sub_type: None,
                }
            ],
        },

        // 2. 直線の一致条件
        TheoremDef {
            name: "直線の一致条件".to_string(),
            entities: entities(&[
                ("P", EntityType::Point), ("L1", EntityType::Line),
                ("L2", EntityType::Line), ("Dir", EntityType::Direction),
            ]),
            patterns: vec![
                fact_ext("DefinedBy", &["L1", "Dir"], Some("DirectionOf"), None, false, None),
                fact_ext("DefinedBy", &["L2", "Dir"], Some("DirectionOf"), None, false, None),
                distinct(&["L1", "L2"]),
                fact_ext("Connected", &["P", "L1"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["P", "L2"], Some("Line"), Some("Point"), false, None),
            ],
            constructions: vec![],
            conclusions: vec![
                FactTemplate {
                    fact_type: "Identical".to_string(),
                    args: vec!["L1".to_string(), "L2".to_string()],
                    target_type: Some("Line".to_string()),
                    sub_type: None,
                }
            ],
        },

        // 3. 中点連結定理
        TheoremDef {
            name: "中点連結定理".to_string(),
            entities: entities(&[
                ("A", EntityType::Point), ("B", EntityType::Point), ("C", EntityType::Point),
                ("M1", EntityType::Point), ("M2", EntityType::Point),
                ("L_BC", EntityType::Line), ("L_M1M2", EntityType::Line),
                ("Dir_BC", EntityType::Direction), ("Dir_M1M2", EntityType::Direction),
            ]),
            patterns: vec![
                fact_ext("DefinedBy", &["A", "B", "M1"], Some("Midpoint"), None, false, None),
                fact_ext("DefinedBy", &["A", "C", "M2"], Some("Midpoint"), None, false, None),
                distinct(&["A", "B", "C", "M1", "M2"]),
                not(fact("Collinear", &["A", "B", "C"])),
            ],
            constructions: vec![
                ConstructTemplate { def_type: "LineThroughPoints".to_string(), args: vec!["B".to_string(), "C".to_string()], target_type: "Line".to_string(), bind_to: "L_BC".to_string() },
                ConstructTemplate { def_type: "LineThroughPoints".to_string(), args: vec!["M1".to_string(), "M2".to_string()], target_type: "Line".to_string(), bind_to: "L_M1M2".to_string() },
                ConstructTemplate { def_type: "DirectionOf".to_string(), args: vec!["L_BC".to_string()], target_type: "Direction".to_string(), bind_to: "Dir_BC".to_string() },
                ConstructTemplate { def_type: "DirectionOf".to_string(), args: vec!["L_M1M2".to_string()], target_type: "Direction".to_string(), bind_to: "Dir_M1M2".to_string() },
            ],
            conclusions: vec![
                FactTemplate {
                    fact_type: "Identical".to_string(),
                    args: vec!["Dir_BC".to_string(), "Dir_M1M2".to_string()],
                    target_type: Some("Direction".to_string()),
                    sub_type: None,
                }
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
    ]
}
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
                fact_ext("Concyclic", &["Apex1", "Apex2", "Base1", "Base2"], None, Some("Unordered"), false, None),
                distinct(&["Apex1", "Apex2", "Base1", "Base2"]),
                
                fact_ext("Connected", &["Apex1", "L_A1_B1"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["Base1", "L_A1_B1"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["Apex1", "L_A1_B2"], Some("Line"), Some("Point"), false, None),
                fact_ext("Connected", &["Base2", "L_A1_B2"], Some("Line"), Some("Point"), false, None),
                distinct(&["L_A1_B1", "L_A1_B2"]),
                
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
            conclusions: vec![
                FactTemplate {
                    fact_type: "Identical".to_string(),
                    args: vec!["Ang1".to_string(), "Ang2".to_string()],
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
    ]
}
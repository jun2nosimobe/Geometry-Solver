# theorems.py

from logic_core import (
    TheoremDef, FactPattern, NotPattern, CustomPattern,
    ConstructTemplate, FactTemplate, get_rep, get_subentity, DistinctPattern,
)

def get_constant_value(scalar_entity):
    comp = get_rep(scalar_entity).get_best_component()
    if not comp: return None
    for d in comp.definitions:
        if d.def_type == "Constant": return d.parents[0] 
    return None

# ==========================================
# 🌟 定理の定義 (Declarative Rules)
# ==========================================

THEOREM_CYCLIC_ANGLES = TheoremDef(
    name="円周角の定理",
    entities={"A": "Point", "B": "Point", "C": "Point", "D": "Point",
              "L_CA": "Line", "L_CB": "Line", "L_DA": "Line", "L_DB": "Line",
              "Dir_CA": "Direction", "Dir_CB": "Direction", "Dir_DA": "Direction", "Dir_DB": "Direction",
              "AngC": "Angle", "AngD": "Angle"},
    patterns=[
        FactPattern("Concyclic", ["A", "B", "C", "D"]),
        DistinctPattern(["A", "B", "C", "D"])
    ],
    constructions=[
        ConstructTemplate("LineThroughPoints", ["C", "A"], "Line", "L_CA"),
        ConstructTemplate("LineThroughPoints", ["C", "B"], "Line", "L_CB"),
        ConstructTemplate("LineThroughPoints", ["D", "A"], "Line", "L_DA"),
        ConstructTemplate("LineThroughPoints", ["D", "B"], "Line", "L_DB"),
        ConstructTemplate("DirectionOf", ["L_CA"], "Direction", "Dir_CA"),
        ConstructTemplate("DirectionOf", ["L_CB"], "Direction", "Dir_CB"),
        ConstructTemplate("DirectionOf", ["L_DA"], "Direction", "Dir_DA"),
        ConstructTemplate("DirectionOf", ["L_DB"], "Direction", "Dir_DB"),
        ConstructTemplate("AnglePair", ["Dir_CA", "Dir_CB"], "Angle", "AngC"),
        ConstructTemplate("AnglePair", ["Dir_DA", "Dir_DB"], "Angle", "AngD")
    ],
    conclusions=[
        FactTemplate("Identical", ["AngC", "AngD"], target_type="Angle")
    ]
)

THEOREM_CONVERSE_CYCLIC = TheoremDef(
    name="円周角の定理の逆",
    entities={"A": "Point", "B": "Point", "C": "Point", "D": "Point",
              "L_CA": "Line", "L_CB": "Line", "L_DA": "Line", "L_DB": "Line",
              "Dir_CA": "Direction", "Dir_CB": "Direction", "Dir_DA": "Direction", "Dir_DB": "Direction",
              "AngC": "Angle", "AngD": "Angle"},
    patterns=[
        # 1. まず一致している角度ペアを特定 (最も強い絞り込み)
        FactPattern("Identical", ["AngC", "AngD"], target_type="Angle"),
        
        # 2. 角度ノードから親の「方向(Direction)」を逆引き (ここで候補が O(1) で絞られる)
        FactPattern("DefinedBy", ["Dir_CA", "Dir_CB", "AngC"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["Dir_DA", "Dir_DB", "AngD"], target_type="AnglePair"),
        
        # 3. 特定された「方向」を持つ「直線」を逆引き
        FactPattern("DefinedBy", ["L_CA", "Dir_CA"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["L_CB", "Dir_CB"], target_type="DirectionOf"),
        DistinctPattern(["L_CA", "L_CB"]),
        FactPattern("DefinedBy", ["L_DA", "Dir_DA"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["L_DB", "Dir_DB"], target_type="DirectionOf"),
        DistinctPattern(["L_DA", "L_DB", "L_CA", "L_CB"]),
        
        # 4. 直線同士の交点(点)を検証 (トポロジー確認)
        FactPattern("CommonEntity", ["L_CA", "L_CB", "C"], target_type="Point"),
        FactPattern("CommonEntity", ["L_DA", "L_DB", "D"], target_type="Point"),
        DistinctPattern(["C", "D"]),
        FactPattern("CommonEntity", ["L_CA", "L_DA", "A"], target_type="Point"),
        FactPattern("CommonEntity", ["L_CB", "L_DB", "B"], target_type="Point"),
        DistinctPattern(["A", "B", "C", "D"])
    ],
    conclusions=[
        FactTemplate("Concyclic", ["A", "B", "C", "D"])
    ]
)

THEOREM_IDENTICAL_LINES_R = TheoremDef(
    name="直線の一致条件(右共通)",
    entities={"P": "Point", "L1": "Line", "L2": "Line", "M": "Line", 
              "Dir1": "Direction", "Dir2": "Direction", "DirM": "Direction",
              "Ang1": "Angle", "Ang2": "Angle"},
   patterns=[
        FactPattern("Identical", ["Ang1", "Ang2"], target_type="Angle"),
        
        # 🌟 ここも AnglePair が先！
        FactPattern("DefinedBy", ["Dir1", "DirM", "Ang1"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["Dir2", "DirM", "Ang2"], target_type="AnglePair"),
        
        FactPattern("DefinedBy", ["L1", "Dir1"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["L2", "Dir2"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["M", "DirM"], target_type="DirectionOf"),
        
        DistinctPattern(["L1", "L2", "M"]),
        FactPattern("Connected", [["P"], "L1"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", [["P"], "L2"], target_type="Line", sub_type="Point")
    ],
    conclusions=[
        FactTemplate("Identical", ["L1", "L2"], target_type="Line")
    ]
)

THEOREM_IDENTICAL_LINES_L = TheoremDef(
    name="直線の一致条件(左共通)",
    entities={"P": "Point", "L1": "Line", "L2": "Line", "M": "Line", 
              "Dir1": "Direction", "Dir2": "Direction", "DirM": "Direction",
              "Ang1": "Angle", "Ang2": "Angle"},
    patterns=[
        FactPattern("Identical", ["Ang1", "Ang2"], target_type="Angle"),
        FactPattern("DefinedBy", ["DirM", "Dir1", "Ang1"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["DirM", "Dir2", "Ang2"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["L1", "Dir1"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["L2", "Dir2"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["M", "DirM"], target_type="DirectionOf"),
        DistinctPattern(["L1", "L2", "M"]),
        FactPattern("Connected", [["P"], "L1"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", [["P"], "L2"], target_type="Line", sub_type="Point")
    ],
    conclusions=[
        FactTemplate("Identical", ["L1", "L2"], target_type="Line")
    ]
)

THEOREM_MIDPOINT_PARALLEL = TheoremDef(
    name="中点連結定理",
    entities={"A": "Point", "B": "Point", "C": "Point", "M1": "Point", "M2": "Point",
              "L_BC": "Line", "L_M1M2": "Line", "Dir_BC": "Direction", "Dir_M1M2": "Direction"},
    patterns=[
        FactPattern("DefinedBy", ["A", "B", "M1"], target_type="Midpoint"),
        FactPattern("DefinedBy", ["A", "C", "M2"], target_type="Midpoint"),
        DistinctPattern(["A", "B", "C", "M1", "M2"]),
        NotPattern(FactPattern("Collinear", ["A", "B", "C"]))
    ],
    constructions=[
        ConstructTemplate("LineThroughPoints", ["B", "C"], "Line", "L_BC"),
        ConstructTemplate("LineThroughPoints", ["M1", "M2"], "Line", "L_M1M2"),
        ConstructTemplate("DirectionOf", ["L_BC"], "Direction", "Dir_BC"),
        ConstructTemplate("DirectionOf", ["L_M1M2"], "Direction", "Dir_M1M2")
    ],
    conclusions=[
        FactTemplate("Identical", ["Dir_BC", "Dir_M1M2"], target_type="Direction")
    ]
)

THEOREM_RIGHT_TRIANGLE_MIDPOINT = TheoremDef(
    name="直角三角形の斜辺の中線",
    entities={
        "A": "Point", "C": "Point", "H": "Point", "M": "Point",
        "L_AH": "Line", "L_CH": "Line", "L_MH": "Line", "L_CA": "Line",
        "Dir_AH": "Direction", "Dir_CH": "Direction", "Dir_MH": "Direction", "Dir_CA": "Direction",
        "Ang90": "Angle", "Ang_AH_CH": "Angle", "Ang_MH_CH": "Angle", "Ang_CH_CA": "Angle"
    },
    patterns=[
        FactPattern("Identical", ["Ang_AH_CH", "Ang90"], target_type="Angle"),
        
        # 🌟 必ず AnglePair を先に！ (1件の直角から、親の方向を O(1) でダイレクトに逆引きする)
        FactPattern("DefinedBy", ["Dir_AH", "Dir_CH", "Ang_AH_CH"], target_type="AnglePair"),
        
        # 🌟 方向が特定されてから、その方向を持つ直線を逆引きする
        FactPattern("DefinedBy", ["L_AH", "Dir_AH"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["L_CH", "Dir_CH"], target_type="DirectionOf"),
        
        FactPattern("CommonEntity", ["L_AH", "L_CH", "H"], target_type="Point"),
        FactPattern("Connected", [["A"], "L_AH"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", [["C"], "L_CH"], target_type="Line", sub_type="Point"),
        FactPattern("DefinedBy", ["A", "C", "M"], target_type="Midpoint"),
        DistinctPattern(["A", "C", "H", "M", "L_AH", "L_CH"])
    ],
    constructions=[
        ConstructTemplate("LineThroughPoints", ["M", "H"], "Line", "L_MH"),
        ConstructTemplate("LineThroughPoints", ["C", "A"], "Line", "L_CA"),
        ConstructTemplate("DirectionOf", ["L_MH"], "Direction", "Dir_MH"),
        ConstructTemplate("DirectionOf", ["L_CA"], "Direction", "Dir_CA"),
        ConstructTemplate("AnglePair", ["Dir_MH", "Dir_CH"], "Angle", "Ang_MH_CH"),
        ConstructTemplate("AnglePair", ["Dir_CH", "Dir_CA"], "Angle", "Ang_CH_CA")
    ],
    conclusions=[
        FactTemplate("Identical", ["Ang_MH_CH", "Ang_CH_CA"], target_type="Angle")
    ]
)

THEOREM_RATIO_TO_PARALLEL = TheoremDef(
    name="平行線と線分の比の逆",
    entities={"A": "Point", "B": "Point", "C": "Point", "D": "Point", "E": "Point",
              "R1": "Scalar", "R2": "Scalar",
              "L_DE": "Line", "L_BC": "Line", "Dir_DE": "Direction", "Dir_BC": "Direction"},
    patterns=[
        FactPattern("Identical", ["R1", "R2"], target_type="Scalar"),
        FactPattern("DefinedBy", ["A", "D", "B", "R1"], target_type="AffineRatio"),
        FactPattern("DefinedBy", ["A", "E", "C", "R2"], target_type="AffineRatio"),
        DistinctPattern(["A", "B", "C", "D", "E"]),
        FactPattern("Collinear", ["A", "D", "B"]),
        FactPattern("Collinear", ["A", "E", "C"]),
        NotPattern(FactPattern("Collinear", ["A", "B", "C"]))
    ],
    constructions=[
        ConstructTemplate("LineThroughPoints", ["D", "E"], "Line", "L_DE"),
        ConstructTemplate("LineThroughPoints", ["B", "C"], "Line", "L_BC"),
        ConstructTemplate("DirectionOf", ["L_DE"], "Direction", "Dir_DE"),
        ConstructTemplate("DirectionOf", ["L_BC"], "Direction", "Dir_BC")
    ],
    conclusions=[
        FactTemplate("Identical", ["Dir_DE", "Dir_BC"], target_type="Direction")
    ]
)

# ==========================================
# 🌟 登録リスト
# ==========================================
THEOREMS = [
    THEOREM_CYCLIC_ANGLES,
    THEOREM_CONVERSE_CYCLIC,
    THEOREM_IDENTICAL_LINES_R,
    THEOREM_IDENTICAL_LINES_L,
    THEOREM_MIDPOINT_PARALLEL,
    THEOREM_RIGHT_TRIANGLE_MIDPOINT,
    THEOREM_RATIO_TO_PARALLEL
]
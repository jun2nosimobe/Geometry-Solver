# theorems.py

from logic_core import (
    TheoremDef, FactPattern, NotPattern, CustomPattern,
    ConstructTemplate, FactTemplate, get_rep, get_subentity, DistinctPattern,
)

# ==========================================
# 🌟 ヘルパー関数 (メネラウス用)
# ==========================================
def are_collinear_egraph(p1, p2, p3):
    p1, p2, p3 = get_rep(p1), get_rep(p2), get_rep(p3)
    return bool(get_subentity(p1, "Line") & get_subentity(p2, "Line") & get_subentity(p3, "Line"))

def get_constant_value(scalar_entity):
    comp = get_rep(scalar_entity).get_best_component()
    if not comp: return None
    for d in comp.definitions:
        if d.def_type == "Constant": return d.parents[0] 
    return None

def get_or_create_constant(val, env):
    from mmp_core import ModInt, create_geo_entity
    val_mod = ModInt(val) if not isinstance(val, ModInt) else val
    for n in env.nodes:
        if getattr(get_rep(n), 'entity_type', '') == "Scalar":
            c = get_constant_value(n)
            if c is not None and c == val_mod: return get_rep(n)
    name = f"Const_{val_mod.value}"
    new_const = create_geo_entity("Constant", [val_mod], name=name, env=env)
    env.nodes.append(new_const)
    return new_const

# ==========================================
# 🌟 定理の定義 (Declarative Rules)
# ==========================================

# --- 1. 円周角の定理 ---
THEOREM_CYCLIC_ANGLES = TheoremDef(
    name="円周角の定理",
    entities={"A": "Point", "B": "Point", "C": "Point", "D": "Point",
              "L_CA": "Line", "L_CB": "Line", "L_DA": "Line", "L_DB": "Line",
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
        ConstructTemplate("AnglePair", ["L_CA", "L_CB"], "Angle", "AngC"),
        ConstructTemplate("AnglePair", ["L_DA", "L_DB"], "Angle", "AngD")
    ],
    conclusions=[
        FactTemplate("Identical", ["AngC", "AngD"], target_type="Angle")
    ]
)

# --- 2. 円周角の定理の逆 ---
THEOREM_CONVERSE_CYCLIC = TheoremDef(
    name="円周角の定理の逆",
    entities={"A": "Point", "B": "Point", "C": "Point", "D": "Point",
              "L_CA": "Line", "L_CB": "Line", "L_DA": "Line", "L_DB": "Line",
              "AngC": "Angle", "AngD": "Angle"},
    patterns=[
        # 🌟 最強の絞り込み: E-Graph上の角度の一致から逆算
        FactPattern("Identical", ["AngC", "AngD"], target_type="Angle"),
        
        FactPattern("DefinedBy", ["L_CA", "L_CB", "AngC"], target_type="AnglePair"),
        DistinctPattern(["L_CA", "L_CB"]),
        FactPattern("DefinedBy", ["L_DA", "L_DB", "AngD"], target_type="AnglePair"),
        DistinctPattern(["L_DA", "L_DB", "L_CA", "L_CB"]),
        
        # 🌟 交点を CommonEntity (O(1)の積集合) で直撃
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
# --- 3. 直線の一致条件 (平行線公準: 方向ベース) ---
THEOREM_IDENTICAL_LINES = TheoremDef(
    name="直線の一致条件(方向)",
    entities={"P": "Point", "L1": "Line", "L2": "Line", "Dir": "Direction"},
    patterns=[
        # 1. 2つの直線が同じ方向(平行)であることを確認
        FactPattern("DefinedBy", ["L1", "Dir"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["L2", "Dir"], target_type="DirectionOf"),
        DistinctPattern(["L1", "L2"]),
        
        # 2. その2直線が交点Pを持つか(O(1))確認
        FactPattern("CommonEntity", ["L1", "L2", "P"], target_type="Point")
    ],
    conclusions=[
        FactTemplate("Identical", ["L1", "L2"], target_type="Line")
    ]
)
# --- 3-a. 直線の一致条件 (右共通) ---
THEOREM_IDENTICAL_LINES_R = TheoremDef(
    name="直線の一致条件(右共通)",
    entities={"P": "Point", "L1": "Line", "L2": "Line", "M": "Line", "Ang1": "Angle", "Ang2": "Angle"},
    patterns=[
        FactPattern("Identical", ["Ang1", "Ang2"], target_type="Angle"),
        FactPattern("DefinedBy", ["L1", "M", "Ang1"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["L2", "M", "Ang2"], target_type="AnglePair"),
        DistinctPattern(["L1", "L2", "M"]),
        # L1 と L2 が点Pを共有している
        FactPattern("Connected", [["P"], "L1"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", [["P"], "L2"], target_type="Line", sub_type="Point")
    ],
    conclusions=[
        FactTemplate("Identical", ["L1", "L2"], target_type="Line")
    ]
)

# --- 3-b. 直線の一致条件 (左共通) ---
THEOREM_IDENTICAL_LINES_L = TheoremDef(
    name="直線の一致条件(左共通)",
    entities={"P": "Point", "L1": "Line", "L2": "Line", "M": "Line", "Ang1": "Angle", "Ang2": "Angle"},
    patterns=[
        FactPattern("Identical", ["Ang1", "Ang2"], target_type="Angle"),
        FactPattern("DefinedBy", ["M", "L1", "Ang1"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["M", "L2", "Ang2"], target_type="AnglePair"),
        DistinctPattern(["L1", "L2", "M"]),
        # L1 と L2 が点Pを共有している
        FactPattern("Connected", [["P"], "L1"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", [["P"], "L2"], target_type="Line", sub_type="Point")
    ],
    conclusions=[
        FactTemplate("Identical", ["L1", "L2"], target_type="Line")
    ]
)
# --- 4. 有向角の一致から平行(方向の同一化)へ ---
# ∠(L1, M) = ∠(L2, M) ならば L1 // L2
THEOREM_ANGLES_TO_DIR_R = TheoremDef(
    name="同位角による平行判定(右共通)",
    entities={"L1": "Line", "L2": "Line", "M": "Line",
              "Ang1": "Angle", "Ang2": "Angle",
              "Dir1": "Direction", "Dir2": "Direction"},
    patterns=[
        FactPattern("Identical", ["Ang1", "Ang2"], target_type="Angle"),
        FactPattern("DefinedBy", ["L1", "M", "Ang1"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["L2", "M", "Ang2"], target_type="AnglePair"),
        DistinctPattern(["L1", "L2", "M"])
    ],
    constructions=[
        ConstructTemplate("DirectionOf", ["L1"], "Direction", "Dir1"),
        ConstructTemplate("DirectionOf", ["L2"], "Direction", "Dir2")
    ],
    conclusions=[
        FactTemplate("Identical", ["Dir1", "Dir2"], target_type="Direction")
    ]
)

# ∠(M, L1) = ∠(M, L2) ならば L1 // L2
THEOREM_ANGLES_TO_DIR_L = TheoremDef(
    name="同位角による平行判定(左共通)",
    entities={"L1": "Line", "L2": "Line", "M": "Line",
              "Ang1": "Angle", "Ang2": "Angle",
              "Dir1": "Direction", "Dir2": "Direction"},
    patterns=[
        FactPattern("Identical", ["Ang1", "Ang2"], target_type="Angle"),
        FactPattern("DefinedBy", ["M", "L1", "Ang1"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["M", "L2", "Ang2"], target_type="AnglePair"),
        DistinctPattern(["L1", "L2", "M"])
    ],
    constructions=[
        ConstructTemplate("DirectionOf", ["L1"], "Direction", "Dir1"),
        ConstructTemplate("DirectionOf", ["L2"], "Direction", "Dir2")
    ],
    conclusions=[
        FactTemplate("Identical", ["Dir1", "Dir2"], target_type="Direction")
    ]
)

# --- 5. 平行(方向の同一)から有向角の一致へ (右共通) ---
THEOREM_DIR_TO_ANGLES_R = TheoremDef(
    name="平行線の同位角(Right)",
    entities={"L1": "Line", "L2": "Line", "M": "Line", "Dir": "Direction",
              "Ang1": "Angle", "Ang2": "Angle"},
    patterns=[
        # 1. L1 と L2 が平行であることを確認
        FactPattern("DefinedBy", ["L1", "Dir"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["L2", "Dir"], target_type="DirectionOf"),
        DistinctPattern(["L1", "L2"]),
        
        # 2. 🌟 解決策: L1 と交わって角度(Ang1)を作っている直線 M を E-Graph から見つける
        FactPattern("DefinedBy", ["L1", "M", "Ang1"], target_type="AnglePair"),
        DistinctPattern(["L1", "L2", "M"])
    ],
    constructions=[
        # 3. L1 側に角度があるなら、平行な L2 側にも同じ向きの角度を自動生成(または取得)する
        ConstructTemplate("AnglePair", ["L2", "M"], "Angle", "Ang2")
    ],
    conclusions=[
        # 4. それらを Identical としてマージ
        FactTemplate("Identical", ["Ang1", "Ang2"], target_type="Angle")
    ]
)

# --- 5-b. 平行(方向の同一)から有向角の一致へ (左共通) ---
THEOREM_DIR_TO_ANGLES_L = TheoremDef(
    name="平行線の同位角(Left)",
    entities={"L1": "Line", "L2": "Line", "M": "Line", "Dir": "Direction",
              "Ang1": "Angle", "Ang2": "Angle"},
    patterns=[
        FactPattern("DefinedBy", ["L1", "Dir"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["L2", "Dir"], target_type="DirectionOf"),
        DistinctPattern(["L1", "L2"]),
        
        # 🌟 左側に M があるパターンの角度が存在するか探す
        FactPattern("DefinedBy", ["M", "L1", "Ang1"], target_type="AnglePair"),
        DistinctPattern(["L1", "L2", "M"])
    ],
    constructions=[
        ConstructTemplate("AnglePair", ["M", "L2"], "Angle", "Ang2")
    ],
    conclusions=[
        FactTemplate("Identical", ["Ang1", "Ang2"], target_type="Angle")
    ]
)

# --- 4. 平行線の性質 (Direction) ---
THEOREM_PARALLEL_ANGLES = TheoremDef(
    name="平行線の性質(Direction)",
    entities={"L1": "Line", "L2": "Line", "M": "Line", "Dir": "Direction",
              "Ang1": "Angle", "Ang2": "Angle"},
    patterns=[
        FactPattern("DefinedBy", ["L1", "Dir"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["L2", "Dir"], target_type="DirectionOf"),
        DistinctPattern(["L1", "L2", "M"])
    ],
    constructions=[
        ConstructTemplate("AnglePair", ["L1", "M"], "Angle", "Ang1"),
        ConstructTemplate("AnglePair", ["L2", "M"], "Angle", "Ang2")
    ],
    conclusions=[
        FactTemplate("Identical", ["Ang1", "Ang2"], target_type="Angle")
    ]
)

# --- 5. 平行線と線分の比 ---
THEOREM_PARALLEL_TO_RATIO = TheoremDef(
    name="平行線と線分の比",
    entities={"A": "Point", "B": "Point", "C": "Point", "D": "Point", "E": "Point",
              "L1": "Line", "L2": "Line", "Dir": "Direction",
              "R1": "Scalar", "R2": "Scalar"},
    patterns=[
        FactPattern("DefinedBy", ["L1", "Dir"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["L2", "Dir"], target_type="DirectionOf"),
        DistinctPattern(["L1", "L2"]),
        
        FactPattern("Connected", [["D", "E"], "L1"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", [["B", "C"], "L2"], target_type="Line", sub_type="Point"),
        
        FactPattern("Collinear", ["A", "D", "B"]),
        FactPattern("Collinear", ["A", "E", "C"]),
        NotPattern(FactPattern("Collinear", ["A", "B", "C"]))
    ],
    constructions=[
        ConstructTemplate("AffineRatio", ["A", "D", "B"], "Scalar", "R1"),
        ConstructTemplate("AffineRatio", ["A", "E", "C"], "Scalar", "R2")
    ],
    conclusions=[
        FactTemplate("Identical", ["R1", "R2"], target_type="Scalar")
    ]
)

# --- 6. 平行線と線分の比の逆 ---
THEOREM_RATIO_TO_PARALLEL = TheoremDef(
    name="平行線と線分の比の逆",
    entities={"A": "Point", "B": "Point", "C": "Point", "D": "Point", "E": "Point",
              "R1": "Scalar", "R2": "Scalar",
              "L_DE": "Line", "L_BC": "Line", "Dir_DE": "Direction", "Dir_BC": "Direction"},
    patterns=[
        # 🌟 比の一致から逆算
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

# --- 7. 二等辺三角形の底角 ---
THEOREM_ISOSCELES_BASE = TheoremDef(
    name="二等辺三角形の底角",
    entities={"P": "Point", "X": "Point", "Y": "Point",
              "Len_PX": "Scalar", "Len_PY": "Scalar",
              "L_PX": "Line", "L_PY": "Line", "L_XY": "Line",
              "AngX": "Angle", "AngY": "Angle"},
    patterns=[
        # 🌟 長さの一致から逆算
        FactPattern("Identical", ["Len_PX", "Len_PY"], target_type="Scalar"),
        FactPattern("DefinedBy", ["P", "X", "Len_PX"], target_type="LengthSq"),
        FactPattern("DefinedBy", ["P", "Y", "Len_PY"], target_type="LengthSq"),
        DistinctPattern(["P", "X", "Y"]),
        NotPattern(FactPattern("Collinear", ["P", "X", "Y"]))
    ],
    constructions=[
        ConstructTemplate("LineThroughPoints", ["P", "X"], "Line", "L_PX"),
        ConstructTemplate("LineThroughPoints", ["P", "Y"], "Line", "L_PY"),
        ConstructTemplate("LineThroughPoints", ["X", "Y"], "Line", "L_XY"),
        ConstructTemplate("AnglePair", ["L_PX", "L_XY"], "Angle", "AngX"),
        ConstructTemplate("AnglePair", ["L_PY", "L_XY"], "Angle", "AngY")
    ],
    conclusions=[
        FactTemplate("Identical", ["AngX", "AngY"], target_type="Angle")
    ]
)

# --- 8. 二等辺三角形の底角の逆 ---
THEOREM_ISOSCELES_CONVERSE = TheoremDef(
    name="二等辺三角形の底角の逆",
    entities={"P": "Point", "X": "Point", "Y": "Point",
              "L_PX": "Line", "L_PY": "Line", "L_XY": "Line",
              "AngX": "Angle", "AngY": "Angle",
              "Len_PX": "Scalar", "Len_PY": "Scalar"},
    patterns=[
        # 🌟 角度の一致から逆算
        FactPattern("Identical", ["AngX", "AngY"], target_type="Angle"),
        FactPattern("DefinedBy", ["L_PX", "L_XY", "AngX"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["L_PY", "L_XY", "AngY"], target_type="AnglePair"),
        DistinctPattern(["L_PX", "L_PY", "L_XY"]),
        
        # 🌟 Connected の全探索を廃止し、CommonEntity (O(1)の積集合) で交点を直撃
        FactPattern("CommonEntity", ["L_PX", "L_XY", "X"], target_type="Point"),
        FactPattern("CommonEntity", ["L_PY", "L_XY", "Y"], target_type="Point"),
        FactPattern("CommonEntity", ["L_PX", "L_PY", "P"], target_type="Point"),
        DistinctPattern(["P", "X", "Y"]),
        
        NotPattern(FactPattern("Collinear", ["P", "X", "Y"]))
    ],
    constructions=[
        ConstructTemplate("LengthSq", ["P", "X"], "Scalar", "Len_PX"),
        ConstructTemplate("LengthSq", ["P", "Y"], "Scalar", "Len_PY")
    ],
    conclusions=[
        FactTemplate("Identical", ["Len_PX", "Len_PY"], target_type="Scalar")
    ]
)

# --- 9. メネラウスの定理 ---
def evaluate_menelaus(env, bind):
    from mmp_core import ModInt
    R1, R2, R3 = bind.get("R1"), bind.get("R2"), bind.get("R3")
    v1, v2, v3 = get_constant_value(R1), get_constant_value(R2), get_constant_value(R3)
    
    new_binds = []
    if v1 is not None and v2 is not None and v3 is None:
        c = get_or_create_constant(ModInt(-1) / (v1 * v2), env)
        new_binds.append({"Target_R": R3, "Target_Const": c})
    elif v2 is not None and v3 is not None and v1 is None:
        c = get_or_create_constant(ModInt(-1) / (v2 * v3), env)
        new_binds.append({"Target_R": R1, "Target_Const": c})
    elif v3 is not None and v1 is not None and v2 is None:
        c = get_or_create_constant(ModInt(-1) / (v3 * v1), env)
        new_binds.append({"Target_R": R2, "Target_Const": c})
    return new_binds

THEOREM_MENELAUS = TheoremDef(
    name="メネラウスの定理",
    entities={"A": "Point", "B": "Point", "C": "Point", "D": "Point", "E": "Point", "F": "Point",
              "R1": "Scalar", "R2": "Scalar", "R3": "Scalar",
              "Target_R": "Scalar", "Target_Const": "Scalar"},
    patterns=[
        FactPattern("Collinear", ["B", "C", "D"]),
        FactPattern("Collinear", ["C", "A", "E"]),
        FactPattern("Collinear", ["A", "B", "F"]),
        FactPattern("DefinedBy", ["B", "D", "C", "R1"], target_type="AffineRatio"),
        FactPattern("DefinedBy", ["C", "E", "A", "R2"], target_type="AffineRatio"),
        FactPattern("DefinedBy", ["A", "F", "B", "R3"], target_type="AffineRatio"),
        CustomPattern(evaluate_menelaus)
    ],
    conclusions=[
        FactTemplate("Identical", ["Target_R", "Target_Const"], target_type="Scalar")
    ]
)

# --- 12. 有向角の交換則 (Angle Swap) ---
# ∠(L1, L2) = ∠(L3, L4) ⇔ ∠(L1, L3) = ∠(L2, L4)
THEOREM_ANGLE_SWAP = TheoremDef(
    name="有向角の交換則",
    entities={"L1": "Line", "L2": "Line", "L3": "Line", "L4": "Line",
              "Ang12": "Angle", "Ang34": "Angle",
              "Ang13": "Angle", "Ang24": "Angle"},
    patterns=[
        FactPattern("Identical", ["Ang12", "Ang34"], target_type="Angle"),
        FactPattern("DefinedBy", ["L1", "L2", "Ang12"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["L3", "L4", "Ang34"], target_type="AnglePair"),
        DistinctPattern(["L1", "L2", "L3", "L4"])
    ],
    constructions=[
        # 移項した新しい角度ペアを強制的に作図・取得する
        ConstructTemplate("AnglePair", ["L1", "L3"], "Angle", "Ang13"),
        ConstructTemplate("AnglePair", ["L2", "L4"], "Angle", "Ang24")
    ],
    conclusions=[
        FactTemplate("Identical", ["Ang13", "Ang24"], target_type="Angle")
    ]
)

# ==========================================
# 🌟 登録リスト
# ==========================================
THEOREMS = [
    THEOREM_CYCLIC_ANGLES,
    THEOREM_CONVERSE_CYCLIC,
    THEOREM_IDENTICAL_LINES_R, # 🌟 直接判定 (右)
    THEOREM_IDENTICAL_LINES_L, # 🌟 直接判定 (左)
    THEOREM_PARALLEL_TO_RATIO,
    THEOREM_RATIO_TO_PARALLEL,
    THEOREM_ISOSCELES_BASE,
    THEOREM_ISOSCELES_CONVERSE
]
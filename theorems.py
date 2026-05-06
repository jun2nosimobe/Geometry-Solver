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

# ==========================================
# 定理: 円周角の定理 (フリップグループによる完全同期版)
# ==========================================
THEOREM_CYCLIC_ANGLES = TheoremDef(
    name="円周角の定理",
    entities={
        "Apex1": "Point", "Apex2": "Point",
        "Base1": "Point", "Base2": "Point",
        "L_A1_B1": "Line", "L_A1_B2": "Line",
        "L_A2_B1": "Line", "L_A2_B2": "Line",
        "Dir_A1_B1": "Direction", "Dir_A1_B2": "Direction",
        "Dir_A2_B1": "Direction", "Dir_A2_B2": "Direction",
        "Ang1": "Angle", "Ang2": "Angle"
    },
    patterns=[
        FactPattern("Concyclic", ["Apex1", "Apex2", "Base1", "Base2"], sub_type="Unordered"),
        DistinctPattern(["Apex1", "Apex2", "Base1", "Base2"]),
        
        FactPattern("Connected", ["Apex1", "L_A1_B1"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["Base1", "L_A1_B1"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["Apex1", "L_A1_B2"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["Base2", "L_A1_B2"], target_type="Line", sub_type="Point"),
        DistinctPattern(["L_A1_B1", "L_A1_B2"]),
        
        FactPattern("Connected", ["Apex2", "L_A2_B1"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["Base1", "L_A2_B1"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["Apex2", "L_A2_B2"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["Base2", "L_A2_B2"], target_type="Line", sub_type="Point"),
        DistinctPattern(["L_A2_B1", "L_A2_B2"]),
        
        FactPattern("DefinedBy", ["L_A1_B1", "Dir_A1_B1"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["L_A1_B2", "Dir_A1_B2"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["L_A2_B1", "Dir_A2_B1"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["L_A2_B2", "Dir_A2_B2"], target_type="DirectionOf"),
        
        # 🌟 変更点1: flip_group="Cyclic" を追加して有向角の向きを同期させる
        FactPattern("DefinedBy", ["Dir_A1_B1", "Dir_A1_B2", "Ang1"], target_type="AnglePair", allow_flip=True, flip_group="Cyclic"),
        FactPattern("DefinedBy", ["Dir_A2_B1", "Dir_A2_B2", "Ang2"], target_type="AnglePair", allow_flip=True, flip_group="Cyclic"),
        
        # 🌟 変更点2: 無駄な自己マージ (Ang1 ≡ Ang1) を探索段階で弾く
        DistinctPattern(["Ang1", "Ang2"])
    ],
    constructions=[],
    conclusions=[
        FactTemplate("Identical", ["Ang1", "Ang2"], target_type="Angle")
    ]
)
# ==========================================
# 定理: 円周角の定理の逆 (Canonical Order 遵守版)
# ==========================================
THEOREM_CONVERSE_CYCLIC= TheoremDef(
    name="円周角の定理の逆",
    entities={
        "Ang1": "Angle", "Ang2": "Angle",
        "Dir_L1": "Direction", "Dir_L2": "Direction",
        "Dir_L3": "Direction", "Dir_L4": "Direction",
        "L1": "Line", "L2": "Line", "L3": "Line", "L4": "Line",
        "P_Apex1": "Point", "P_Apex2": "Point",
        "P_Base1": "Point", "P_Base2": "Point"
    },
    patterns=[
        FactPattern("Identical", ["Ang1", "Ang2"], target_type="Angle"),
        
        # 🌟 最重要: ここでも sub_type="Unordered" を削除！
        FactPattern("DefinedBy", ["Dir_L1", "Dir_L2", "Ang1"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["Dir_L3", "Dir_L4", "Ang2"], target_type="AnglePair"),
        
        FactPattern("Connected", ["L1", "Dir_L1"], target_type="Direction", sub_type="Line"),
        FactPattern("Connected", ["L2", "Dir_L2"], target_type="Direction", sub_type="Line"),
        FactPattern("Connected", ["L3", "Dir_L3"], target_type="Direction", sub_type="Line"),
        FactPattern("Connected", ["L4", "Dir_L4"], target_type="Direction", sub_type="Line"),
        
        DistinctPattern(["L1", "L2", "L3", "L4"]),

        FactPattern("Connected", ["P_Apex1", "L1"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["P_Apex1", "L2"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["P_Apex2", "L3"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["P_Apex2", "L4"], target_type="Line", sub_type="Point"),

        FactPattern("Connected", ["P_Base1", "L1"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["P_Base1", "L3"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["P_Base2", "L2"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["P_Base2", "L4"], target_type="Line", sub_type="Point"),
        

        DistinctPattern(["P_Apex1", "P_Apex2", "P_Base1", "P_Base2"])
    ],
    constructions=[],
    conclusions=[
        FactTemplate("Concyclic", ["P_Apex1", "P_Apex2", "P_Base1", "P_Base2"], target_type="Circle")
    ]
)

# --- 直線の一致条件 ---
THEOREM_IDENTICAL_LINES = TheoremDef(
    name="直線の一致条件",
    entities={"P": "Point", "L1": "Line", "L2": "Line", "Dir": "Direction"},
    patterns=[
        # 1. 同じ方向(Direction)を共有する2直線を O(1) で逆引き
        FactPattern("DefinedBy", ["L1", "Dir"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["L2", "Dir"], target_type="DirectionOf"),
        DistinctPattern(["L1", "L2"]),
        
        # 2. その2直線が共通の交点を持つか確認
        FactPattern("CommonEntity", ["L1", "L2", "P"], target_type="Point")
    ],
    conclusions=[
        FactTemplate("Identical", ["L1", "L2"], target_type="Line")
    ]
)


# ==========================================
# 定理: 同位角による平行判定(右共通)
# ==========================================
THEOREM_ANGLES_TO_DIR_R = TheoremDef(
    name="同位角による平行判定(右共通)",
    entities={"Dir1": "Direction", "Dir2": "Direction", "DirM": "Direction", "Ang": "Angle"},
    patterns=[
        # 🚨 修正: allow_flip=True や sub_type="Unordered" を絶対に書かない！
        FactPattern("DefinedBy", ["Dir1", "DirM", "Ang"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["Dir2", "DirM", "Ang"], target_type="AnglePair"),
        DistinctPattern(["Dir1", "Dir2", "DirM"])
    ],
    conclusions=[
        FactTemplate("Identical", ["Dir1", "Dir2"], target_type="Direction")
    ]
)

# ==========================================
# 定理: 同位角による平行判定(左共通)
# ==========================================
THEOREM_ANGLES_TO_DIR_L = TheoremDef(
    name="同位角による平行判定(左共通)",
    entities={"Dir1": "Direction", "Dir2": "Direction", "DirM": "Direction", "Ang": "Angle"},
    patterns=[
        # 🚨 修正: 同上。厳格に順序を守る。
        FactPattern("DefinedBy", ["DirM", "Dir1", "Ang"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["DirM", "Dir2", "Ang"], target_type="AnglePair"),
        DistinctPattern(["Dir1", "Dir2", "DirM"])
    ],
    conclusions=[
        FactTemplate("Identical", ["Dir1", "Dir2"], target_type="Direction")
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

# ==========================================
# 定理: 直角三角形の斜辺の中線 (最強・最速版) これは上の定理があるから不要では？
# ==========================================
# ==========================================
# 定理: 直角三角形の斜辺の中線 (直線と距離の完全作図版)
# ==========================================
THEOREM_RIGHT_TRIANGLE_MEDIAN = TheoremDef(
    name="直角三角形の斜辺の中線",
    entities={
        "A": "Point", "B": "Point", "C": "Point", "Mid_BC": "Point",
        "L1": "Line", "L2": "Line",
        "Dir1": "Direction", "Dir2": "Direction",
        "Ang_A": "Angle", "Ang90": "Angle"
    },
    patterns=[
        # 1. 90度の特定
        FactPattern("Identical", ["Ang_A", "Ang90"], target_type="Angle"),
        FactPattern("DefinedBy", ["Dir1", "Dir2", "Ang_A"], target_type="AnglePair", sub_type="Unordered"),
        # 2. 直線の特定
        FactPattern("DefinedBy", ["L1", "Dir1"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["L2", "Dir2"], target_type="DirectionOf"),
        # 3. 頂点と斜辺の特定
        FactPattern("Connected", ["A", "L1"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["A", "L2"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["B", "L1"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["C", "L2"], target_type="Line", sub_type="Point"),
        DistinctPattern(["A", "B", "C"]),
        # 4. 中点の特定
        FactPattern("DefinedBy", ["B", "C", "Mid_BC"], target_type="Midpoint")
    ],
    constructions=[
        ConstructTemplate("LineThroughPoints", ["Mid_BC", "A"], "Line", "Line_Median"),
        # 🌟 追加: 中線の方向(Direction)も作図して E-Graph に放り込む
        ConstructTemplate("DirectionOf", ["Line_Median"], "Direction", "Dir_Median"),
        
        ConstructTemplate("LengthSq", ["Mid_BC", "B"], "Scalar", "Dist_MB"),
        ConstructTemplate("LengthSq", ["Mid_BC", "A"], "Scalar", "Dist_MA")
    ],
    conclusions=[
        # 2つの距離が等しいことをマージ (これにより、のちに垂直二等分線の逆定理が発火する)
        FactTemplate("Identical", ["Dist_MB", "Dist_MA"])
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
# 定理: 垂直二等分線上の点は、両端からの距離が等しい
# ==========================================
THEOREM_PERP_BISECTOR_DISTANCE = TheoremDef(
    name="垂直二等分線の距離の等価性",
    entities={"B": "Point", "C": "Point", "Mid_BC": "Point", "LineBC": "Line", "PerpMid": "Line", "P": "Point"},
    patterns=[
        # 1. Mid_BC は B, C の中点 (引数の最後に結果の変数名 "Mid_BC" を追加)
        FactPattern("DefinedBy", ["B", "C", "Mid_BC"], target_type="Midpoint"),
        # 2. LineBC は B, C を通る
        FactPattern("DefinedBy", ["B", "C", "LineBC"], target_type="LineThroughPoints"),
        # 3. PerpMid は Mid_BC を通り LineBC に垂直
        FactPattern("DefinedBy", ["LineBC", "Mid_BC", "PerpMid"], target_type="PerpendicularLine"),
        # 4. 点 P は PerpMid 上にある
        FactPattern("Connected", ["P", "PerpMid"], target_type="Line", sub_type="Point"),
        DistinctPattern(["B", "C", "P"])
    ],
    constructions=[
        ConstructTemplate("LengthSq", ["P", "B"], "Scalar", "Dist_PB"),
        ConstructTemplate("LengthSq", ["P", "C"], "Scalar", "Dist_PC")
    ],
    conclusions=[
        FactTemplate("Identical", ["Dist_PB", "Dist_PC"])
    ]
)

# ==========================================
# 定理: 二等辺三角形の底角の定理 (完全・有向角フリップ同期版)
# ==========================================
THEOREM_ISOSCELES_BASE_ANGLES = TheoremDef(
    name="二等辺三角形の底角",
    entities={
        "A": "Point", "B": "Point", "C": "Point", 
        "Dist_AB": "Scalar", "Dist_AC": "Scalar",
        "LineAB": "Line", "LineAC": "Line", "LineBC": "Line",
        "DirAB": "Direction", "DirAC": "Direction", "DirBC": "Direction",
        "Ang_B": "Angle", "Ang_C": "Angle"
    },
    patterns=[
        # 1. 距離の一致
        FactPattern("DefinedBy", ["A", "B", "Dist_AB"], target_type="LengthSq", sub_type="Unordered"),
        FactPattern("DefinedBy", ["A", "C", "Dist_AC"], target_type="LengthSq", sub_type="Unordered"),
        FactPattern("Identical", ["Dist_AB", "Dist_AC"]),
        DistinctPattern(["A", "B", "C"]),
        
        # 2. 直線と方向の特定 (退化三角形を DistinctPattern で排除)
        FactPattern("DefinedBy", ["A", "B", "LineAB"], target_type="LineThroughPoints", sub_type="Unordered"),
        FactPattern("DefinedBy", ["A", "C", "LineAC"], target_type="LineThroughPoints", sub_type="Unordered"),
        FactPattern("DefinedBy", ["B", "C", "LineBC"], target_type="LineThroughPoints", sub_type="Unordered"),
        FactPattern("DefinedBy", ["LineAB", "DirAB"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["LineAC", "DirAC"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["LineBC", "DirBC"], target_type="DirectionOf"),
        DistinctPattern(["DirAB", "DirAC", "DirBC"]),
        
        # 3. 🚨 角度の取得 (flip_group を使って向きを完全同期)
        FactPattern("DefinedBy", ["DirAB", "DirBC", "Ang_B"], target_type="AnglePair", allow_flip=True, flip_group="Isosceles"),
        FactPattern("DefinedBy", ["DirBC", "DirAC", "Ang_C"], target_type="AnglePair", allow_flip=True, flip_group="Isosceles")
    ],
    constructions=[], # 危険な作図は全廃
    conclusions=[
        FactTemplate("Identical", ["Ang_B", "Ang_C"])
    ]
)
# ==========================================
# 定理: 二等辺三角形の底角の逆 (完全・有向角フリップ同期版)
# ==========================================
THEOREM_ISOSCELES_CONVERSE = TheoremDef(
    name="二等辺三角形の底角の逆",
    entities={
        "A": "Point", "B": "Point", "C": "Point",
        "Ang_B": "Angle", "Ang_C": "Angle",
        "DirAB": "Direction", "DirAC": "Direction", "DirBC": "Direction",
        "LineAB": "Line", "LineAC": "Line", "LineBC": "Line",
        "Dist_AB": "Scalar", "Dist_AC": "Scalar"
    },
    patterns=[
        # 1. 直線と方向の特定
        FactPattern("DefinedBy", ["A", "B", "LineAB"], target_type="LineThroughPoints", sub_type="Unordered"),
        FactPattern("DefinedBy", ["A", "C", "LineAC"], target_type="LineThroughPoints", sub_type="Unordered"),
        FactPattern("DefinedBy", ["B", "C", "LineBC"], target_type="LineThroughPoints", sub_type="Unordered"),
        DistinctPattern(["A", "B", "C"]),
        
        FactPattern("DefinedBy", ["LineAB", "DirAB"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["LineAC", "DirAC"], target_type="DirectionOf"),
        FactPattern("DefinedBy", ["LineBC", "DirBC"], target_type="DirectionOf"),
        DistinctPattern(["DirAB", "DirAC", "DirBC"]),

        # 2. 🚨 角度の取得 (flip_group を使って向きを完全同期)
        FactPattern("DefinedBy", ["DirAB", "DirBC", "Ang_B"], target_type="AnglePair", allow_flip=True, flip_group="IsoscelesConv"),
        FactPattern("DefinedBy", ["DirBC", "DirAC", "Ang_C"], target_type="AnglePair", allow_flip=True, flip_group="IsoscelesConv"),
        
        # 3. 角度の一致
        FactPattern("Identical", ["Ang_B", "Ang_C"], target_type="Angle")
    ],
    constructions=[
        ConstructTemplate("LengthSq", ["A", "B"], "Scalar", "Dist_AB"),
        ConstructTemplate("LengthSq", ["A", "C"], "Scalar", "Dist_AC")
    ],
    conclusions=[
        FactTemplate("Identical", ["Dist_AB", "Dist_AC"])
    ]
)

# ==========================================
# 定理: 垂直二等分線の距離の等価性の逆 (距離が等しければ垂直二等分線上にある)
# ==========================================
THEOREM_PERP_BISECTOR_CONVERSE = TheoremDef(
    name="垂直二等分線の距離の等価性の逆",
    entities={
        "B": "Point", "C": "Point", "Mid_BC": "Point", 
        "LineBC": "Line", "PerpMid": "Line", "P": "Point", 
        "Dist_PB": "Scalar", "Dist_PC": "Scalar"
    },
    patterns=[
        # 1. 垂直二等分線 PerpMid の定義
        FactPattern("DefinedBy", ["B", "C", "Mid_BC"], target_type="Midpoint"),
        FactPattern("DefinedBy", ["B", "C", "LineBC"], target_type="LineThroughPoints"),
        FactPattern("DefinedBy", ["LineBC", "Mid_BC", "PerpMid"], target_type="PerpendicularLine"),
        
        # 2. 点 P が B, C から等距離であること
        FactPattern("DefinedBy", ["P", "B", "Dist_PB"], target_type="LengthSq"),
        FactPattern("DefinedBy", ["P", "C", "Dist_PC"], target_type="LengthSq"),
        FactPattern("Identical", ["Dist_PB", "Dist_PC"]),
        
        DistinctPattern(["B", "C", "P"])
    ],
    conclusions=[
        # ならば、点 P は PerpMid 上に存在する (Connected)
        FactTemplate("Connected", ["P", "PerpMid"], target_type="Line", sub_type="Point")
    ]
)

# ==========================================
# 定理: 2直線の交点の一意性 (最強バージョン)
# ==========================================
THEOREM_UNIQUE_INTERSECTION = TheoremDef(
    name="2直線の交点の一意性",
    entities={"L1": "Line", "L2": "Line", "P_Int": "Point", "P_Test": "Point"},
    patterns=[
        # 1. すでにグラフ上に、L1 と L2 の交点(P_Int) が存在している
        FactPattern("DefinedBy", ["L1", "L2", "P_Int"], target_type="Intersection", sub_type="Unordered"),
        
        # 2. P_Test が L1 と L2 に乗っていることを、直接 Connected で聞くのではなく
        # 「P_Test を通る直線」として L1 と L2 が定義に絡んでいるかを探る
        FactPattern("Connected", ["P_Test", "L1"], target_type="Line", sub_type="Point"),
        FactPattern("Connected", ["P_Test", "L2"], target_type="Line", sub_type="Point"),

        DistinctPattern(["L1", "L2"]),
        DistinctPattern(["P_Int", "P_Test"])
    ],
    constructions=[
        # 🌟 魔法のステップ: P_Test を「L1 と L2 の交点」として強制的に再作図する！
        # (E-Graph は、P_Test が本当に両方の直線に乗っているなら、この新しい交点を P_Test と同じ同値類に置く)
        ConstructTemplate("Intersection", ["L1", "L2"], "Point", "P_New_Int")
    ],
    conclusions=[
        # ならば、もともとあった P_Int と、P_Test は同一人物である
        FactTemplate("Identical", ["P_Int", "P_Test"])
    ]
)

# ==========================================
# 🌟 登録リスト
# ==========================================
THEOREMS = [
    THEOREM_CYCLIC_ANGLES,
    THEOREM_CONVERSE_CYCLIC,
    THEOREM_IDENTICAL_LINES,
    THEOREM_ANGLES_TO_DIR_R,
    THEOREM_ANGLES_TO_DIR_L,
    THEOREM_MIDPOINT_PARALLEL,
    THEOREM_RIGHT_TRIANGLE_MIDPOINT,
    THEOREM_RIGHT_TRIANGLE_MEDIAN,
    THEOREM_RATIO_TO_PARALLEL,
    THEOREM_PERP_BISECTOR_DISTANCE,
    THEOREM_ISOSCELES_BASE_ANGLES,
    THEOREM_ISOSCELES_CONVERSE,
    THEOREM_PERP_BISECTOR_CONVERSE,
    THEOREM_UNIQUE_INTERSECTION 
]
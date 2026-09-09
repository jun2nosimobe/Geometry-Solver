import logging
from logic_core import ProofEnvironment, LogicProver, UniversalRuleEngine, setup_proof_logger, FactTemplate
from theorems import TheoremDef, FactPattern, DistinctPattern
from mmp_core import GeoEntity, LogicalComponent, Definition, create_geo_entity

# ==========================================
# 1. 🌟 有向角の加法性 (最適化版) の定義
# ==========================================
THEOREM_DIRECTED_ANGLE_ADDITION = TheoremDef(
    name="有向角の加法性",
    entities={
        "Ang12": "Angle", "Ang45": "Angle", "Ang23": "Angle", "Ang56": "Angle",
        "D1": "Direction", "D2": "Direction", "D3": "Direction",
        "D4": "Direction", "D5": "Direction", "D6": "Direction",
        "Ang13": "Angle", "Ang46": "Angle"
    },
    patterns=[
        # 1. 「すでに等しい」角度のペアから検索 (爆速化の要)
        FactPattern("Identical", ["Ang12", "Ang45"], target_type="Angle"),
        FactPattern("Identical", ["Ang23", "Ang56"], target_type="Angle"),

        # 2. 方向ベクトルを逆引き
        FactPattern("DefinedBy", ["D1", "D2", "Ang12"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["D4", "D5", "Ang45"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["D2", "D3", "Ang23"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["D5", "D6", "Ang56"], target_type="AnglePair"),

        # 3. 退化(同じ方向)を排除
        DistinctPattern(["D1", "D2", "D3"]),
        DistinctPattern(["D4", "D5", "D6"]),

        # 4. 全体をまたぐ角度の取得
        FactPattern("DefinedBy", ["D1", "D3", "Ang13"], target_type="AnglePair"),
        FactPattern("DefinedBy", ["D4", "D6", "Ang46"], target_type="AnglePair")
    ],
    constructions=[],
    conclusions=[
        FactTemplate("Identical", ["Ang13", "Ang46"])
    ]
)

# ==========================================
# 2. ロガーとエンジンの初期化
# ==========================================
# 詳細な探索数を見たいので is_debug=True に設定
setup_proof_logger("test_angle_add", is_debug=True)
logger = logging.getLogger("GeometryProver")

env = ProofEnvironment(enable_numerical_debug=False)
prover = LogicProver(env, [THEOREM_DIRECTED_ANGLE_ADDITION])
engine = UniversalRuleEngine(env, prover)

logger.info("=== 有向角の加法性 純粋テスト構築開始 ===")

# ==========================================
# 3. E-Graph への図形シード構築関数
# ==========================================
def make_angle_system(prefix):
    """3つの方向ベクトルと、それらがなす3つの有向角を生成"""
    dirs = []
    for i in range(1, 4):
        d = GeoEntity("Direction", name=f"D_{prefix}{i}")
        d.importance = 10.0
        d.components.append(LogicalComponent(initial_def=Definition("Given", [])))
        env.nodes.append(d)
        dirs.append(d)

    d1, d2, d3 = dirs

    # 3つの有向角(隣接するパーツ2つと、全体をまたぐ1つ)を生成
    ang12 = create_geo_entity("AnglePair", [d1, d2], name=f"Ang_{prefix}12", env=env)
    ang23 = create_geo_entity("AnglePair", [d2, d3], name=f"Ang_{prefix}23", env=env)
    ang13 = create_geo_entity("AnglePair", [d1, d3], name=f"Ang_{prefix}13", env=env)
    
    env.nodes.extend([ang12, ang23, ang13])
    return d1, d2, d3, ang12, ang23, ang13

# システムA (例: 三角形の内角の一部)
dA1, dA2, dA3, angA_12, angA_23, angA_13 = make_angle_system("A")

# システムB (例: 別の三角形の内角の一部)
dB4, dB5, dB6, angB_45, angB_56, angB_46 = make_angle_system("B")

# ==========================================
# 4. テストケースの注入 (前提条件)
# ==========================================
logger.info("💡 初期条件として、2つのパーツの角をそれぞれマージします")
env.merge_entities_logically(angA_12, angB_45)
env.merge_entities_logically(angA_23, angB_56)

# ==========================================
# 5. エンジンの実行
# ==========================================
logger.info("=== 評価開始 ===")
engine.run_all(prover.theorems)
logger.info("=== 評価終了 ===")

prover.print_proof_trace()
print("\n✅ 実行完了。 result/proof_test_angle_add.log を確認してください。")
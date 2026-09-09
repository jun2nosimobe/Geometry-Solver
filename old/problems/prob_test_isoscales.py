import logging
from logic_core import ProofEnvironment, LogicProver, UniversalRuleEngine, setup_proof_logger
from theorems import THEOREM_ISOSCELES_BASE_ANGLES, THEOREM_ISOSCELES_CONVERSE
from mmp_core import GeoEntity, LogicalComponent, Definition, create_geo_entity, link_logical_incidence

# ==========================================
# 1. ロガーとエンジンの初期化
# ==========================================
setup_proof_logger("test_isosceles")
logger = logging.getLogger("GeometryProver")

# 数値デバッグはオフ（純粋な論理マッチングのテスト）
env = ProofEnvironment(enable_numerical_debug=False)

# 🌟 登録する定理は「二等辺三角形」に関する2つだけ
prover = LogicProver(env, [THEOREM_ISOSCELES_BASE_ANGLES, THEOREM_ISOSCELES_CONVERSE])
engine = UniversalRuleEngine(env, prover)

logger.info("=== 二等辺三角形の底角定理・逆 純粋テスト構築開始 ===")

# ==========================================
# 2. E-Graph への図形シード構築関数
# ==========================================
def make_triangle_env(prefix):
    """プレフィックス(T1_, T2_)をつけて三角形の点・線・方向・角・長さを生成"""
    pts = {}
    for pt_name in ["A", "B", "C"]:
        name = f"{prefix}{pt_name}"
        # 🚨 Unknownにならないよう明示的にPoint型として生成
        pt = GeoEntity("Point", name=name)
        pt.base_importance = 10.0
        pt.components.append(LogicalComponent(initial_def=Definition("Given", [])))
        env.nodes.append(pt)
        pts[pt_name] = pt

    pA, pB, pC = pts["A"], pts["B"], pts["C"]

    # (B) 3本の直線と方向
    lineAB = create_geo_entity("LineThroughPoints", [pA, pB], name=f"Line_{prefix}AB", env=env)
    lineAC = create_geo_entity("LineThroughPoints", [pA, pC], name=f"Line_{prefix}AC", env=env)
    lineBC = create_geo_entity("LineThroughPoints", [pB, pC], name=f"Line_{prefix}BC", env=env)
    env.nodes.extend([lineAB, lineAC, lineBC])

    dirAB = create_geo_entity("DirectionOf", [lineAB], name=f"Dir_{prefix}AB", env=env)
    dirAC = create_geo_entity("DirectionOf", [lineAC], name=f"Dir_{prefix}AC", env=env)
    dirBC = create_geo_entity("DirectionOf", [lineBC], name=f"Dir_{prefix}BC", env=env)
    env.nodes.extend([dirAB, dirAC, dirBC])

    # (C) 2つの底角 (AnglePair)
    # 有向角の定義に厳密に従う: ∠B = ∠(AB, BC), ∠C = ∠(BC, AC)
    angB = create_geo_entity("AnglePair", [dirAB, dirBC], name=f"Ang_{prefix}B", env=env)
    angC = create_geo_entity("AnglePair", [dirBC, dirAC], name=f"Ang_{prefix}C", env=env)
    env.nodes.extend([angB, angC])

    # (D) 2つの辺の長さ (LengthSq)
    distAB = create_geo_entity("LengthSq", [pA, pB], name=f"Dist_{prefix}AB", env=env)
    distAC = create_geo_entity("LengthSq", [pA, pC], name=f"Dist_{prefix}AC", env=env)
    env.nodes.extend([distAB, distAC])

    return distAB, distAC, angB, angC


# ==========================================
# 3. テストケースの注入
# ==========================================

# 🟢 【テスト1】底角定理 (辺が等しければ、角が等しい)
dist1_AB, dist1_AC, ang1_B, ang1_C = make_triangle_env("T1_")
# 初期条件として「辺の長さが等しい」ことを E-Graph でマージしておく
env.merge_entities_logically(dist1_AB, dist1_AC)

# 🟢 【テスト2】底角定理の逆 (角が等しければ、辺が等しい)
dist2_AB, dist2_AC, ang2_B, ang2_C = make_triangle_env("T2_")
# 初期条件として「底角が等しい」ことを E-Graph でマージしておく
env.merge_entities_logically(ang2_B, ang2_C)


# ==========================================
# 4. エンジンの実行
# ==========================================
logger.info("=== 評価開始 ===")
engine.run_all(prover.theorems)
logger.info("=== 評価終了 ===")

# トレースをコンソールに出力
prover.print_proof_trace()
print("\n✅ 実行完了。 result/proof_test_isosceles.log を確認してください。")
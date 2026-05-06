import logging
import itertools
from logic_core import ProofEnvironment, LogicProver, UniversalRuleEngine, setup_proof_logger, Fact  # 🌟 Fact を追加
from theorems import THEOREM_CYCLIC_ANGLES
from mmp_core import create_geo_entity, link_logical_incidence


# ==========================================
# 1. ロガーとエンジンの初期化
# ==========================================
# "proof_test_cyclic.log" というログファイルが生成されます
setup_proof_logger("test_cyclic")
logger = logging.getLogger("GeometryProver")

# 数値デバッグはオフ（純粋な論理マッチングとフリップのテスト）
env = ProofEnvironment(enable_numerical_debug=False)

# 🌟 登録する定理は「円周角の定理」ただ1つだけ！
prover = LogicProver(env, [THEOREM_CYCLIC_ANGLES])
engine = UniversalRuleEngine(env, prover)

logger.info("=== 4点共円（円周角の定理）純粋テスト構築開始 ===")

# ==========================================
# 2. E-Graph への図形シード (初期状態の構築)
# ==========================================
from mmp_core import GeoEntity, LogicalComponent, Definition

pts = {}
for name in ["A", "B", "C", "D"]:
    # 🚨 create_geo_entity ではなく、直接 "Point" 型を指定して生成する
    pt = GeoEntity("Point", name=name)
    pt.base_importance = 10.0
    pt.components.append(LogicalComponent(initial_def=Definition("Given", [])))
    env.nodes.append(pt)
    pts[name] = pt

# (B) 共円 (Circumcircle)
# A,B,C,D すべてが乗っている円を1つ定義
circle = create_geo_entity("Circumcircle", [pts["A"], pts["B"], pts["C"]], name="Circle_ABCD", env=env)
env.nodes.append(circle)
for pt in pts.values():
    link_logical_incidence(pt, circle)

# (C) 6本の直線と、その方向 (Direction)
dirs = {}
for p1, p2 in itertools.combinations(["A", "B", "C", "D"], 2):
    # 直線 (例: Line_AB)
    line_name = f"Line_{p1}{p2}"
    line = create_geo_entity("LineThroughPoints", [pts[p1], pts[p2]], name=line_name, env=env)
    env.nodes.append(line)
    link_logical_incidence(pts[p1], line)
    link_logical_incidence(pts[p2], line)
    
    # 方向 (例: Dir_AB)
    dir_name = f"Dir_{p1}{p2}"
    direction = create_geo_entity("DirectionOf", [line], name=dir_name, env=env)
    env.nodes.append(direction)
    # 逆引き用に両方のキーで保存しておく
    dirs[(p1, p2)] = direction
    dirs[(p2, p1)] = direction

# (D) 有向角 (AnglePair) の総当たり生成
# 各頂点 (Apex) について、他の3点との方向ベクトルのなす角を作る
for apex in ["A", "B", "C", "D"]:
    bases = [p for p in ["A", "B", "C", "D"] if p != apex]
    for b1, b2 in itertools.combinations(bases, 2):
        d1 = dirs[(apex, b1)]
        d2 = dirs[(apex, b2)]
        
        # 正規順序 (Canonical) を気にせず、とりあえず両方の順序で作って E-Graph に放り込む
        # ※実際の geom.py では抽出ロジックで Canonical なものだけが入るはずですが、
        # 今回はテストなので強制シードします。
        ang_name = f"AnglePair_{d1.name}_{d2.name}"
        ang = create_geo_entity("AnglePair", [d1, d2], name=ang_name, env=env)
        env.nodes.append(ang)

concyclic_fact = Fact("Concyclic", [pts["A"], pts["B"], pts["C"], pts["D"]])
concyclic_fact.is_proven = True          # 🚨 重要: MMP予想ではなく「証明済み」とする
concyclic_fact.is_mmp_conjecture = False # 🚨 重要: 予想フラグを折る
prover.facts.append(concyclic_fact)

# ==========================================
# 3. エンジンの実行
# ==========================================
logger.info("=== 評価開始 ===")
engine.run_all(prover.theorems)
logger.info("=== 評価終了 ===")

# トレースをコンソールにも出力
prover.print_proof_trace()
print("\n✅ 実行完了。 result/proof_test_cyclic.log を確認してください。")
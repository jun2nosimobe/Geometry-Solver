import logging
from logic_core import ProofEnvironment, LogicProver, UniversalRuleEngine, setup_proof_logger, Fact
from theorems import THEOREM_ALTERNATE_SEGMENT_CONVERSE
from mmp_core import GeoEntity, LogicalComponent, Definition, create_geo_entity, link_logical_incidence # 🌟 追加

setup_proof_logger("test_alt_seg_conv", is_debug=True)
logger = logging.getLogger("GeometryProver")

env = ProofEnvironment(enable_numerical_debug=False)
prover = LogicProver(env, [THEOREM_ALTERNATE_SEGMENT_CONVERSE])
engine = UniversalRuleEngine(env, prover)

logger.info("=== 接弦定理の逆 純粋論理テスト開始 ===")

# 1. 点の生成
pts = {}
for name in ["A", "B", "D"]:
    pt = GeoEntity("Point", name=name)
    pt.base_importance = 10.0
    pt.components.append(LogicalComponent(initial_def=Definition("Given", [])))
    env.nodes.append(pt)
    pts[name] = pt

# 2. 円 C と 直線 L の生成
circle = create_geo_entity("Circumcircle", [pts["A"], pts["B"], pts["D"]], name="C", env=env)
link_logical_incidence(pts["A"], circle) # 🌟 物理リンクを追加
link_logical_incidence(pts["B"], circle)
link_logical_incidence(pts["D"], circle)

# 接線 L を作成（"Given" として独立した実体にする）
line_L = GeoEntity("Line", name="L")
line_L.base_importance = 10.0
line_L.components.append(LogicalComponent(initial_def=Definition("Given", [])))
env.nodes.append(line_L)

# LはAを通る (接線かどうかはまだ不明)
link_logical_incidence(pts["A"], line_L) # 🌟 物理リンクを追加
# 🚨 逆定理なので、L と C の link_logical_incidence は意図的に書かない！(それが結論だから)

# 3. 弦となる直線の生成
lines = {}
for p1, p2 in [("A", "B"), ("A", "D"), ("B", "D")]:
    l = create_geo_entity("LineThroughPoints", [pts[p1], pts[p2]], name=f"Line_{p1}{p2}", env=env)
    link_logical_incidence(pts[p1], l) # 🌟 物理リンクを追加
    link_logical_incidence(pts[p2], l) # 🌟 物理リンクを追加
    lines[(p1, p2)] = l

# 4. 方向ベクトルの生成
dirs = {}
dir_L = create_geo_entity("DirectionOf", [line_L], name="Dir_L", env=env)
link_logical_incidence(line_L, dir_L) # 🌟 物理リンクを追加

for (p1, p2), l in lines.items():
    d = create_geo_entity("DirectionOf", [l], name=f"Dir_{p1}{p2}", env=env)
    link_logical_incidence(l, d) # 🌟 物理リンクを追加
    dirs[(p1, p2)] = d

# 5. 有向角の生成
ang_L_AB = create_geo_entity("AnglePair", [dir_L, dirs[("A", "B")]], name="Ang_L_AB", env=env)
ang_AD_BD = create_geo_entity("AnglePair", [dirs[("A", "D")], dirs[("B", "D")]], name="Ang_AD_BD", env=env)

env.merge_entities_logically(ang_L_AB, ang_AD_BD)

# ==========================================
# 🚨 E-Graph に Fact を強制シード
# ==========================================
initial_facts = []

for f in initial_facts:
    f.is_proven = True
    f.is_mmp_conjecture = False
    prover.facts.append(f)

# 🔍 X-Ray デバッグ (Connectedが埋まっているか確認用)
print("\n" + "="*60)
print("🔍 [X-Ray デバッガ] E-Graph 完全ダンプ")
from logic_core import get_rep
for node in env.nodes:
    rep = get_rep(node)
    e_type = getattr(rep, 'entity_type', 'Unknown')
    comp = rep.get_best_component()
    print(f"  🟢 {rep.name} (Type: {e_type})")
    connected_names = [getattr(n, 'name', '?') for n in getattr(rep, 'subobjects', [])]
    if connected_names: print(f"     - Connected: {connected_names}")
    if comp:
        for d in comp.definitions:
            parent_names = [getattr(p, 'name', '?') for p in d.parents]
            print(f"     - DefinedBy: {d.def_type}({', '.join(parent_names)})")
print("="*60 + "\n")

# エンジンの実行
logger.info("=== 評価開始 ===")
engine.run_all(prover.theorems)

prover.print_proof_trace()
print("\n✅ 実行完了。")
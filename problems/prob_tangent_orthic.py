# problems/prob_tangent_orthic.py
from mmp_core import create_geo_entity
from proof_manager import Fact

def setup_problem(env):
    all_vars = ["t1", "t2", "t3", "t4", "t5", "t6"]
    
    # 1. 三角形の3頂点と辺
    A = create_geo_entity("FreePoint", ["t1", "t2"], name="A", env=env)
    B = create_geo_entity("FreePoint", ["t3", "t4"], name="B", env=env)
    C = create_geo_entity("FreePoint", ["t5", "t6"], name="C", env=env)
    
    Line_AB = create_geo_entity("LineThroughPoints", [A, B], name="Line_AB", env=env)
    Line_BC = create_geo_entity("LineThroughPoints", [B, C], name="Line_BC", env=env)
    Line_CA = create_geo_entity("LineThroughPoints", [C, A], name="Line_CA", env=env)
    
    # 2. 頂点Aにおける外接円と接線
    Circ = create_geo_entity("Circumcircle", [A, B, C], name="Circ_ABC", env=env)
    Tan_A = create_geo_entity("TangentLine", [Circ, A], name="Tan_A", env=env)
    
    # 3. 頂点B, Cからの垂線と垂足 D, E
    Perp_B = create_geo_entity("PerpendicularLine", [Line_CA, B], name="Perp_B", env=env)
    Perp_C = create_geo_entity("PerpendicularLine", [Line_AB, C], name="Perp_C", env=env)
    
    D = create_geo_entity("Intersection", [Line_CA, Perp_B], name="D", env=env)
    E = create_geo_entity("Intersection", [Line_AB, Perp_C], name="E", env=env)
    
    # 4. 垂足D, Eを結ぶ直線
    Line_DE = create_geo_entity("LineThroughPoints", [D, E], name="Line_DE", env=env)
    
    # 目標: 接線 Tan_A と 直線 DE が平行であること (方向ベクトルが一致)
    Dir_Tan_A = create_geo_entity("DirectionOf", [Tan_A], name="Dir_Tan_A", env=env)
    Dir_DE = create_geo_entity("DirectionOf", [Line_DE], name="Dir_DE", env=env)
    
    target_fact = Fact("Identical", [Dir_Tan_A, Dir_DE])
    initial_facts = []
    
    return all_vars, target_fact, initial_facts
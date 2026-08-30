from mmp_core import create_geo_entity
from logic_core import Fact

def setup_problem(env):
    all_vars = ["t1", "t2", "t3", "t4", "t5", "t6", "t7", "t8"]
    
    A = create_geo_entity("FreePoint", ["t1", "t2"], name="A", env=env)
    B = create_geo_entity("FreePoint", ["t3", "t4"], name="B", env=env)
    C = create_geo_entity("FreePoint", ["t5", "t6"], name="C", env=env)
    D = create_geo_entity("FreePoint", ["t7", "t8"], name="D", env=env)
    
    P = create_geo_entity("Midpoint", [A, B], name="P", env=env)
    Q = create_geo_entity("Midpoint", [B, C], name="Q", env=env)
    R = create_geo_entity("Midpoint", [C, D], name="R", env=env)
    S = create_geo_entity("Midpoint", [D, A], name="S", env=env)
    
    L_PQ = create_geo_entity("LineThroughPoints", [P, Q], name="Line_PQ", env=env)
    L_SR = create_geo_entity("LineThroughPoints", [S, R], name="Line_SR", env=env)
    Dir_PQ = create_geo_entity("DirectionOf", [L_PQ], name="Dir_PQ", env=env)
    Dir_SR = create_geo_entity("DirectionOf", [L_SR], name="Dir_SR", env=env)
    
    target_fact = Fact("Identical", [Dir_PQ, Dir_SR])
    initial_facts = [] # 仮定として与えるべき初期ファクトのリスト
    
    return all_vars, target_fact, initial_facts
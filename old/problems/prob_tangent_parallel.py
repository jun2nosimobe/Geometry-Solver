from mmp_core import create_geo_entity
from logic_core import Fact

def setup_problem(env):
    all_vars = ["t1", "t2", "t3", "t4", "t5", "t6"]
    
    A = create_geo_entity("FreePoint", ["t1", "t2"], name="A", env=env)
    B = create_geo_entity("FreePoint", ["t3", "t4"], name="B", env=env)
    C = create_geo_entity("FreePoint", ["t5", "t6"], name="C", env=env)
    
    Circ = create_geo_entity("Circumcircle", [A, B, C], name="Circ", env=env)
    
    Tan_A = create_geo_entity("TangentLine", [Circ, A], name="Tan_A", env=env)
    Line_BC = create_geo_entity("LineThroughPoints", [B, C], name="Line_BC", env=env)
    
    Dir_Tan = create_geo_entity("DirectionOf", [Tan_A], name="Dir_Tan", env=env)
    L_AB = create_geo_entity("LineThroughPoints", [A, B], name="L_AB", env=env)
    Dir_AB = create_geo_entity("DirectionOf", [L_AB], name="Dir_AB", env=env)
    Ang_Tan_AB = create_geo_entity("AnglePair", [Dir_Tan, Dir_AB], name="Ang_Tan_AB", env=env)
    
    Dir_BC = create_geo_entity("DirectionOf", [Line_BC], name="Dir_BC", env=env)
    L_CA = create_geo_entity("LineThroughPoints", [C, A], name="L_CA", env=env)
    Dir_CA = create_geo_entity("DirectionOf", [L_CA], name="Dir_CA", env=env)
    Ang_CA_BC = create_geo_entity("AnglePair", [Dir_CA, Dir_BC], name="Ang_CA_BC", env=env)
    
    target_fact = Fact("Identical", [Ang_Tan_AB, Ang_CA_BC])
    initial_facts = []
    
    return all_vars, target_fact, initial_facts
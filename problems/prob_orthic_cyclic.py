from mmp_core import create_geo_entity
from logic_core import Fact

def setup_problem(env):
    all_vars = ["t1", "t2", "t3", "t4", "t5", "t6"]
    
    A = create_geo_entity("FreePoint", ["t1", "t2"], name="A", env=env)
    B = create_geo_entity("FreePoint", ["t3", "t4"], name="B", env=env)
    C = create_geo_entity("FreePoint", ["t5", "t6"], name="C", env=env)
    
    Line_BC = create_geo_entity("LineThroughPoints", [B, C], name="Line_BC", env=env)
    Line_CA = create_geo_entity("LineThroughPoints", [C, A], name="Line_CA", env=env)
    Line_AB = create_geo_entity("LineThroughPoints", [A, B], name="Line_AB", env=env)
    
    Perp_A = create_geo_entity("PerpendicularLine", [Line_BC, A], name="Perp_A", env=env)
    Perp_B = create_geo_entity("PerpendicularLine", [Line_CA, B], name="Perp_B", env=env)
    
    D = create_geo_entity("Intersection", [Line_BC, Perp_A], name="D", env=env)
    E = create_geo_entity("Intersection", [Line_CA, Perp_B], name="E", env=env)
    
    target_fact = Fact("Concyclic", [A, B, D, E])
    initial_facts = []
    
    return all_vars, target_fact, initial_facts
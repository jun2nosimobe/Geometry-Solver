# problems/prob_euler.py
from mmp_core import GeoEntity, Definition, LogicalComponent, create_geo_entity, link_logical_incidence
from logic_core import Fact

class Variable:
    def __init__(self, name):
        self.name = name
    def evaluate(self, t_dict):
        return t_dict[self]

def setup_problem(env):
    # 三角形の自由度は3つ (A=(0,0), B=(u1,0), C=(u2,u3))
    u1, u2, u3 = Variable('u1'), Variable('u2'), Variable('u3')
    all_vars = ["u1", "u2", "u3"]

    def make_given_point(name, coords_func):
        pt = GeoEntity("Point", name)
        pt._evaluate_given = coords_func
        pt.components.append(LogicalComponent(initial_def=Definition("Given", depth=0)))
        pt.importance = 10.0 # 基準点は重要
        env.nodes.append(pt)
        return pt

    # 1. 基本となる点 A, B, C
    A = make_given_point("A", lambda t: (0, 0, 1))
    B = make_given_point("B", lambda t: (u1.evaluate(t), 0, 1))
    C = make_given_point("C", lambda t: (u2.evaluate(t), u3.evaluate(t), 1))

    # 2. 各辺の直線
    LineBC = create_geo_entity("LineThroughPoints", [B, C], "LineBC", env=env)
    LineCA = create_geo_entity("LineThroughPoints", [C, A], "LineCA", env=env)
    LineAB = create_geo_entity("LineThroughPoints", [A, B], "LineAB", env=env)
    
    # 物理リンク（確実なIncidenceの登録）
    link_logical_incidence(LineBC, B); link_logical_incidence(LineBC, C)
    link_logical_incidence(LineCA, C); link_logical_incidence(LineCA, A)
    link_logical_incidence(LineAB, A); link_logical_incidence(LineAB, B)

    # ==========================================
    # 3. 垂心 H の作図 (垂線の交点)
    # ==========================================
    Perp_A = create_geo_entity("PerpendicularLine", [LineBC, A], "Perp_A", env=env)
    Perp_B = create_geo_entity("PerpendicularLine", [LineCA, B], "Perp_B", env=env)
    H = create_geo_entity("Intersection", [Perp_A, Perp_B], "H", env=env)

    # ==========================================
    # 4. 外心 O の作図 (垂直二等分線の交点)
    # ==========================================
    Mid_BC = create_geo_entity("Midpoint", [B, C], "Mid_BC", env=env)
    Mid_CA = create_geo_entity("Midpoint", [C, A], "Mid_CA", env=env)
    PerpMid_BC = create_geo_entity("PerpendicularLine", [LineBC, Mid_BC], "PerpMid_BC", env=env)
    PerpMid_CA = create_geo_entity("PerpendicularLine", [LineCA, Mid_CA], "PerpMid_CA", env=env)
    O = create_geo_entity("Intersection", [PerpMid_BC, PerpMid_CA], "O", env=env)

    # ==========================================
    # 5. 重心 G の作図 (中線の交点)
    # ==========================================
    Median_A = create_geo_entity("LineThroughPoints", [A, Mid_BC], "Median_A", env=env)
    Median_B = create_geo_entity("LineThroughPoints", [B, Mid_CA], "Median_B", env=env)
    G = create_geo_entity("Intersection", [Median_A, Median_B], "G", env=env)

    # ターゲット: 外心(O), 重心(G), 垂心(H) は同一直線上にある
    target_fact = Fact("Collinear", [O, G, H])

    initial_facts = []

    # ノード追加 (A, B, C は make_given_point 内で追加済みのため除外)
    env.nodes.extend([
        LineBC, LineCA, LineAB,
        Perp_A, Perp_B, H,
        Mid_BC, Mid_CA, PerpMid_BC, PerpMid_CA, O,
        Median_A, Median_B, G
    ])

    return all_vars, target_fact, initial_facts
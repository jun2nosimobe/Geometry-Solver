# problems/prob_miquel.py
from mmp_core import GeoEntity, Definition, LogicalComponent, create_geo_entity, link_logical_incidence
from logic_core import Fact, get_rep

class Variable:
    def __init__(self, name):
        self.name = name
    def evaluate(self, t_dict):
        return t_dict[self]

def setup_problem(env):
    u1, u2, u3, u4, u5, u6 = Variable('u1'), Variable('u2'), Variable('u3'), Variable('u4'), Variable('u5'), Variable('u6')
    # 🌟 FIX: 文字列ではなくVariableオブジェクトのリストを返す
    all_vars = [u1, u2, u3, u4, u5, u6]

    def make_given_point(name, coords_func):
        pt = GeoEntity("Point", name)
        pt._evaluate_given = coords_func
        pt.components.append(LogicalComponent(initial_def=Definition("Given", depth=0)))
        pt.importance = 8.0 
        env.nodes.append(pt)
        return pt

    # A, B, C の定義[cite: 13]
    A = make_given_point("A", lambda t: (0, 0, 1))
    B = make_given_point("B", lambda t: (u1.evaluate(t), 0, 1))
    C = make_given_point("C", lambda t: (u2.evaluate(t), u3.evaluate(t), 1))

    # 各辺を直線として定義[cite: 13]
    LineBC = create_geo_entity("LineThroughPoints", [B, C], "LineBC", env=env)
    LineCA = create_geo_entity("LineThroughPoints", [C, A], "LineCA", env=env)
    LineAB = create_geo_entity("LineThroughPoints", [A, B], "LineAB", env=env)
    
    # 辺上の点 D, E, F[cite: 13]
    D = make_given_point("D", lambda t: (u1.evaluate(t)*(1-u4.evaluate(t))+u2.evaluate(t)*u4.evaluate(t), u3.evaluate(t)*u4.evaluate(t), 1))
    E = make_given_point("E", lambda t: (u2.evaluate(t)*u5.evaluate(t), u3.evaluate(t)*u5.evaluate(t), 1))
    F = make_given_point("F", lambda t: (u1.evaluate(t)*u6.evaluate(t), 0, 1))

    # D, E, F が各辺上にあることを E-Graph に焼き付ける[cite: 13]
    link_logical_incidence(LineBC, D)
    link_logical_incidence(LineCA, E)
    link_logical_incidence(LineAB, F)

    # 2つの外接円 (AEF) と (BFD)[cite: 13]
    CircAEF = create_geo_entity("Circumcircle", [A, E, F], "CircAEF", env=env)
    CircBFD = create_geo_entity("Circumcircle", [B, F, D], "CircBFD", env=env)

    # 円(AEF) と 円(BFD) の交点 M (F 以外の点)[cite: 13]
    M = create_geo_entity("CirclesIntersection", [CircAEF, CircBFD, F], "M", env=env)

    # M が両方の円上にあることを登録[cite: 13]
    link_logical_incidence(CircAEF, M)
    link_logical_incidence(CircBFD, M)

    # ターゲット: M, C, D, E が共円であること[cite: 13]
    target_fact = Fact("Concyclic", [M, C, D, E])

    # 🌟 NEW: 全てE-Graphに書き込んだため、初期Factリストは空で返す
    return all_vars, target_fact, []
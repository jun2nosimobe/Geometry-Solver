# problems/prob_simson.py
from mmp_core import GeoEntity, Definition, LogicalComponent, create_geo_entity, link_logical_incidence
from logic_core import Fact, get_rep

class Variable:
    def __init__(self, name):
        self.name = name
    def evaluate(self, t_dict):
        return t_dict[self]

def setup_problem(env):
    u1, u2, u3, u4 = Variable('u1'), Variable('u2'), Variable('u3'), Variable('u4')
    all_vars = [u1, u2, u3, u4]

    def make_given_point(name, coords_func):
        pt = GeoEntity("Point", name)
        pt._evaluate_given = coords_func
        pt.components.append(LogicalComponent(initial_def=Definition("Given", depth=0)))
        pt.importance = 8.0 
        env.nodes.append(pt)
        return pt

    # A, B, C の定義 (一般性を失わず A=(0,0), B=(u1,0), C=(u2,u3))[cite: 12]
    A = make_given_point("A", lambda t: (0, 0, 1))
    B = make_given_point("B", lambda t: (u1.evaluate(t), 0, 1))
    C = make_given_point("C", lambda t: (u2.evaluate(t), u3.evaluate(t), 1))

    # 各辺の作図[cite: 12]
    LineBC = create_geo_entity("LineThroughPoints", [B, C], "LineBC", env)
    LineCA = create_geo_entity("LineThroughPoints", [C, A], "LineCA", env)
    LineAB = create_geo_entity("LineThroughPoints", [A, B], "LineAB", env)

    # 外接円[cite: 12]
    Circum_ABC = create_geo_entity("Circumcircle", [A, B, C], "Circum_ABC", env)

    # 点P (外接円上の動点) の厳密な代数パラメータ化[cite: 12]
    def eval_P(t_dict):
        v1, v2, v3, v4 = u1.evaluate(t_dict), u2.evaluate(t_dict), u3.evaluate(t_dict), u4.evaluate(t_dict)
        Y_num = v1*v4*v3 - v1*v2 + v2*v2 + v3*v3
        X = v4 * Y_num
        Y = Y_num
        Z = v3 * (v4*v4 + 1)
        return (X, Y, Z)

    P = make_given_point("P", eval_P)
    
    # 🌟 NEW: Pが外接円上にあることをE-Graphに登録
    link_logical_incidence(Circum_ABC, P)

    # 垂線の足 D, E, F の作図と直角の登録[cite: 12]
    # -- D --
    Perp_P_BC = create_geo_entity("PerpendicularLine", [LineBC, P], "Perp_P_BC", env)
    D = create_geo_entity("Intersection", [LineBC, Perp_P_BC], "D", env)
    link_logical_incidence(D, LineBC)
    link_logical_incidence(D, Perp_P_BC)
    ang_D = create_geo_entity("AnglePair", [LineBC, Perp_P_BC], "Angle_D", env, is_given=True)
    if hasattr(env, 'right_angle'):
        env.merge_entities_logically(get_rep(env.right_angle), get_rep(ang_D))

    # -- E --
    Perp_P_CA = create_geo_entity("PerpendicularLine", [LineCA, P], "Perp_P_CA", env)
    E = create_geo_entity("Intersection", [LineCA, Perp_P_CA], "E", env)
    link_logical_incidence(E, LineCA)
    link_logical_incidence(E, Perp_P_CA)
    ang_E = create_geo_entity("AnglePair", [LineCA, Perp_P_CA], "Angle_E", env, is_given=True)
    if hasattr(env, 'right_angle'):
        env.merge_entities_logically(get_rep(env.right_angle), get_rep(ang_E))

    # -- F --
    Perp_P_AB = create_geo_entity("PerpendicularLine", [LineAB, P], "Perp_P_AB", env)
    F = create_geo_entity("Intersection", [LineAB, Perp_P_AB], "F", env)
    link_logical_incidence(F, LineAB)
    link_logical_incidence(F, Perp_P_AB)
    ang_F = create_geo_entity("AnglePair", [LineAB, Perp_P_AB], "Angle_F", env, is_given=True)
    if hasattr(env, 'right_angle'):
        env.merge_entities_logically(get_rep(env.right_angle), get_rep(ang_F))

    # 目標は D, E, F が一直線上にあること[cite: 12]
    target_fact = Fact("Collinear", [D, E, F])
    
    # 🌟 NEW: 全てE-Graphに書き込んだため、初期Factリストは空で返す
    return all_vars, target_fact, []
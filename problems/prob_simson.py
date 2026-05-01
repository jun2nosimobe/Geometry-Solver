# problems/prob_simson.py
from mmp_core import GeoEntity, Definition, LogicalComponent, create_geo_entity
from logic_core import Fact

# Variable クラスが mmp_core にある想定
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
        pt.importance = 8.0 # 初期ノードの重要度を高めに設定
        env.nodes.append(pt)
        return pt

    # A, B, C の定義 (一般性を失わず A=(0,0), B=(u1,0), C=(u2,u3))
    A = make_given_point("A", lambda t: (0, 0, 1))
    B = make_given_point("B", lambda t: (u1.evaluate(t), 0, 1))
    C = make_given_point("C", lambda t: (u2.evaluate(t), u3.evaluate(t), 1))

    # 各辺の作図
    LineBC = create_geo_entity("LineThroughPoints", [B, C], "LineBC", env)
    LineCA = create_geo_entity("LineThroughPoints", [C, A], "LineCA", env)
    LineAB = create_geo_entity("LineThroughPoints", [A, B], "LineAB", env)
    env.nodes.extend([LineBC, LineCA, LineAB])

    # 外接円
    Circum_ABC = create_geo_entity("Circumcircle", [A, B, C], "Circum_ABC", env)
    env.nodes.append(Circum_ABC)

    # 🌟 点P (外接円上の動点) の厳密な代数パラメータ化
    # Aを通る傾きu4の直線と、外接円との交点を計算する有理式
    def eval_P(t_dict):
        v1, v2, v3, v4 = u1.evaluate(t_dict), u2.evaluate(t_dict), u3.evaluate(t_dict), u4.evaluate(t_dict)
        Y_num = v1*v4*v3 - v1*v2 + v2*v2 + v3*v3
        X = v4 * Y_num
        Y = Y_num
        Z = v3 * (v4*v4 + 1)
        return (X, Y, Z)

    P = make_given_point("P", eval_P)

    # 垂線の足 D, E, F の作図
    Perp_P_BC = create_geo_entity("PerpendicularLine", [LineBC, P], "Perp_P_BC", env)
    D = create_geo_entity("Intersection", [LineBC, Perp_P_BC], "D", env)
    
    Perp_P_CA = create_geo_entity("PerpendicularLine", [LineCA, P], "Perp_P_CA", env)
    E = create_geo_entity("Intersection", [LineCA, Perp_P_CA], "E", env)
    
    Perp_P_AB = create_geo_entity("PerpendicularLine", [LineAB, P], "Perp_P_AB", env)
    F = create_geo_entity("Intersection", [LineAB, Perp_P_AB], "F", env)
    
    #env.nodes.extend([Perp_P_BC, D, Perp_P_CA, E, Perp_P_AB, F])

    # 目標は D, E, F が一直線上にあること
    target_fact = Fact("Collinear", [D, E, F])
    
    # 初期事実: P が A,B,C と共円であること
    initial_facts = [Fact("Concyclic", [A, B, C, P], is_proven=True, proof_source="問題の前提条件")]

    # 戻り値から initial_right_angles を削除 (新構造で自動登録されるため)
    return all_vars, target_fact, initial_facts
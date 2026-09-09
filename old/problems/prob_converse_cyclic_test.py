# problems/prob_converse_cyclic_test.py
from mmp_core import GeoEntity, Definition, LogicalComponent, create_geo_entity
from logic_core import Fact

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
        pt.components.append(LogicalComponent(initial_def=Definition("Given", [], naive_degree=0, depth=0)))
        pt.importance = 10.0 
        env.nodes.append(pt)
        return pt

    # A, B を Base(底点)、C, D を Apex(頂点) とする
    A = make_given_point("A", lambda t: (0, 0, 1))
    B = make_given_point("B", lambda t: (u1.evaluate(t), 0, 1))
    C = make_given_point("C", lambda t: (u2.evaluate(t), u3.evaluate(t), 1))

    # A, B, C を通る円上の点 D の厳密な代数パラメータ化
    def eval_D(t_dict):
        from mmp_math import ModInt 
        v1, v2, v3, v4 = u1.evaluate(t_dict), u2.evaluate(t_dict), u3.evaluate(t_dict), u4.evaluate(t_dict)
        Y_num = v1*v4*v3 - v1*v2 + v2*v2 + v3*v3
        X = v4 * Y_num
        Y = Y_num
        Z = v3 * (v4*v4 + ModInt(1)) 
        return (X, Y, Z)

    D = make_given_point("D", eval_D)

    # 4本の直線 (CA, CB, DA, DB)
    LineCA = create_geo_entity("LineThroughPoints", [C, A], "LineCA", env)
    LineCB = create_geo_entity("LineThroughPoints", [C, B], "LineCB", env)
    LineDA = create_geo_entity("LineThroughPoints", [D, A], "LineDA", env)
    LineDB = create_geo_entity("LineThroughPoints", [D, B], "LineDB", env)

    # それぞれの方向ベクトル
    DirCA = create_geo_entity("DirectionOf", [LineCA], "DirCA", env)
    DirCB = create_geo_entity("DirectionOf", [LineCB], "DirCB", env)
    DirDA = create_geo_entity("DirectionOf", [LineDA], "DirDA", env)
    DirDB = create_geo_entity("DirectionOf", [LineDB], "DirDB", env)

    # 円周角となる2つの角度
    Ang_C = create_geo_entity("AnglePair", [DirCA, DirCB], "Ang_C", env)
    Ang_D = create_geo_entity("AnglePair", [DirDA, DirDB], "Ang_D", env)

    # 🌟 「角度が等しい」という状態を E-Graph に強制的に注入する
    if Ang_C and Ang_D:
        env.merge_entities_logically(
            Ang_C.get_rep(), 
            Ang_D.get_rep(), 
            force_bypass_verify=True, 
            reason_fact="[テスト用] 角度の強制一致"
        )

    # ターゲット: 4点が共円であること
    target_fact = Fact("Concyclic", [C, D, A, B])

    return all_vars, target_fact, []
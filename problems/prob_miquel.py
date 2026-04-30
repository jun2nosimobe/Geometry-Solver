# problems/prob_miquel.py
from mmp_core import GeoEntity, Definition, LogicalComponent, create_geo_entity, link_logical_incidence
from logic_core import Fact

# Variable クラスが mmp_core にある想定
class Variable:
    def __init__(self, name):
        self.name = name
    def evaluate(self, t_dict):
        return t_dict[self]

def setup_problem(env):
    u1, u2, u3, u4, u5, u6, u7, u8, u9 = Variable('u1'), Variable('u2'), Variable('u3'), Variable('u4'), Variable('u5'), Variable('u6'), Variable('u7'), Variable('u8'), Variable('u9')
    all_vars = ["u1", "u2", "u3", "u4", "u5", "u6"]

    """
    ミケルの定理のセットアップ:
    △ABC の辺 BC, CA, AB 上にそれぞれ点 D, E, F をとる。
    円(AEF) と 円(BFD) の交点を M とするとき、M, C, D, E は共円である。
    """
    # 自由度は A, B, C の座標と、D, E, F の各辺上の位置の計9個
    
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

    # 2. 各辺を直線として定義
    LineBC = create_geo_entity("LineThroughPoints", [B, C], "LineBC", env=env)
    LineCA = create_geo_entity("LineThroughPoints", [C, A], "LineCA", env=env)
    LineAB = create_geo_entity("LineThroughPoints", [A, B], "LineAB", env=env)

    
    # 3. 辺上の点 D, E, F
    D = make_given_point("D", lambda t: (u1.evaluate(t)*(1-u4.evaluate(t))+u2.evaluate(t)*u4.evaluate(t), u3.evaluate(t)*u4.evaluate(t), 1))
    E = make_given_point("E", lambda t: (u2.evaluate(t)*u5.evaluate(t), u3.evaluate(t)*u5.evaluate(t), 1))
    F = make_given_point("F", lambda t: (u1.evaluate(t)*u6.evaluate(t), 0, 1))

    link_logical_incidence(LineBC, D)
    link_logical_incidence(LineCA, E)
    link_logical_incidence(LineAB, F)

    # 4. 2つの外接円 (AEF) と (BFD)
    CircAEF = create_geo_entity("Circumcircle", [A, E, F], "CircAEF", env=env)
    CircBFD = create_geo_entity("Circumcircle", [B, F, D], "CircBFD", env=env)

    # 5. 円(AEF) と 円(BFD) の交点 M (F 以外の点)
    M = create_geo_entity("CirclesIntersection", [CircAEF, CircBFD, F], "M", env=env)

    # 6. ターゲット: M, C, D, E が共円であること
    target_fact = Fact("Concyclic", [M, C, D, E])

    link_logical_incidence(CircAEF, M)
    link_logical_incidence(CircBFD, M)

    # 初期事実の登録 [cite: 2]
    initial_facts = [
        Fact("Collinear", [B, D, C], is_proven=True, proof_source="問題の前提条件"),
        Fact("Collinear", [C, E, A], is_proven=True, proof_source="問題の前提条件"),
        Fact("Collinear", [A, F, B], is_proven=True, proof_source="問題の前提条件"),
        Fact("Concyclic", [A, E, F, M], is_proven=True, proof_source="問題の前提条件"),
        Fact("Concyclic", [B, F, D, M], is_proven=True, proof_source="問題の前提条件")
    ]

    # nodes に登録
    env.nodes.extend([LineBC, LineCA, LineAB, CircAEF, CircBFD, M])

    return all_vars, target_fact, initial_facts
# problems/prob_angle_to_line_test.py
from mmp_core import GeoEntity, Definition, LogicalComponent, create_geo_entity
from logic_core import Fact

class Variable:
    def __init__(self, name):
        self.name = name
    def evaluate(self, t_dict):
        return t_dict[self]

def setup_problem(env):
    u1 = Variable('u1')
    all_vars = [u1]

    def make_given_point(name, coords_func):
        pt = GeoEntity("Point", name)
        pt._evaluate_given = coords_func
        pt.components.append(LogicalComponent(initial_def=Definition("Given", [], naive_degree=0, depth=0)))
        pt.importance = 10.0 
        env.nodes.append(pt)
        return pt

    # 1. 共通の交点 P と、基準となる方向を持つ点 M
    P = make_given_point("P", lambda t: (0, 0, 1))
    M = make_given_point("M", lambda t: (0, 1, 1))
    
    # 2. P を通り、互いに同じ方向を持つ点 A と B (実際にはどちらも x軸上)
    A = make_given_point("A", lambda t: (1, 0, 1))
    B = make_given_point("B", lambda t: (u1.evaluate(t), 0, 1))

    # 3. 直線の作図
    LinePM = create_geo_entity("LineThroughPoints", [P, M], "LinePM", env)
    LinePA = create_geo_entity("LineThroughPoints", [P, A], "LinePA", env)
    LinePB = create_geo_entity("LineThroughPoints", [P, B], "LinePB", env)

    # 4. 方向ベクトルの作図
    DirPM = create_geo_entity("DirectionOf", [LinePM], "DirPM", env)
    DirPA = create_geo_entity("DirectionOf", [LinePA], "DirPA", env)
    DirPB = create_geo_entity("DirectionOf", [LinePB], "DirPB", env)

    # 5. 角度の作図 (右共通で基準線 LinePM に対する角度を測る)
    Ang_A = create_geo_entity("AnglePair", [DirPA, DirPM], "Ang_A", env)
    Ang_B = create_geo_entity("AnglePair", [DirPB, DirPM], "Ang_B", env)

    # 🌟 「角度が等しい」という状態を E-Graph に強制的に注入する
    if Ang_A and Ang_B:
        env.merge_entities_logically(
            Ang_A.get_rep(), 
            Ang_B.get_rep(), 
            force_bypass_verify=True, 
            reason_fact="[テスト用] 角度の強制一致"
        )

    # ターゲット: 角度の一致から「直線PAと直線PBが同一であること」が証明されるか？
    target_fact = Fact("Identical", [LinePA, LinePB])

    return all_vars, target_fact, []
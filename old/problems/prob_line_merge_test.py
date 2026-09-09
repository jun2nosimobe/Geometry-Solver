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

    # A, B, C を一直線（x軸）上に定義
    A = make_given_point("A", lambda t: (0, 0, 1))
    B = make_given_point("B", lambda t: (1, 0, 1))
    C = make_given_point("C", lambda t: (u1.evaluate(t), 0, 1))

    # 直線AB と 直線BC を作図
    LineAB = create_geo_entity("LineThroughPoints", [A, B], "LineAB", env)
    LineBC = create_geo_entity("LineThroughPoints", [B, C], "LineBC", env)

    # 方向ベクトルを作図
    DirAB = create_geo_entity("DirectionOf", [LineAB], "DirAB", env)
    DirBC = create_geo_entity("DirectionOf", [LineBC], "DirBC", env)

    env.merge_entities_logically(
            DirAB.get_rep(), 
            DirBC.get_rep(), 
            force_bypass_verify=True, 
            reason_fact="[テスト用] 角度の強制一致"
    )

    # ターゲット: 直線AB と 直線BC が同一であること
    target_fact = Fact("Identical", [LineAB, LineBC])

    return all_vars, target_fact, []
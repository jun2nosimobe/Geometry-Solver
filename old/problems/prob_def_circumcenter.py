from mmp_core import GeoEntity, Definition, LogicalComponent, create_geo_entity, link_logical_incidence
from logic_core import Fact, get_rep

class Variable:
    def __init__(self, name):
        self.name = name
    def evaluate(self, t_dict):
        return t_dict[self]

def setup_problem(env):
    # ==========================================
    # 0. 自由変数のセットアップ (🚨 前回の教訓: 文字列にしない！)
    # ==========================================
    u1, u2, u3 = Variable('u1'), Variable('u2'), Variable('u3')
    all_vars = [u1, u2, u3]  # オブジェクトそのものを渡す

    def make_given_point(name, coords_func):
        pt = GeoEntity("Point", name)
        pt._evaluate_given = coords_func
        pt.components.append(LogicalComponent(initial_def=Definition("Given", depth=0)))
        pt.importance = 10.0 
        env.nodes.append(pt)
        return pt

    # ==========================================
    # 1. 基本となる点 A, B, C と各辺
    # ==========================================
    A = make_given_point("A", lambda t: (0, 0, 1))
    B = make_given_point("B", lambda t: (u1.evaluate(t), 0, 1))
    C = make_given_point("C", lambda t: (u2.evaluate(t), u3.evaluate(t), 1))

    LineBC = create_geo_entity("LineThroughPoints", [B, C], "LineBC", env=env)
    LineCA = create_geo_entity("LineThroughPoints", [C, A], "LineCA", env=env)
    LineAB = create_geo_entity("LineThroughPoints", [A, B], "LineAB", env=env)
    
    link_logical_incidence(LineBC, B); link_logical_incidence(LineBC, C)
    link_logical_incidence(LineCA, C); link_logical_incidence(LineCA, A)
    link_logical_incidence(LineAB, A); link_logical_incidence(LineAB, B)

    # ==========================================
    # 2. 外心 O と直線 AO の作図
    # ==========================================
    Mid_BC = create_geo_entity("Midpoint", [B, C], "Mid_BC", env=env)
    Mid_CA = create_geo_entity("Midpoint", [C, A], "Mid_CA", env=env)
    
    PerpMid_BC = create_geo_entity("PerpendicularLine", [LineBC, Mid_BC], "PerpMid_BC", env=env)
    PerpMid_CA = create_geo_entity("PerpendicularLine", [LineCA, Mid_CA], "PerpMid_CA", env=env)
    
    O = create_geo_entity("Intersection", [PerpMid_BC, PerpMid_CA], "O", env=env)

    LineAO = create_geo_entity("LineThroughPoints", [A, O], "LineAO", env=env)
    link_logical_incidence(LineAO, A); link_logical_incidence(LineAO, O)

    # ==========================================
    # 3. 垂線の足 D, E, F の作図
    # ==========================================
    # 点D: AからBCへの垂線の足
    Perp_A_BC = create_geo_entity("PerpendicularLine", [LineBC, A], "Perp_A_BC", env=env)
    D = create_geo_entity("Intersection", [LineBC, Perp_A_BC], "D", env=env)
    link_logical_incidence(D, LineBC); link_logical_incidence(D, Perp_A_BC)

    # 点E: BからAOへの垂線の足
    Perp_B_AO = create_geo_entity("PerpendicularLine", [LineAO, B], "Perp_B_AO", env=env)
    E = create_geo_entity("Intersection", [LineAO, Perp_B_AO], "E", env=env)
    link_logical_incidence(E, LineAO); link_logical_incidence(E, Perp_B_AO)

    # 点F: CからAOへの垂線の足
    Perp_C_AO = create_geo_entity("PerpendicularLine", [LineAO, C], "Perp_C_AO", env=env)
    F = create_geo_entity("Intersection", [LineAO, Perp_C_AO], "F", env=env)
    link_logical_incidence(F, LineAO); link_logical_incidence(F, Perp_C_AO)

    # ==========================================
    # 4. 三角形DEFの外心 O_DEF の作図
    # ==========================================
    # 辺DEの垂直二等分線
    LineDE = create_geo_entity("LineThroughPoints", [D, E], "LineDE", env=env)
    Mid_DE = create_geo_entity("Midpoint", [D, E], "Mid_DE", env=env)
    PerpMid_DE = create_geo_entity("PerpendicularLine", [LineDE, Mid_DE], "PerpMid_DE", env=env)

    # 辺EFの垂直二等分線
    LineEF = create_geo_entity("LineThroughPoints", [E, F], "LineEF", env=env)
    Mid_EF = create_geo_entity("Midpoint", [E, F], "Mid_EF", env=env)
    PerpMid_EF = create_geo_entity("PerpendicularLine", [LineEF, Mid_EF], "PerpMid_EF", env=env)

    # 外心 O_DEF はその交点
    O_DEF = create_geo_entity("Intersection", [PerpMid_DE, PerpMid_EF], "O_DEF", env=env)

    # ==========================================
    # 5. ターゲット設定
    # ==========================================
    # 「三角形DEFの外心(O_DEF)が、辺BCの中点(Mid_BC)と一致する」
    target_fact = Fact("Identical", [O_DEF, Mid_BC])

    # 構成的アプローチによりE-Graphに全て登録済みなので、初期Factsは空で返す
    return all_vars, target_fact, []
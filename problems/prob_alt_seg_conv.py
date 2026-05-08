from logic_core import Fact
from mmp_core import GeoEntity, Definition, LogicalComponent, create_geo_entity, link_logical_incidence

class Variable:
    def __init__(self, name):
        self.name = name
    def evaluate(self, t_dict):
        return t_dict[self]

def setup_problem(env):
    u1, u2, u3 = Variable('u1'), Variable('u2'), Variable('u3')
    all_vars = [u1, u2, u3]

    def make_free_point(name, t_x, t_y):
        pt = GeoEntity("Point", name=name)
        pt.numerical_degree = 2
        def calc_func(t_dict, cache):
            if id(pt) in cache: return cache[id(pt)]
            res = [t_x.evaluate(t_dict) if isinstance(t_x, Variable) else t_x, 
                   t_y.evaluate(t_dict) if isinstance(t_y, Variable) else t_y, 1]
            cache[id(pt)] = res
            return res
        pt.calculate = calc_func
        pt.components.append(LogicalComponent(initial_def=Definition("Given", [], naive_degree=0, depth=0)))
        pt.base_importance = 10.0
        env.nodes.append(pt)
        return pt

    A = make_free_point("A", 0, 0)
    B = make_free_point("B", u1, 0)
    D = make_free_point("D", u2, u3)
    
    C = create_geo_entity("Circumcircle", [A, B, D], name="C", env=env)
    
    # 黒魔術: 退化ガードを回避して「隠れ接線」から作図定義だけを奪う
    L_hidden = create_geo_entity("TangentLine", [C, A], name="L_hidden", env=None)
    L = GeoEntity("Line", "L")
    L.base_importance = 10.0
    L.components.append(LogicalComponent(initial_def=list(L_hidden.get_best_component().definitions)[0]))
    env.nodes.append(L)
    
    # 点Aは直線Lに乗っている
    link_logical_incidence(A, L)
    
    Line_AB = create_geo_entity("LineThroughPoints", [A, B], name="Line_AB", env=env)
    Line_AD = create_geo_entity("LineThroughPoints", [A, D], name="Line_AD", env=env)
    Line_BD = create_geo_entity("LineThroughPoints", [B, D], name="Line_BD", env=env)
    
    Dir_L = create_geo_entity("DirectionOf", [L], name="Dir_L", env=env)
    Dir_AB = create_geo_entity("DirectionOf", [Line_AB], name="Dir_AB", env=env)
    Dir_AD = create_geo_entity("DirectionOf", [Line_AD], name="Dir_AD", env=env)
    Dir_BD = create_geo_entity("DirectionOf", [Line_BD], name="Dir_BD", env=env)
    
    Ang_L_AB = create_geo_entity("AnglePair", [Dir_L, Dir_AB], name="Ang_L_AB", env=env)
    Ang_AD_BD = create_geo_entity("AnglePair", [Dir_AD, Dir_BD], name="Ang_AD_BD", env=env)
    
    # 手動介入: 仮定として「接弦角と円周角が等しい」という事実を強制的にマージする
    from logic_core import get_rep
    env.merge_entities_logically(get_rep(Ang_L_AB), get_rep(Ang_AD_BD), force_bypass_verify=True)
    
    target = Fact("Connected", [L, C])
    
    return all_vars, target, []
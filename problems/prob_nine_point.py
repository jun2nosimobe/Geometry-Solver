# problems/prob_nine_point.py
from logic_core import Fact
from mmp_core import GeoEntity, LogicalComponent, Definition, create_geo_entity, make_free_point

class Var:
    """MMPで値を代入するためのシンボリック変数クラス"""
    def __init__(self, name):
        self.name = name
    def evaluate(self, t_dict):
        # t_dict（乱数辞書）から自身の値を取得
        return t_dict.get(self, 1) 
    def __hash__(self):
        return hash(self.name)
    def __eq__(self, other):
        return isinstance(other, Var) and self.name == other.name

def setup_problem(env):
    # 1. 独立変数の定義 (A, B, C の 6自由度)
    t1, t2, t3, t4, t5, t6 = [Var(f"t{i}") for i in range(1, 7)]
    all_vars = [t1, t2, t3, t4, t5, t6]

    # 2. 初期点 A, B, C の手動定義ヘルパー
    def make_free_point1(name, coords):
        pt = GeoEntity("Point", name=name)
        pt.numerical_degree = 2 # SVD計算用に自由度2を設定
        pt._given_coords = coords
        
        # Given(与えられた点)として定義を登録
        comp = LogicalComponent(initial_def=Definition("Given", [], naive_degree=1, depth=0))
        pt.components.append(comp)
        
        # ==========================================
        # 🌟 NEW: MMPの計算エンジン(calculate)を実装
        # coords (t1, t2, 1) などを、t_dict を使って評価して返す
        # ==========================================
        def calc_func(t_dict, cache):
            if id(pt) in cache:
                return cache[id(pt)]
            
            # coords の各要素が Var なら evaluate し、数値ならそのまま使う
            val_x = coords[0].evaluate(t_dict) if hasattr(coords[0], 'evaluate') else coords[0]
            val_y = coords[1].evaluate(t_dict) if hasattr(coords[1], 'evaluate') else coords[1]
            val_z = coords[2].evaluate(t_dict) if hasattr(coords[2], 'evaluate') else coords[2]
            
            result = [val_x, val_y, val_z]
            cache[id(pt)] = result
            return result
            
        pt.calculate = calc_func # メソッドを上書き
        
        env.nodes.append(pt)
        return pt

    # A, B, C を作図 (同次座標系)
    A = make_free_point1("A", (t1, t2, 1))
    B = make_free_point1("B", (t3, t4, 1))
    C = make_free_point1("C", (t5, t6, 1))

    # 3. 問題の作図 (九点円の一部)
    # 辺の中点
    Mid_B_C = create_geo_entity("Midpoint", [B, C], name="Mid_BC", env=env, is_given=True)
    Mid_C_A = create_geo_entity("Midpoint", [C, A], name="Mid_CA", env=env, is_given=True)
    Mid_A_B = create_geo_entity("Midpoint", [A, B], name="Mid_AB", env=env, is_given=True)
    
    # 頂点Aから対辺BCへの垂線と、その足 (H_A)
    Line_BC = create_geo_entity("LineThroughPoints", [B, C], name="Line_BC", env=env, is_given=True)
    Perp_A_BC = create_geo_entity("PerpendicularLine", [Line_BC, A], name="Perp_A_BC", env=env, is_given=True)
    H_A = create_geo_entity("Intersection", [Line_BC, Perp_A_BC], name="H_A", env=env, is_given=True)


    # 4. 初期事実の登録
    # ※当たり前ですが、MCTSが「H_AはBC上にある」ことを忘れないようにFactsとして入れます
    initial_facts = [
        Fact("Collinear", [B, H_A, C], is_proven=True, proof_source="作図の定義 (垂線の足)"),
        Fact("Perpendicular", [Line_BC, Perp_A_BC], is_proven=True, proof_source="作図の定義 (垂線)")
    ]
    
    # E-Graph (環境) にも直角を登録しておく
    if hasattr(env, 'add_right_angle'):
        env.add_right_angle(Line_BC, Perp_A_BC)

    # 5. 目標となる Fact (Target Fact)
    # 4点 Mid_BC, H_A, Mid_CA, Mid_AB が共円であること！
    target_fact = Fact("Concyclic", [Mid_B_C, H_A, Mid_C_A, Mid_A_B])

    return all_vars, target_fact, initial_facts
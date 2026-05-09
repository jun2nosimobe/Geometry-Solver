import uuid
from typing import List, Set, Any, Dict
import numpy as np
import itertools
from mmp_math import ModInt

# ==========================================
# 作図定義 (Definition)
# ==========================================
class Definition:
    def __init__(self, def_type: str, parents: List[Any] = None, naive_degree: int = 1, depth: int = 1):
        self.def_type = def_type
        self.parents = parents or []
        self.naive_degree = naive_degree
        self.depth = depth

    def __hash__(self):
        # 🌟 修正: 定数(Constant)としてModInt等のリテラルが渡された場合も安全にハッシュ化する
        return hash((self.def_type, tuple(p.id if hasattr(p, 'id') else (p.value if hasattr(p, 'value') else p) for p in self.parents)))

    def __eq__(self, other):
        if not isinstance(other, Definition): return False
        return self.def_type == other.def_type and self.parents == other.parents

# ==========================================
# 論理コンポーネント (LogicalComponent)
# ==========================================
class LogicalComponent:
    def __init__(self, initial_def: Definition = None):
        self.definitions: Set[Definition] = set()
        self.subobjects: Set['GeoEntity'] = set() 
        self.importance = 1.0
        self.naive_degree = float('inf')
        self.depth = float('inf')
        self.supporting_facts = set()
        
        if initial_def:
            self.definitions.add(initial_def)
            self.naive_degree = initial_def.naive_degree
            self.depth = initial_def.depth

    def merge_logical(self, other: 'LogicalComponent'):
        self.definitions.update(other.definitions)
        self.subobjects.update(other.subobjects)
        self.importance = max(self.importance, other.importance)
        self.naive_degree = min(self.naive_degree, other.naive_degree)
        self.depth = min(self.depth, other.depth)
        self.supporting_facts.update(other.supporting_facts)

# ==========================================
# 幾何学実体 (GeoEntity)
# ==========================================
class GeoEntity:
    def __init__(self, entity_type: str, name: str = ""):
        self.id = uuid.uuid4()
        self.name = name                 
        self.entity_type = entity_type   
        
        self.base_importance = 1.0       # 基礎重要度 (作図時に固定、絶対に下がらない)
        self.heat_bonus = 0.0            # 一時的な熱 (発見で上がり、毎ターン減衰する)
        
        self.numerical_degree = None     
        self.components: List[LogicalComponent] = []
        self.mmp_subobjects: Set['GeoEntity'] = set() 
        self.associated_facts = []
        
        self._merged_into = None
        self.shape_members: Dict['GeoEntity', tuple] = {} 

        self._parent = self
        self._merge_reason = None

    def get_rep(self):
        """Union-Find木の根（代表元）を返す。
           (旧 get_representative / get_rep)"""
        curr = self
        # もし旧型の _merged_into を使っているなら:
        # while getattr(curr, '_merged_into', None) is not None:
        #     curr = curr._merged_into
        while curr._parent != curr:
            curr = curr._parent
        return curr

    def is_valid(self):
        """このノードが有効（削除や無効化されていない）か判定する。"""
        rep = self.get_rep()
        # base_importance が 0 以下のものは無効(刈り取られた)ノードと判定
        return getattr(rep, 'base_importance', 1.0) > 0.0

    @property
    def importance(self):
        """実効重要度 = 基礎重要度 + 熱ボーナス"""
        return self.base_importance + self.heat_bonus

    @importance.setter
    def importance(self, value):
        """【後方互換性用】古いコードから代入された場合、熱ボーナスとして差分を吸収する"""
        self.heat_bonus = max(0.0, value - self.base_importance)

    def add_heat(self, bonus: float):
        """🌟 NEW: 熱(ボーナス)を追加するための専用メソッド"""
        if getattr(self, 'base_importance', 1.0) <= 0.0:
            return
        self.heat_bonus += bonus

    def get_best_component(self) -> LogicalComponent:
        if not self.components: return None
        return min(self.components, key=lambda c: (c.naive_degree, c.depth))

    def merge_numerical(self, other: 'GeoEntity'):
        if self == other: return
        self.components.extend(other.components)
        self.mmp_subobjects.update(other.mmp_subobjects)
        
        # 基礎重要度と熱は高い方を引き継ぐ（ゴーストが実体化した時に熱を継承するため）
        self.base_importance = max(self.base_importance, other.base_importance)
        self.heat_bonus = max(self.heat_bonus, other.heat_bonus)
        
        # 🌟 NEW: 最短名戦略 (Shortest Name Strategy)
        if len(other.name) < len(self.name):
            self.name = other.name
        elif len(other.name) == len(self.name) and "(Ghost)" not in other.name and "(Ghost)" in self.name:
            self.name = other.name # 長さが同じならゴーストじゃない方の名前を優先
            
        if self.numerical_degree is None:
            self.numerical_degree = other.numerical_degree
        elif other.numerical_degree is not None:
            self.numerical_degree = min(self.numerical_degree, other.numerical_degree)


    def prove_components_equal(self, comp_idx_1: int, comp_idx_2: int):
        if comp_idx_1 == comp_idx_2: return
        c1 = self.components[comp_idx_1]
        c2 = self.components[comp_idx_2]
        c1.merge_logical(c2)
        self.components.remove(c2) 

    def calculate(self, t_dict, cache):
        from mmp_calculators import CALCULATORS
        import traceback

        cache_key = (self.id, id(t_dict))
        if cache_key in cache:
            return cache[cache_key]

        result = []
        comp = self.get_best_component()
        if not comp or not comp.definitions:
            return []
            
        best_def = list(comp.definitions)[0]
        def_type = best_def.def_type
        parents = best_def.parents

        # ==========================================
        # 1. Given (初期点) の座標取得（_evaluate_given 対応版！）
        # ==========================================
        if def_type in ["Point", "Given", "Free", "GivenPoint", "FreePoint"]:
            if not parents:
                val = None
                
                # 🌟 NEW パターン0: あなたのシステム特有の座標関数！
                if hasattr(self, '_evaluate_given'):
                    try:
                        val = self._evaluate_given(t_dict)
                    except Exception as e:
                        self._calc_err_trace = f"_evaluate_givenの実行エラー: {str(e)}"
                        cache[cache_key] = []
                        return []

                # パターン1: 直接のキー探索
                if val is None:
                    if self in t_dict: val = t_dict[self]
                    elif getattr(self, 'name', '') in t_dict: val = t_dict[self.name]
                    elif getattr(self, 'id', '') in t_dict: val = t_dict[self.id]
                
                # パターン2: オブジェクトの name プロパティでの一致探索
                if val is None:
                    for k, v in t_dict.items():
                        if getattr(k, 'name', str(k)) == getattr(self, 'name', ''):
                            val = v
                            break
                            
                # パターン3: 'A_x', 'A_y' のような成分ごとの探索
                if val is None:
                    name = getattr(self, 'name', '')
                    vx, vy, vz = None, None, None
                    for k, v in t_dict.items():
                        kstr = str(getattr(k, 'name', k))
                        if kstr in [f"{name}_x", f"x_{name}"]: vx = v
                        elif kstr in [f"{name}_y", f"y_{name}"]: vy = v
                        elif kstr in [f"{name}_z", f"z_{name}"]: vz = v
                    if vx is not None and vy is not None:
                        val = [vx, vy, vz if vz is not None else 1]
                        
                # パターン4: オブジェクトが直接座標属性を持っている場合
                if val is None:
                    if hasattr(self, 'coord'): val = self.coord
                    elif hasattr(self, 'coords'): val = self.coords
                    elif hasattr(self, 'value'): val = self.value
                
                if val is not None:
                    result = [val[0], val[1], val[2]] if isinstance(val, (list, tuple)) else [val, val, val]
                    cache[cache_key] = result
                    return result
                else:
                    t_keys = [str(getattr(k, 'name', k)) for k in t_dict.keys()][:8]
                    a_attrs = [k for k in self.__dict__.keys() if not k.startswith('_')]
                    self._calc_err_trace = f"座標不在: '{getattr(self, 'name', '')}'の座標が見つかりません。t_dictキー: {t_keys}, Aの属性: {a_attrs}"
                    cache[cache_key] = []
                    return []
            else:
                # パラメータで定義された点 (Symbol, String, または GeoEntity)
                res = []
                for p in parents:
                    if hasattr(p, 'calculate'):
                        pval = p.calculate(t_dict, cache)
                        res.append(pval[0] if isinstance(pval, (list, tuple)) and pval else pval)
                    elif p in t_dict: 
                        res.append(t_dict[p])
                    elif isinstance(p, str) and p in t_dict: 
                        res.append(t_dict[p])
                    else:
                        matched = False
                        for k, v in t_dict.items():
                            if str(k) == str(p):
                                res.append(v)
                                matched = True
                                break
                        if not matched:
                            if isinstance(p, (int, float)):
                                res.append(ModInt(int(p)))
                            else:
                                res.append(p) 
                
                if len(res) >= 2:
                    if len(res) == 2:
                        one = res[0].__class__(1) if hasattr(res[0], 'value') else 1
                        res.append(one)
                    cache[cache_key] = res
                    return res
                else:
                    self._calc_err_trace = f"初期点の座標構築に失敗 (parents={parents}, res={res})"
                    cache[cache_key] = []
                    return []

        # ==========================================
        # 2. レジストリに登録された計算の実行と監視
        # ==========================================
        if def_type in CALCULATORS:
            try:
                result = CALCULATORS[def_type](parents, t_dict, cache)
                if not result:
                    parent_errs = []
                    for p in parents:
                        if hasattr(p, '_calc_err_trace') and p._calc_err_trace:
                            parent_errs.append(f"[{getattr(p, 'name', '?')}]: {p._calc_err_trace}")
                    
                    err_msg = "計算結果が空([])"
                    if parent_errs: err_msg += f" <- 親エラー: {' | '.join(parent_errs)}"
                    else: err_msg += " (親図形が退化しているか無効な値)"
                    self._calc_err_trace = err_msg
            except Exception as e:
                self._calc_err_trace = traceback.format_exc()
                result = []
        else:
            self._calc_err_trace = f"未登録の def_type: '{def_type}'"
            result = []
                
        cache[cache_key] = result
        return result

    def _evaluate_given(self, t_dict):
        return tuple(v.evaluate(t_dict) if hasattr(v, 'evaluate') else v for v in self._given_coords)

# ==========================================
# ヘルパー関数群
# ==========================================
def link_logical_incidence(entity1: GeoEntity, entity2: GeoEntity):
    c1 = entity1.get_best_component()
    c2 = entity2.get_best_component()
    if c1 and entity2 not in c1.subobjects:
        c1.subobjects.add(entity2)
    if c2 and entity1 not in c2.subobjects:
        c2.subobjects.add(entity1)

def apply_trivial_relations(new_entity: GeoEntity, definition: Definition, env):
    if env is None: return
    def_type = definition.def_type
    parents = definition.parents

    if def_type == "LineThroughPoints":
        link_logical_incidence(parents[0], new_entity)
        link_logical_incidence(parents[1], new_entity)
    elif def_type == "Intersection":
        link_logical_incidence(new_entity, parents[0])
        link_logical_incidence(new_entity, parents[1])

    elif def_type == "PerpendicularLine":
        ln, pt = parents[0], parents[1]
        link_logical_incidence(pt, new_entity)
        if env is not None:
            if hasattr(env, 'add_right_angle'): 
                pass
            else: 
                # 🌟 FIX: 明示的に名前を生成して渡す
                dir1_name = f"Dir_{getattr(ln, 'name', 'Unknown')}_(Auto)"
                dir2_name = f"Dir_{getattr(new_entity, 'name', 'Unknown')}_(Auto)"
                
                dir1 = create_geo_entity("DirectionOf", [ln], name=dir1_name, env=env)
                dir2 = create_geo_entity("DirectionOf", [new_entity], name=dir2_name, env=env)
                
                env.right_angle.components[0].definitions.add(Definition("AnglePair", [dir1, dir2]))
                env.right_angle.components[0].definitions.add(Definition("AnglePair", [dir2, dir1]))
                
    elif def_type == "ParallelLine":
        ln, pt = parents[0], parents[1]
        link_logical_incidence(pt, new_entity)
        if env is not None:
            if hasattr(env, 'add_right_angle'): 
                pass
            else: 
                # 🌟 FIX: 明示的に名前を生成して渡す
                dir1_name = f"Dir_{getattr(ln, 'name', 'Unknown')}_(Auto)"
                dir2_name = f"Dir_{getattr(new_entity, 'name', 'Unknown')}_(Auto)"
                
                dir1 = create_geo_entity("DirectionOf", [ln], name=dir1_name, env=env)
                dir2 = create_geo_entity("DirectionOf", [new_entity], name=dir2_name, env=env)
                
                rep1, rep2 = dir1.get_rep(), dir2.get_rep()
                if rep1 != rep2:
                    env.merge_entities_logically(rep1, rep2)
    elif def_type == "TangentLine":
        circle, pt = parents[0], parents[1]
        link_logical_incidence(new_entity, circle) # Connected(L, C)
        link_logical_incidence(pt, new_entity)     # Connected(A, L)
        link_logical_incidence(pt, circle)         # Connected(A, C)
        
    elif def_type == "Midpoint":
        c1, c2 = parents[0].get_best_component(), parents[1].get_best_component()
        if c1 and c2:
            common_lines = [obj for obj in (c1.subobjects & c2.subobjects) if obj.entity_type == "Line"]
            for ln in common_lines: link_logical_incidence(new_entity, ln)
    elif def_type == "Circumcircle":
        for p in parents[:3]: link_logical_incidence(p, new_entity)
    elif def_type == "OtherLineCircleIntersection":
        ln, circ, pt_exclude = parents[0], parents[1], parents[2]
        link_logical_incidence(new_entity, ln)
        link_logical_incidence(new_entity, circ)
    elif def_type == "CirclesIntersection":
        c1, c2, pt_exclude = parents[0], parents[1], parents[2]
        link_logical_incidence(new_entity, c1)
        link_logical_incidence(new_entity, c2)
    # ==========================================
    # 🌟 修正: 中点の自明な性質 (共線と辺比)
    # ==========================================
    elif def_type == "Midpoint":
        A, B = parents[0], parents[1]
        M = new_entity
        c1, c2 = A.get_best_component(), B.get_best_component()
        
        # 1. A, B を通る直線を取得 (なければ裏で作図する)
        common_lines = []
        if c1 and c2:
            common_lines = [obj for obj in (c1.subobjects & c2.subobjects) if getattr(obj, 'entity_type', '') == "Line"]
            
        if not common_lines and env is not None:
            line_name = f"Line_{A.name}_{B.name}_(Auto)"
            # 直線を作図 (この時点でAとBは直線に自動リンクされる)
            line_AB = create_geo_entity("LineThroughPoints", [A, B], name=line_name, env=env)
            line_AB.importance = 0.5
            env.nodes.append(line_AB)
            A.mmp_subobjects.add(line_AB)
            B.mmp_subobjects.add(line_AB)
            common_lines = [line_AB]

        # 2. 中点 M をその直線にリンク (これで A, M, B が同一直線に所属する)
        for ln in common_lines:
            link_logical_incidence(M, ln)
            
        # 👉 この結果、次の _run_logic_step() で `match_collinear_from_line_identity` が発火し、
        # 自動的に Fact("Collinear", [A, M, B]) が発行されます！

        # 3. 作図と同時に「AM/MB = 1」をE-Graphに直結する
        if hasattr(env, 'merge_entities_logically'):
            val_1 = ModInt(1)
            const_1 = None
            for n in env.nodes:
                if getattr(n, 'entity_type', '') == "Scalar":
                    nc = n.get_best_component()
                    if nc and any(d.def_type == "Constant" and d.parents and d.parents[0] == val_1 for d in nc.definitions):
                        const_1 = n
                        break
            if not const_1:
                const_1 = GeoEntity("Scalar", "Const_1")
                const_1.components.append(LogicalComponent(initial_def=Definition("Constant", [val_1], 0, 1)))
                env.nodes.append(const_1)

            ratio_name = f"Ratio_{A.name}{M.name}_{M.name}{B.name}_(Auto)"
            ratio_ent = None
            for n in env.nodes:
                if getattr(n, 'entity_type', '') == "Scalar":
                    nc = n.get_best_component()
                    if nc and any(d.def_type == "AffineRatio" and d.parents == [A, M, B] for d in nc.definitions):
                        ratio_ent = n
                        break
            if not ratio_ent:
                ratio_ent = GeoEntity("Scalar", ratio_name)
                ratio_ent.components.append(LogicalComponent(initial_def=Definition("AffineRatio", [A, M, B], 1, 1)))
                env.nodes.append(ratio_ent)

            c_rep = const_1.get_rep()
            r_rep = ratio_ent.get_rep()
            if c_rep != r_rep:
                env.merge_entities_logically(c_rep, r_rep)
    for p in parents:
        if isinstance(p, GeoEntity):
            link_logical_incidence(p, new_entity)


# ==========================================
# 🌟 図形タイプのマッピング辞書
# ==========================================
ENTITY_TYPE_MAP = {
    "Intersection": "Point", "Midpoint": "Point", "CirclesIntersection": "Point", "PoleOfLine": "Point",
    "LineThroughPoints": "Line", "PerpendicularLine": "Line", "ParallelLine": "Line", "TangentLine": "Line",
    "Circumcircle": "Circle",
    "DirectionOf": "Direction",
    "AnglePair": "Angle",
    "LengthSq": "Scalar", "AffineRatio": "Scalar", "Constant": "Scalar",
    "Triangle": "Triangle",
    "ShapeOf": "Shape"
}

def create_geo_entity(def_type: str, parents: List[Any], name: str = "", env=None, is_given=False, is_ghost=False, importance: float = None) -> 'GeoEntity':
    # 1. entity_type の決定
    entity_type = ENTITY_TYPE_MAP.get(def_type, "Unknown")

    # 2. 親からコンポーネントを安全に抽出
    valid_parents = [p for p in parents if hasattr(p, 'get_best_component')]
    parent_comps = [p.get_best_component() for p in valid_parents if p.get_best_component()]

    # ==========================================
    # 🌟 NEW: E-Graphの核心技術「Hash Consing (メモ化)」
    # まったく同じ設計図を持つ図形が既に存在する場合は、それ(最新の代表元)を返す
    # ==========================================
    if env is not None and not is_ghost and def_type not in ["Point", "Given", "Free", "Constant", "GivenPoint", "FreePoint"]:
        rep_parents = tuple(p.get_rep() for p in valid_parents)
        
        # 順不同図形の場合はソートして比較
        unordered_types = ["LengthSq", "Intersection", "CirclesIntersection", "Midpoint", "LineThroughPoints", "Circumcircle", "OtherLineCircleIntersection"]
        if def_type in unordered_types:
            rep_parents_sorted = tuple(sorted(rep_parents, key=lambda x: getattr(x, 'name', str(id(x)))))
        else:
            rep_parents_sorted = rep_parents
            
        target_signature = (def_type, rep_parents_sorted)
        
        for existing_node in env.nodes:
            if not existing_node.is_valid(): continue
            existing_rep = existing_node.get_rep()
            comp = existing_rep.get_best_component()
            if not comp: continue
            
            for d in comp.definitions:
                if d.def_type == def_type and len(d.parents) == len(rep_parents):
                    # 既存図形の親を最新にして比較
                    existing_d_parents = tuple(p.get_rep() for p in d.parents)
                    if def_type in unordered_types:
                        existing_d_parents = tuple(sorted(existing_d_parents, key=lambda x: getattr(x, 'name', str(id(x)))))
                        
                    if target_signature == (def_type, existing_d_parents):
                        import logging
                        logger = logging.getLogger("GeometryProver")
                        logger.debug(f"    ♻️ [メモ化再利用] 新規作成をスキップし既存図形 {existing_rep.name} を流用します: {def_type}({', '.join(getattr(p, 'name', '') for p in rep_parents)})")
                        
                        # 重要度が上がっていれば更新してあげる
                        if importance is not None:
                            existing_rep.base_importance = max(getattr(existing_rep, 'base_importance', 0.0), importance)
                        return existing_rep

    # 3. ゴースト判定
    parent_is_ghost = any(getattr(p, 'base_importance', 1.0) <= 0.0 for p in parents if hasattr(p, 'base_importance'))
    is_true_ghost = (env is None) or is_ghost or parent_is_ghost

    # 4. メタデータの計算
    if is_true_ghost:
        depth, naive_degree, base_imp = 1, 0, 0.0
        if not name.endswith("_(Ghost)"): name += "_(Ghost)"
    elif def_type == "Constant":
        depth, naive_degree, base_imp = 1, 0, 1.0 
    elif is_given:
        depth = 1
        naive_degree = sum(c.naive_degree for c in parent_comps)
        base_imp = 10.0 
    else:
        depth = max((c.depth for c in parent_comps), default=0) + 1
        naive_degree = sum(c.naive_degree for c in parent_comps)
        
        avg_parent_imp = sum(getattr(p, 'base_importance', 1.0) for p in parents if hasattr(p, 'base_importance')) / max(1, len(parents))
        decay_factor = 0.99 if entity_type in ["Scalar", "Direction", "Shape", "Triangle"] else 0.5
        base_imp = max(0.01, avg_parent_imp * decay_factor)

    # 5. エンティティの生成
    new_entity = GeoEntity(entity_type, name)
    new_entity.base_importance = base_imp 
    
    new_def = Definition(def_type, parents, naive_degree, depth)
    new_entity.components.append(LogicalComponent(initial_def=new_def))

    # ==========================================
    # 🌟 NEW: 退化テスト（試し斬り）をここで実行！
    # ==========================================
    # グラフに追加する前に、ランダム値で計算可能かチェックする
    if env is not None and getattr(env, 'all_vars', None) and def_type not in ["Point", "Given", "Free", "Constant"]:
        from mmp_core import ModInt
        import numpy as np
        
        # 乱数で1回だけ座標を計算してみる
        t_dict = {v: ModInt(np.random.randint(1, ModInt.MOD)) for v in env.all_vars}
        cache = {}
        test_val = new_entity.calculate(t_dict, cache)
        
        if not test_val:
            import logging
            logger = logging.getLogger("GeometryProver")
            logger.debug(f"    🚫 [生成ブロック] {name} ({def_type}) は退化図形のため生成をキャンセルしました")
            return None # 🌟 グラフを汚染する前に None を返して完全消滅させる！

    # ==========================================
    # 6. 環境(E-Graph)への登録とリンク（健康な図形のみ到達）
    # ==========================================
    if env is not None:
        apply_trivial_relations(new_entity, new_def, env)
        for p in valid_parents:
            link_logical_incidence(p, new_entity)
            
        if new_entity not in env.nodes:
            env.nodes.append(new_entity)

    return new_entity

def make_free_point(name, t_x, t_y, env):
    # t_x, t_y は Var オブジェクト
    coords = (t_x, t_y, 1)
    pt = GeoEntity("Point", name=name)
    pt.numerical_degree = 2
    # 前述の通り calculate メソッドをパッチ
    def calc_func(t_dict, cache):
        if id(pt) in cache: return cache[id(pt)]
        res = [coords[0].evaluate(t_dict), coords[1].evaluate(t_dict), 1]
        cache[id(pt)] = res
        return res
    pt.calculate = calc_func
    
    comp = LogicalComponent(initial_def=Definition("Given", [], naive_degree=0, depth=0))
    pt.components.append(comp)
    # 初期点なので基礎重要度を高く設定
    pt.base_importance = 10.0
    env.nodes.append(pt)
    return pt

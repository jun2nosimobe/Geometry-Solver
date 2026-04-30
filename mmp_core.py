import uuid
from typing import List, Set, Any, Dict
import numpy as np
import itertools

# ==========================================
# 1. 作図定義 (Definition)
# ==========================================
class Definition:
    def __init__(self, def_type: str, parents: List['GeoEntity'] = None, naive_degree: int = 1, depth: int = 1):
        self.def_type = def_type
        self.parents = parents or []
        self.naive_degree = naive_degree
        self.depth = depth

    def __hash__(self):
        return hash((self.def_type, tuple(p.id for p in self.parents)))

    def __eq__(self, other):
        if not isinstance(other, Definition): return False
        return self.def_type == other.def_type and self.parents == other.parents

# ==========================================
# 2. 論理コンポーネント (LogicalComponent)
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
# 3. 幾何学実体 (GeoEntity)
# ==========================================
class GeoEntity:
    def __init__(self, entity_type: str, name: str = ""):
        self.id = uuid.uuid4()
        self.name = name                 
        self.entity_type = entity_type   
        self.importance = 1.0            
        self.numerical_degree = None     
        self.components: List[LogicalComponent] = []
        self.mmp_subobjects: Set['GeoEntity'] = set() 
        self.associated_facts = []
        
        # 🌟 NEW: E-Graphマージ時のゾンビポインタ対策用
        self._merged_into = None
        
        # 🌟 NEW: Shape(相似クラス) エンティティ専用の辞書 {Triangle: (p1, p2, p3)}
        self.shape_members: Dict['GeoEntity', tuple] = {} 

    def get_best_component(self) -> LogicalComponent:
        if not self.components: return None
        return min(self.components, key=lambda c: (c.naive_degree, c.depth))

    def merge_numerical(self, other: 'GeoEntity'):
        if self == other: return
        self.components.extend(other.components)
        self.mmp_subobjects.update(other.mmp_subobjects)
        
        if self.numerical_degree is None:
            self.numerical_degree = other.numerical_degree
        elif other.numerical_degree is not None:
            self.numerical_degree = min(self.numerical_degree, other.numerical_degree)

        if other.name not in self.name:
            self.name = f"{self.name} = {other.name}"

    def prove_components_equal(self, comp_idx_1: int, comp_idx_2: int):
        if comp_idx_1 == comp_idx_2: return
        c1 = self.components[comp_idx_1]
        c2 = self.components[comp_idx_2]
        c1.merge_logical(c2)
        self.components.remove(c2) 

    def calculate(self, t_dict: Dict, cache: Dict) -> Any:
        cache_key = id(self)
        if cache_key in cache:
            return cache[cache_key]

        best_comp = self.get_best_component()
        if not best_comp or not best_comp.definitions:
            raise ValueError(f"{self.name} には計算可能な定義がありません。")
        
        best_def = min(best_comp.definitions, key=lambda d: d.naive_degree)
        if best_def.def_type == "Given":
            val = self._evaluate_given(t_dict)
        elif best_def.def_type in CALCULATION_REGISTRY:
            val = CALCULATION_REGISTRY[best_def.def_type](best_def.parents, t_dict, cache)
        else:
            raise NotImplementedError(f"未知の作図タイプ: {best_def.def_type}")

        cache[cache_key] = val
        return val

    def _evaluate_given(self, t_dict):
        return tuple(v.evaluate(t_dict) if hasattr(v, 'evaluate') else v for v in self._given_coords)


def normalize(v):
    if not v or isinstance(v[0], ModInt): return v
    max_val = max(abs(x) for x in v)
    if max_val < 1e-12: return v
    return tuple(x / max_val for x in v)

def cross_product(v1, v2):
    return (v1[1]*v2[2] - v1[2]*v2[1], 
            v1[2]*v2[0] - v1[0]*v2[2], 
            v1[0]*v2[1] - v1[1]*v2[0])

# ==========================================
# 作図ロジック (Calculation Registry)
# (既存のまま)
# ==========================================
def calc_intersection(parents, t_dict, cache):
    L1 = parents[0].calculate(t_dict, cache)
    L2 = parents[1].calculate(t_dict, cache)
    return normalize(cross_product(L1, L2))

def calc_line_through_points(parents, t_dict, cache):
    P1 = parents[0].calculate(t_dict, cache)
    P2 = parents[1].calculate(t_dict, cache)
    return normalize(cross_product(P1, P2))

def calc_midpoint(parents, t_dict, cache):
    P1 = parents[0].calculate(t_dict, cache)
    P2 = parents[1].calculate(t_dict, cache)
    z_term = P1[2] * P2[2]
    return normalize((P1[0]*P2[2] + P2[0]*P1[2], P1[1]*P2[2] + P2[1]*P1[2], z_term + z_term))

def calc_perpendicular(parents, t_dict, cache):
    L = parents[0].calculate(t_dict, cache)
    P = parents[1].calculate(t_dict, cache)
    inf_pt = (L[0], L[1], 0) if hasattr(L[0], 'value') else (L[0], L[1], 0)
    return normalize(cross_product(inf_pt, P))

def calc_parallel(parents, t_dict, cache):
    L = parents[0].calculate(t_dict, cache)
    P = parents[1].calculate(t_dict, cache)
    inf_pt = (-L[1], L[0], 0) if hasattr(L[0], 'value') else (-L[1], L[0], 0)
    return normalize(cross_product(inf_pt, P))

def calc_other_line_circle_intersection(parents, t_dict, cache):
    L = parents[0].calculate(t_dict, cache)
    C = parents[1].calculate(t_dict, cache)
    P_e = parents[2].calculate(t_dict, cache)
    u, v, w, s = C
    a, b, c = L
    vx, vy = -b, a
    A = u * (vx**2 + vy**2)
    B = 2 * u * (P_e[1]*a - P_e[0]*b) + (v*vx + w*vy) * P_e[2]
    new_x = A * P_e[0] - B * vx
    new_y = A * P_e[1] - B * vy
    new_z = A * P_e[2]
    return normalize((new_x, new_y, new_z))

def calc_other_circle_circle_intersection(parents, t_dict, cache):
    C1 = parents[0].calculate(t_dict, cache)
    C2 = parents[1].calculate(t_dict, cache)
    u1, v1, w1, s1 = C1
    u2, v2, w2, s2 = C2
    line_a = u2 * v1 - u1 * v2
    line_b = u2 * w1 - u1 * w2
    line_c = u2 * s1 - u1 * s2
    L_rad = (line_a, line_b, line_c)
    P_e = parents[2].calculate(t_dict, cache)
    u, v, w, s = C1
    a, b, c = L_rad
    vx, vy = -b, a
    A = u * (vx**2 + vy**2)
    B = 2 * u * (P_e[1]*a - P_e[0]*b) + (v*vx + w*vy) * P_e[2]
    return normalize((A*P_e[0] - B*vx, A*P_e[1] - B*vy, A*P_e[2]))

def calc_circumcircle(parents, t_dict, cache):
    P1 = parents[0].calculate(t_dict, cache)
    P2 = parents[1].calculate(t_dict, cache)
    P3 = parents[2].calculate(t_dict, cache)
    x1, y1, z1 = P1
    x2, y2, z2 = P2
    x3, y3, z3 = P3
    sq1 = x1**2 + y1**2
    sq2 = x2**2 + y2**2
    sq3 = x3**2 + y3**2
    u = z1*z2*z3 * (x1*(y2*z3 - y3*z2) - y1*(x2*z3 - x3*z2) + z1*(x2*y3 - x3*y2))
    v = -(sq1*(y2*z2*z3**2 - y3*z3*z2**2) - y1*z1*(sq2*z3**2 - sq3*z2**2) + z1**2*(sq2*y3*z3 - sq3*y2*z2))
    w = (sq1*(x2*z2*z3**2 - x3*z3*z2**2) - x1*z1*(sq2*z3**2 - sq3*z2**2) + z1**2*(sq2*x3*z3 - sq3*x2*z2))
    s = -(sq1*(x2*z2*y3*z3 - x3*z3*y2*z2) - x1*z1*(sq2*y3*z3 - sq3*y2*z2) + y1*z1*(sq2*x3*z3 - sq3*x2*z2))
    return normalize((u, v, w, s))

CALCULATION_REGISTRY = {
    "Intersection": calc_intersection,
    "LineThroughPoints": calc_line_through_points,
    "Midpoint": calc_midpoint,
    "PerpendicularLine": calc_perpendicular,
    "ParallelLine": calc_parallel,
    "Circumcircle": calc_circumcircle,
    "CirclesIntersection": calc_other_circle_circle_intersection,
}

# ==========================================
# 🌟 ヘルパー関数群 (代表元取得など)
# ==========================================
def get_representative(obj: GeoEntity) -> GeoEntity:
    """E-Graph上でマージされた古い図形から、最新の真の本体を遡る"""
    while getattr(obj, '_merged_into', None) is not None:
        obj = obj._merged_into
    return obj

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
            if hasattr(env, 'add_right_angle'): env.add_right_angle(ln, new_entity)
            else: env.right_angle.components[0].definitions.add(Definition("AnglePair", [ln, new_entity]))
    elif def_type == "ParallelLine":
        ln, pt = parents[0], parents[1]
        link_logical_incidence(pt, new_entity)
        if env is not None:
            if hasattr(env, 'add_right_angle'): env.add_right_angle(ln, new_entity)
            else: env.zero_angle.components[0].definitions.add(Definition("AnglePair", [ln, new_entity]))
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
# 🌟 作図ビルダー (Construction Builder)
# ==========================================
def create_geo_entity(def_type: str, parents: List['GeoEntity'], name: str = "", env=None) -> 'GeoEntity':
    if env:
        for node in env.nodes:
            comp = node.get_best_component()
            if comp:
                for d in comp.definitions:
                    if d.def_type == def_type and d.parents == parents:
                        return node 
                        
    if def_type in ["Intersection", "Midpoint", "CirclesIntersection"]:
        entity_type = "Point"
    elif def_type in ["LineThroughPoints", "PerpendicularLine", "ParallelLine"]:
        entity_type = "Line"
    elif def_type == "Circumcircle":
        entity_type = "Circle"
    elif def_type == "DirectionOf":
        entity_type = "Direction"
    elif def_type == "LengthOf":
        entity_type = "LengthSq"
    # 🌟 NEW: Triangle と ShapeOf 型を追加
    elif def_type == "Triangle":
        entity_type = "Triangle"
    elif def_type == "ShapeOf":
        entity_type = "Shape"
    else:
        entity_type = "Unknown"

    depth = max((p.get_best_component().depth for p in parents if p.get_best_component()), default=0) + 1
    naive_degree = sum((p.get_best_component().naive_degree for p in parents if p.get_best_component())) 

    new_entity = GeoEntity(entity_type, name)
    new_def = Definition(def_type, parents, naive_degree, depth)
    new_comp = LogicalComponent(initial_def=new_def)
    new_entity.components.append(new_comp)

    apply_trivial_relations(new_entity, new_def, env)

    return new_entity


# ==========================================
# 🌟 枝刈り付き 三角形＆相似クラス 作成・マージ群
# ==========================================
def get_or_create_triangle(p1: GeoEntity, p2: GeoEntity, p3: GeoEntity, env) -> GeoEntity:
    """有望な三角形のみを辞書順で1つだけ登録し、同時にShape(相似クラス)を初期化する"""
    p1, p2, p3 = get_representative(p1), get_representative(p2), get_representative(p3)
    pts = {p1, p2, p3}
    if len(pts) < 3: return None
    
    # すでにこの3点のTriangleが存在するか検索
    for node in env.nodes:
        if getattr(node, 'entity_type', '') == "Triangle":
            comp = node.get_best_component()
            if comp:
                for d in comp.definitions:
                    if d.def_type == "Triangle" and set(d.parents) == pts:
                        return node
                        
    # 次数(Degree)による枝刈り
    deg1 = getattr(p1, 'numerical_degree', 1) or 1
    deg2 = getattr(p2, 'numerical_degree', 1) or 1
    deg3 = getattr(p3, 'numerical_degree', 1) or 1
    if deg1 + deg2 + deg3 > 30:
        return None
        
    # 物理コンテナは必ず辞書順で作成
    sorted_pts = sorted(list(pts), key=lambda x: x.name)
    name = f"Tri_{sorted_pts[0].name}{sorted_pts[1].name}{sorted_pts[2].name}"
    
    new_tri = create_geo_entity("Triangle", sorted_pts, name=name, env=env)
    new_tri.importance = 2.0
    
    # 🌟 Triangle作成と同時に、それを1つだけ含むShape(相似クラス)を初期化
    shape_name = f"Shape_{name}"
    new_shape = create_geo_entity("ShapeOf", [new_tri], name=shape_name, env=env)
    
    # そのShapeの中で、各スロット(0, 1, 2)にどの頂点が入っているかを記録
    new_shape.shape_members[new_tri] = tuple(sorted_pts)
    
    # 環境に追加
    env.nodes.extend([new_tri, new_shape])
    return new_tri

def merge_shapes(shape1: GeoEntity, shape2: GeoEntity) -> GeoEntity:
    """2つの相似クラス(Shape)を、対応順序(S3群の演算)を壊さずにマージする"""
    shape1 = get_representative(shape1)
    shape2 = get_representative(shape2)
    if shape1 == shape2: return shape1
    
    # 両方に属している「橋渡し」の三角形を探す
    common_tri = next((t for t in shape1.shape_members if t in shape2.shape_members), None)
    if not common_tri: return None
    
    tuple1 = shape1.shape_members[common_tri]
    tuple2 = shape2.shape_members[common_tri]
    
    # 順列のマッピングを計算 (tuple2の i 番目が tuple1の 何番目に入るか)
    mapping = {}
    for i, pt in enumerate(tuple2):
        mapping[i] = tuple1.index(pt)
        
    # shape2のメンバーを、順序を補正しながらshape1にお引っ越し
    for tri, pts in shape2.shape_members.items():
        if tri == common_tri: continue
        new_pts = [None, None, None]
        for i, pt in enumerate(pts):
            new_pts[mapping[i]] = pt
        shape1.shape_members[tri] = tuple(new_pts)
        
    # 統合された側をマーク (E-Graphのゾンビ化)
    shape2._merged_into = shape1
    return shape1

# ==========================================
# 1. 有限体 (ModInt) クラスと数学エンジン
# (既存のまま)
# ==========================================
class ModInt:
    MOD = 998244353 
    I = 911660635
    def __init__(self, value):
        if isinstance(value, ModInt): self.value = value.value
        elif isinstance(value, complex): self.value = (int(value.real) + int(value.imag) * ModInt.I) % ModInt.MOD
        else: self.value = int(value) % ModInt.MOD
    def __add__(self, other): return ModInt(self.value + (other.value if isinstance(other, ModInt) else int(other)))
    def __radd__(self, other): return self.__add__(other)
    def __sub__(self, other): return ModInt(self.value - (other.value if isinstance(other, ModInt) else int(other)))
    def __rsub__(self, other): return ModInt((other.value if isinstance(other, ModInt) else int(other)) - self.value)
    def __mul__(self, other): return ModInt(self.value * (other.value if isinstance(other, ModInt) else int(other)))
    def __rmul__(self, other): return self.__mul__(other)
    def __truediv__(self, other):
        ov = other.value if isinstance(other, ModInt) else int(other)
        if ov == 0: raise ZeroDivisionError()
        return ModInt(self.value * pow(ov, self.MOD - 2, self.MOD))
    def __rtruediv__(self, other):
        ov = other.value if isinstance(other, ModInt) else int(other)
        if self.value == 0: raise ZeroDivisionError()
        return ModInt(ov * pow(self.value, self.MOD - 2, self.MOD))
    def __pow__(self, power): return ModInt(pow(self.value, int(power), self.MOD))
    def __neg__(self): return ModInt(-self.value)
    def __eq__(self, other):
        if other == 0: return self.value == 0
        return self.value == (other.value if isinstance(other, ModInt) else int(other) % self.MOD)
    def __abs__(self): return abs(self.value)
    def __repr__(self): return str(self.value)

def matrix_rank_mod(matrix_mod):
    rows, cols = len(matrix_mod), len(matrix_mod[0]) if matrix_mod else 0
    rank = 0
    M = [[matrix_mod[r][c] for c in range(cols)] for r in range(rows)]
    for c in range(cols):
        pivot_r = next((r for r in range(rank, rows) if M[r][c].value != 0), -1)
        if pivot_r == -1: continue
        M[rank], M[pivot_r] = M[pivot_r], M[rank]
        inv_val = ModInt(1) / M[rank][c]
        for j in range(c, cols): M[rank][j] = M[rank][j] * inv_val
        for r in range(rows):
            if r != rank and M[r][c].value != 0:
                factor = M[r][c]
                for j in range(c, cols): M[r][j] = M[r][j] - factor * M[rank][j]
        rank += 1
        if rank == rows: break
    return rank

def get_numerical_degree(t_values, x_values, max_d, mode='mod', tolerance=1e-8):
    N = len(t_values)
    if mode == 'mod':
        for d in range(max_d + 1):
            if N < 2 * d + 2: continue
            A = [[ModInt(0) for _ in range(2 * d + 2)] for _ in range(N)]
            for i in range(N):
                t, x = t_values[i], x_values[i]
                for k in range(d + 1):
                    A[i][k] = t**k
                    A[i][d + 1 + k] = -x * (t**k)
            if matrix_rank_mod(A) < 2 * d + 2: return d
        return max_d
    return max_d
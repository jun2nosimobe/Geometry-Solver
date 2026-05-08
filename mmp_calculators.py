# mmp_calculators.py
from mmp_core import ModInt

CALCULATORS = {}

def register_calc(def_type):
    def decorator(func):
        CALCULATORS[def_type] = func
        return func
    return decorator

# ==========================================
# 🌟 ヘルパー関数群
# ==========================================
def normalize(v):
    if not v: return v
    for x in v:
        if (hasattr(x, 'value') and x.value != 0) or (not hasattr(x, 'value') and abs(float(x)) > 1e-9):
            inv = ModInt(1) / x if hasattr(x, 'value') else 1.0 / x
            return tuple(e * inv if hasattr(e, 'value') else e * inv for e in v)
    return tuple(v)

def cross_product(v1, v2):
    return (v1[1]*v2[2] - v1[2]*v2[1], 
            v1[2]*v2[0] - v1[0]*v2[2], 
            v1[0]*v2[1] - v1[1]*v2[0])

def get_cartesian(P):
    inv_z = ModInt(1) / P[-1]
    return P[0] * inv_z, P[1] * inv_z

# ==========================================
# 🌟 各図形の計算ロジック
# ==========================================

@register_calc("Intersection")
def calc_intersection(parents, t_dict, cache):
    L1 = parents[0].calculate(t_dict, cache)
    L2 = parents[1].calculate(t_dict, cache)
    if not L1 or not L2: return []
    return list(normalize(cross_product(L1, L2)))

@register_calc("LineThroughPoints")
@register_calc("Line")
def calc_line_through_points(parents, t_dict, cache):
    P1 = parents[0].calculate(t_dict, cache)
    P2 = parents[1].calculate(t_dict, cache)
    if not P1 or not P2 or len(P1) != 3 or len(P2) != 3: return []
    
    cx = P1[1] * P2[2] - P1[2] * P2[1]
    cy = P1[2] * P2[0] - P1[0] * P2[2]
    cz = P1[0] * P2[1] - P1[1] * P2[0]
    
    def is_zero(val):
        if hasattr(val, 'value'): return val.value == 0
        return abs(float(val)) < 1e-9
        
    if is_zero(cx) and is_zero(cy) and is_zero(cz):
        return []
    return list(normalize((cx, cy, cz)))

@register_calc("Midpoint")
@register_calc("Mid")
def calc_midpoint(parents, t_dict, cache):
    P1 = parents[0].calculate(t_dict, cache)
    P2 = parents[1].calculate(t_dict, cache)
    if not P1 or not P2: return []
    z_term = P1[2] * P2[2]
    return list(normalize((P1[0]*P2[2] + P2[0]*P1[2], P1[1]*P2[2] + P2[1]*P1[2], z_term + z_term)))

@register_calc("PerpendicularLine")
@register_calc("Perp")
def calc_perpendicular(parents, t_dict, cache):
    L = parents[0].calculate(t_dict, cache)
    P = parents[1].calculate(t_dict, cache)
    if not L or len(L) < 3 or not P or len(P) < 3: return []
    inf_pt = (L[0], L[1], 0) if hasattr(L[0], 'value') else (L[0], L[1], 0)
    return list(normalize(cross_product(inf_pt, P)))

@register_calc("ParallelLine")
def calc_parallel(parents, t_dict, cache):
    L = parents[0].calculate(t_dict, cache)
    P = parents[1].calculate(t_dict, cache)
    if not L or len(L) < 3 or not P or len(P) < 3: return []
    inf_pt = (-L[1], L[0], 0) if hasattr(L[0], 'value') else (-L[1], L[0], 0)
    return list(normalize(cross_product(inf_pt, P)))

@register_calc("LineCircleIntersection")
def calc_other_line_circle_intersection(parents, t_dict, cache):
    L = parents[0].calculate(t_dict, cache)
    C = parents[1].calculate(t_dict, cache)
    P_e = parents[2].calculate(t_dict, cache)
    if not L or not C or not P_e: return []
    u, v, w, s = C
    a, b, c = L
    vx, vy = -b, a
    A = u * (vx**2 + vy**2)
    B = 2 * u * (P_e[1]*a - P_e[0]*b) + (v*vx + w*vy) * P_e[2]
    new_x = A * P_e[0] - B * vx
    new_y = A * P_e[1] - B * vy
    new_z = A * P_e[2]
    return list(normalize((new_x, new_y, new_z)))

@register_calc("CirclesIntersection")
def calc_other_circle_circle_intersection(parents, t_dict, cache):
    C1 = parents[0].calculate(t_dict, cache)
    C2 = parents[1].calculate(t_dict, cache)
    P_e = parents[2].calculate(t_dict, cache)
    if not C1 or not C2 or not P_e: return []
    u1, v1, w1, s1 = C1
    u2, v2, w2, s2 = C2
    line_a = u2 * v1 - u1 * v2
    line_b = u2 * w1 - u1 * w2
    line_c = u2 * s1 - u1 * s2
    L_rad = (line_a, line_b, line_c)
    
    u, v, w, s = C1
    a, b, c = L_rad
    vx, vy = -b, a
    A = u * (vx**2 + vy**2)
    B = 2 * u * (P_e[1]*a - P_e[0]*b) + (v*vx + w*vy) * P_e[2]
    return list(normalize((A*P_e[0] - B*vx, A*P_e[1] - B*vy, A*P_e[2])))

@register_calc("Circumcircle")
def calc_circumcircle(parents, t_dict, cache):
    P1 = parents[0].calculate(t_dict, cache)
    P2 = parents[1].calculate(t_dict, cache)
    P3 = parents[2].calculate(t_dict, cache)
    if not P1 or not P2 or not P3: return []
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
    return list(normalize((u, v, w, s)))

@register_calc("Direction")
@register_calc("DirectionOf")
@register_calc("Dir")
def calc_direction(parents, t_dict, cache):
    """方向ベクトルの計算 (1つの直線、または2点から)"""
    if len(parents) == 1:
        L = parents[0].calculate(t_dict, cache)
        if not L or len(L) < 3: return []
        return list(normalize((L[0], L[1], 0)))
    elif len(parents) == 2:
        P1 = parents[0].calculate(t_dict, cache)
        P2 = parents[1].calculate(t_dict, cache)
        if not P1 or not P2 or len(P1) != 3 or len(P2) != 3: return []
        dx = P2[0]*P1[2] - P1[0]*P2[2]
        dy = P2[1]*P1[2] - P1[1]*P2[2]
        return list(normalize((dy, -dx, 0))) # 射影座標の法線として扱う
    return []

@register_calc("LengthSq")
def calc_length_sq(parents, t_dict, cache):
    P1 = parents[0].calculate(t_dict, cache)
    P2 = parents[1].calculate(t_dict, cache)
    if not P1 or not P2 or len(P1) < 3 or len(P2) < 3: return []
    x1, y1 = get_cartesian(P1)
    x2, y2 = get_cartesian(P2)
    val = (x1 - x2)**2 + (y1 - y2)**2
    return [val]

@register_calc("AffineRatio")
def calc_affine_ratio(parents, t_dict, cache):
    A = parents[0].calculate(t_dict, cache)
    B = parents[1].calculate(t_dict, cache)
    C = parents[2].calculate(t_dict, cache)
    if not A or not B or not C: return []
    xa, ya = get_cartesian(A)
    xb, yb = get_cartesian(B)
    xc, yc = get_cartesian(C)
    dx1, dy1 = xb - xa, yb - ya
    dx2, dy2 = xc - xb, yc - yb
    if dx2 != 0: val = dx1 / dx2
    elif dy2 != 0: val = dy1 / dy2
    else: val = ModInt(0)
    return [val, ModInt(1)]

@register_calc("Constant")
def calc_constant(parents, t_dict, cache):
    return [parents[0], ModInt(1)]

@register_calc("AnglePair")
def calc_angle_pair(parents, t_dict, cache):
    dir1 = parents[0].calculate(t_dict, cache)
    dir2 = parents[1].calculate(t_dict, cache)
    if not dir1 or not dir2 or len(dir1) < 2 or len(dir2) < 2: return []
    a1, b1 = dir1[0], dir1[1]
    a2, b2 = dir2[0], dir2[1]
    cross_val = a1 * b2 - b1 * a2
    dot_val = a1 * a2 + b1 * b2
    return [cross_val**2, dot_val**2]


@register_calc("TangentLine")
def calc_tangent_line(entity, t_dict, cache):
    """円の周上の点における接線 (parents: [Circumcircle, Point])"""
    if len(entity.parents) != 2: return []
    circle = entity.parents[0]
    pt = entity.parents[1]
    
    comp = circle.get_best_component()
    if not comp: return []
    
    # 円を定義している3点を取得
    circle_def = None
    for d in comp.definitions:
        if d.def_type == "Circumcircle" and len(d.parents) == 3:
            circle_def = d; break
    if not circle_def: return []
    
    p1 = circle_def.parents[0].calculate(t_dict, cache)
    p2 = circle_def.parents[1].calculate(t_dict, cache)
    p3 = circle_def.parents[2].calculate(t_dict, cache)
    p_t = pt.calculate(t_dict, cache)
    if not (p1 and p2 and p3 and p_t): return []
    
    # 射影座標からデカルト座標 (x, y) に変換
    x1, y1 = p1[0]/p1[2], p1[1]/p1[2]
    x2, y2 = p2[0]/p2[2], p2[1]/p2[2]
    x3, y3 = p3[0]/p3[2], p3[1]/p3[2]
    xt, yt = p_t[0]/p_t[2], p_t[1]/p_t[2]
    
    # 外心 O の座標 (Ox, Oy) を計算
    D = 2 * (x1*(y2 - y3) + x2*(y3 - y1) + x3*(y1 - y2))
    if hasattr(D, 'value') and D.value == 0: return []
    if D == 0: return []
    
    sq1, sq2, sq3 = x1**2 + y1**2, x2**2 + y2**2, x3**2 + y3**2
    Ox = (sq1*(y2 - y3) + sq2*(y3 - y1) + sq3*(y1 - y2)) / D
    Oy = (sq1*(x3 - x2) + sq2*(x1 - x3) + sq3*(x2 - x1)) / D
    
    # 法線ベクトル n = (xt - Ox, yt - Oy)
    nx = xt - Ox
    ny = yt - Oy
    
    # 接線の方程式: nx * X + ny * Y - (nx * xt + ny * yt) * Z = 0
    c_val = -(nx * xt + ny * yt)
    
    return [nx, ny, c_val]
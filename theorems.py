# theorems.py
import itertools
from logic_core import Fact, GeometryTheorem
from mmp_core import create_geo_entity 
import numpy as np
from mmp_core import get_numerical_degree, ModInt

# ==========================================
# ヘルパー関数群
# ==========================================
def get_representative(obj):
    while hasattr(obj, '_merged_into') and obj._merged_into is not None:
        obj = obj._merged_into
    return obj

def get_points_on(curve_entity):
    curve_entity = get_representative(curve_entity)
    comp = curve_entity.get_best_component()
    if not comp: return set()
    return {get_representative(obj) for obj in comp.subobjects if getattr(get_representative(obj), 'entity_type', '') == "Point"}

def are_collinear_egraph(p1, p2, p3):
    c1, c2, c3 = p1.get_best_component(), p2.get_best_component(), p3.get_best_component()
    if not (c1 and c2 and c3): return False
    return any(obj.entity_type == "Line" for obj in (c1.subobjects & c2.subobjects & c3.subobjects))

def get_or_create_line(p1, p2, env):
    p1 = get_representative(p1)
    p2 = get_representative(p2)
    c1 = p1.get_best_component()
    c2 = p2.get_best_component()
    
    lines_1 = set()
    lines_2 = set()
    if c1: lines_1.update(get_representative(obj) for obj in c1.subobjects if getattr(get_representative(obj), 'entity_type', '') == "Line")
    lines_1.update(get_representative(obj) for obj in p1.mmp_subobjects if getattr(get_representative(obj), 'entity_type', '') == "Line")
    if c2: lines_2.update(get_representative(obj) for obj in c2.subobjects if getattr(get_representative(obj), 'entity_type', '') == "Line")
    lines_2.update(get_representative(obj) for obj in p2.mmp_subobjects if getattr(get_representative(obj), 'entity_type', '') == "Line")
    
    l2_dict = {id(ln): ln for ln in lines_2}
    l2_names = {ln.name: ln for ln in lines_2}

    common_lines = []
    for ln1 in lines_1:
        if id(ln1) in l2_dict: common_lines.append(ln1)
        elif ln1.name in l2_names: common_lines.append(l2_names[ln1.name]) 

    if common_lines: return common_lines[0]

    name = f"Line_{p1.name}_{p2.name}_(Auto)"
    new_line = create_geo_entity("LineThroughPoints", [p1, p2], name=name, env=env)
    new_line.importance = 0.5 
    env.nodes.append(new_line)
    p1.mmp_subobjects.add(new_line)
    p2.mmp_subobjects.add(new_line)
    return new_line

def get_or_create_length_sq(p1, p2, env):
    p1, p2 = get_representative(p1), get_representative(p2)
    pts = {p1, p2}
    for n in env.nodes:
        if getattr(get_representative(n), 'entity_type', '') == "Scalar":
            comp = n.get_best_component()
            if comp:
                for d in comp.definitions:
                    if d.def_type == "LengthSq" and set(d.parents) == pts: return n
    name = f"LenSq_{p1.name}{p2.name}_(Auto)"
    new_len = create_geo_entity("LengthSq", [p1, p2], name=name, env=env)
    env.nodes.append(new_len)
    return new_len

def get_or_create_affine_ratio(A, B, C, env):
    A, B, C = get_representative(A), get_representative(B), get_representative(C)
    parents = [A, B, C]
    for n in env.nodes:
        if getattr(get_representative(n), 'entity_type', '') == "Scalar":
            comp = n.get_best_component()
            if comp:
                for d in comp.definitions:
                    if d.def_type == "AffineRatio" and d.parents == parents: return n
    name = f"Ratio_{A.name}{B.name}_{B.name}{C.name}_(Auto)"
    new_ratio = create_geo_entity("AffineRatio", parents, name=name, env=env)
    env.nodes.append(new_ratio)
    return new_ratio

def get_constant_value(scalar_entity):
    rep = get_representative(scalar_entity)
    comp = rep.get_best_component()
    if not comp: return None
    for d in comp.definitions:
        if d.def_type == "Constant": return d.parents[0] 
    return None

def get_or_create_constant(val, env):
    val_mod = ModInt(val) if not isinstance(val, ModInt) else val
    for n in env.nodes:
        if getattr(get_representative(n), 'entity_type', '') == "Scalar":
            c = get_constant_value(n)
            if c is not None and c == val_mod: return n
    name = f"Const_{val_mod.value}"
    new_const = create_geo_entity("Constant", [val_mod], name=name, env=env)
    env.nodes.append(new_const)
    return new_const

# ==========================================
# 定理群
# ==========================================

# --- 円周角の定理 ---
def match_cyclic_lines(facts, env):
    matches = []
    for f in facts:
        if f.fact_type == "Concyclic":
            points = list(set(f.objects))
            if len(points) >= 4:
                for chord in itertools.combinations(points, 2):
                    A, B = chord
                    others = [p for p in points if p not in chord]
                    for C, D in itertools.combinations(others, 2):
                        L_CA = get_or_create_line(C, A, env)
                        L_CB = get_or_create_line(C, B, env)
                        L_DA = get_or_create_line(D, A, env)
                        L_DB = get_or_create_line(D, B, env)
                        if L_CA and L_CB and L_DA and L_DB:
                            matches.append((L_CA, L_CB, L_DA, L_DB, f))
    return matches

def apply_cyclic_lines(match):
    L_CA, L_CB, L_DA, L_DB, source_fact = match
    conclusion = Fact("EqualAngle_Line", [L_CA, L_CB, L_DA, L_DB], is_proven=False, proof_source=f"円周角の定理 (前提: {source_fact})")
    return [source_fact], conclusion

# --- 円周角の定理の逆 ---
def match_converse_cyclic_lines(facts, env):
    matches = []
    angle_entities = [n for n in env.nodes if getattr(get_representative(n), 'entity_type', '') == "Angle"]
    
    for angle_ent in set(get_representative(a) for a in angle_entities):
        comp = angle_ent.get_best_component()
        if not comp: continue
        
        angle_pairs = [d.parents for d in comp.definitions if d.def_type == "AnglePair" and len(d.parents) == 2]
        if len(angle_pairs) < 2: continue
        
        for (L1, L2), (L3, L4) in itertools.combinations(angle_pairs, 2):
            pts_C = get_points_on(L1) & get_points_on(L2)
            pts_D = get_points_on(L3) & get_points_on(L4)
            pts_A = get_points_on(L1) & get_points_on(L3)
            pts_B = get_points_on(L2) & get_points_on(L4)
            
            for C in pts_C:
                for D in pts_D:
                    if C == D: continue
                    for A in pts_A:
                        if A in (C, D): continue
                        for B in pts_B:
                            if B in (A, C, D): continue
                            # ★ 修正: 4点がいずれも共線になっていないことを厳密にチェック
                            if are_collinear_egraph(A, B, C) or are_collinear_egraph(A, B, D) or \
                               are_collinear_egraph(A, C, D) or are_collinear_egraph(B, C, D):
                                continue
                            matches.append((A, B, C, D, f"E-Graph上で ∠({L1.name},{L2.name}) = ∠({L3.name},{L4.name}) が確認されたため"))
    return matches

def apply_converse_cyclic_lines(match):
    A, B, C, D, detailed_reason = match
    conclusion = Fact("Concyclic", [A, B, C, D], is_proven=False, proof_source=f"円周角の定理の逆 ({detailed_reason})")
    return [], conclusion

# --- 平行線の性質 ---
def match_parallel_angles_by_direction(facts, env):
    matches = []
    directions = [n for n in env.nodes if n.entity_type == "Direction"]
    all_lines = {n for n in env.nodes if n.entity_type == "Line"}
    
    for dir_node in directions:
        comp = dir_node.get_best_component()
        if not comp: continue
        parallel_lines = [d.parents[0] for d in comp.definitions if d.def_type == "DirectionOf"]
        if len(parallel_lines) < 2: continue
        
        for L1, L2 in itertools.combinations(parallel_lines, 2):
            pts_L1 = get_points_on(L1)
            pts_L2 = get_points_on(L2)
            for M in all_lines:
                if M == L1 or M == L2: continue
                pts_M = get_points_on(M)
                if (pts_L1 & pts_M) and (pts_L2 & pts_M):
                    matches.append((L1, M, L2, M, f"平行線の性質({dir_node.name})"))
    return matches

def apply_parallel_angles_by_direction(match):
    L1, M, L2, M_dup, reason = match
    conclusion = Fact("EqualAngle_Line", [L1, M, L2, M_dup], is_proven=False, proof_source=reason)
    return [], conclusion


# --- 平行線と線分の比 (平行 -> 比が等しい) ---
def match_parallel_to_ratio(facts, env):
    matches = []
    directions = [n for n in env.nodes if getattr(get_representative(n), 'entity_type', '') == "Direction"]
    for dir_node in set(get_representative(d) for d in directions):
        comp = dir_node.get_best_component()
        if not comp: continue
        parallel_lines = [d.parents[0] for d in comp.definitions if d.def_type == "DirectionOf"]
        if len(parallel_lines) < 2: continue
        
        for L1, L2 in itertools.combinations(parallel_lines, 2):
            pts1 = get_points_on(L1)
            pts2 = get_points_on(L2)
            if len(pts1) < 2 or len(pts2) < 2: continue
            
            for D, E in itertools.permutations(pts1, 2):
                for B, C in itertools.permutations(pts2, 2):
                    L_DB = get_or_create_line(D, B, env)
                    L_EC = get_or_create_line(E, C, env)
                    if L_DB and L_EC and L_DB != L_EC:
                        common_A = get_points_on(L_DB) & get_points_on(L_EC)
                        if common_A:
                            A = list(common_A)[0]
                            if A not in (B, C, D, E):
                                R1 = get_or_create_affine_ratio(A, D, B, env)
                                R2 = get_or_create_affine_ratio(A, E, C, env)
                                matches.append((R1, R2, f"平行線と線分の比 ({L1.name} // {L2.name})"))
    return matches

def apply_parallel_to_ratio(match):
    R1, R2, reason = match
    return [], Fact("Identical", [R1, R2], is_proven=False, proof_source=reason)

# --- 平行線と線分の比の逆 (比が等しい -> 平行) ---
def match_ratio_to_parallel(facts, env):
    matches = []
    scalars = [n for n in env.nodes if getattr(get_representative(n), 'entity_type', '') == "Scalar"]
    
    for scalar in set(get_representative(s) for s in scalars):
        comp = scalar.get_best_component()
        if not comp: continue
        
        ratios = [d.parents for d in comp.definitions if d.def_type == "AffineRatio" and len(d.parents) == 3]
        
        for (A1, D, B), (A2, E, C) in itertools.combinations(ratios, 2):
            if A1 == A2:
                A = A1
                if len({A, D, B, E, C}) >= 5:  
                    L_DE = get_or_create_line(D, E, env)
                    L_BC = get_or_create_line(B, C, env)
                    if L_DE and L_BC and L_DE != L_BC:
                        dir_DE = get_direction(L_DE, env)
                        dir_BC = get_direction(L_BC, env)
                        matches.append((dir_DE, dir_BC, f"平行線と線分の比の逆 (△{A.name}{B.name}{C.name} において {A.name}{D.name}:{D.name}{B.name} = {A.name}{E.name}:{E.name}{C.name})"))
    return matches

def apply_ratio_to_parallel(match):
    dir_DE, dir_BC, reason = match
    return [], Fact("Identical", [dir_DE, dir_BC], is_proven=False, proof_source=reason)


# --- 二等辺三角形の底角定理 (辺 -> 角) ---
def match_isosceles_base_angle(facts, env):
    matches = []
    scalars = [n for n in env.nodes if getattr(get_representative(n), 'entity_type', '') == "Scalar"]
    
    for scalar in set(get_representative(s) for s in scalars):
        comp = scalar.get_best_component()
        if not comp: continue
        segments = [d.parents for d in comp.definitions if d.def_type == "LengthSq" and len(d.parents) == 2]
        
        for (A, B), (C, D) in itertools.combinations(segments, 2):
            shared = set([A, B]) & set([C, D])
            if len(shared) == 1:
                P = list(shared)[0] 
                X = A if B == P else B
                Y = C if D == P else D
                
                if X != Y and not are_collinear_egraph(P, X, Y):
                    L_PX = get_or_create_line(P, X, env)
                    L_PY = get_or_create_line(P, Y, env)
                    L_XY = get_or_create_line(X, Y, env)
                    if L_PX and L_PY and L_XY:
                        matches.append((L_PX, L_XY, L_PY, L_XY, f"二等辺三角形の底角定理 (△{P.name}{X.name}{Y.name}, {P.name}{X.name}={P.name}{Y.name})"))
    return matches

def apply_isosceles_base_angle(match):
    L_PX, L_XY, L_PY, L_XY_dup, reason = match
    conclusion = Fact("EqualAngle_Line", [L_PX, L_XY, L_PY, L_XY_dup], is_proven=False, proof_source=reason)
    return [], conclusion

# --- 二等辺三角形の底角定理の逆 (角 -> 辺) ---
def match_isosceles_converse(facts, env):
    matches = []
    angles = [n for n in env.nodes if getattr(get_representative(n), 'entity_type', '') == "Angle"]
    
    for angle in set(get_representative(a) for a in angles):
        comp = angle.get_best_component()
        if not comp: continue
        pairs = [d.parents for d in comp.definitions if d.def_type == "AnglePair" and len(d.parents) == 2]
        
        for (L1, M1), (L2, M2) in itertools.combinations(pairs, 2):
            target_M = None
            L_PX, L_PY = None, None
            
            if M1 == M2: target_M, L_PX, L_PY = M1, L1, L2
            elif L1 == L2: target_M, L_PX, L_PY = L1, M1, M2
            elif M1 == L2: target_M, L_PX, L_PY = M1, L1, M2
            elif L1 == M2: target_M, L_PX, L_PY = L1, M1, L2
            
            if target_M and L_PX != L_PY:
                P_set = get_points_on(L_PX) & get_points_on(L_PY)
                X_set = get_points_on(L_PX) & get_points_on(target_M)
                Y_set = get_points_on(L_PY) & get_points_on(target_M)
                
                if P_set and X_set and Y_set:
                    P, X, Y = list(P_set)[0], list(X_set)[0], list(Y_set)[0]
                    if len({P, X, Y}) == 3 and not are_collinear_egraph(P, X, Y):
                        Len_PX = get_or_create_length_sq(P, X, env)
                        Len_PY = get_or_create_length_sq(P, Y, env)
                        matches.append((Len_PX, Len_PY, f"二等辺三角形の底角の逆 (∠{X.name} = ∠{Y.name})"))
    return matches

def apply_isosceles_converse(match):
    Len_PX, Len_PY, reason = match
    conclusion = Fact("Identical", [Len_PX, Len_PY], is_proven=False, proof_source=reason)
    return [], conclusion

# --- メネラウスの定理 (定数代入) ---
def match_menelaus(facts, env):
    matches = []
    collinears = [f for f in facts if f.fact_type == "Collinear" and f.is_proven]
    
    for f in collinears:
        if len(f.objects) < 3: continue
        D, E, F = f.objects[:3]
        
        triangles = [n for n in env.nodes if getattr(get_representative(n), 'entity_type', '') == "Triangle"]
        for tri in set(get_representative(t) for t in triangles):
            A, B, C = tri.get_best_component().triangle_points
            
            if are_collinear_egraph(B, C, D) and are_collinear_egraph(C, A, E) and are_collinear_egraph(A, B, F):
                R1 = get_or_create_affine_ratio(B, D, C, env) # BD/DC
                R2 = get_or_create_affine_ratio(C, E, A, env) # CE/EA
                R3 = get_or_create_affine_ratio(A, F, B, env) # AF/FB
                matches.append((R1, R2, R3, f"メネラウスの定理 (△{A.name}{B.name}{C.name} と 横断線{D.name}{E.name}{F.name})"))
    return matches

def apply_menelaus(match):
    R1, R2, R3, reason = match
    v1 = get_constant_value(R1)
    v2 = get_constant_value(R2)
    v3 = get_constant_value(R3)
    
    if v1 is not None and v2 is not None and v3 is None:
        target_val = ModInt(-1) / (v1 * v2)
        target_const = get_or_create_constant(target_val, R1.env) # ※R1から辿って一時的に作成
        conclusion = Fact("Identical", [R3, target_const], is_proven=False, proof_source=reason)
        return [], conclusion
    elif v2 is not None and v3 is not None and v1 is None:
        target_val = ModInt(-1) / (v2 * v3)
        target_const = get_or_create_constant(target_val, R1.env) 
        conclusion = Fact("Identical", [R1, target_const], is_proven=False, proof_source=reason)
        return [], conclusion
    elif v3 is not None and v1 is not None and v2 is None:
        target_val = ModInt(-1) / (v3 * v1)
        target_const = get_or_create_constant(target_val, R1.env) 
        conclusion = Fact("Identical", [R2, target_const], is_proven=False, proof_source=reason)
        return [], conclusion
        
    return [], None

# --- その他基礎定理群 (抜粋) ---
def match_identical_lines_by_angle(facts, env):
    matches = []
    angles = [n for n in env.nodes if getattr(get_representative(n), 'entity_type', '') == "Angle"]
    for angle_ent in set(get_representative(a) for a in angles):
        comp = angle_ent.get_best_component()
        if not comp: continue
        pairs = [d.parents for d in comp.definitions if d.def_type == "AnglePair" and len(d.parents) == 2]
        if len(pairs) < 2: continue
        for (L1, M1), (L2, M2) in itertools.combinations(pairs, 2):
            target_M, candidate_L1, candidate_L2 = None, None, None
            if M1 == M2: target_M, candidate_L1, candidate_L2 = M1, L1, L2
            elif L1 == L2: target_M, candidate_L1, candidate_L2 = L1, M1, M2
            elif M1 == L2: target_M, candidate_L1, candidate_L2 = M1, L1, M2
            elif L1 == M2: target_M, candidate_L1, candidate_L2 = L1, M1, L2
            if target_M and candidate_L1 != candidate_L2:
                common = get_points_on(candidate_L1) & get_points_on(candidate_L2)
                if common:
                    matches.append((candidate_L1, candidate_L2, list(common)[0], target_M, angle_ent.name))
    return matches

def apply_identical_lines_by_angle(match):
    L1, L2, P, M, angle_name = match
    return [], Fact("Identical", [L1, L2], is_proven=False, proof_source=f"直線の一致条件: {P.name}を通り{M.name}と等角")

def match_collinear_from_line_identity(facts, env):
    matches = []
    lines = [n for n in env.nodes if getattr(get_representative(n), 'entity_type', '') == "Line"]
    for ln in set(get_representative(l) for l in lines):
        pts = list(get_points_on(ln))
        if len(pts) >= 3:
            for p1, p2, p3 in itertools.combinations(pts, 3):
                matches.append((p1, p2, p3, ln))
    return matches

def apply_collinear_from_line_identity(match):
    p1, p2, p3, ln = match
    return [], Fact("Collinear", [p1, p2, p3], is_proven=False, proof_source=f"同一直線上の点 ({ln.name})")


THEOREMS = [
    GeometryTheorem("円周角の定理(Line)", match_cyclic_lines, apply_cyclic_lines),
    GeometryTheorem("円周角の定理の逆(Line)", match_converse_cyclic_lines, apply_converse_cyclic_lines),
    GeometryTheorem("直線の一致条件", match_identical_lines_by_angle, apply_identical_lines_by_angle),
    GeometryTheorem("平行線の性質(Direction)", match_parallel_angles_by_direction, apply_parallel_angles_by_direction),
    GeometryTheorem("平行線と線分の比", match_parallel_to_ratio, apply_parallel_to_ratio),
    GeometryTheorem("平行線と線分の比の逆", match_ratio_to_parallel, apply_ratio_to_parallel),
    GeometryTheorem("同一性からの共線", match_collinear_from_line_identity, apply_collinear_from_line_identity),
    GeometryTheorem("二等辺三角形の底角", match_isosceles_base_angle, apply_isosceles_base_angle),
    GeometryTheorem("二等辺三角形の底角の逆", match_isosceles_converse, apply_isosceles_converse),
    GeometryTheorem("メネラウスの定理", match_menelaus, apply_menelaus)
]
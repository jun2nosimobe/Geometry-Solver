# theorems.py
import itertools
from logic_core import Fact, GeometryTheorem
from mmp_core import create_geo_entity # ★ 作図ビルダーをインポート
import numpy as np
from mmp_core import get_numerical_degree, ModInt

"""
本当はgeom.pyに追加すべき！！！！！！！！！！！一旦ここに仮置き
"""

def get_triangle_numerical_degree(p1, p2, p3, env):
    """
    3点の座標を1次元にランダム射影し、真の代数的自由度(式の退化を考慮した次数)をSVDで推定する
    """
    naive_d = getattr(p1, 'numerical_degree', 1) + getattr(p2, 'numerical_degree', 1) + getattr(p3, 'numerical_degree', 1)
    # ナイーブ次数が低ければ計算不要
    if naive_d <= 1 or not hasattr(env, 't_samples') or not env.all_vars: 
        return naive_d
        
    true_d = 0
    # 6つの座標成分(x1, y1, x2, y2, x3, y3)を1次元スカラーに潰すためのランダム係数
    coeffs = [ModInt(np.random.randint(1, ModInt.MOD)) for _ in range(6)]
    
    # 環境の変数を1つずつ動かして、結合ベクトルの次数を測る
    for target_var in env.all_vars:
        t_values, val_values = [], []
        fixed_vars = {v: ModInt(np.random.randint(1, ModInt.MOD - 1)) for v in env.all_vars if v != target_var}
        
        for t in env.t_samples[:2 * naive_d + 3]:
            cache = {}
            t_dict = {**fixed_vars, target_var: t}
            try:
                v1, v2, v3 = p1.calculate(t_dict, cache), p2.calculate(t_dict, cache), p3.calculate(t_dict, cache)
                if is_zero_mod(v1[-1]) or is_zero_mod(v2[-1]) or is_zero_mod(v3[-1]): continue
                
                # 同次座標からデカルト座標へ
                x1, y1 = v1[0]/v1[-1], v1[1]/v1[-1]
                x2, y2 = v2[0]/v2[-1], v2[1]/v2[-1]
                x3, y3 = v3[0]/v3[-1], v3[1]/v3[-1]
                
                # 1次元へのランダム射影によるハッシュ的評価
                val = coeffs[0]*x1 + coeffs[1]*y1 + coeffs[2]*x2 + coeffs[3]*y2 + coeffs[4]*x3 + coeffs[5]*y3
                t_values.append(t)
                val_values.append(val)
            except: pass
            
        if len(t_values) >= 2:
            d = get_numerical_degree(t_values, val_values, naive_d, mode='mod')
            true_d += d
            
    # ナイーブ次数と、1変数SVDで実測した真の次数のうち、小さい方を採用
    return min(naive_d, true_d)

def check_similar_mmp(p1, p2, p3, q1, q2, q3, env):
    """MMPを用いて、2つの三角形が相似か(3辺の距離の2乗の比が等しいか)を平方根なしで高速判定する"""
    valid_count = 0
    samples = getattr(env, 't_samples', [])
    if not samples: return False
    
    for t in samples[:5]:
        cache = {}
        # MMPテスト用: 全変数を同じtで動かして簡易チェック
        t_dict = {v: t for v in env.all_vars} 
        try:
            vp1, vp2, vp3 = p1.calculate(t_dict, cache), p2.calculate(t_dict, cache), p3.calculate(t_dict, cache)
            vq1, vq2, vq3 = q1.calculate(t_dict, cache), q2.calculate(t_dict, cache), q3.calculate(t_dict, cache)
            
            xp1, yp1 = vp1[0]/vp1[-1], vp1[1]/vp1[-1]
            xp2, yp2 = vp2[0]/vp2[-1], vp2[1]/vp2[-1]
            xp3, yp3 = vp3[0]/vp3[-1], vp3[1]/vp3[-1]
            
            xq1, yq1 = vq1[0]/vq1[-1], vq1[1]/vq1[-1]
            xq2, yq2 = vq2[0]/vq2[-1], vq2[1]/vq2[-1]
            xq3, yq3 = vq3[0]/vq3[-1], vq3[1]/vq3[-1]
            
            # 距離の2乗
            dp12 = (xp1-xp2)**2 + (yp1-yp2)**2
            dp23 = (xp2-xp3)**2 + (yp2-yp3)**2
            dp31 = (xp3-xp1)**2 + (yp3-yp1)**2
            
            dq12 = (xq1-xq2)**2 + (yq1-yq2)**2
            dq23 = (xq2-xq3)**2 + (yq2-yq3)**2
            dq31 = (xq3-xq1)**2 + (yq3-yq1)**2
            
            # 辺の比の2乗の比較: (A/B = C/D) <=> (A*D == B*C)
            if is_zero_mod(dp12 * dq23 - dp23 * dq12) and is_zero_mod(dp23 * dq31 - dp31 * dq23):
                valid_count += 1
        except: pass
        
    return valid_count == 5


# ==========================================
# グラフ検索 兼 自動作図ヘルパー関数
# ==========================================

def get_representative(obj):
    """マージされて消えた古い図形(ゾンビ)から、現在の真の本体を辿る"""
    while hasattr(obj, '_merged_into') and obj._merged_into is not None:
        obj = obj._merged_into
    return obj

def get_points_on(curve_entity):
    """直線や円の上にある(論理的に確実な)点の集合を取得する"""
    curve_entity = get_representative(curve_entity)
    comp = curve_entity.get_best_component()
    if not comp: return set()
    # 🌟 ゾンビポインタを真の本体に変換して返す
    return {get_representative(obj) for obj in comp.subobjects if getattr(get_representative(obj), 'entity_type', '') == "Point"}

def get_lines_on(point_entity):
    """点を通る(論理的に確実な)直線の集合を取得する"""
    point_entity = get_representative(point_entity)
    comp = point_entity.get_best_component()
    if not comp: return set()
    return {get_representative(obj) for obj in comp.subobjects if getattr(get_representative(obj), 'entity_type', '') == "Line"}

def is_line_strict(obj):
    """新構造の型判定"""
    return getattr(get_representative(obj), 'entity_type', '') == "Line"

def get_or_create_line(p1, p2, env):
    """p1とp2を通る直線を取得する。なければ作図して環境(E-Graph)にこっそり追加する。"""
    import logging
    logger = logging.getLogger("GeometryProver")

    # 真の本体を取得
    p1 = get_representative(p1)
    p2 = get_representative(p2)
    
    c1 = p1.get_best_component()
    c2 = p2.get_best_component()
    
    # 直線を集める（この時点では重複やクローンが混ざっている可能性がある）
    lines_1 = set()
    lines_2 = set()
    
    if c1:
        lines_1.update(get_representative(obj) for obj in c1.subobjects if getattr(get_representative(obj), 'entity_type', '') == "Line")
    lines_1.update(get_representative(obj) for obj in p1.mmp_subobjects if getattr(get_representative(obj), 'entity_type', '') == "Line")
    
    if c2:
        lines_2.update(get_representative(obj) for obj in c2.subobjects if getattr(get_representative(obj), 'entity_type', '') == "Line")
    lines_2.update(get_representative(obj) for obj in p2.mmp_subobjects if getattr(get_representative(obj), 'entity_type', '') == "Line")
    
    # ==========================================
    # 🚨 デバッグ 兼 最強の検索ロジック
    # IDや名前をベースにして、確実に共通直線を探す
    # ==========================================
    # lines_2 を id ベースの辞書に変換しておく（名前の一致も考慮）
    l2_dict = {id(ln): ln for ln in lines_2}
    l2_names = {ln.name: ln for ln in lines_2}

    common_lines = []
    for ln1 in lines_1:
        if id(ln1) in l2_dict:
            common_lines.append(ln1)
        elif ln1.name in l2_names:
            common_lines.append(l2_names[ln1.name]) # 名前が同じクローンがいたら同一視する！

    # --- 🔍 ログ出力（原因特定用） ---
    if common_lines:
        #logger.debug(f"🔍 [Auto作図 発生] {p1.name} と {p2.name} の共通直線が見つかりません。")
        #logger.debug(f"   ▶ {p1.name} が知っている直線: {[ln.name for ln in lines_1]}")
        #logger.debug(f"   ▶ {p2.name} が知っている直線: {[ln.name for ln in lines_2]}")
    #else:
        # 見つかった場合は既存の直線を返す
        return common_lines[0]

    # ==========================================
    # 本当にまだ引かれていない補助線の場合のみ作図
    # ==========================================
    name = f"Line_{p1.name}_{p2.name}_(Auto)"
    #logger.debug(f"   ⚠️ 新規作図を実行: {name}")
    from mmp_core import create_geo_entity
    new_line = create_geo_entity("LineThroughPoints", [p1, p2], name=name, env=env)
    
    new_line.importance = 0.5 
    env.nodes.append(new_line)
    
    # ★ Auto直線を引いた後、点側にも所属関係を強制登録しておく（念のため）
    p1.mmp_subobjects.add(new_line)
    p2.mmp_subobjects.add(new_line)
    
    return new_line

def get_direction(L, env):
    """直線の傾き(Direction)エンティティを取得する。なければ正規ビルダーで作る"""
    from mmp_core import create_geo_entity # ★ ビルダーをインポート
    
    # 既に L の方向として定義されたエンティティがあるか探す
    for node in env.nodes:
        if getattr(node, 'entity_type', '') == "Direction":
            nc = node.get_best_component()
            if nc and any(d.def_type == "DirectionOf" and L in d.parents for d in nc.definitions):
                return node
                
    # ★ 修正: mmp_coreの正規ビルダーにすべて任せる！
    new_dir = create_geo_entity("DirectionOf", [L], name=f"Dir_{L.name}", env=env)
    new_dir.importance = 2.0 # 概念エンティティの初期重要度
    env.nodes.append(new_dir)
    
    return new_dir

def are_collinear_egraph(p1, p2, p3):
    """E-Graph上で3点が同一直線上にあるか判定する"""
    c1, c2, c3 = p1.get_best_component(), p2.get_best_component(), p3.get_best_component()
    if not (c1 and c2 and c3): return False
    return any(obj.entity_type == "Line" for obj in (c1.subobjects & c2.subobjects & c3.subobjects))


def get_or_create_triangle(p1, p2, p3, env):
    import itertools
    p1, p2, p3 = get_representative(p1), get_representative(p2), get_representative(p3)
    pts = {p1, p2, p3}
    if len(pts) < 3: return None 
    
    triangles = [n for n in env.nodes if getattr(n, 'entity_type', '') == "Triangle"]
    for t in triangles:
        t_comp = t.get_best_component()
        if t_comp and hasattr(t_comp, 'triangle_points') and set(t_comp.triangle_points) == pts:
            return t
    # ==========================================
    # 🌟 修正: ナイーブ次数ではなく、実測された「真の次数」で足切りする！
    # ==========================================
    true_degree = get_triangle_numerical_degree(p1, p2, p3, env)
    if true_degree > 30:
        return None

    sorted_pts = sorted(list(pts), key=lambda x: x.name)
    name = f"Tri_{sorted_pts[0].name}{sorted_pts[1].name}{sorted_pts[2].name}"
    
    from mmp_core import create_geo_entity
    new_tri = create_geo_entity("Triangle", sorted_pts, name=name, env=env)
    new_tri.get_best_component().triangle_points = tuple(sorted_pts)
    new_tri.importance = 2.0
    env.nodes.append(new_tri)
    return new_tri

# ==========================================
# 定理1: 円周角の定理 (Full-Angle)
# ==========================================
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
                        # 待ちの姿勢をやめ、無ければ強制的に直線を引く
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

# ==========================================
# 定理2: 円周角の定理の逆 (E-Graph 集合演算版)
# ==========================================
def match_converse_cyclic_lines(facts, env):
    matches = []
    angle_entities = [n for n in env.nodes if n.entity_type == "Angle"]
    
    for angle_ent in angle_entities:
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
                            if len({A, B, C, D}) == 4:
                                if are_collinear_egraph(A, B, C) or are_collinear_egraph(A, B, D) or \
                                   are_collinear_egraph(A, C, D) or are_collinear_egraph(B, C, D):
                                    continue
                                # ★ 修正: どの直線ペアが等角だったのかを詳細に渡す
                                matches.append((A, B, C, D, f"E-Graph上で ∠({L1.name},{L2.name}) = ∠({L3.name},{L4.name}) が確認されたため"))
    return matches

def apply_converse_cyclic_lines(match):
    A, B, C, D, detailed_reason = match
    # ★ 修正: proof_source に詳細な理由を埋め込む
    conclusion = Fact("Concyclic", [A, B, C, D], is_proven=False, proof_source=f"円周角の定理の逆 ({detailed_reason})")
    return [], conclusion

# ==========================================
# 定理3: 鏡映の性質
# ==========================================
def match_reflection_angles(facts, env):
    matches = []
    # ★ 古いクラス判定 ("Reflection" in type(n).__name__) を廃止し、Definition を探す
    reflections = [n for n in env.nodes if any(d.def_type == "Reflection" for c in n.components for d in c.definitions)]
    
    for ref_node in reflections:
        comp = ref_node.get_best_component()
        ref_def = next((d for d in comp.definitions if d.def_type == "Reflection"), None)
        if not ref_def or len(ref_def.parents) < 2: continue
        
        Q = ref_def.parents[0]
        axis_line = ref_def.parents[1]
        
        # ★ env.points_on_curve ではなく get_points_on を使う
        for X in get_points_on(axis_line):
            L_XQ = get_or_create_line(X, Q, env)
            L_XQ_prime = get_or_create_line(X, ref_node, env)
            if L_XQ and L_XQ_prime:
                matches.append((axis_line, L_XQ, L_XQ_prime, axis_line, ref_node))
    return matches

def apply_reflection_angles(match):
    L_axis, L_XQ, L_XQ_prime, L_axis2, source_node = match
    conclusion = Fact("EqualAngle_Line", [L_axis, L_XQ, L_XQ_prime, L_axis2], is_proven=False, proof_source=f"鏡映の性質 ({source_node.name})")
    return [], conclusion 

# ==========================================
# 定理4: 平行線の性質
# ==========================================
# ==========================================
# 定理: 傾き類（Direction）による等角の証明
# ==========================================
def match_angle_from_directions(facts, env):
    """【傾き⇔角度】L1//L3 かつ L2//L4 ならば、∠(L1,L2) = ∠(L3,L4)"""
    matches = []
    directions = [n for n in env.nodes if n.entity_type == "Direction"]
    
    for dir1, dir2 in itertools.combinations(directions, 2):
        comp1 = dir1.get_best_component()
        comp2 = dir2.get_best_component()
        if not comp1 or not comp2: continue
        
        # 同じ傾きを持つ直線のグループを取得
        lines1 = [d.parents[0] for d in comp1.definitions if d.def_type == "DirectionOf"]
        lines2 = [d.parents[0] for d in comp2.definitions if d.def_type == "DirectionOf"]
        
        if len(lines1) < 2 or len(lines2) < 2: continue
        
        # L1とL3が平行、L2とL4が平行なら、そのペアのなす角は必ず等しい
        for L1, L3 in itertools.combinations(lines1, 2):
            for L2, L4 in itertools.combinations(lines2, 2):
                matches.append((L1, L2, L3, L4, f"傾きの一致({dir1.name}, {dir2.name})"))
                    
    return matches

def apply_angle_from_directions(match):
    L1, L2, L3, L4, reason = match
    conclusion = Fact("EqualAngle_Line", [L1, L2, L3, L4], is_proven=False, proof_source=reason)
    return [], conclusion

# ==========================================
# 定理: 平行線の性質（Direction版にアップデート）
# ==========================================
def match_parallel_angles_by_direction(facts, env):
    """【平行線の性質】同じ傾きを持つ2直線と、それに交わる横断線"""
    matches = []
    directions = [n for n in env.nodes if n.entity_type == "Direction"]
    all_lines = {n for n in env.nodes if n.entity_type == "Line"}
    
    for dir_node in directions:
        comp = dir_node.get_best_component()
        if not comp: continue
        
        # この傾きに属する(平行な)直線のリスト
        parallel_lines = [d.parents[0] for d in comp.definitions if d.def_type == "DirectionOf"]
        if len(parallel_lines) < 2: continue
        
        for L1, L2 in itertools.combinations(parallel_lines, 2):
            pts_L1 = get_points_on(L1)
            pts_L2 = get_points_on(L2)
            
            for M in all_lines:
                if M == L1 or M == L2: continue
                pts_M = get_points_on(M)
                
                # MがL1, L2の両方と交点を持つ（Z角・F角を形成する）場合のみ
                if (pts_L1 & pts_M) and (pts_L2 & pts_M):
                    matches.append((L1, M, L2, M, f"平行線の性質({dir_node.name})"))
                    
    return matches

def apply_parallel_angles_by_direction(match):
    L1, M, L2, M_dup, reason = match
    conclusion = Fact("EqualAngle_Line", [L1, M, L2, M_dup], is_proven=False, proof_source=reason)
    return [], conclusion

def match_identical_lines_by_angle(facts, env):
    matches = []
    angle_entities = [n for n in env.nodes if n.entity_type == "Angle"]
    
    for angle_ent in angle_entities:
        comp = angle_ent.get_best_component()
        if not comp: continue
        
        pairs = [d.parents for d in comp.definitions if d.def_type == "AnglePair" and len(d.parents) == 2]
        if len(pairs) < 2: continue
        
        for (L1, M1), (L2, M2) in itertools.combinations(pairs, 2):
            # ★ 修正: 順序に依存しない柔軟なマッチング！
            target_M = None
            candidate_L1, candidate_L2 = None, None
            
            if M1 == M2: target_M, candidate_L1, candidate_L2 = M1, L1, L2
            elif L1 == L2: target_M, candidate_L1, candidate_L2 = L1, M1, M2
            elif M1 == L2: target_M, candidate_L1, candidate_L2 = M1, L1, M2
            elif L1 == M2: target_M, candidate_L1, candidate_L2 = L1, M1, L2
                
            if target_M and candidate_L1 != candidate_L2:
                pts1 = get_points_on(candidate_L1)
                pts2 = get_points_on(candidate_L2)
                common = pts1 & pts2
                if common:
                    P = list(common)[0]
                    matches.append((candidate_L1, candidate_L2, P, target_M, angle_ent.name))
                    
    return matches

def apply_identical_lines_by_angle(match):
    L1, L2, P, M, angle_name = match
    conclusion = Fact("Identical", [L1, L2], is_proven=False, proof_source=f"直線の一致条件: {P.name}を通り{M.name}と等角")
    return [], conclusion



def match_collinear_from_line_identity(facts, env):
    """【同一性からの共線】D, E, F が同じ直線オブジェクトの上に乗っていれば、それらは共線である"""
    matches = []
    lines = [n for n in env.nodes if n.entity_type == "Line"]
    for ln in lines:
        pts = list(get_points_on(ln))
        if len(pts) >= 3:
            for p1, p2, p3 in itertools.combinations(pts, 3):
                # 目標の点 D, E, F が含まれているか？
                matches.append((p1, p2, p3, ln))
    return matches

def apply_collinear_from_line_identity(match):
    p1, p2, p3, ln = match
    return [], Fact("Collinear", [p1, p2, p3], is_proven=False, proof_source=f"同一直線上の点 ({ln.name})")


def match_similar_triangles(facts, env):
    matches = []
    
    # 片方は「登録済みの有望な三角形」に限定 (O(K))
    registered_triangles = [n for n in env.nodes if getattr(n, 'entity_type', '') == "Triangle"]
    if not registered_triangles: return matches
    
    # もう片方は任意の3点 (O(N^3))
    all_points = [n for n in env.nodes if getattr(n, 'entity_type', '') == "Point"]
    if len(all_points) < 3: return matches

    for T1 in registered_triangles:
        pts1 = T1.get_best_component().triangle_points
        
        for pts2 in itertools.combinations(all_points, 3):
            # 全く同じ3点ならスキップ
            if set(pts1) == set(pts2): continue
            
            # ==========================================
            # 🌟 MMP フィルター: 頂点の対応順序(6通り)を高速チェック
            # ==========================================
            valid_permutation = None
            for p2_perm in itertools.permutations(pts2):
                if check_similar_mmp(pts1[0], pts1[1], pts1[2], p2_perm[0], p2_perm[1], p2_perm[2], env):
                    valid_permutation = p2_perm
                    break # 1つでも対応順序が見つかればOK
            
            if not valid_permutation:
                continue # MMPが相似を否定したペアは、論理探索を完全にスキップ！
                
            # =================-----------------------
            # MMPを通過したペアだけ、E-Graphで論理的証拠(角度など)を探す
            # =================-----------------------
            evidence = find_logical_similarity_evidence(pts1, valid_permutation, env)
            if evidence:
                matches.append((T1, valid_permutation, evidence))

    return matches

# ==========================================
# 定理: 相似な三角形の対応する角は等しい
# ==========================================
def match_angles_from_similar_triangles(facts, env):
    matches = []
    # Shape(相似クラス)を全て取得
    shapes = [n for n in env.nodes if getattr(get_representative(n), 'entity_type', '') == "Shape"]
    
    for shape in set(get_representative(s) for s in shapes):
        # このShape(相似クラス)に属する三角形と、そのスロット順列のリスト
        members = list(shape.shape_members.items())
        if len(members) < 2: continue
        
        for (tri1, pts1), (tri2, pts2) in itertools.combinations(members, 2):
            # pts1 = (A, B, C), pts2 = (D, E, F) などの対応順序が保証されている
            # 3つの頂点角について、それぞれ等角関係(EqualAngle_Line)を発行する
            for i in range(3):
                A, B, C = pts1[i-1], pts1[i], pts1[(i+1)%3]
                D, E, F = pts2[i-1], pts2[i], pts2[(i+1)%3]
                
                # 直線を引く（無ければ裏で作図）
                L_AB = get_or_create_line(A, B, env)
                L_BC = get_or_create_line(B, C, env)
                L_DE = get_or_create_line(D, E, env)
                L_EF = get_or_create_line(E, F, env)
                
                if L_AB and L_BC and L_DE and L_EF:
                    matches.append((L_AB, L_BC, L_DE, L_EF, f"相似な三角形 ({tri1.name} ∽ {tri2.name})"))
                    
    return matches

def apply_angles_from_similar_triangles(match):
    L1, L2, L3, L4, reason = match
    # L1とL2のなす角 ＝ L3とL4のなす角
    conclusion = Fact("EqualAngle_Line", [L1, L2, L3, L4], is_proven=False, proof_source=reason)
    return [], conclusion

THEOREMS = [
    GeometryTheorem("円周角の定理(Line)", match_cyclic_lines, apply_cyclic_lines),
    GeometryTheorem("円周角の定理の逆(Line)", match_converse_cyclic_lines, apply_converse_cyclic_lines),
    GeometryTheorem("鏡映の性質", match_reflection_angles, apply_reflection_angles),
    GeometryTheorem("直線の一致条件", match_identical_lines_by_angle, apply_identical_lines_by_angle),
    GeometryTheorem("傾きの一致から等角", match_angle_from_directions, apply_angle_from_directions),
    GeometryTheorem("平行線の性質(Direction)", match_parallel_angles_by_direction, apply_parallel_angles_by_direction),
    GeometryTheorem("同一性からの共線", match_collinear_from_line_identity, apply_collinear_from_line_identity),
    GeometryTheorem("相似な三角形の対応する角", match_angles_from_similar_triangles, apply_angles_from_similar_triangles)
]

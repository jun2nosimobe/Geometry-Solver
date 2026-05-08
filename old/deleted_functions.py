
def verify_concyclic_runtime(pts, all_vars, test_runs=3):
    """実行時に4点が共円であるか検証する"""
    from mmp_core import ModInt, create_geo_entity
    if len(pts) != 4: return True
    
    # 仮の外接円を作成 (検証用なので環境には紐付けない)
    circle = create_geo_entity("Circumcircle", [pts[0], pts[1], pts[2]], env=None)
    
    valid_count = 0
    for _ in range(test_runs):
        t_dict = {v: ModInt(np.random.randint(1, ModInt.MOD)) for v in all_vars}
        cache = {}
        try:
            c_val = circle.calculate(t_dict, cache)
            p4_val = pts[3].calculate(t_dict, cache)
            if p4_val[2].value == 0: continue
            
            u, v, w, s = c_val[0], c_val[1], c_val[2], c_val[3]
            x, y, z = p4_val[0], p4_val[1], p4_val[2]
            
            val = u * (x**2 + y**2) + v * x * z + w * y * z + s * (z**2)
            if val.value == 0:
                valid_count += 1
        except Exception:
            pass
    return valid_count > 0 and valid_count == test_runs



def make_point_on_line(name, pt_a, pt_b, t_var, env):
    # t_var は 0〜1 などで動く Var
    pt = GeoEntity("Point", name=name)
    pt.numerical_degree = 1 # 直線上なので自由度は1
    
    def calc_func(t_dict, cache):
        if id(pt) in cache: return cache[id(pt)]
        va = pt_a.calculate(t_dict, cache)
        vb = pt_b.calculate(t_dict, cache)
        t = t_var.evaluate(t_dict)
        # 線分ABを t:(1-t) に内分する点
        res = [va[0]*(1-t) + vb[0]*t, va[1]*(1-t) + vb[1]*t, 1]
        cache[id(pt)] = res
        return res
    pt.calculate = calc_func

    # 論理的には「直線AB上に乗っている」という定義を与える
    L_AB = get_or_create_line(pt_a, pt_b, env)
    comp = LogicalComponent(initial_def=Definition("PointOn", [L_AB], naive_degree=1, depth=1))
    pt.components.append(comp)
    link_logical_incidence(pt, L_AB)
    
    pt.base_importance = 10.0 # 問題文に登場する拘束点なので高め
    env.nodes.append(pt)
    return pt

# ==========================================
# 🌟 枝刈り付き 三角形＆相似クラス 作成・マージ群
# ==========================================
def get_or_create_triangle(p1: GeoEntity, p2: GeoEntity, p3: GeoEntity, env) -> GeoEntity:
    p1, p2, p3 = get_representative(p1), get_representative(p2), get_representative(p3)
    pts = {p1, p2, p3}
    if len(pts) < 3: return None
    
    for node in env.nodes:
        if getattr(node, 'entity_type', '') == "Triangle":
            comp = node.get_best_component()
            if comp:
                for d in comp.definitions:
                    if d.def_type == "Triangle" and set(d.parents) == pts:
                        return node
                        
    deg1 = getattr(p1, 'numerical_degree', 1) or 1
    deg2 = getattr(p2, 'numerical_degree', 1) or 1
    deg3 = getattr(p3, 'numerical_degree', 1) or 1
    if deg1 + deg2 + deg3 > 30:
        return None
        
    sorted_pts = sorted(list(pts), key=lambda x: x.name)
    name = f"Tri_{sorted_pts[0].name}{sorted_pts[1].name}{sorted_pts[2].name}"
    
    new_tri = create_geo_entity("Triangle", sorted_pts, name=name, env=env)
    new_tri.importance = 2.0
    
    shape_name = f"Shape_{name}"
    new_shape = create_geo_entity("ShapeOf", [new_tri], name=shape_name, env=env)
    new_shape.shape_members[new_tri] = tuple(sorted_pts)
    
    env.nodes.extend([new_tri, new_shape])
    return new_tri

def merge_shapes(shape1: GeoEntity, shape2: GeoEntity) -> GeoEntity:
    shape1 = get_representative(shape1)
    shape2 = get_representative(shape2)
    if shape1 == shape2: return shape1
    
    common_tri = next((t for t in shape1.shape_members if t in shape2.shape_members), None)
    if not common_tri: return None
    
    tuple1 = shape1.shape_members[common_tri]
    tuple2 = shape2.shape_members[common_tri]
    
    mapping = {}
    for i, pt in enumerate(tuple2):
        mapping[i] = tuple1.index(pt)
        
    for tri, pts in shape2.shape_members.items():
        if tri == common_tri: continue
        new_pts = [None, None, None]
        for i, pt in enumerate(pts):
            new_pts[mapping[i]] = pt
        shape1.shape_members[tri] = tuple(new_pts)
        
    shape2._merged_into = shape1
    return shape1
import numpy as np
import itertools
import logging
import traceback
from mmp_math import ModInt, get_numerical_degree
from mmp_core import create_geo_entity
from proof_manager import Fact

logger = logging.getLogger("GeometryProver")

def is_zero_mod(v):
    if hasattr(v, 'value'): return v.value == 0
    if hasattr(v, 'val'): return v.val == 0
    if hasattr(v, 'n'): return v.n == 0
    
    # 🌟 FIX: 標準のfloatだけでなく、NumPyのすべての実数型(np.floating)もカバーする！
    if isinstance(v, (float, np.floating)):
        return abs(float(v)) < 1e-8 
        
    try: return int(v) == 0
    except: return v == 0

def is_point(obj): return hasattr(obj, 'entity_type') and obj.entity_type == "Point"
def is_line(obj): return hasattr(obj, 'entity_type') and obj.entity_type == "Line"
def is_circle(obj): return hasattr(obj, 'entity_type') and obj.entity_type == "Circle"

class MMPTester:
    def __init__(self, env, all_vars, prover):
        self.env = env
        self.all_vars = all_vars
        self.prover = prover
        self.t_samples = [ModInt(np.random.randint(1, ModInt.MOD - 1)) for _ in range(400)]
        self.canonical_t_dict = {v: self.t_samples[i % len(self.t_samples)] for i, v in enumerate(self.all_vars)}

    # ==========================================
    # 🌟 NEW: グローバル・キャッシュを使用した安全な計算機構
    # （親図形の再帰計算による「座標不在」エラーを根絶する）
    # ==========================================
    def _evaluate_all_nodes(self, t_dict):
        global_cache = {}
        nodes_sorted = sorted([n for n in self.env.nodes if getattr(n, 'is_valid', lambda: True)()], 
                              key=lambda x: getattr(x.get_rep().get_best_component(), 'depth', float('inf')))
        for n in nodes_sorted:
            try: n.get_rep().calculate(t_dict, global_cache)
            except: pass
        return global_cache

    def _eval_point(self, P, t_dict, global_cache=None):
        cache = global_cache if global_cache is not None else {}
        try:
            val = P.calculate(t_dict, cache)
            if is_zero_mod(val[-1]): return None
            return (val[0]/val[-1], val[1]/val[-1])
        except:
            return None

    def _apply_conjecture_heat(self, objects, base_bonus):
        valid_objs = [o for o in objects if hasattr(o, 'base_importance')]
        if not valid_objs: return 0.0
        
        # 修正: 平均値(sum/N)ではなく、関与した「最も熱い図形」の熱を基準に波及させる
        max_importance = max(getattr(o, 'importance', 1.0) for o in valid_objs)
        scaled_bonus = base_bonus * min(1.5, (max_importance / 10.0))
        
        for obj in valid_objs:
            if hasattr(obj, 'add_heat'):
                obj.add_heat(scaled_bonus)
                
        return scaled_bonus

    def _add_and_log_conjecture(self, fact_type, objects, log_message, base_bonus=10.0):
        test_fact = Fact(fact_type, objects)
        existing = next((f for f in self.prover.facts if f == test_fact), None)
        
        if existing:
            if existing.is_proven: return False 
            if existing.is_mmp_conjecture: return False 
            existing.is_mmp_conjecture = True
            existing.proof_source = f"MMP予想({fact_type})"
            score = self._apply_conjecture_heat(objects, base_bonus)
            existing.conjecture_score = score
            logger.info(f"{log_message} (熱ボーナス: +{score:.2f})")
            return True
            
        test_fact.is_proven = False
        test_fact.is_mmp_conjecture = True
        test_fact.proof_source = f"MMP予想({fact_type})"
        score = self._apply_conjecture_heat(objects, base_bonus)
        test_fact.conjecture_score = score
        self.prover.facts.append(test_fact)
        logger.info(f"{log_message} (熱ボーナス: +{score:.2f})")
        
        if hasattr(self.env, 'emit'):
            from logic_core import EventType
            self.env.emit(EventType.NEW_CONJECTURE, test_fact)
        return True


    def discover_all_mmp_relations(self, Z, parents):
        if getattr(Z, 'base_importance', 1.0) <= 0.0: return
        deg = getattr(Z, 'numerical_degree', 1) or 1
        if Z.entity_type in ["Point", "Line", "Direction"]:
            if deg > 15: return  
        elif Z.entity_type in ["Circle", "Scalar", "LengthSq", "AffineRatio", "Angle"]: 
            if deg > 25: return  

        # ==========================================
        # 🌟 爆速化: 比較の前に「5回分の乱数と全体キャッシュ」を一括生成する！
        # これにより、毎回のペア比較での再計算(O(N^3))が消滅し、O(N)になります。
        # ==========================================
        t_dicts = []
        caches = []
        for _ in range(5):
            t = {v: np.random.choice(self.t_samples) for v in self.all_vars}
            t_dicts.append(t)
            caches.append(self._evaluate_all_nodes(t))

        # 1. 🌟 同一性(Identical)の判定 (AngleやDirectionの一致をこれで爆速発見)
        if Z.entity_type in ["Angle", "Direction", "Line", "Circle", "Point"]:
            hot_targets = [n for n in self.env.nodes if n.entity_type == Z.entity_type and n != Z and getattr(n, 'base_importance', 1.0) > 0.0]
            for target in hot_targets:
                valid_count = 0
                for i in range(5):
                    try:
                        v1 = Z.calculate(t_dicts[i], caches[i])
                        v2 = target.calculate(t_dicts[i], caches[i])
                        if v1 and v2 and len(v1) == len(v2) and self._check_numerical_match(v1, v2):
                            valid_count += 1
                    except: pass
                if valid_count == 5:
                    self._add_and_log_conjecture("Identical", [Z, target], f"    🟡 MMP予想(同一): {Z.name} ≡ {target.name}", base_bonus=15.0)

        # 2. 🌟 点と直線の検証 (Incidence)
        if is_point(Z):
            valid_curves = [n for n in self.env.nodes if (is_line(n) or is_circle(n)) and n not in parents and getattr(n, 'base_importance', 1.0) > 0.0]
            for c in valid_curves: 
                self._fast_check_incidence(Z, c, t_dicts, caches)
        elif is_line(Z) or is_circle(Z):
            valid_pts = [n for n in self.env.nodes if is_point(n) and n not in parents and getattr(n, 'base_importance', 1.0) > 0.0]
            for p in valid_pts: 
                self._fast_check_incidence(p, Z, t_dicts, caches)
                
        # 3. 🌟 平行・垂直
        if is_line(Z):
            hot_lines = [n for n in self.env.nodes if is_line(n) and n not in parents and getattr(n, 'importance', 1.0) >= 3.0]
            for ln in hot_lines:
                if Z == ln: continue
                valid_para, valid_perp = 0, 0
                for i in range(5):
                    try:
                        cZ = Z.calculate(t_dicts[i], caches[i])
                        cln = ln.calculate(t_dicts[i], caches[i])
                        if is_zero_mod(cZ[0]*cln[1] - cZ[1]*cln[0]): valid_para += 1
                        if is_zero_mod(cZ[0]*cln[0] + cZ[1]*cln[1]): valid_perp += 1
                    except: pass
                    
                if valid_para == 5:
                    self._add_and_log_conjecture("Parallel", [Z, ln], f"    🟡 MMP予想(平行): {Z.name} // {ln.name}", base_bonus=10.0)
                if valid_perp == 5:
                    if hasattr(self.env, 'add_right_angle'):
                        self.env.add_right_angle(Z, ln)
                        score = self._apply_conjecture_heat([Z, ln], 10.0)
                        logger.debug(f"    🌟 MMP発見(垂直): {Z.name} ⊥ {ln.name} (熱ボーナス: +{score:.2f})")

        # 4. 🌟 共線・共円判定
        if is_point(Z):
            hot_pts = [n for n in self.env.nodes if is_point(n) and n != Z and n not in parents and getattr(n, 'importance', 1.0) >= 3.0]
            if len(hot_pts) >= 3:
                collinear_groups = []
                for p1, p2 in itertools.combinations(hot_pts, 2):
                    cZ, c1, c2 = Z.get_best_component(), p1.get_best_component(), p2.get_best_component()
                    if cZ and c1 and c2:
                        common_lines = [obj for obj in (cZ.subobjects & c1.subobjects & c2.subobjects) if getattr(obj, 'entity_type', '') == "Line"]
                        if common_lines: continue 
                    
                    valid_collinear = 0
                    for i in range(5):
                        try:
                            v_Z = self._eval_point(Z, t_dicts[i], caches[i])
                            v_p1 = self._eval_point(p1, t_dicts[i], caches[i])
                            v_p2 = self._eval_point(p2, t_dicts[i], caches[i])
                            if not (v_Z and v_p1 and v_p2): continue
                            area = v_Z[0]*(v_p1[1]-v_p2[1]) + v_p1[0]*(v_p2[1]-v_Z[1]) + v_p2[0]*(v_Z[1]-v_p1[1])
                            if is_zero_mod(area): valid_collinear += 1
                        except: pass
                            
                    if valid_collinear == 5:
                        self._add_and_log_conjecture("Collinear", [Z, p1, p2], f"    🟡 MMP予想(共線): {Z.name}, {p1.name}, {p2.name}", base_bonus=15.0)
                        collinear_groups.append({Z, p1, p2})

                for p1, p2, p3 in itertools.combinations(hot_pts, 3):
                    pts_set = {Z, p1, p2, p3}
                    if any(len(group & pts_set) >= 3 for group in collinear_groups): continue 
                    
                    pts_list = list(pts_set)
                    is_degenerate = False
                    for comb in itertools.combinations(pts_list, 3):
                        valid_col = 0
                        for i in range(3): 
                            try:
                                v_A = self._eval_point(comb[0], t_dicts[i], caches[i])
                                v_B = self._eval_point(comb[1], t_dicts[i], caches[i])
                                v_C = self._eval_point(comb[2], t_dicts[i], caches[i])
                                if not (v_A and v_B and v_C): continue
                                area = v_A[0]*(v_B[1]-v_C[1]) + v_B[0]*(v_C[1]-v_A[1]) + v_C[0]*(v_A[1]-v_B[1])
                                if is_zero_mod(area): valid_col += 1
                            except: pass
                        if valid_col >= 2:
                            is_degenerate = True; break
                    if is_degenerate: continue 

                    cZ, c1, c2, c3 = Z.get_best_component(), p1.get_best_component(), p2.get_best_component(), p3.get_best_component()
                    if cZ and c1 and c2 and c3:
                        common_circs = [obj for obj in (cZ.subobjects & c1.subobjects & c2.subobjects & c3.subobjects) if getattr(obj, 'entity_type', '') == "Circle"]
                        if common_circs: continue

                    temp_circle = create_geo_entity("Circumcircle", [p1, p2, p3], name="temp", env=None)
                    valid_count = 0
                    for i in range(5):
                        try:
                            c_val = temp_circle.calculate(t_dicts[i], caches[i])
                            Z_val = Z.calculate(t_dicts[i], caches[i])
                            if not c_val or not Z_val or is_zero_mod(Z_val[-1]): continue
                            
                            u, v, w, s = c_val
                            x, y, z = Z_val
                            val = u*(x**2 + y**2) + v*x*z + w*y*z + s*z**2
                            if is_zero_mod(val): valid_count += 1
                        except: pass

                    if valid_count == 5:
                        self._add_and_log_conjecture("Concyclic", [Z, p1, p2, p3], f"    🟡 MMP予想(共円): {Z.name}, {p1.name}, {p2.name}, {p3.name}", base_bonus=20.0)

    # 🌟 NEW: キャッシュを使い回して Incidence をチェックする関数
    def _fast_check_incidence(self, pt, curve, t_dicts, caches):
        c_pt = pt.get_best_component()
        if c_pt and curve in c_pt.subobjects: return False
        if curve in pt.mmp_subobjects: return False
        
        valid_count = 0
        for i in range(5):
            try:
                pt_val = pt.calculate(t_dicts[i], caches[i])
                c_val = curve.calculate(t_dicts[i], caches[i])
                if not pt_val or not c_val or is_zero_mod(pt_val[-1]): continue 
                
                is_on_curve = False
                if curve.entity_type == "Line":
                    if is_zero_mod(c_val[0]) and is_zero_mod(c_val[1]): continue
                    dot = c_val[0]*pt_val[0] + c_val[1]*pt_val[1] + c_val[2]*pt_val[2]
                    if is_zero_mod(dot): is_on_curve = True
                elif curve.entity_type == "Circle":
                    u, v, w, s = c_val
                    x, y, z = pt_val
                    val = u*(x**2 + y**2) + v*x*z + w*y*z + s*z**2
                    if is_zero_mod(val): is_on_curve = True

                if is_on_curve: valid_count += 1
            except: pass
        
        if valid_count == 5: 
            pt.mmp_subobjects.add(curve)
            curve.mmp_subobjects.add(pt)
            fact_type = "Concyclic" if curve.entity_type == "Circle" else "Collinear"
            c_curve = curve.get_best_component()
            curve_pts = [p for p in next(iter(c_curve.definitions)).parents if getattr(p, 'entity_type', '') == "Point"] if c_curve and c_curve.definitions else []
            objs = [pt] + curve_pts
            self._add_and_log_conjecture(fact_type, objs, f"    🟡 MMP予想(Incidence): {pt.name} ∈ {curve.name}", base_bonus=10.0)
            return True
        return False

    
    def check_and_add_incidence(self, pt, curve):
        c_pt = pt.get_best_component()
        if c_pt and curve in c_pt.subobjects: return False
        if curve in pt.mmp_subobjects: return False
        
        valid_count = 0
        for _ in range(5): 
            t_dict = {v: np.random.choice(self.t_samples) for v in self.all_vars}
            cache = self._evaluate_all_nodes(t_dict)
            try:
                pt_val = pt.calculate(t_dict, cache)
                c_val = curve.calculate(t_dict, cache)
                
                if all(is_zero_mod(v) for v in pt_val) or all(is_zero_mod(v) for v in c_val): continue
                if is_zero_mod(pt_val[-1]): continue 
                if curve.entity_type == "Line" and is_zero_mod(c_val[0]) and is_zero_mod(c_val[1]): continue

                is_on_curve = False
                if curve.entity_type == "Line":
                    dot = c_val[0]*pt_val[0] + c_val[1]*pt_val[1] + c_val[2]*pt_val[2]
                    if is_zero_mod(dot): is_on_curve = True
                elif curve.entity_type == "Circle":
                    u, v, w, s = c_val
                    x, y, z = pt_val
                    val = u*(x**2 + y**2) + v*x*z + w*y*z + s*z**2
                    if is_zero_mod(val): is_on_curve = True

                if is_on_curve: valid_count += 1
            except: pass
        
        if valid_count == 5: 
            pt.mmp_subobjects.add(curve)
            curve.mmp_subobjects.add(pt)
            
            fact_type = "Concyclic" if curve.entity_type == "Circle" else "Collinear"
            c_curve = curve.get_best_component()
            curve_pts = [p for p in next(iter(c_curve.definitions)).parents if getattr(p, 'entity_type', '') == "Point"] if c_curve and c_curve.definitions else []
            
            objs = [pt] + curve_pts
            self._add_and_log_conjecture(fact_type, objs, f"    🟡 MMP予想(Incidence): {pt.name} ∈ {curve.name}", base_bonus=10.0)
            return True
        return False

    def check_identical_mmp(self, entity1, entity2) -> bool:
        if entity1.entity_type != entity2.entity_type: return False
        
        valid_count = 0
        for _ in range(5):
            t_dict = {v: np.random.choice(self.t_samples) for v in self.all_vars}
            # 🌟 FIX: キャッシュを用いて角度や方向も確実に同一性を判定する
            cache = self._evaluate_all_nodes(t_dict) 
            try:
                val1 = entity1.calculate(t_dict, cache)
                val2 = entity2.calculate(t_dict, cache)
                if not val1 or not val2 or len(val1) != len(val2): continue
                
                if self._check_numerical_match(val1, val2):
                    valid_count += 1
            except: pass
            
        return valid_count == 5

    # ==========================================
    # 以下、既存の Degree・Canonical メソッドなどそのまま
    # ==========================================
    def evaluate_numerical_degree(self, Z, naive_d, target_var, max_samples=None):
        t_values, x_values, y_values = [], [], []
        fixed_vars = {v: ModInt(np.random.randint(1, ModInt.MOD - 1)) for v in self.all_vars if v != target_var}
        required_samples = 2 * naive_d + 3 
        sample_pool = self.t_samples[:max_samples] if max_samples else self.t_samples
        
        for t in sample_pool:
            current_t_dict = {**fixed_vars, target_var: t}
            cache = self._evaluate_all_nodes(current_t_dict)
            try:
                val = Z.calculate(current_t_dict, cache)
                if val[-1].value == 0: continue
                x, y = val[0] / val[-1], val[1] / val[-1]
                t_values.append(t); x_values.append(x); y_values.append(y)
                if len(t_values) >= required_samples: break
            except: continue
            
        if len(t_values) < 2 * naive_d + 2: return naive_d
        return max(get_numerical_degree(t_values, x_values, naive_d, mode='mod'),
                   get_numerical_degree(t_values, y_values, naive_d, mode='mod'))

    def evaluate_triangle_numerical_degree(self, p1, p2, p3):
        d1, d2, d3 = getattr(p1, 'numerical_degree', 1) or 1, getattr(p2, 'numerical_degree', 1) or 1, getattr(p3, 'numerical_degree', 1) or 1
        naive_d = d1 + d2 + d3
        if naive_d <= 1 or not self.all_vars: return naive_d
        
        true_d = 0
        coeffs = [ModInt(np.random.randint(1, ModInt.MOD)) for _ in range(6)]
        
        for target_var in self.all_vars:
            t_values, val_values = [], []
            fixed_vars = {v: ModInt(np.random.randint(1, ModInt.MOD - 1)) for v in self.all_vars if v != target_var}
            required_samples = 2 * naive_d + 3 
            
            for t in self.t_samples:
                t_dict = {**fixed_vars, target_var: t}
                cache = self._evaluate_all_nodes(t_dict)
                try:
                    v1, v2, v3 = p1.calculate(t_dict, cache), p2.calculate(t_dict, cache), p3.calculate(t_dict, cache)
                    if is_zero_mod(v1[-1]) or is_zero_mod(v2[-1]) or is_zero_mod(v3[-1]): continue
                    
                    x1, y1 = v1[0]/v1[-1], v1[1]/v1[-1]
                    x2, y2 = v2[0]/v2[-1], v2[1]/v2[-1]
                    x3, y3 = v3[0]/v3[-1], v3[1]/v3[-1]
                    
                    val = coeffs[0]*x1 + coeffs[1]*y1 + coeffs[2]*x2 + coeffs[3]*y2 + coeffs[4]*x3 + coeffs[5]*y3
                    t_values.append(t)
                    val_values.append(val)
                    if len(t_values) >= required_samples: break
                except: pass
                
            if len(t_values) >= 2:
                true_d += get_numerical_degree(t_values, val_values, naive_d, mode='mod')
                
        return min(naive_d, true_d)
    
    def is_canonical_angle_order(self, Dir1, Dir2):
        try:
            cache = self._evaluate_all_nodes(self.canonical_t_dict)
            vec1 = Dir1.calculate(self.canonical_t_dict, cache)
            vec2 = Dir2.calculate(self.canonical_t_dict, cache)
            
            a1, b1 = vec1[0], vec1[1]
            a2, b2 = vec2[0], vec2[1]
            cross_val = a1 * b2 - b1 * a2
            
            if cross_val == 0: 
                val1 = a1.value if hasattr(a1, 'value') else int(a1) % ModInt.MOD
                val2 = a2.value if hasattr(a2, 'value') else int(a2) % ModInt.MOD
                return val1 < val2
                
            cross_int = cross_val.value if hasattr(cross_val, 'value') else int(cross_val) % ModInt.MOD
            return cross_int < (ModInt.MOD // 2)
        except: return True
        
    def verify_identical(self, node1, node2, test_runs=3):
        rep1, rep2 = node1.get_rep(), node2.get_rep()
        if rep1.entity_type != rep2.entity_type: return False

        valid_count = 0
        error_log = None
        last_v1, last_v2 = None, None

        for i in range(test_runs):
            t_dict = {v: np.random.choice(self.t_samples) for v in self.all_vars}
            cache = self._evaluate_all_nodes(t_dict)
            try:
                v1 = rep1.calculate(t_dict, cache)
                v2 = rep2.calculate(t_dict, cache)
                last_v1, last_v2 = v1, v2
                if not v1 or not v2 or len(v1) != len(v2): continue
                if self._check_numerical_match(v1, v2): valid_count += 1
            except Exception:
                if not error_log: error_log = traceback.format_exc()
                continue

        is_valid = (valid_count > 0 and valid_count == test_runs)
        if not is_valid:
            rep1._debug_v = [x.value if hasattr(x, 'value') else x for x in (last_v1 or [])]
            rep2._debug_v = [x.value if hasattr(x, 'value') else x for x in (last_v2 or [])]
            if error_log: rep1._calc_err_trace = error_log 
            
            print(f"❌ [拒否詳細] {rep1.name} vs {rep2.name}")
            print(f"   => 値1: {rep1._debug_v}")
            print(f"   => 値2: {rep2._debug_v}")
            if error_log: print(f"   => 💥 エラー発生:\n{error_log}")

        return is_valid

    def _check_numerical_match(self, v1, v2):
        def is_zero(val): return val.value == 0 if hasattr(val, 'value') else val == 0
        if len(v1) == 3: return (is_zero(v1[0]*v2[1] - v1[1]*v2[0]) and is_zero(v1[1]*v2[2] - v1[2]*v2[1]) and is_zero(v1[2]*v2[0] - v1[0]*v2[2]))
        elif len(v1) == 2:
            if (is_zero(v1[0]) and is_zero(v1[1])) or (is_zero(v2[0]) and is_zero(v2[1])): return False
            return is_zero(v1[0]*v2[1] - v1[1]*v2[0])
        elif len(v1) == 1: return is_zero(v1[0] - v2[0])
        return False
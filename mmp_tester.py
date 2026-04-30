# mmp_tester.py
import numpy as np
import itertools
import logging
from mmp_core import ModInt, get_numerical_degree, create_geo_entity
from logic_core import Fact

logger = logging.getLogger("GeometryProver")

def is_zero_mod(v):
    if hasattr(v, 'value'): return v.value == 0
    if hasattr(v, 'val'): return v.val == 0
    if hasattr(v, 'n'): return v.n == 0
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

    def _eval_point(self, P, t_dict):
        cache = {}
        try:
            val = P.calculate(t_dict, cache)
            if is_zero_mod(val[-1]): return None
            return (val[0]/val[-1], val[1]/val[-1])
        except:
            return None

    def _add_and_log_conjecture(self, fact_type, objects, log_message):
        """🌟 NEW: 既に証明済みの事実や登録済みの予想を重複登録しないためのラッパー"""
        test_fact = Fact(fact_type, objects)
        
        # 既存のFactを検索
        existing = next((f for f in self.prover.facts if f == test_fact), None)
        
        if existing:
            # すでに証明済み（または問題の仮定）ならスキップ
            if existing.is_proven:
                return False 
            # すでに予想として登録済みならログをスパムしない
            if existing.is_mmp_conjecture:
                return False 

            # 既存だが未証明で予想フラグも立っていない場合
            existing.is_mmp_conjecture = True
            existing.proof_source = f"MMP予想({fact_type})"
            logger.debug(log_message)
            return True
            
        # 完全な新規Factの場合
        test_fact.is_proven = False
        test_fact.is_mmp_conjecture = True
        test_fact.proof_source = f"MMP予想({fact_type})"
        self.prover.facts.append(test_fact)
        logger.debug(log_message)
        return True


    def discover_all_mmp_relations(self, Z, parents):
        if is_point(Z):
            for c in [n for n in self.env.nodes if (is_line(n) or is_circle(n)) and n not in parents]: 
                self.check_and_add_incidence(Z, c)
        elif is_line(Z) or is_circle(Z):
            for p in [n for n in self.env.nodes if is_point(n) and n not in parents]: 
                self.check_and_add_incidence(p, Z)
                
        if is_line(Z):
            hot_lines = [n for n in self.env.nodes if is_line(n) and n not in parents and n.importance >= 3.0]
            for ln in hot_lines:
                if Z == ln: continue
                valid_para, valid_perp = 0, 0
                for _ in range(5):
                    cache = {}
                    random_t_dict = {v: np.random.choice(self.t_samples) for v in self.all_vars}
                    try:
                        cZ = Z.calculate(random_t_dict, cache)
                        cln = ln.calculate(random_t_dict, cache)
                        if is_zero_mod(cZ[0]*cln[1] - cZ[1]*cln[0]): valid_para += 1
                        if is_zero_mod(cZ[0]*cln[0] + cZ[1]*cln[1]): valid_perp += 1
                    except: pass
                    
                if valid_para == 5:
                    self._add_and_log_conjecture("Parallel", [Z, ln], f"    🟡 MMP予想(平行): {Z.name} // {ln.name}")
                    
                if valid_perp == 5:
                    if hasattr(self.env, 'add_right_angle'):
                        self.env.add_right_angle(Z, ln)
                        logger.debug(f"    🌟 MMP発見(垂直): {Z.name} ⊥ {ln.name}")

        if is_point(Z):
            hot_pts = [n for n in self.env.nodes if is_point(n) and n != Z and n not in parents and getattr(n, 'importance', 1.0) >= 3.0]
            if len(hot_pts) < 3: return
            
            collinear_groups = []

            for p1, p2 in itertools.combinations(hot_pts, 2):
                if self.check_identical_mmp(p1, p2) or self.check_identical_mmp(Z, p1): continue
                
                valid_collinear = 0
                for _ in range(5):
                    t_dict = {v: np.random.choice(self.t_samples) for v in self.all_vars}
                    v_Z = self._eval_point(Z, t_dict)
                    v_p1 = self._eval_point(p1, t_dict)
                    v_p2 = self._eval_point(p2, t_dict)
                    if not (v_Z and v_p1 and v_p2): continue
                    
                    area = v_Z[0]*(v_p1[1]-v_p2[1]) + v_p1[0]*(v_p2[1]-v_Z[1]) + v_p2[0]*(v_Z[1]-v_p1[1])
                    if is_zero_mod(area): valid_collinear += 1
                        
                if valid_collinear == 5:
                    self._add_and_log_conjecture("Collinear", [Z, p1, p2], f"    🟡 MMP予想(共線): {Z.name}, {p1.name}, {p2.name}")
                    collinear_groups.append({Z, p1, p2})

            for p1, p2, p3 in itertools.combinations(hot_pts, 3):
                pts_set = {Z, p1, p2, p3}
                is_sub_collinear = False
                for group in collinear_groups:
                    if len(group & pts_set) >= 3:
                        is_sub_collinear = True
                        break
                if is_sub_collinear:
                    continue 
                
                temp_circle = create_geo_entity("Circumcircle", [p1, p2, p3], name="temp", env=None)
                valid_count = 0
                for _ in range(5):
                    cache = {}
                    t_dict = {v: np.random.choice(self.t_samples) for v in self.all_vars}
                    try:
                        c_val = temp_circle.calculate(t_dict, cache)
                        Z_val = Z.calculate(t_dict, cache)
                        if all(is_zero_mod(v) for v in c_val) or all(is_zero_mod(v) for v in Z_val): continue
                        if is_zero_mod(Z_val[-1]): continue
                        
                        u, v, w, s = c_val
                        x, y, z = Z_val
                        val = u*(x**2 + y**2) + v*x*z + w*y*z + s*z**2
                        if is_zero_mod(val):
                            valid_count += 1
                    except: pass

                if valid_count == 5:
                    self._add_and_log_conjecture("Concyclic", [Z, p1, p2, p3], f"    🟡 MMP予想(共円): {Z.name}, {p1.name}, {p2.name}, {p3.name}")


    def check_and_add_incidence(self, pt, curve):
        c_pt = pt.get_best_component()
        if c_pt and curve in c_pt.subobjects: return False
        if curve in pt.mmp_subobjects: return False
        
        valid_count = 0
        for _ in range(5): 
            cache = {}
            t_dict = {v: np.random.choice(self.t_samples) for v in self.all_vars}
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

                if is_on_curve:
                    valid_count += 1
            except: pass
        
        if valid_count == 5: 
            pt.mmp_subobjects.add(curve)
            curve.mmp_subobjects.add(pt)
            
            fact_type = "Concyclic" if curve.entity_type == "Circle" else "Collinear"
            c_curve = curve.get_best_component()
            curve_pts = [p for p in next(iter(c_curve.definitions)).parents if getattr(p, 'entity_type', '') == "Point"] if c_curve and c_curve.definitions else []
            
            objs = [pt] + curve_pts
            self._add_and_log_conjecture(fact_type, objs, f"    🟡 MMP予想(Incidence): {pt.name} ∈ {curve.name}")
            return True
        return False

    def check_identical_mmp(self, entity1, entity2) -> bool:
        if entity1.entity_type != entity2.entity_type: return False
        
        valid_count = 0
        for _ in range(5):
            cache = {}
            random_t_dict = {v: np.random.choice(self.t_samples) for v in self.all_vars}
            try:
                val1 = entity1.calculate(random_t_dict, cache)
                val2 = entity2.calculate(random_t_dict, cache)
                
                idx1 = next((i for i, x in enumerate(val1) if not is_zero_mod(x)), -1)
                idx2 = next((i for i, x in enumerate(val2) if not is_zero_mod(x)), -1)
                
                if idx1 == idx2:
                    if idx1 == -1: 
                        valid_count += 1 
                    else:
                        ratio = val2[idx1] / val1[idx1]
                        if all(is_zero_mod(val1[i] * ratio - val2[i]) for i in range(len(val1))):
                            valid_count += 1
            except: pass
            
        return valid_count == 5

    def evaluate_numerical_degree(self, Z, naive_d, target_var, max_samples=None):
        t_values, x_values, y_values = [], [], []
        fixed_vars = {v: ModInt(np.random.randint(1, ModInt.MOD - 1)) for v in self.all_vars if v != target_var}
        
        required_samples = 2 * naive_d + 3 
        sample_pool = self.t_samples[:max_samples] if max_samples else self.t_samples
        
        for t in sample_pool:
            cache = {}
            current_t_dict = {**fixed_vars, target_var: t}
            try:
                val = Z.calculate(current_t_dict, cache)
                if val[-1].value == 0: continue
                x, y = val[0] / val[-1], val[1] / val[-1]
                t_values.append(t); x_values.append(x); y_values.append(y)
                
                if len(t_values) >= required_samples:
                    break
            except: continue
            
        if len(t_values) < 2 * naive_d + 2: return naive_d
        return max(get_numerical_degree(t_values, x_values, naive_d, mode='mod'),
                   get_numerical_degree(t_values, y_values, naive_d, mode='mod'))

    def evaluate_triangle_numerical_degree(self, p1, p2, p3):
        d1 = getattr(p1, 'numerical_degree', 1) or 1
        d2 = getattr(p2, 'numerical_degree', 1) or 1
        d3 = getattr(p3, 'numerical_degree', 1) or 1
        naive_d = d1 + d2 + d3
        
        if naive_d <= 1 or not self.all_vars: return naive_d
        
        true_d = 0
        coeffs = [ModInt(np.random.randint(1, ModInt.MOD)) for _ in range(6)]
        
        for target_var in self.all_vars:
            t_values, val_values = [], []
            fixed_vars = {v: ModInt(np.random.randint(1, ModInt.MOD - 1)) for v in self.all_vars if v != target_var}
            required_samples = 2 * naive_d + 3 
            
            for t in self.t_samples:
                cache = {}
                t_dict = {**fixed_vars, target_var: t}
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
                d = get_numerical_degree(t_values, val_values, naive_d, mode='mod')
                true_d += d
                
        return min(naive_d, true_d)
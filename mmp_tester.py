# mmp_tester.py
import numpy as np
import itertools
import logging
from mmp_core import ModInt, get_numerical_degree, create_geo_entity, set_canonical_t_dict
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
        
        # 🌟 NEW: mmp_core に正規化用の「絶対基準座標」を注入！
        canonical_t_dict = {v: self.t_samples[0] for v in self.all_vars}
        set_canonical_t_dict(canonical_t_dict)

    def _eval_point(self, P, t_dict):
        cache = {}
        try:
            val = P.calculate(t_dict, cache)
            if is_zero_mod(val[-1]): return None
            return (val[0]/val[-1], val[1]/val[-1])
        except:
            return None

    # ==========================================
    # 🌟 NEW: 関連度に基づく熱(Heat)の計算と付与
    # ==========================================
    def _apply_conjecture_heat(self, objects, base_bonus):
        """予想に関わった図形の基礎重要度に応じてボーナスを減衰させ、付与する"""
        valid_objs = [o for o in objects if hasattr(o, 'base_importance')]
        if not valid_objs: return 0.0
        
        # 関わった図形の基礎重要度(Base Importance)の平均をとる
        avg_base = sum(o.base_importance for o in valid_objs) / len(valid_objs)
        
        # 初期のGiven点が 10.0 程度であることを基準にスケール
        # 基礎重要度が低い(深い作図の)図形同士の発見ほど、得られるボーナスは小さくなる
        scaled_bonus = base_bonus * (avg_base / 10.0)
        
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
            
            # 🌟 NEW: スコアを計算して記録、図形を加熱する
            score = self._apply_conjecture_heat(objects, base_bonus)
            existing.conjecture_score = score
            logger.debug(f"{log_message} (熱ボーナス: +{score:.2f})")
            return True
            
        test_fact.is_proven = False
        test_fact.is_mmp_conjecture = True
        test_fact.proof_source = f"MMP予想({fact_type})"
        
        # 🌟 NEW: スコアを計算して記録、図形を加熱する
        score = self._apply_conjecture_heat(objects, base_bonus)
        test_fact.conjecture_score = score
        self.prover.facts.append(test_fact)
        logger.debug(f"{log_message} (熱ボーナス: +{score:.2f})")
        return True


    def discover_all_mmp_relations(self, Z, parents):
        # ==========================================
        # 🌟 NEW: 次数(Degree)によるハードリミット
        # ==========================================
        if getattr(Z, 'base_importance', 1.0) <= 0.0:
            return
        deg = getattr(Z, 'numerical_degree', 1) or 1
        if Z.entity_type in ["Point", "Line", "Direction"]:
            if deg > 15: return  # 複雑すぎる点や線はテストしない
        elif Z.entity_type in ["Circle", "Scalar", "LengthSq", "AffineRatio"]:
            if deg > 25: return  # 複雑すぎる円やスカラーはテストしない

        if is_point(Z):
            valid_curves = [n for n in self.env.nodes if (is_line(n) or is_circle(n)) and n not in parents and getattr(n, 'base_importance', 1.0) > 0.0]
            for c in valid_curves: 
                self.check_and_add_incidence(Z, c)
        elif is_line(Z) or is_circle(Z):
            valid_pts = [n for n in self.env.nodes if is_point(n) and n not in parents and getattr(n, 'base_importance', 1.0) > 0.0]
            for p in valid_pts: 
                self.check_and_add_incidence(p, Z)
                
        if is_line(Z):
            hot_lines = [n for n in self.env.nodes if is_line(n) and n not in parents and getattr(n, 'importance', 1.0) >= 3.0]
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
                    self._add_and_log_conjecture("Parallel", [Z, ln], f"    🟡 MMP予想(平行): {Z.name} // {ln.name}", base_bonus=10.0)
                    
                if valid_perp == 5:
                    if hasattr(self.env, 'add_right_angle'):
                        self.env.add_right_angle(Z, ln)
                        score = self._apply_conjecture_heat([Z, ln], 10.0)
                        logger.debug(f"    🌟 MMP発見(垂直): {Z.name} ⊥ {ln.name} (熱ボーナス: +{score:.2f})")

        if is_point(Z):
            hot_pts = [n for n in self.env.nodes if is_point(n) and n != Z and n not in parents and getattr(n, 'importance', 1.0) >= 3.0]
            if len(hot_pts) < 3: return
            
            collinear_groups = []

            for p1, p2 in itertools.combinations(hot_pts, 2):
                if self.check_identical_mmp(p1, p2) or self.check_identical_mmp(Z, p1): continue
                
                # 🌟 Trivial Check: E-Graph上ですでに共線であることが分かっているならテストをスキップ
                cZ, c1, c2 = Z.get_best_component(), p1.get_best_component(), p2.get_best_component()
                if cZ and c1 and c2:
                    common_lines = [obj for obj in (cZ.subobjects & c1.subobjects & c2.subobjects) if getattr(obj, 'entity_type', '') == "Line"]
                    if common_lines:
                        continue # 自明な共線なので無視
                
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
                    # 共線は幾何的に強力なサブゴールなので base_bonus=15.0
                    self._add_and_log_conjecture("Collinear", [Z, p1, p2], f"    🟡 MMP予想(共線): {Z.name}, {p1.name}, {p2.name}", base_bonus=15.0)
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
                
                # ==========================================
                # 🌟 NEW: MMPを用いた強力な共線ガード (縮退円の排除)
                # 4点のうち、どの3点を選んでも「面積0（共線）」にならないかチェック
                # ==========================================
                pts_list = list(pts_set)
                is_degenerate = False
                for comb in itertools.combinations(pts_list, 3):
                    valid_col = 0
                    for _ in range(3): # 3回テストすれば十分
                        t_dict = {v: np.random.choice(self.t_samples) for v in self.all_vars}
                        v_A = self._eval_point(comb[0], t_dict)
                        v_B = self._eval_point(comb[1], t_dict)
                        v_C = self._eval_point(comb[2], t_dict)
                        if not (v_A and v_B and v_C): continue
                        
                        area = v_A[0]*(v_B[1]-v_C[1]) + v_B[0]*(v_C[1]-v_A[1]) + v_C[0]*(v_A[1]-v_B[1])
                        if is_zero_mod(area): valid_col += 1
                            
                    if valid_col >= 2:
                        is_degenerate = True
                        break # いずれかの3点が共線なので、これは円ではなく直線
                
                if is_degenerate:
                    continue # 縮退しているので共円テストを行わない
                # ==========================================

                # 🌟 Trivial Check: E-Graph上ですでに共円であることが分かっているならテストをスキップ
                c3 = p3.get_best_component()
                if cZ and c1 and c2 and c3:
                    common_circs = [obj for obj in (cZ.subobjects & c1.subobjects & c2.subobjects & c3.subobjects) if getattr(obj, 'entity_type', '') == "Circle"]
                    if common_circs:
                        continue # 自明な共円なので無視

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
                    # 共円は非常に強力なサブゴールなので base_bonus=20.0
                    self._add_and_log_conjecture("Concyclic", [Z, p1, p2, p3], f"    🟡 MMP予想(共円): {Z.name}, {p1.name}, {p2.name}, {p3.name}", base_bonus=20.0)


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
            self._add_and_log_conjecture(fact_type, objs, f"    🟡 MMP予想(Incidence): {pt.name} ∈ {curve.name}", base_bonus=10.0)
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

    def get_canonical_line_vector(self, L):
        """
        直線のMMP座標を「射影空間の標準形」に変換する。
        先頭の非零要素の逆元を掛けることで、スカラー倍の揺らぎを完全に吸収し、
        E-Graph全体で絶対に揺るがない Canonical なタプルを生成する。
        """
        cache = {}
        # 常に固定のシード(t_samples[0])を使って評価を完全に固定する
        t_dict = {v: self.t_samples[0] for v in self.all_vars}
        
        try:
            vec = L.calculate(t_dict, cache)
            
            # 先頭の非零要素のインデックスを探す
            idx = next((i for i, x in enumerate(vec) if not is_zero_mod(x)), -1)
            if idx == -1: 
                return (0, 0, 0) # ゼロベクトルのフォールバック
            
            # 先頭の非零要素が必ず 1 になるように全体を正規化 (ユーザー提案の究極系)
            inv_val = ModInt(1) / vec[idx]
            norm_vec = []
            for x in vec:
                val = x.value if hasattr(x, 'value') else int(x) % ModInt.MOD
                norm_val = (val * inv_val.value) % ModInt.MOD
                norm_vec.append(norm_val)
                
            return tuple(norm_vec)
        except:
            return (0, 0, 0) # 計算不能時のフォールバック

    def is_canonical_angle_order(self, L1, L2):
        """
        正規化されたMMP座標の辞書順比較によって、
        2直線のなす角の「順序」を完全に一意(Ordered)に決定する。
        """
        v1 = self.get_canonical_line_vector(L1)
        v2 = self.get_canonical_line_vector(L2)
        
        # 辞書順で完全に一意な True/False が決まる！
        return v1 < v2
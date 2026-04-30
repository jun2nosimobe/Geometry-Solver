
class Fact:
    """システムが認識している幾何学的事実（証明済み/未証明の両方を含む）"""
    # ★ is_proven と proof_source の両方を受け取れるように変更
    def __init__(self, fact_type, objects, is_proven=False, proof_source=""):
        self.fact_type = fact_type  
        self.objects = objects
        self.is_proven = is_proven
        self.proof_source = proof_source
        self.dependents = [] 

    def mark_as_proven(self, source_description):
        if not self.is_proven:
            self.is_proven = True
            self.proof_source = source_description
            print(f"  🟢 [証明完了] {self} が証明されました！ (理由: {source_description})")
            for step in self.dependents:
                step.check_if_proven()

    def __eq__(self, other):
        if not isinstance(other, Fact) or self.fact_type != other.fact_type:
            return False
        if self.fact_type in ["Concyclic", "Collinear"]:
            return set(self.objects) == set(other.objects)
        return self.objects == other.objects
        
    def __repr__(self):
        status = "🟢" if self.is_proven else "🟡"
        names = [o.name for o in self.objects]
        return f"{status} [{self.fact_type}] {', '.join(names)}"

class ProofStep:
    """ある事実から別の事実を導く推論の1ステップ（辺）"""
    def __init__(self, theorem_name, premises, conclusion):
        self.theorem_name = theorem_name
        self.premises = premises     # 前提となる Fact のリスト
        self.conclusion = conclusion # 導かれる Fact
        
        # 自身を「前提事実」たちの依存先として登録する（辺を張る）
        for p in self.premises:
            if p not in p.dependents:
                p.dependents.append(self)

    def check_if_proven(self):
        """前提がすべて証明済みになったかチェックし、OKなら結論も証明済みにする"""
        if self.conclusion.is_proven:
            return # すでに証明済みなら何もしない
            
        if all(p.is_proven for p in self.premises):
            # すべての前提が緑色（証明済み）になった！
            premise_strs = ", ".join([str(p) for p in self.premises])
            self.conclusion.mark_as_proven(f"{self.theorem_name} (前提: {premise_strs})")

# ★ ここを GeometryTheorem に統一し、プロパティ名を match_func に変更
class GeometryTheorem:
    def __init__(self, name, match_func, apply_func):
        self.name = name
        self.match_func = match_func
        self.apply_func = apply_func

# --- 定理の定義 ---
def match_cyclic_quadrilateral(facts):
    """円に内接する四角形から、円周角が等しいという事実を導出"""
    matches = []
    for f in facts:
        if f.fact_type == "Concyclic" and len(f.objects) >= 4:
            import itertools
            points = list(f.objects)
            # 4点から「弦」の端点となる2点を選ぶ (6通りに最適化)
            for chord in itertools.combinations(points, 2):
                A, B = chord
                # 残りの2点を「円周上の頂点」とする
                others = [p for p in points if p not in chord]
                C, D = others[0], others[1]
                
                # 重複や対称な生成を防ぐためソート
                if id(C) > id(D):
                    C, D = D, C
                
                matches.append((C, A, C, B, D, A, D, B, f))
    return matches

def apply_cyclic_quadrilateral(match):
    C, A, C2, B, D, A2, D2, B2, source_fact = match
    # ★ 修正: 結論は未証明(is_proven=False)として生成
    conclusion = Fact("EqualAngle", [C, A, C, B, D, A, D, B], is_proven=False, proof_source=f"円周角の定理 (前提: {source_fact})")
    # ★ 修正: (前提のリスト, 結論) のタプルを返す
    return [source_fact], conclusion

def match_converse_cyclic(facts):
    """等しい円周角から、共円を導出"""
    matches = []
    for f in facts:
        if f.fact_type == "EqualAngle":
            objs = f.objects
            if objs[0] == objs[2] and objs[4] == objs[6]: 
                C, A, B = objs[0], objs[1], objs[3]
                D, A2, B2 = objs[4], objs[5], objs[7]
                if (A == A2 and B == B2) or (A == B2 and B == A2):
                    matches.append((A, B, C, D, f))
    return matches

def apply_converse_cyclic(match):
    A, B, C, D, source_fact = match
    # ★ 修正: 結論は未証明(is_proven=False)として生成
    conclusion = Fact("Concyclic", [A, B, C, D], is_proven=False, proof_source=f"円周角の定理の逆 (前提: {source_fact})")
    # ★ 修正: (前提のリスト, 結論) のタプルを返す
    return [source_fact], conclusion

# ★ 新しい定理3: 共線（Collinear）の推移律
# A, B, C が共線で、A, B, D が共線なら、C, D もその直線上にある
def match_collinear_transitive(facts):
    matches = []
    collinear_facts = [f for f in facts if f.fact_type == "Collinear"]
    for f1, f2 in itertools.combinations(collinear_facts, 2):
        # 2つの共線事実に共通する点が2つ以上あれば、それらは同じ直線
        common_points = set(f1.objects) & set(f2.objects)
        if len(common_points) >= 2:
            all_points = list(set(f1.objects) | set(f2.objects))
            matches.append((all_points, f1, f2))
    return matches

def apply_collinear_transitive(match):
    all_points, f1, f2 = match
    conclusion = Fact("Collinear", all_points, is_proven=False, proof_source=f"共線の推移律")
    return [f1, f2], conclusion

# ★ 新しい定理4: 垂直（Perpendicular）と有向角
# L1 と L2 が垂直なら、∠(L1, L2) = 90度（有向角の特殊なFact）
# ... (実装を THEOREMS リストに追加していく)

# ★ インスタンス化も GeometryTheorem に統一
THEOREMS = [
    GeometryTheorem("円周角の定理", match_cyclic_quadrilateral, apply_cyclic_quadrilateral),
    GeometryTheorem("円周角の定理の逆", match_converse_cyclic, apply_converse_cyclic),
    GeometryTheorem("共線の推移律", match_collinear_transitive, apply_collinear_transitive)
]


class LogicProver:
    def __init__(self, target_fact):
        self.facts = []
        self.target_fact = target_fact
        
    def get_or_add_fact(self, new_fact):
        """すでに同じ事実が存在すればそれを返し、無ければ登録する"""
        for existing in self.facts:
            if existing == new_fact:
                return existing
        self.facts.append(new_fact)
        print(f"  🔍 [事実登録] {new_fact}")
        return new_fact
            
    def add_fact(self, fact):
        """初期の事実（仮定やMMPの発見など）を直接登録する"""
        return self.get_or_add_fact(fact)

    def run_forward_chaining(self, max_steps=10):
        print("\n=== 論理推論(Forward Chaining) 開始 ===")
        for step in range(max_steps):
            new_steps_count = 0
            
            for theorem in THEOREMS:
                # 未証明の事実も含めて、すべての事実からマッチを探す
                matches = theorem.match_func(self.facts)
                for match in matches:
                    # theorem.apply_func は (premises_list, new_fact_template) を返すと仮定
                    premises, conclusion_template = theorem.apply_func(match)
                    
                    # グラフ内の既存のFactと紐付ける
                    actual_premises = [self.get_or_add_fact(p) for p in premises]
                    actual_conclusion = self.get_or_add_fact(conclusion_template)
                    
                    # すでにこの推論ステップが存在するかチェック（重複防止）
                    step_exists = any(
                        isinstance(dep, ProofStep) and dep.conclusion == actual_conclusion and dep.theorem_name == theorem.name 
                        for p in actual_premises for dep in p.dependents
                    )
                    
                    if not step_exists:
                        # ★ ここで「事実A -> 事実B」の依存関係の辺を張る！
                        proof_step = ProofStep(theorem.name, actual_premises, actual_conclusion)
                        new_steps_count += 1
                        
                        # 辺を張った瞬間に、前提がすでにすべて証明済みなら即座に証明される
                        proof_step.check_if_proven()

            # 目標の事実が証明済みになったら終了
            target_in_graph = next((f for f in self.facts if f == self.target_fact), None)
            if target_in_graph and target_in_graph.is_proven:
                print("\n🎉 ★論理的証明に成功しました！★")
                return True

            if new_steps_count == 0:
                print("  -> これ以上新しい推論の辺を張れません。")
                break
        return False

    def print_proof_trace(self, target_fact):
        print("\n【証明のトレース（証明された事実の連鎖）】")
        proven_facts = [f for f in self.facts if f.is_proven]
        for i, f in enumerate(proven_facts):
            print(f" {i+1}. {f}")
            print(f"      <= {f.proof_source}")



class SymbolicProver:
    def __init__(self, initial_facts, target_fact):
        self.known_facts = initial_facts
        self.target_fact = target_fact
        self.proof_history = []
        
    def prove(self, max_steps=10):
        print(f"\n--- 論理的証明の開始 ---")
        print(f"目標: {self.target_fact}")
        
        for step in range(max_steps):
            new_facts_in_this_step = []
            
            # すべての定理を現在の事実に適用してみる
            for theorem in THEOREMS:
                matches = theorem.check_rule(self.known_facts)
                for match in matches:
                    new_fact = theorem.apply_rule(match)
                    
                    if new_fact not in self.known_facts and new_fact not in new_facts_in_this_step:
                        new_facts_in_this_step.append(new_fact)
                        self.proof_history.append(f"[{theorem.name}] により、{new_fact} が導かれた。")
                        
                        # 目標に到達したか？
                        if new_fact == self.target_fact:
                            print("★論理的証明に成功しました！★")
                            self._print_proof()
                            return True
                            
            if not new_facts_in_this_step:
                print("これ以上新しい事実を導けません（手詰まり）。")
                return False
                
            self.known_facts.extend(new_facts_in_this_step)
            
        return False
        
    def _print_proof(self):
        print("\n【証明のステップ】")
        for i, step in enumerate(self.proof_history):
            print(f" {i+1}. {step}")



class ProofGoal:
    def __init__(self, target_condition, desc=""):
        self.target_condition = target_condition
        self.desc = desc
        self.subgoals = []
        self.is_proven = False

def solve_goal_with_mmp(all_nodes, moving_point, current_goal, depth=0, history=None):
    if history is None: history = set()
    indent = "  " * depth
    print(f"\n{indent}▶ サブゴール開始: {current_goal.desc}")
    
    if depth > 3:
        print(f"{indent}  [中断] 探索が深すぎるため打ち切ります。")
        return False
        
    if current_goal.desc in history:
        print(f"{indent}  [スキップ] すでに探索済みのゴールです。")
        return False
    history.add(current_goal.desc)
    
    N_samples = 60
    t_samples = []
    while len(t_samples) < N_samples:
        t = ModInt(np.random.randint(1, ModInt.MOD - 1))
        try: 
            current_goal.target_condition.evaluate(t, {})
            t_samples.append(t)
        except: pass

    priorities = {n.id: 50 for n in all_nodes}
    for n in all_nodes:
        if isinstance(n, PointFixed): priorities[n.id] = 10
    priorities[moving_point.id] = 5
    for p in current_goal.target_condition.parents: priorities[p.id] = 1

    iteration = 1
    while iteration < 20: 
        for n in all_nodes: n.naive_degree_cache.clear()
        
        current_deg = current_goal.target_condition.calc_naive_degree(moving_point)
        print(f"{indent}  [第 {iteration} 世代] 目標式のナイーブ次数: {current_deg}")
        
        if current_deg <= 6:
            is_zero = True
            for i in range(current_deg + 1):
                if current_goal.target_condition.evaluate(t_samples[i], {}) != 0: is_zero = False
            if is_zero:
                print(f"{indent}  => ★証明完了★ 次数 {current_deg} の多項式が {current_deg+1} 点で 0 になることを確認しました！")
                current_goal.is_proven = True
                return True

        active_nodes = [n for n in all_nodes if not n.redefined_as and not isinstance(n, (EvaluateCircleCondition, EvaluateLineCondition))]
        points = [n for n in active_nodes if isinstance(n, (PointFixed, MovingPoint, Intersection, CircleLineOtherIntersection, Reflection)) or n.overridden_degree is not None]
        lines = [n for n in active_nodes if isinstance(n, Line)]
        circles = [n for n in active_nodes if isinstance(n, Circle)]
        
        candidates = []
        for l1, l2 in itertools.combinations(lines, 2): candidates.append(Intersection(l1, l2, name=f"Int_{l1.name}_{l2.name}"))
        for p1, p2 in itertools.combinations(points, 2): candidates.append(LineThroughPoints(p1, p2, name=f"Line_{p1.name}_{p2.name}"))
        if isinstance(current_goal.target_condition, EvaluateCircleCondition):
            tc = current_goal.target_condition.parents[0]
            for c in circles:
                if c != tc: candidates.append(RadicalAxis(tc, c, name=f"Rad_{tc.name}_{c.name}"))

        candidates.sort(key=lambda c: sum(priorities.get(p.id, 50) for p in c.parents) + c.calc_naive_degree(moving_point)*10)
        
        new_objects = []
        discovery_made = False
        coeff_n = [ModInt(np.random.randint(1, ModInt.MOD - 1)) for _ in range(4)]
        coeff_d = [ModInt(np.random.randint(1, ModInt.MOD - 1)) for _ in range(4)]
        
        for cand in candidates[:20]:
            naive_d = cand.calc_naive_degree(moving_point)
            if naive_d <= 1: continue 
            x_vals, valid_t = [], []
            for t in t_samples:
                try:
                    val = cand.evaluate(t, {})
                    num = sum(coeff_n[i] * val[i] for i in range(len(val)))
                    den = sum(coeff_d[i] * val[i] for i in range(len(val)))
                    if den != 0: x_vals.append(num / den); valid_t.append(t)
                except: pass
            if len(valid_t) < 5: continue
            
            true_d = get_numerical_degree(valid_t, x_vals, naive_d, mode='mod')
            if true_d < naive_d:
                if true_d == 0:
                    new_obj = FixedNode(cand.evaluate(valid_t[0], {}), name=f"Fixed_{cand.name}")
                    print(f"{indent}    [発見] 定数オブジェクト {cand.name} (次数0) を発見。")
                    cand.redefine(new_obj) 
                else:
                    new_obj = cand
                    new_obj.overridden_degree = true_d 
                    print(f"{indent}    [発見] {cand.name} の次数低下 ({naive_d}->{true_d}) を発見。")
                    
                new_objects.append(new_obj)
                if new_obj not in all_nodes: all_nodes.append(new_obj)
                priorities[new_obj.id] = 0 
                discovery_made = True

        incidences = []
        eval_points = points + [n for n in new_objects if "Int" in n.name]
        eval_curves = lines + circles + [n for n in new_objects if "Line" in n.name or "Rad" in n.name]
        
        for pt in eval_points:
            for curve in eval_curves:
                subgoal_desc = f"{pt.name} ∈ {curve.name}"
                if subgoal_desc not in history:
                    if check_incidence(pt, curve, t_samples): incidences.append((pt, curve, subgoal_desc))
                    
        for pt, curve, subgoal_desc in incidences:
            curve_deg = curve.calc_naive_degree(moving_point)
            pt_naive_deg = pt.calc_naive_degree(moving_point)
            
            d_true = pt.overridden_degree if pt.overridden_degree is not None else pt_naive_deg
            
            if curve_deg > 0 and d_true > 0 and d_true % curve_deg == 0:
                k = d_true // curve_deg; theo_max = curve_deg * k
            else:
                theo_max = curve_deg + (2 if isinstance(curve, Circle) else 1)
                
            if theo_max < pt_naive_deg:
                print(f"{indent}    [軌跡発見] {pt.name} が {curve.name} 上にあるようです！ (サブゴール化)")
                
                inc_cond = EvaluateLineCondition(curve, pt) if isinstance(curve, Line) else EvaluateCircleCondition(curve, pt)
                subgoal = ProofGoal(inc_cond, desc=subgoal_desc)
                current_goal.subgoals.append(subgoal)
                
                if solve_goal_with_mmp(all_nodes, moving_point, subgoal, depth + 1, history):
                    print(f"{indent}    [反映] 補題 '{subgoal.desc}' が証明されたため、{pt.name} の次数を {theo_max} に下げます。")
                    pt.overridden_degree = theo_max 
                    priorities[pt.id] = 0
                    discovery_made = True
                    break 

        if not discovery_made: break
        iteration += 1
        
    return current_goal.is_proven

# geom.py
import math
import numpy as np
import logging
import importlib
import sys

# コアモジュールのインポート
from mmp_core import create_geo_entity, link_logical_incidence
from logic_core import ProofEnvironment, LogicProver, ProofStep
from theorems import THEOREMS

# リファクタリングで分離したモジュールのインポート
from mmp_tester import MMPTester
from action_space import ActionGenerator

# ログの設定
logger = logging.getLogger("GeometryProver")
logger.setLevel(logging.DEBUG)
if not logger.handlers:
    file_handler = logging.FileHandler('proof.log', mode='w', encoding='utf-8')
    file_handler.setFormatter(logging.Formatter('%(message)s'))
    logger.addHandler(file_handler)

def get_representative(obj):
    """マージされて消えた古い図形から、現在の真の本体を遡る"""
    while hasattr(obj, '_merged_into') and obj._merged_into is not None:
        obj = obj._merged_into
    return obj

def is_zero_mod(v):
    if hasattr(v, 'value'): return v.value == 0
    if hasattr(v, 'val'): return v.val == 0
    if hasattr(v, 'n'): return v.n == 0
    try: return int(v) == 0
    except: return v == 0


# ==========================================
# 1. モンテカルロ木探索 (MCTS) エンジン
# ==========================================
class MCTSNode:
    def __init__(self, action=None, parent=None):
        self.action = action  
        self.parent = parent
        self.children = []
        self.visits = 0
        self.total_score = 0.0
        self.untried_actions = []
        self.is_expanded = False

    def ucb1(self, c=2.0):
        if self.visits == 0: return float('inf')
        return (self.total_score / self.visits) + c * math.sqrt(math.log(self.parent.visits) / self.visits)

class MCTSSearchEngine:
    def __init__(self, env, all_vars, prover):
        self.env = env
        self.all_vars = all_vars
        self.prover = prover
        
        self.tester = MMPTester(self.env, self.all_vars, self.prover)
        self.action_gen = ActionGenerator(set(), self.tester)

    def _playout(self, initial_nodes, depth=3):
        sim_nodes = list(initial_nodes)
        score = 0.0
        
        for step_idx in range(depth):
            actions = self.action_gen.get_possible_actions(sim_nodes, is_simulation=True)
            if not actions: break
            
            action_weights = [sum(getattr(p, 'importance', 1.0) for p in a[0]) for a in actions]
            total_w = sum(action_weights)
            probs = [w / total_w for w in action_weights]
            action = actions[np.random.choice(len(actions), p=probs)]
            
            parents, def_type, name = action[0], action[1], action[2]
            Z = create_geo_entity(def_type, parents, name)
            cZ = Z.get_best_component()
            
            if not cZ or cZ.depth > 6: 
                score -= 1.0
                continue 
            
            score += (sum(getattr(p, 'importance', 1.0) for p in parents) / len(parents)) * (0.5 ** step_idx)

            if Z.entity_type in ["Point", "Line", "Circle"]:
                for var in self.all_vars:
                    nd = cZ.naive_degree
                    if nd > 30: continue
                    score += max(0.1, 2.0 / (nd + 1))
                    if 1 < nd <= 15:
                        td = self.tester.evaluate_numerical_degree(Z, nd, var, max_samples=40)
                        if td <= 15: score += max(0, nd - td) * 20.0 
                            
            if Z.entity_type == "Point":
                hot_curves = [n for n in sim_nodes if n.entity_type in ["Line", "Circle"] and getattr(n, 'importance', 1.0) >= 5.0 and n not in parents]
                for c in hot_curves:
                    cache = {}
                    random_t_dict = {v: self.tester.t_samples[0] for v in self.all_vars}
                    try:
                        Z_val = Z.calculate(random_t_dict, cache)
                        c_val = c.calculate(random_t_dict, cache)
                        
                        # 🌟 修正: ガバガバ判定を修正し、実際に曲線の方程式を満たすかチェックする
                        if c.entity_type == "Line":
                            val = c_val[0]*Z_val[0] + c_val[1]*Z_val[1] + c_val[2]*Z_val[2]
                        elif c.entity_type == "Circle":
                            val = c_val[0]*(Z_val[0]**2 + Z_val[1]**2) + c_val[1]*Z_val[0]*Z_val[2] + c_val[2]*Z_val[1]*Z_val[2] + c_val[3]*Z_val[2]**2
                        else:
                            val = 1 # ダミー
                            
                        if is_zero_mod(val):
                            score += getattr(c, 'importance', 1.0) * 3.0
                            break # 乗っていることが確認できた場合のみブレイク
                    except: pass
            sim_nodes.append(Z)
            
        return score

    def _run_logic_step(self):
        processed_fact_strings = getattr(self, '_debug_processed_facts', set())
        self._debug_processed_facts = processed_fact_strings

        def is_already_in_egraph(fact):
            if any(getattr(obj, '_is_merged_and_dead', False) for obj in fact.objects): return True
            if fact.fact_type == "Concyclic" and len(fact.objects) >= 4:
                comps = [p.get_best_component() for p in fact.objects[:4]]
                if all(comps):
                    common_circles = set.intersection(*(c.subobjects for c in comps))
                    if any(obj.entity_type == "Circle" for obj in common_circles): return True
            elif fact.fact_type == "Collinear" and len(fact.objects) >= 3:
                comps = [p.get_best_component() for p in fact.objects[:3]]
                if all(comps):
                    common_lines = set.intersection(*(c.subobjects for c in comps))
                    if any(obj.entity_type == "Line" for obj in common_lines): return True
            elif fact.fact_type == "EqualAngle_Line" and len(fact.objects) == 4:
                L1, L2, L3, L4 = fact.objects
                for node in self.env.nodes:
                    if getattr(node, 'entity_type', '') == "Angle":
                        comp = node.get_best_component()
                        if not comp: continue
                        has_12 = has_34 = False
                        for d in comp.definitions:
                            if d.def_type == "AnglePair" and len(d.parents) == 2:
                                p_set = {d.parents[0].id, d.parents[1].id}
                                if {L1.id, L2.id} == p_set: has_12 = True
                                if {L3.id, L4.id} == p_set: has_34 = True
                        if has_12 and has_34: return True 
            elif fact.fact_type == "Identical" and len(fact.objects) == 2:
                if get_representative(fact.objects[0]) == get_representative(fact.objects[1]): return True
            return False

        for theorem in THEOREMS:
            matches = theorem.match_func(self.prover.facts, self.env)
            for match in matches:
                premises, conclusion_template = theorem.apply_func(match)

                if conclusion_template is None: continue
                
                if is_already_in_egraph(conclusion_template): continue
                actual_premises = [self.prover.get_or_add_fact(p) for p in premises]
                if not all(p.is_proven for p in actual_premises): continue
                actual_conclusion = self.prover.get_or_add_fact(conclusion_template)
                if actual_conclusion.is_proven: continue

                conclusion_str = str(actual_conclusion)
                if actual_conclusion.fact_type == "Identical" and conclusion_str in processed_fact_strings:
                    if get_representative(actual_conclusion.objects[0]) == get_representative(actual_conclusion.objects[1]): continue
                
                if is_already_in_egraph(conclusion_template): continue
                
                step_exists = any(getattr(dep, 'conclusion', None) == actual_conclusion and getattr(dep, 'theorem_name', '') == theorem.name 
                                  for p in actual_premises for dep in p.dependents)
                
                if not step_exists:
                    proof_step = ProofStep(theorem.name, actual_premises, actual_conclusion)
                    proof_step.check_if_proven()
                    
                    if actual_conclusion.is_proven:
                        processed_fact_strings.add(conclusion_str)
                        logger.debug(f"  [推論] 🟢 {actual_conclusion} (定理: {theorem.name})")
                        
                        # データ還元 (E-Graphへの書き戻し)
                        if actual_conclusion.fact_type == "Concyclic" and len(actual_conclusion.objects) >= 4:
                            pts = actual_conclusion.objects
                            comps = [p.get_best_component() for p in pts[:3]]
                            if all(comps):
                                common_circles = [obj for obj in set.intersection(*(c.subobjects for c in comps)) if obj.entity_type == "Circle"]
                                if common_circles: circ = common_circles[0]
                                else:
                                    circ = create_geo_entity("Circumcircle", pts[:3], name=f"Circum_{pts[0].name}{pts[1].name}{pts[2].name}_(Auto)", env=self.env)
                                    self.env.nodes.append(circ)
                                    for node in self.env.nodes:
                                        if node != circ and self.tester.check_identical_mmp(circ, node):
                                            merged = self.env.merge_entities_logically(node, circ)
                                            if merged: circ = merged
                                            break
                                # 🌟 修正: 4点目以降の「すべて」の点を円にリンクする
                                for p in pts[3:]:
                                    link_logical_incidence(circ, p)

                        elif actual_conclusion.fact_type == "Collinear" and len(actual_conclusion.objects) >= 3:
                            pts = actual_conclusion.objects
                            comps = [p.get_best_component() for p in pts[:2]]
                            if all(comps):
                                common_lines = [obj for obj in set.intersection(*(c.subobjects for c in comps)) if obj.entity_type == "Line"]
                                if common_lines: line_obj = common_lines[0]
                                else:
                                    line_obj = create_geo_entity("LineThroughPoints", pts[:2], name=f"Line_{pts[0].name}{pts[1].name}_(Auto)", env=self.env)
                                    self.env.nodes.append(line_obj)
                                    for node in self.env.nodes:
                                        if node != line_obj and self.tester.check_identical_mmp(line_obj, node):
                                            merged = self.env.merge_entities_logically(node, line_obj)
                                            if merged: line_obj = merged
                                            break
                                # 🌟 修正: 3点目以降の「すべて」の点を直線にリンクする
                                for p in pts[2:]:
                                    link_logical_incidence(line_obj, p)
                        
                        elif actual_conclusion.fact_type == "EqualAngle_Line":
                            self.env.add_equal_angle(*actual_conclusion.objects)

                        elif actual_conclusion.fact_type == "Identical":
                            rep1, rep2 = get_representative(actual_conclusion.objects[0]), get_representative(actual_conclusion.objects[1])
                            if rep1 != rep2:
                                name1, name2 = rep1.name, rep2.name
                                if self.env.merge_entities_logically(rep1, rep2):
                                    actual_conclusion.proof_source += f" (対象: {name1} ≡ {name2})"
                                    logger.debug(f"    🔄 [同一性還元] {name1} と {name2} を統合しました。")
                        
                        for obj in actual_conclusion.objects:
                            obj.importance = min(getattr(obj, 'importance', 1.0) + 5.0, 50.0)

    def run_step(self, num_simulations=40):
        root = MCTSNode()
        root.untried_actions = self.action_gen.get_possible_actions(self.env.nodes)
        if not root.untried_actions: return

        for _ in range(num_simulations):
            node = root
            sim_nodes = list(self.env.nodes)
            
            while node.is_expanded and node.children:
                node = max(node.children, key=lambda c: c.ucb1())
                Z = create_geo_entity(node.action[1], node.action[0], node.action[2], env=None)
                if Z: sim_nodes.append(Z)
                
            if not node.is_expanded and node.untried_actions:
                action = node.untried_actions.pop()
                child = MCTSNode(action=action, parent=node)
                node.children.append(child)
                node = child
                Z = create_geo_entity(action[1], action[0], action[2], env=None)
                if Z: sim_nodes.append(Z)
                if not node.parent.untried_actions: node.parent.is_expanded = True
            
            score = self._playout(sim_nodes, depth=3)
            
            while node is not None:
                node.visits += 1
                node.total_score += score
                node = node.parent

        if not root.children: return
        best_child = max(root.children, key=lambda c: c.visits)
        parents, def_type, name = best_child.action
        
        Z = create_geo_entity(def_type, parents, name, env=self.env)
        cZ = Z.get_best_component()
        
        if def_type == "Triangle":
            cZ.triangle_points = tuple(parents)
            shape_name = f"Shape_{name}"
            new_shape = create_geo_entity("ShapeOf", [Z], name=shape_name, env=self.env)
            new_shape.shape_members[Z] = tuple(parents)
            self.env.nodes.extend([Z, new_shape])
            Z.numerical_degree = self.tester.evaluate_triangle_numerical_degree(*parents)
            logger.debug(f"🤖 [MCTS] {Z.name} を採用 (期待スコア: {best_child.total_score/best_child.visits:.2f})")
        else:
            logger.debug(f"🤖 [MCTS] {Z.name} を採用 (期待スコア: {best_child.total_score/best_child.visits:.2f})")
            total_drop = 0
            for var in self.all_vars:
                nd = cZ.naive_degree
                if cZ.depth > 6 or nd > 40: continue 
                if 1 < nd <= 40:
                    td = self.tester.evaluate_numerical_degree(Z, nd, var)
                    if cZ.depth + td <= 50: total_drop += max(0, nd - td)

            Z.numerical_degree = nd - total_drop 
            self.env.nodes.append(Z)
            
            merged = False
            for node in self.env.nodes:
                if node != Z and self.tester.check_identical_mmp(Z, node):
                    merged_node = self.env.merge_entities_logically(node, Z)
                    if merged_node:
                        merged_node.importance += total_drop * 3 + 5.0
                        Z = merged_node
                    merged = True
                    break
                    
            if not merged:
                Z.importance = sum(getattr(p, 'importance', 1.0) for p in parents) / len(parents) + total_drop * 3

        self.tester.discover_all_mmp_relations(Z, parents) 
        self._run_logic_step()

        for node in self.env.nodes:
            node.importance = max(1.0, min(getattr(node, 'importance', 1.0) * 0.95, 50.0))


# ==========================================
# 2. メインエンジン
# ==========================================
class HybridEngine:
    def __init__(self, env, all_vars, target_fact, theorems):
        self.env = env  
        self.all_vars = all_vars
        self.target_fact = target_fact
        self.prover = LogicProver(self.env, theorems)
        self.agent = MCTSSearchEngine(self.env, self.all_vars, self.prover)
        
    def check_target_reached(self):
        target_f = next((f for f in self.prover.facts if f == self.target_fact), None)
        if target_f and target_f.is_proven: return target_f

        if self.target_fact.fact_type == "Collinear":
            pts = self.target_fact.objects
            comps = [p.get_best_component() for p in pts]
            if len(comps) == len(pts) and all(comps):
                common_lines = {obj for obj in comps[0].subobjects if getattr(obj, 'entity_type', '') == "Line"}
                for c in comps[1:]:
                    lines_here = {obj for obj in c.subobjects if getattr(obj, 'entity_type', '') == "Line"}
                    common_lines = common_lines.intersection(lines_here)
                if common_lines:
                    self.target_fact.is_proven = True
                    self.target_fact.proof_source = f"E-Graph 構造解析 (同一性からの帰結: {list(common_lines)[0].name})"
                    return self.target_fact
                
        elif self.target_fact.fact_type == "Concyclic":
            pts = self.target_fact.objects
            comps = [p.get_best_component() for p in pts]
            if len(comps) == len(pts) and all(comps):
                common_circles = {obj for obj in comps[0].subobjects if getattr(obj, 'entity_type', '') == "Circle"}
                for c in comps[1:]:
                    circles_here = {obj for obj in c.subobjects if getattr(obj, 'entity_type', '') == "Circle"}
                    common_circles = common_circles.intersection(circles_here)
                if common_circles:
                    self.target_fact.is_proven = True
                    self.target_fact.proof_source = f"E-Graph 構造解析 (共円の同定: {list(common_circles)[0].name})"
                    return self.target_fact
        return None

    def run(self, max_steps=100):
        print(f"\n🔄 探索開始 (問題: {self.target_fact})")
        for fact in self.prover.facts:
            if fact.is_proven:
                for obj in fact.objects:
                    if hasattr(obj, 'id'):
                        obj.importance = max(getattr(obj, 'importance', 1.0), 8.0)
        
        for step in range(1, max_steps + 1):
            logger.debug(f"第{step}ステップ")
            if step % 10 == 0: print(f"  ... Step {step}/{max_steps}")
            self.agent.run_step()
            proven_target = self.check_target_reached()
            if proven_target:
                print(f"🎉 🎉 🎉 証明完了！ (Step: {step})")
                print(f"最終結論: {proven_target}")
                self.prover.print_proof_trace(proven_target)
                return True
        return False

if __name__ == "__main__":
    problem_name = "prob_miquel" # テストしやすさを考慮して適当な名前に変更可
    if len(sys.argv) > 1: problem_name = sys.argv[1]

    print(f"=== ハイブリッド自動定理証明システム 起動 ===")
    print(f"▶ 読み込み中の問題: {problem_name}")
    env = ProofEnvironment()

    try:
        prob_module = importlib.import_module(f"problems.{problem_name}")
        all_vars, target_fact, initial_facts = prob_module.setup_problem(env)
    except Exception as e:
        print(f"❌ エラー: 問題ファイル 'problems/{problem_name}.py' の読み込みに失敗しました。詳細: {e}")
        sys.exit(1)

    engine = HybridEngine(env, all_vars, target_fact, THEOREMS)
    for fact in initial_facts:
        engine.prover.add_fact(fact)
        for obj in fact.objects: obj.importance = max(getattr(obj, 'importance', 1.0), 8.0)

    print("▶ 初期状態のMMP大発見を実行中...")
    for n in list(env.nodes):
        if getattr(n, 'entity_type', '') in ["Point", "Line"]:
            engine.agent.tester.discover_all_mmp_relations(n, [])

    engine.run(max_steps=10)
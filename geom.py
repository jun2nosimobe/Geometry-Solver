import math
import numpy as np
import logging
import importlib
import sys

from mmp_core import create_geo_entity, link_logical_incidence
from logic_core import ProofEnvironment, LogicProver, UniversalRuleEngine, get_rep, get_subentity
from theorems import THEOREMS
from mmp_tester import MMPTester
from action_space import ActionGenerator

logger = logging.getLogger("GeometryProver")
logger.setLevel(logging.DEBUG)
if not logger.handlers:
    file_handler = logging.FileHandler('proof.log', mode='w', encoding='utf-8')
    file_handler.setFormatter(logging.Formatter('%(message)s'))
    logger.addHandler(file_handler)

def is_zero_mod(v):
    if hasattr(v, 'value'): return v.value == 0
    if hasattr(v, 'val'): return v.val == 0
    if hasattr(v, 'n'): return v.n == 0
    try: return int(v) == 0
    except: return v == 0

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
        sim_nodes = [get_rep(n) for n in initial_nodes]
        score = 0.0
        
        for step_idx in range(depth):
            actions = self.action_gen.get_possible_actions(sim_nodes, is_simulation=True)
            if not actions: break
            
            valid_actions = []
            for parents, def_type, name in actions:
                rep_parents = [get_rep(p) for p in parents]
                
                # Trivial Check 1: 論理的重複の排除
                is_redundant = False
                for node in sim_nodes:
                    comp = node.get_best_component()
                    if comp and any(d.def_type == def_type and [get_rep(p) for p in d.parents] == rep_parents for d in comp.definitions):
                        is_redundant = True
                        break
                
                if not is_redundant:
                    valid_actions.append((rep_parents, def_type, name))

            if not valid_actions:
                score -= 2.0
                break

            action_weights = [sum(getattr(p, 'importance', 0.0) for p in a[0]) for a in valid_actions]
            total_w = sum(action_weights)
            probs = [1.0 / len(valid_actions)] * len(valid_actions) if total_w <= 0 else [w / total_w for w in action_weights]
                
            chosen_action = valid_actions[np.random.choice(len(valid_actions), p=probs)]
            rep_parents, def_type, name = chosen_action
            
            # 一時生成してテスト
            Z_temp = create_geo_entity(def_type, rep_parents, name, env=None)
            cZ = Z_temp.get_best_component()
            
            if not cZ or cZ.depth > 6: 
                score -= 1.0
                continue 

            is_physically_redundant = False
            matched_node = None
            for node in sim_nodes:
                if self.tester.check_identical_mmp(Z_temp, node):
                    is_physically_redundant = True
                    matched_node = node
                    break
            
            if is_physically_redundant:
                score -= 5.0 # 「垂直の垂直」等の無駄な手にはペナルティ
                sim_nodes.append(matched_node)
                continue

            # 物理的にも新しい図形なら、E-Graphに「ゴースト」として正式登録
            env_nodes_before = len(self.env.nodes)
            Z = create_geo_entity(def_type, rep_parents, name, env=self.env, is_ghost=True)

            avg_parent_imp = sum(getattr(p, 'base_importance', 0.0) for p in rep_parents) / len(rep_parents) # ここもbase_importanceに修正

            score += avg_parent_imp * (0.5 ** step_idx)

            if Z.entity_type in ["Point", "Line", "Circle"]:
                for var in self.all_vars:
                    nd = cZ.naive_degree
                    if nd > 30: continue
                    score += max(0.1, 2.0 / (nd + 1))
                    if 1 < nd <= 15:
                        td = self.tester.evaluate_numerical_degree(Z, nd, var, max_samples=40)
                        if td <= 15: score += max(0, nd - td) * 10.0 
                            
            if Z.entity_type == "Point":
                hot_curves = [n for n in sim_nodes if n.entity_type in ["Line", "Circle"] and getattr(n, 'importance', 0.0) >= 3.0 and n not in rep_parents]
                for c in hot_curves:
                    cache = {}
                    random_t_dict = {v: np.random.choice(self.tester.t_samples) for v in self.all_vars}
                    try:
                        Z_val = Z.calculate(random_t_dict, cache)
                        c_val = c.calculate(random_t_dict, cache)
                        
                        if c.entity_type == "Line":
                            val = c_val[0]*Z_val[0] + c_val[1]*Z_val[1] + c_val[2]*Z_val[2]
                        elif c.entity_type == "Circle":
                            val = c_val[0]*(Z_val[0]**2 + Z_val[1]**2) + c_val[1]*Z_val[0]*Z_val[2] + c_val[2]*Z_val[1]*Z_val[2] + c_val[3]*Z_val[2]**2
                        else: val = 1 
                            
                        if is_zero_mod(val):
                            if c not in cZ.subobjects:
                                score += getattr(c, 'importance', 0.0) * 2.0
                            break 
                    except: pass
                    
            sim_nodes.append(Z)
            
        return score

    def _run_logic_step(self):
        """🌟 修正: 何も推論できなくなるまで連鎖的にエンジンを回し続ける固定点ループ"""
        engine = UniversalRuleEngine(self.env, self.prover)
        
        changed = True
        loop_count = 0
        max_loops = 10 # 無限ループストッパー
        
        while changed and loop_count < max_loops:
            loop_count += 1
            logger.debug(f"\n--- 🔄 Logic Loop {loop_count} ---")
            
            # engine.run_all が True を返せば、まだ推論の余地があるということ
            changed = engine.run_all(self.prover.theorems)

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
            
            merged = False
            for node in self.env.nodes:
                if node != Z and self.tester.check_identical_mmp(Z, node):
                    
                    # ==========================================
                    # 🌟 NEW: ゴーストの「昇格 (Promotion)」システム
                    # ==========================================
                    if getattr(node, 'base_importance', 1.0) <= 0.0:
                        # 眠っていたゴーストに命(importance)を吹き込み、名前からGhostを消す
                        node.base_importance = Z.base_importance
                        node.heat_bonus = 0.0
                        if "_(Ghost)" in node.name:
                            node.name = node.name.replace("_(Ghost)", "")
                        logger.debug(f"    👻 -> 🟢 ゴースト {node.name} が本番採用され、実体化(昇格)しました！")
                        
                    merged_node = self.env.merge_entities_logically(node, Z)
                    if merged_node:
                        merged_node.add_heat(total_drop * 2.0 + 5.0)
                        Z = merged_node
                    merged = True
                    break
                    
            if not merged:
                avg_heat = sum(getattr(p, 'heat_bonus', 0.0) for p in parents) / max(1, len(parents))
                Z.heat_bonus = avg_heat + total_drop * 2.0

        self.tester.discover_all_mmp_relations(Z, parents) 
        self._run_logic_step()

        # ターン終了時の冷却サイクル (Decay)
        for node in self.env.nodes:
            if hasattr(node, 'heat_bonus'):
                node.heat_bonus *= 0.85 


class HybridEngine:
    def __init__(self, env, all_vars, target_fact, theorems):
        self.env = env  
        self.all_vars = all_vars
        self.target_fact = target_fact
        self.prover = LogicProver(self.env, theorems)
        self.agent = MCTSSearchEngine(self.env, self.all_vars, self.prover)
        
    def check_target_reached(self):
        """🌟 汎用クエリ(get_subentity)を使った美しいゴール判定"""
        tf = self.target_fact
        if tf.fact_type == "Collinear":
            pts = tf.objects
            common_lines = get_subentity(pts[0], "Line")
            for p in pts[1:]:
                common_lines &= get_subentity(p, "Line")
            if common_lines:
                tf.is_proven = True
                tf.proof_source = f"E-Graph 構造解析 (同一性からの帰結: {list(common_lines)[0].name})"
                return tf
                
        elif tf.fact_type == "Concyclic":
            pts = tf.objects
            common_circles = get_subentity(pts[0], "Circle")
            for p in pts[1:]:
                common_circles &= get_subentity(p, "Circle")
            if common_circles:
                tf.is_proven = True
                tf.proof_source = f"E-Graph 構造解析 (共円の同定: {list(common_circles)[0].name})"
                return tf

        elif tf.fact_type == "Identical":
            if get_rep(tf.objects[0]) == get_rep(tf.objects[1]):
                tf.is_proven = True
                tf.proof_source = f"E-Graph マージ確認 (対象: {tf.objects[0].name} ≡ {tf.objects[1].name})"
                return tf
                
        return None

    def run(self, max_steps=100):
        print(f"\n🔄 探索開始 (問題: {self.target_fact})")
        # ==========================================
        # 🌟 最強のターゲット注入 (Goal Injection v3)
        # ==========================================
        if self.target_fact.fact_type == "Collinear":
            pts = self.target_fact.objects
            from mmp_core import create_geo_entity, link_logical_incidence # 🌟 link_logical_incidence を追加！
            import itertools
            
            target_lines = []
            for p1, p2 in itertools.combinations(pts, 2):
                line_name = f"LineThroughPoints_{p1.name}_{p2.name}_(Target)"
                target_line = create_geo_entity("LineThroughPoints", [p1, p2], name=line_name, env=self.env)
                target_line.base_importance = 50.0 
                p1.base_importance = 50.0
                p2.base_importance = 50.0
                target_lines.append(target_line)
                
            existing_lines = [n for n in self.env.nodes if getattr(n, 'entity_type', '') == "Line" and getattr(n, 'base_importance', 0.0) > 0.0]
            
            for t_line in target_lines:
                for e_line in existing_lines:
                    if t_line == e_line: continue
                    
                    ang_name1 = f"AnglePair_{t_line.name}_{e_line.name}_(Target)"
                    a1 = create_geo_entity("AnglePair", [t_line, e_line], name=ang_name1, env=self.env)
                    a1.base_importance = 10.0
                    self.env.nodes.append(a1)
                    link_logical_incidence(t_line, a1) # 🌟 必須: 親直線とリンク！
                    link_logical_incidence(e_line, a1) # 🌟 必須: 親直線とリンク！

                    ang_name2 = f"AnglePair_{e_line.name}_{t_line.name}_(Target)"
                    a2 = create_geo_entity("AnglePair", [e_line, t_line], name=ang_name2, env=self.env)
                    a2.base_importance = 10.0
                    self.env.nodes.append(a2)
                    link_logical_incidence(e_line, a2) # 🌟 必須: 親直線とリンク！
                    link_logical_incidence(t_line, a2) # 🌟 必須: 親直線とリンク！
        # ==========================================
                
        elif self.target_fact.fact_type == "Concyclic":
            # 共円が目標なら、目標の点同士を結ぶ直線をすべて引いておく(円周角を作りやすくするため)
            pts = self.target_fact.objects
            from mmp_core import create_geo_entity
            import itertools
            for p1, p2 in itertools.combinations(pts, 2):
                line_name = f"LineThroughPoints_{p1.name}_{p2.name}_(Target)"
                target_line = create_geo_entity("LineThroughPoints", [p1, p2], name=line_name, env=self.env)
                target_line.base_importance = 50.0
                p1.base_importance = 50.0
                p2.base_importance = 50.0
        # ==========================================

        # 初期状態における Given 点への強烈な熱注入 (既存のコード)
        for node in self.env.nodes:
            if hasattr(node, 'add_heat'):
                node.add_heat(10.0)

        # 🌟 NEW: MCTSを回す前に、注入した図形だけで一回論理エンジンを回す！
        print("🔄 初期推論 (Target Injection) を実行中...")
        from logic_core import UniversalRuleEngine
        engine = UniversalRuleEngine(self.env, self.prover)
        while True:
            changed = engine.run_all(self.prover.theorems)
            if not changed: break

        for step in range(1, max_steps + 1):

            logger.debug(f"\n第{step}ステップ")
            if step % 10 == 0: print(f"  ... Step {step}/{max_steps}")
            
            self.agent.run_step()
            proven_target = self.check_target_reached()
            
            if proven_target:
                print(f"🎉 🎉 🎉 証明完了！ (Step: {step})")
                print(f"最終結論: {proven_target}")
                self.prover.print_proof_trace()
                return True
        return False

if __name__ == "__main__":
    problem_name = "prob_nine_point"
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

    print("▶ 初期状態のMMP大発見を実行中...")
    for n in list(env.nodes):
        if getattr(n, 'entity_type', '') in ["Point", "Line"]:
            engine.agent.tester.discover_all_mmp_relations(n, [])

    engine.run(max_steps=5)

    print("E_Graphの描画")

    from visualize import draw_egraph
    draw_egraph(env, filename=f"egraph_{problem_name}")
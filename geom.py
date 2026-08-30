import math
import numpy as np
import logging
import importlib
import sys
import re
import itertools

from mmp_core import create_geo_entity
from logic_core import ProofEnvironment, setup_proof_logger
from proof_manager import Fact, LogicProver, print_proof_tree
from theorems import THEOREMS
from mmp_tester import MMPTester, is_zero_mod
from action_space import ActionGenerator



logger = logging.getLogger("GeometryProver")
logger.setLevel(logging.DEBUG)
if not logger.handlers:
    file_handler = logging.FileHandler('proof.log', mode='w', encoding='utf-8')
    file_handler.setFormatter(logging.Formatter('%(message)s'))
    logger.addHandler(file_handler)

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
        sim_nodes = [n.get_rep() for n in initial_nodes]
        score = 0.0
        
        for step_idx in range(depth):
            actions = self.action_gen.get_possible_actions(sim_nodes, is_simulation=True)
            if not actions: break
            
            valid_actions = []
            for parents, def_type, name in actions:
                rep_parents = [p.get_rep() for p in parents]
                
                # Trivial Check 1: 論理的重複の排除
                is_redundant = False
                for node in sim_nodes:
                    comp = node.get_best_component()
                    if comp and any(d.def_type == def_type and [p.get_rep() for p in d.parents] == rep_parents for d in comp.definitions):
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
            
            # ==========================================
            # 🌟 NEW: 退化テストで弾かれて None になった場合のガードを追加
            # ==========================================
            if Z is None:
                score -= 10.0  # 退化するような無駄な作図には重いペナルティ！
                continue
                
            Z.created_by_theorem = "MCTS_Exploration"

            avg_parent_imp = sum(getattr(p, 'base_importance', 0.0) for p in rep_parents) / len(rep_parents)

            score += avg_parent_imp * (0.5 ** step_idx)

            if Z.entity_type in ["Point", "Line", "Circle"]:
                cZ = Z.get_best_component() # 🌟 Z_temp のものではなく、本物から取り直す
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


    def run_step(self, num_simulations=10): # 🌟 シミュレーション回数を減らして応答性を上げる
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
        
        # ==========================================
        # 🌟 FIX: 本番適用時の退化ガード (Noneチェック)
        # ==========================================
        if Z is None:
            logger.warning(f"⚠️ [MCTS] 採用候補だった手 ({name}) が本番環境で退化判定されたため、適用をキャンセルします。")
            return # ループの中なら continue、関数の末尾なら return
            
        cZ = Z.get_best_component()
        
        if def_type == "Triangle":
            cZ.triangle_points = tuple(parents)
            shape_name = f"Shape_{name}"
            new_shape = create_geo_entity("ShapeOf", [Z], name=shape_name, env=self.env)
            
            # Triangleに付随するShapeOfも退化する可能性が微レ存なので一応ガード
            if new_shape is not None:
                new_shape.shape_members[Z] = tuple(parents)
                # self.env.nodes.extend([Z, new_shape]) # 🌟 create_geo_entity内で既に追加されるならここは削除でOK
                
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
                    # 🌟 修正: MCTSによる数値計算だけの「強制マージ(チート)」を禁止！
                    # 代わりに「同一である」という予想を立てて論理エンジンに証明を任せる
                    if getattr(node, 'base_importance', 1.0) <= 0.0:
                        node.base_importance = getattr(Z, 'base_importance', 1.0)
                        node.heat_bonus = 0.0
                        if "_(Ghost)" in node.name:
                            node.name = node.name.replace("_(Ghost)", "")
                    
                    # 予想ファクトを発行
                    self.tester._add_and_log_conjecture("Identical", [node, Z], f"    🟡 MMP予想(同一): {node.name} ≡ {Z.name}", base_bonus=15.0)
                    
                    # 生成したZはE-Graphから取り除き、既存ノードにフォーカスを移す
                    if Z in self.env.nodes:
                        self.env.nodes.remove(Z)
                    Z = node 
                    merged = True
                    break
                    
            if not merged:
                avg_heat = sum(getattr(p, 'heat_bonus', 0.0) for p in parents) / max(1, len(parents))
                Z.heat_bonus = avg_heat + getattr(Z, 'numerical_degree', 0) * 2.0

        self.tester.discover_all_mmp_relations(Z, parents) 

# ==========================================
# 🌟 geom.py 内の HybridEngine の修正
# ==========================================
class HybridEngine:
    def __init__(self, env, all_vars, target_fact, theorems):
        self.env = env
        self.all_vars = all_vars
        self.target_fact = target_fact
        self.env.all_vars = all_vars
        
        from proof_manager import LogicProver
        from logic_core import ParallelBlackboardEngine, EventType 
        
        self.prover = LogicProver(self.env, theorems)
        self.rule_engine = ParallelBlackboardEngine(self.env, self.prover)
        self.env.emit = self.rule_engine.emit
        self.EventType = EventType
        
        # 🌟 FIX: ここで確実にビジュアライザを起動し、envにも紐付ける
        try:
            from visualizer import RealtimeVisualizer
            self.visualizer = RealtimeVisualizer(self.env)
            self.env.visualizer = self.visualizer
        except Exception as e:
            print(f"🚨 [Visualizer] 起動失敗 (モジュールが見つからない等): {e}")
        
        # MCTSエンジンで推論エンジンが使われるため、visualizer起動より後に置く
        self.agent = MCTSSearchEngine(self.env, self.all_vars, self.prover)
        
    def check_target_reached(self):
        if not self.target_fact: return None
        
        t_type = self.target_fact.fact_type
        t_objs = [obj.get_rep() if hasattr(obj, 'get_rep') else obj for obj in self.target_fact.objects]
        
        if t_type == "Identical" and len(t_objs) == 2:
            if t_objs[0] == t_objs[1]:
                self.target_fact.is_proven = True
                self.target_fact.proof_source = "E-Graph 同値類マージ (Identical)"
                return self.target_fact

        if t_type in ["Collinear", "Concyclic"]:
            target_entity = "Line" if t_type == "Collinear" else "Circle"
            for n in self.env.nodes:
                if not n.is_valid() or getattr(n.get_rep(), 'entity_type', '') != target_entity: continue
                rep = n.get_rep()
                pts = set()
                for comp in getattr(rep, 'components', []):
                    for sub in comp.subobjects:
                        if getattr(sub.get_rep(), 'entity_type', '') == "Point": pts.add(sub.get_rep())
                    for d in comp.definitions:
                        for p in d.parents:
                            if getattr(p.get_rep(), 'entity_type', '') == "Point": pts.add(p.get_rep())
                            
                if all(t in pts for t in t_objs):
                    self.target_fact.is_proven = True
                    self.target_fact.proof_source = f"E-Graph 構造的真実 ({target_entity}への包含)"
                    return self.target_fact
                    
        t_obj_set = set(t_objs)
        for fact in self.prover.facts:
            if getattr(fact, 'is_proven', False) and fact.fact_type == t_type:
                f_objs = [obj.get_rep() if hasattr(obj, 'get_rep') else obj for obj in fact.objects]
                if t_type in ["Concyclic", "Collinear", "Identical"]:
                    if set(f_objs) == t_obj_set: return fact
                else:
                    if f_objs == t_objs: return fact
        return None

    def resolve_demands(self):
        """フェーズ2: 論理エンジンの要求に基づくオンデマンド作図"""
        if not hasattr(self.rule_engine, 'construction_demands') or not self.rule_engine.construction_demands:
            return False
            
        from mmp_core import create_geo_entity
        # 🌟 FIX: 要求を需要が高い(スコア順)にソートし、上位5件のみ作図する(組み合わせ爆発防止)
        demands = sorted(self.rule_engine.construction_demands.items(), key=lambda x: x[1], reverse=True)[:5]
        self.rule_engine.construction_demands.clear()
        
        applied = False
        for demand_sig, score in demands:
            pts = list(demand_sig)
            new_obj = None
            if len(pts) == 2:
                p1, p2 = pts
                print(f"  💡 [オンデマンド作図] 要請により {p1.name} と {p2.name} を結ぶ直線を生成 (需要: {score:.1f})")
                new_obj = create_geo_entity("LineThroughPoints", [p1, p2], name=f"Line_{p1.name}_{p2.name}_(Demand)", env=self.env, importance=10.0)
            #elif len(pts) == 3:
            #    p1, p2, p3 = pts
            #    print(f"  💡 [オンデマンド作図] 要請により {p1.name}, {p2.name}, {p3.name} を通る円を生成 (需要: {score:.1f})")
            #    new_obj = create_geo_entity("Circumcircle", [p1, p2, p3], name=f"Circ_{p1.name}_{p2.name}_{p3.name}_(Demand)", env=self.env, importance=10.0)
            
            if new_obj:
                self.env.tester.discover_all_mmp_relations(new_obj, pts)
                applied = True
                
        if applied:
            self.rule_engine.schedule_full_sweep()
        return applied

    def resolve_angle_demands(self):
        """フェーズ1.5: 欠落Directionの補完と、意味のある有向角(交点を持つ直線のペア)のみを生成"""
        from mmp_core import create_geo_entity
        import itertools
        
        applied = False
        
        # 🌟 1. Directionの欠落を補完 (直線があるのに方向がないものを救済)
        for n in self.env.nodes:
            if n.is_valid() and getattr(n.get_rep(), 'entity_type', '') == 'Line':
                line_rep = n.get_rep()
                has_dir = False
                comp = line_rep.get_best_component()
                if comp:
                    for sub in comp.subobjects:
                        if getattr(sub.get_rep(), 'entity_type', '') == 'Direction':
                            has_dir = True; break
                if not has_dir:
                    dir_name = f"Dir_{getattr(line_rep, 'name', 'Unknown')}_(Fallback)"
                    new_dir = create_geo_entity("DirectionOf", [line_rep], name=dir_name, env=self.env, importance=2.0)
                    if new_dir: applied = True

        # 🌟 2. 筋の良い角度生成: 「共通の交点を持つ2直線」の方向ペアだけを抽出
        valid_angle_pairs = set()
        for pt in self.env.nodes:
            if not pt.is_valid() or getattr(pt.get_rep(), 'entity_type', '') != 'Point': continue
            
            # この点(交点)を通る直線をすべて集める
            lines_on_pt = []
            for n in self.env.nodes:
                if not n.is_valid() or getattr(n.get_rep(), 'entity_type', '') != 'Line': continue
                l_rep = n.get_rep()
                comp = l_rep.get_best_component()
                if comp:
                    # Line の構成要素や定義の中にこの点が含まれているか
                    pts_on_line = [s.get_rep() for s in comp.subobjects if getattr(s.get_rep(), 'entity_type', '') == 'Point']
                    pts_on_line += [p.get_rep() for d in comp.definitions for p in d.parents if hasattr(p, 'get_rep') and getattr(p.get_rep(), 'entity_type', '') == 'Point']
                    if pt.get_rep() in pts_on_line:
                        lines_on_pt.append(l_rep)
            
            # その点を通る2直線の方向ペアを有効リストに追加
            if len(lines_on_pt) >= 2:
                for l1, l2 in itertools.combinations(lines_on_pt, 2):
                    d1, d2 = None, None
                    for sub in l1.get_best_component().subobjects:
                        if getattr(sub.get_rep(), 'entity_type', '') == 'Direction': d1 = sub.get_rep()
                    for sub in l2.get_best_component().subobjects:
                        if getattr(sub.get_rep(), 'entity_type', '') == 'Direction': d2 = sub.get_rep()
                    if d1 and d2:
                        valid_angle_pairs.add(frozenset([d1, d2]))

        # 3. 既に存在するAnglePairをハッシュ化して高速チェック
        existing_pairs = set()
        for n in self.env.nodes:
            if n.is_valid() and getattr(n.get_rep(), 'entity_type', '') == 'Angle':
                comp = n.get_rep().get_best_component()
                if comp:
                    for d in comp.definitions:
                        if d.def_type == "AnglePair" and len(d.parents) == 2:
                            p1 = d.parents[0].get_rep() if hasattr(d.parents[0], 'get_rep') else d.parents[0]
                            p2 = d.parents[1].get_rep() if hasattr(d.parents[1], 'get_rep') else d.parents[1]
                            existing_pairs.add(frozenset([p1, p2]))

        # 4. 未生成の意味のあるペアだけを実際に作図
        sorted_pairs = sorted(list(valid_angle_pairs), key=lambda x: str([getattr(d, 'name', '') for d in x]))
        for pair in sorted_pairs:
            if pair not in existing_pairs:
                d1, d2 = tuple(pair)
                name = f"AnglePair_{getattr(d1, 'name', 'D1')}_{getattr(d2, 'name', 'D2')}_(Auto)"
                new_ang = create_geo_entity("AnglePair", [d1, d2], name=name, env=self.env, importance=2.0)
                if new_ang:
                    existing_pairs.add(pair)
                    self.env.tester.discover_all_mmp_relations(new_ang, [d1, d2])
                    applied = True
                    
        if applied:
            print(f"  💡 [スマート補完] 欠落Directionと、交点を持つ意味のある有向角のみを自動生成しました。")
            self.rule_engine.schedule_full_sweep()
            
        return applied
    
    def resolve_fallbacks(self):
        """フェーズ3: 共円グループの未結線補完"""
        found_fallback = False
        import itertools
        from mmp_core import create_geo_entity
        
        circle_groups = []
        for fact in self.prover.facts:
            if fact.fact_type == "Concyclic" and getattr(fact, 'is_proven', False):
                pts = [p.get_rep() for p in fact.objects if hasattr(p, 'get_rep') and getattr(p.get_rep(), 'entity_type', '') == 'Point']
                if len(pts) >= 3: circle_groups.append(pts)
                
        for n in self.env.nodes:
            if n.is_valid() and getattr(n.get_rep(), 'entity_type', '') == 'Circle':
                c_rep = n.get_rep()
                pts_on_curve = set()
                comp = c_rep.get_best_component()
                if comp:
                    for sub in comp.subobjects:
                        if getattr(sub.get_rep(), 'entity_type', '') == 'Point': pts_on_curve.add(sub.get_rep())
                    for d in comp.definitions:
                        for p in d.parents:
                            if getattr(p.get_rep(), 'entity_type', '') == 'Point': pts_on_curve.add(p.get_rep())
                if len(pts_on_curve) >= 3: 
                    circle_groups.append(list(pts_on_curve))
                
        for group in circle_groups:
            if found_fallback: break
            for p1, p2 in itertools.combinations(set(group), 2):
                c1, c2 = p1.get_best_component(), p2.get_best_component()
                common_lines = [obj for obj in (c1.subobjects & c2.subobjects) if getattr(obj, 'entity_type', '') == "Line"] if c1 and c2 else []
                if not common_lines:
                    print(f"  💡 [フォールバック作図] 共円グループ内の未結線 {getattr(p1, 'name', str(p1))} と {getattr(p2, 'name', str(p2))} を結ぶ直線を生成します")
                    new_line = create_geo_entity("LineThroughPoints", [p1, p2], name=f"Line_{getattr(p1, 'name', str(p1))}_{getattr(p2, 'name', str(p2))}_(Fallback)", env=self.env, importance=10.0)
                    if new_line:
                        self.env.tester.discover_all_mmp_relations(new_line, [p1, p2])
                        self.rule_engine.schedule_full_sweep()
                    found_fallback = True
                    break
                    
        return found_fallback
    

    def run(self, max_time_seconds=60.0):
        import time

        print(f"\n🔄 探索開始 (問題: {self.target_fact}, 制限時間: {max_time_seconds}秒)")
        start_time = time.time()

        # 🌟 AttentionManager を使用したクリーンな熱注入
        if self.target_fact:
            for obj in self.target_fact.objects:
                self.env.attention.inject_heat(obj, 20.0)

        print("▶ 初期状態のMMP大発見を実行中 (全有効図形を爆速テスト)...")
        nodes_to_test = [n for n in list(self.env.nodes) if getattr(n, 'base_importance', 0.0) > 0.0 and getattr(n, 'entity_type', '') in ["Point", "Line", "Circle", "Angle", "Direction"]]
        for n in nodes_to_test:
            self.env.tester.discover_all_mmp_relations(n, [])

        print("🔄 並行ブラックボード推論を開始...")
        for fact in self.prover.facts:
            evt_type = self.EventType.NEW_CONJECTURE if getattr(fact, 'is_mmp_conjecture', False) else self.EventType.FACT_PROVEN
            self.env.emit(evt_type, fact)

        self.rule_engine.schedule_full_sweep()

        while time.time() - start_time < max_time_seconds:
            logic_start = time.time()
            
            # 🌟 ターンの開始時にもビジュアライザを更新
            if hasattr(self, 'visualizer'):
                self.visualizer.broadcast_state()

            # フェーズ1: 演繹推論
            while (self.rule_engine.matcher_queue or self.rule_engine.prover_queue) and (time.time() - logic_start < 5.0):
                self.rule_engine.run_parallel_loop(matcher_budget=10000)
            
            proven_target = self.check_target_reached()
            if proven_target:
                print(f"\n🎉 🎉 🎉 証明完了！ (Time: {time.time() - start_time:.1f}s)")
                print(f"最終結論: {proven_target.proof_source}")
                self.prover.print_proof_trace()
                self.rule_engine.print_profiling_report()
                return True

            if not self.rule_engine.matcher_queue and not self.rule_engine.prover_queue:
                print(f"\n⏳ [Time: {time.time()-start_time:.1f}s] ロジックがStallしました。リカバリーフェーズに移行します...")
                self.rule_engine.print_bottlenecks()
                
                # 🌟 FIX: オンデマンド作図(直線/円)とスマート角度生成を「両方とも」実行する
                recovered = False
                
                # フェーズ2: まず論理エンジンが切望している補助線や円を引く
                if self.resolve_demands():
                    recovered = True
                
                # フェーズ1.5: その新しく引かれた線も含めて、意味のある角度を網羅する
                if self.resolve_angle_demands():
                    recovered = True
                
                # どちらか一方でも作図・生成が行われていれば推論ループに戻る
                if recovered:
                    continue
                
                # フェーズ3: フォールバック作図
                if self.resolve_fallbacks(): continue
                
                # フェーズ4: MCTSヒューリスティック探索
                print("  -> 要求がなく、共円の未結線もないため、MCTSで補助線を探索中...")
                self.agent.run_step(num_simulations=10)
                
            # 🌟 ターン終了時に AttentionManager で一括冷却
            self.env.attention.cool_down_all()
                
        print("\n⏳ タイムアウト: 指定された時間内に証明できませんでした。")
        self.rule_engine.print_profiling_report()
        return False


if __name__ == "__main__":
    problem_name = "prob_simson"
    DEBUG_MODE = False
    
    if len(sys.argv) > 1: 
        problem_name = sys.argv[1]

    log_file = setup_proof_logger(problem_name, is_debug=DEBUG_MODE)

    print(f"=== ハイブリッド自動定理証明システム 起動 ===")
    print(f"▶ 読み込み中の問題: {problem_name}")
    print(f"▶ ログ出力先: {log_file}")
    print(f"▶ 数値デバッグモード: {'ON (厳格チェック有効)' if DEBUG_MODE else 'OFF (爆速モード)'}")
    
    # 1. 環境(土台)の作成
    env = ProofEnvironment(enable_numerical_debug=DEBUG_MODE)

    try:
        prob_module = importlib.import_module(f"problems.{problem_name}")
        # all_vars を取得 (※Testerの初期化に必須なため、最初に読み込む)
        all_vars, target_fact, initial_facts = prob_module.setup_problem(env)
        env.all_vars = all_vars 
    except Exception as e:
        print(f"❌ エラー: 問題ファイル 'problems/{problem_name}.py' の読み込みに失敗しました。詳細: {e}")
        sys.exit(1)

    # ==========================================
    # 🌟 依存関係の構築と仮定の登録
    # ==========================================
    prover = LogicProver(env, THEOREMS)

    # 🌟 FIX: 問題で与えられた「仮定」を、確実に証明済みの事実として登録する！
    if initial_facts:
        for fact in initial_facts:
            fact.is_proven = True
            fact.proof_source = "Given (仮定)"
            if fact not in prover.facts:
                prover.facts.append(fact)

    tester = MMPTester(env, all_vars, prover)
    env.tester = tester  # 🎯 土台(env)に電卓(tester)をセット

    # ==========================================
    # 2. エンジンの初期化
    # ==========================================
    engine = HybridEngine(env, all_vars, target_fact, THEOREMS)
    
    # ProverとTesterをエンジン全体に正しく行き渡らせる
    engine.prover = prover
    engine.tester = tester
    if hasattr(engine, 'rule_engine'):
        engine.rule_engine.prover = prover
    if hasattr(engine, 'agent'):
        engine.agent.tester = tester

    # ==========================================
    # 3. 実行フェーズ
    # ==========================================
    print("\n=== ハイブリッド探索 (Seeding + 局所探索 + MCTS) を開始 ===")
    
    # タイムベースの実行ループを呼び出し（デフォルト60秒制限）
    engine.run(max_time_seconds=30.0)

import math
import numpy as np
import logging
import importlib
import sys
import re

from mmp_core import create_geo_entity, link_logical_incidence
from logic_core import ProofEnvironment, setup_proof_logger, LogicProver, UniversalRuleEngine, get_rep, get_subentity
from theorems import THEOREMS
from mmp_tester import MMPTester
from action_space import ActionGenerator
from heuristic_engine import FocusSearchEngine


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
    def __init__(self, env, all_vars, prover, focus_engine): # 🌟 focus_engine を追加
        self.env = env
        self.all_vars = all_vars
        self.prover = prover
        self.focus_engine = focus_engine # 🌟 受け取る
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
            Z.created_by_theorem = "MCTS_Exploration"

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

    def _run_logic_step(self, target_checker=None):
        """🌟 MCTSターンの局所論理探索"""
        logger.debug(f"\n--- 🔄 MCTSターンの局所論理探索 ---")
        self.focus_engine.run_until_stalled(
            self.prover.theorems, 
            max_steps=15,
            target_checker=target_checker
        )

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
        # 🌟 NEW: 局所探索エンジンに対して「この図形(Z)と親に注目しろ！」と強烈な熱を注入する
        self.focus_engine.scoring.heat_table[Z] += 50.0 
        for p in parents:
            self.focus_engine.scoring.heat_table[p] += 20.0

        self.tester.discover_all_mmp_relations(Z, parents) 
        
        # 🌟 ここで上記の _run_logic_step (局所探索) が呼ばれる
        self._run_logic_step()

        # ターン終了時の冷却サイクル (既存のコード)
        for node in self.env.nodes:
            if hasattr(node, 'heat_bonus'):
                node.heat_bonus *= 0.85


class HybridEngine:
    def __init__(self, env, all_vars, target_fact, theorems):
        self.env = env  
        self.all_vars = all_vars
        self.target_fact = target_fact
        self.prover = LogicProver(self.env, theorems)
        
        # 🌟 NEW: 全探索エンジンと局所探索エンジンをここで初期化
        self.rule_engine = UniversalRuleEngine(self.env, self.prover)
        # focus_size は問題の複雑さに応じて 5〜7 程度がベストです
        self.focus_engine = FocusSearchEngine(self.env, self.prover, self.rule_engine, focus_size=5)
        
        # MCTSSearchEngine に focus_engine を渡す
        self.agent = MCTSSearchEngine(self.env, self.all_vars, self.prover, self.focus_engine)
        
    def check_target_reached(self):
        """🌟 汎用クエリ(get_subentity)を使った美しいゴール判定"""
        from logic_core import get_rep, get_subentity # get_rep を確実にインポート
        tf = self.target_fact
        
        if tf.fact_type == "Collinear":
            pts = [get_rep(p) for p in tf.objects] # 🌟 修正: 必ず get_rep で最新の代表元を取得！
            common_lines = get_subentity(pts[0], "Line")
            for p in pts[1:]:
                common_lines &= get_subentity(p, "Line")
            if common_lines:
                tf.is_proven = True
                tf.proof_source = f"E-Graph 構造解析 (同一性からの帰結: {list(common_lines)[0].name})"
                return tf
                
        elif tf.fact_type == "Concyclic":
            pts = [get_rep(p) for p in tf.objects] # 🌟 修正: 必ず get_rep で最新の代表元を取得！
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

        self.focus_engine.set_target(self.target_fact)
        
        print("🔄 全結合シーディング (Universal Seeding) を実行中...")
        from mmp_core import create_geo_entity, link_logical_incidence, is_canonical_angle_order
        from logic_core import get_subentity
        import itertools

        initial_points = [n for n in self.env.nodes if getattr(n, 'entity_type', '') == "Point" and getattr(n, 'base_importance', 0.0) > 0.0]
        
        for p1, p2 in itertools.combinations(initial_points, 2):
            common_lines = get_subentity(p1, "Line") & get_subentity(p2, "Line")
            if not common_lines:
                line_name = f"LineThroughPoints_{p1.name}_{p2.name}_(Seed)"
                new_line = create_geo_entity("LineThroughPoints", [p1, p2], name=line_name, env=self.env)
                new_line.base_importance = 10.0
                self.env.nodes.append(new_line)
                link_logical_incidence(p1, new_line)
                link_logical_incidence(p2, new_line)

        all_lines = [n for n in self.env.nodes if getattr(n, 'entity_type', '') == "Line" and getattr(n, 'base_importance', 0.0) > 0.0]
        seed_dirs = []
        for line in all_lines:
            dir_name = f"Dir_{line.name}_(Seed)"
            d = create_geo_entity("DirectionOf", [line], name=dir_name, env=self.env)
            d.base_importance = 10.0
            self.env.nodes.append(d)
            link_logical_incidence(line, d)
            seed_dirs.append(d)

        # 🌟 ここを修正: すべての直線ペアに対して、"Canonical Order" に従った角度ペアを「必ず」生成する
        for d1, d2 in itertools.combinations(seed_dirs, 2):
            # Canonical Order を判定し、正しい順序で角度ペアを作る
            if is_canonical_angle_order(d1, d2):
                ordered_pair = [d1, d2]
            else:
                ordered_pair = [d2, d1]
                
            # 🌟 正順の角度をシード
            ang_name = f"AnglePair_{ordered_pair[0].name}_{ordered_pair[1].name}_(Seed)"
            a = create_geo_entity("AnglePair", ordered_pair, name=ang_name, env=self.env)
            a.base_importance = 5.0
            self.env.nodes.append(a)
        # ==========================================

        # 初期状態における Given 点への強烈な熱注入 (既存のコード)
        for node in self.env.nodes:
            if hasattr(node, 'add_heat'):
                node.add_heat(10.0)

       # 初期状態における Given 点への強烈な熱注入 (既存のコード)
        for node in self.env.nodes:
            if hasattr(node, 'add_heat'):
                node.add_heat(10.0)
                # 🌟 NEW: 局所探索エンジン側にも初期熱を登録
                self.focus_engine.scoring.heat_table[node] += 10.0

       # 🌟 初期図形だけで一回局所探索を限界まで回す！
        print("🔄 初期推論 (Target Injection) を局所探索で実行中...")
        # target_checker に self.check_target_reached メソッドをそのまま渡す
        self.focus_engine.run_until_stalled(
            self.prover.theorems, 
            max_steps=50, 
            target_checker=self.check_target_reached
        )

        # この時点で証明が完了しているかチェック
        proven_target = self.check_target_reached()
        if proven_target:
            print(f"🎉 🎉 🎉 証明完了！ (初期推論フェーズにて)")
            print(f"最終結論: {proven_target.proof_source}")
            self.prover.print_proof_trace()
            return True

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


def analyze_node_utility(env, prover):
    """E-Graph内のノードの「真の貢献度」をプロファイリングする"""
    print("\n" + "="*40)
    print(" 📊 E-Graph ノード貢献度プロファイリング")
    print("="*40)
    
    # 1. 証明トレースから「実際に使われたノード」の名前を抽出
    used_node_names = set()
    
    # 例: "AnglePair_Dir_A_Dir_B ≡ AnglePair_Dir_C_Dir_D <= 円周角の定理" から名前を抜く
    # アンダースコア、英数字、カッコを含むノード名を大雑把に抽出する正規表現
    node_pattern = re.compile(r'[a-zA-Z0-9_()]+') 
    
    for log in prover.trace_log:
        words = node_pattern.findall(log)
        for w in words:
            # 短すぎる単語や定理名などを除外
            if len(w) > 2 and w not in ["AnglePair", "Dir", "Concyclic", "Collinear"]:
                used_node_names.add(w)

    # 2. 現在の env.nodes を分類
    from logic_core import get_rep, is_valid_node
    
    total_nodes = 0
    used_nodes = []
    unused_but_hot = []   # 探索されたが証明には繋がらなかった
    completely_useless = [] # 探索すらされなかった完全なゴミ

    for node in env.nodes:
        rep = get_rep(node)
        if rep != node or not is_valid_node(node):
            continue # マージされて消えたノードやゴーストはスキップ
            
        total_nodes += 1
        name = node.name
        
        # 名前の一部でも使われていればOKとする (緩い判定)
        is_used = any(name in un or un in name for un in used_node_names)
        
        if is_used:
            used_nodes.append(node)
        else:
            heat = getattr(node, 'heat_bonus', 0.0)
            if heat > 0.5:
                unused_but_hot.append(node)
            else:
                completely_useless.append(node)

    # 3. 結果の出力
    print(f"📈 最終有効ノード総数 (Canonical): {total_nodes} 個")
    print(f"  🟢 証明に貢献したノード    : {len(used_nodes)} 個 ({(len(used_nodes)/max(1, total_nodes))*100:.1f}%)")
    print(f"  🟡 探索されたが無駄だった  : {len(unused_but_hot)} 個 ({(len(unused_but_hot)/max(1, total_nodes))*100:.1f}%)")
    print(f"  🔴 完全に無駄な(孤立)ノード: {len(completely_useless)} 個 ({(len(completely_useless)/max(1, total_nodes))*100:.1f}%)\n")

    if completely_useless:
        print("【🔴 完全に無駄だったノードのサンプル (Top 100)】")
        # seedやautoが付いているものを優先して表示
        useless_sorted = sorted(completely_useless, key=lambda n: "Seed" in n.name or "Auto" in n.name, reverse=True)
        for n in useless_sorted[:100]:
            comp = n.get_best_component()
            parents = []
            if comp and comp.definitions:
                first_def = next(iter(comp.definitions))
                parents = [p.name for p in first_def.parents]
            print(f"  - {n.name} (型: {n.entity_type}, 親: {parents})")
            
    print("="*40 + "\n")

    print("\n【🗑️ 無駄ノード生成元 (戦犯) ランキング】")
    blame_counts = {}
    for n in completely_useless:
        creator = getattr(n, 'created_by_theorem', 'Unknown / Seed')
        blame_counts[creator] = blame_counts.get(creator, 0) + 1
        
    for creator, count in sorted(blame_counts.items(), key=lambda x: x[1], reverse=True):
        print(f"  - {creator}: {count} 個")
    print("="*40 + "\n")

if __name__ == "__main__":
    problem_name = "prob_simson"
    DEBUG_MODE = False
    
    if len(sys.argv) > 1: 
        problem_name = sys.argv[1]

    log_file = setup_proof_logger(problem_name, is_debug=DEBUG_MODE) # 🌟 is_debugフラグを渡す

    print(f"=== ハイブリッド自動定理証明システム 起動 ===")
    print(f"▶ 読み込み中の問題: {problem_name}")
    print(f"▶ ログ出力先: {log_file}")
    print(f"▶ 数値デバッグモード: {'ON (厳格チェック有効)' if DEBUG_MODE else 'OFF (爆速モード)'}")
    
    env = ProofEnvironment(enable_numerical_debug=DEBUG_MODE)

    try:
        prob_module = importlib.import_module(f"problems.{problem_name}")
        all_vars, target_fact, initial_facts = prob_module.setup_problem(env)
        env.all_vars = all_vars 
        
    except Exception as e:
        print(f"❌ エラー: 問題ファイル 'problems/{problem_name}.py' の読み込みに失敗しました。詳細: {e}")
        sys.exit(1)

    # HybridEngine の初期化
    engine = HybridEngine(env, all_vars, target_fact, THEOREMS)

    print("▶ 初期状態のMMP大発見を実行中...")
    for n in list(env.nodes):
        if getattr(n, 'entity_type', '') in ["Point", "Line"]:
            engine.agent.tester.discover_all_mmp_relations(n, [])

    # ==========================================
    # 🌟 NEW: 初期状態の「論理的帰結」を局所探索で全て出し切る
    # ==========================================
    print("\n=== 初期状態の論理推論 (局所探索) を開始 ===")
    
    # HybridEngineが内部に持っているproverとrule_engineを取得 (変数名が違う場合は適宜修正してください)
    prover = getattr(engine, 'prover', LogicProver(env, THEOREMS))
    base_engine = getattr(engine, 'rule_engine', UniversalRuleEngine(env, prover))
    
    # 局所探索エンジンの初期化 (注目サイズ: 5)
    focus_engine = FocusSearchEngine(env, prover, base_engine, focus_size=6)
    
    # 行き詰まるまで(最大50ターン)、初期図形だけで分かる事実をマージしまくる
    focus_engine.run_until_stalled(THEOREMS, max_steps=50)

    # ==========================================
    # 🚀 全て準備が整った状態で、MCTSスタート
    # ==========================================
    print("\n=== MCTS (モンテカルロ木探索) 探索開始 ===")
    engine.run(max_steps=3)


    #結果の分析
    analyze_node_utility(env, engine.prover)

    # print("E_Graphの描画")
    # from visualize import draw_egraph
    # draw_egraph(env, filename=f"egraph_{problem_name}")
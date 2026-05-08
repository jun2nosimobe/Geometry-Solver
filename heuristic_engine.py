import random
import math
import logging
import numpy as np
from collections import defaultdict
from logic_core import get_rep, is_valid_node, get_subentity

logger = logging.getLogger("GeometryProver")

# ==========================================
# 🌟 スコアリングとフィードバックの独立モジュール (進化版)
# ==========================================
class ScoringPolicy:
    def __init__(self):
        self.cooldown_table = defaultdict(int)
        self.heat_table = defaultdict(float)
        self.MAX_HEAT = 30.0  # 🌟 オーバーヒート防止のキャップ

    def get_selection_score(self, node, target_nodes=None):
        """ノードが「次の注目セット」の主役に選ばれる確率"""
        from logic_core import get_rep
        
        base_score = getattr(node, 'importance', 1.0)
        heat = min(self.heat_table[node], self.MAX_HEAT)
        cooldown = self.cooldown_table[node]
        
        # ------------------------------------------------
        # 1. 目標への引力 (Conjectureボーナス等もここに追加可能)
        # ------------------------------------------------
        target_bonus = 0.0
        if target_nodes and node in target_nodes:
            target_bonus = 20.0

        # ------------------------------------------------
        # 2. 「嬉しい性質」ボーナス (幾何学的な美しさ・対称性)
        # ------------------------------------------------
        prop_bonus = 0.0
        comp = getattr(node, 'get_best_component', lambda: None)()
        if comp:
            # 作図の由来としての嬉しい性質
            for d in comp.definitions:
                if d.def_type in ["Midpoint", "PerpendicularLine", "ParallelLine", "Circumcircle", "AnglePair", "RightAngle"]:
                    prop_bonus += 3.0
                elif d.def_type in ["Collinear", "Concyclic"]:
                    prop_bonus += 5.0
                    
            # 所属図形の多さ（＝拘束の強さ）
            entity_type = getattr(node, 'entity_type', '')
            if entity_type in ["Line", "Circle"]:
                pts_on = sum(1 for sub in comp.subobjects if getattr(get_rep(sub), 'entity_type', '') == "Point")
                if pts_on >= 3:
                    # 共線(3点以上)や共円(4点以上)は極めて重要！
                    prop_bonus += (pts_on - 2) * 5.0 
            elif entity_type == "Point":
                # たくさんの直線や円が交わる点（対称性の中心）
                lines_circles = sum(1 for sub in comp.subobjects if getattr(get_rep(sub), 'entity_type', '') in ["Line", "Circle"])
                if lines_circles >= 2:
                    prop_bonus += lines_circles * 2.0

        # ------------------------------------------------
        # 3. アフィン空間上の「次数(Degree)」ペナルティ
        # 無関係でカオスな図形（次数が大きすぎるもの）を避ける
        # ------------------------------------------------
        nd = getattr(node, 'numerical_degree', None)
        if nd is None and comp:
            nd = getattr(comp, 'naive_degree', 1)
        elif nd is None:
            nd = 1
            
        # 次数が高い＝代数的に複雑すぎる（スパゲッティ状態）ためペナルティ
        degree_factor = 1.0
        if nd > 2:
            degree_factor = 1.0 / math.sqrt(nd)

        # ------------------------------------------------
        # 4. 最終スコアの計算
        # ------------------------------------------------
        cooldown_penalty = 0.3 ** cooldown # クールダウン
        
        final_score = (base_score + heat + target_bonus + prop_bonus) * degree_factor * cooldown_penalty
        return max(0.001, final_score)

    def apply_feedback(self, focus_set, success):
        for node in focus_set:
            if success:
                # 発見があったら熱を上げ、クールダウンを即リセット
                self.heat_table[node] = min(self.heat_table[node] + 3.0, self.MAX_HEAT)
                self.cooldown_table[node] = 0
            else:
                self.cooldown_table[node] += 1
                # 失敗した場所の熱は急速に冷ます(沼防止)
                self.heat_table[node] *= 0.5 

    def decay_global_heat(self):
        for node in list(self.heat_table.keys()):
            self.heat_table[node] *= 0.85
            if self.heat_table[node] < 0.1:
                del self.heat_table[node]


# ==========================================
# 🌟 局所探索エンジン 本体 (Graph-Walk型へ進化)
# ==========================================
class FocusSearchEngine:
    def __init__(self, env, prover, base_engine, focus_size=5):
        self.env = env
        self.prover = prover
        self.base_engine = base_engine
        self.focus_size = focus_size
        self.scoring = ScoringPolicy()
        self.target_nodes = set() # 🌟 NEW: ターゲット図形の保持

    def set_target(self, target_fact):
        """🌟 NEW: 証明目標を受け取り、関連する点や直線をターゲットノードとして登録する"""
        if not target_fact: return
        self.target_nodes.clear()
        
        # ターゲットに直接関わる図形(点)を登録
        for obj in target_fact.objects:
            rep = get_rep(obj)
            if is_valid_node(rep):
                self.target_nodes.add(rep)
                # その点に繋がる直線や円も「準ターゲット」として登録
                self.target_nodes.update(get_subentity(rep, ["Line", "Circle"]))

    def _get_neighbors(self, node):
        """🌟 NEW: ある図形と「直接繋がっている」図形のリストを返す"""
        neighbors = set()
        comp = node.get_best_component()
        if not comp: return neighbors
        
        # 子要素
        for sub in comp.subobjects:
            rep = get_rep(sub)
            if is_valid_node(rep): neighbors.add(rep)
        # 親要素
        for d in comp.definitions:
            for p in d.parents:
                rep = get_rep(p)
                if is_valid_node(rep): neighbors.add(rep)
        
        return list(neighbors)

    def _sample_focus_set(self):
        """🌟 劇的改善: 嬉しい性質と次数を考慮した Graph-Walk サンプリング"""
        from logic_core import get_rep, is_valid_node
        
        base_types = {"Point", "Line", "Circle"}
        all_candidates = [get_rep(n) for n in self.env.nodes if getattr(get_rep(n), 'entity_type', '') in base_types and is_valid_node(n)]
        all_candidates = list(set(all_candidates))
        
        # 🌟 NEW: 選ばれた図形のスコアを記録する辞書
        chosen_scores = {}
        
        if len(all_candidates) <= self.focus_size:
            for c in all_candidates:
                chosen_scores[c] = self.scoring.get_selection_score(c, self.target_nodes)
            return all_candidates, chosen_scores

        # 1. まず「主役 (Center)」をスコアに基づいて1つだけ選ぶ
        scores = [self.scoring.get_selection_score(c, self.target_nodes) for c in all_candidates]
        total_score = sum(scores)
        probs = [s / total_score for s in scores]
        
        center_node = np.random.choice(all_candidates, p=probs)
        focus_set = {center_node}
        chosen_scores[center_node] = scores[all_candidates.index(center_node)]
        
        # 2. 主役の「近傍」を取得し、そこからも優先的に【スコア順】で選ぶ
        neighbors = self._get_neighbors(center_node)
        valid_neighbors = [n for n in neighbors if getattr(n, 'entity_type', '') in base_types and n != center_node]
        
        if valid_neighbors:
            n_scores = [self.scoring.get_selection_score(n, self.target_nodes) for n in valid_neighbors]
            n_total = sum(n_scores)
            n_probs = [s / n_total for s in n_scores] if n_total > 0 else None
            
            num_to_pick = min(len(valid_neighbors), self.focus_size - 1)
            chosen_neighbors = np.random.choice(valid_neighbors, size=num_to_pick, replace=False, p=n_probs)
            focus_set.update(chosen_neighbors)
            for cn in chosen_neighbors:
                chosen_scores[cn] = n_scores[valid_neighbors.index(cn)]
            
        # 3. それでもサイズに満たない場合は、全体から【スコア順】で埋める
        remaining_slots = self.focus_size - len(focus_set)
        if remaining_slots > 0:
            remaining_candidates = list(set(all_candidates) - focus_set)
            if remaining_candidates:
                r_scores = [self.scoring.get_selection_score(c, self.target_nodes) for c in remaining_candidates]
                r_total = sum(r_scores)
                r_probs = [s / r_total for s in r_scores] if r_total > 0 else None
                
                fillers = np.random.choice(remaining_candidates, size=remaining_slots, replace=False, p=r_probs)
                focus_set.update(fillers)
                for filler in fillers:
                    chosen_scores[filler] = r_scores[remaining_candidates.index(filler)]

        return list(focus_set), chosen_scores

    def _extract_local_graph(self, focus_set):
        local_nodes = set(focus_set)
        
        # 1. 注目ノードに直接関連する直線と円を確実に追加
        for base_node in focus_set:
            local_nodes.update(get_subentity(base_node, ["Line", "Circle"]))
            
        # ==========================================
        # 🌟 NEW: 局所ノードの爆発を防ぐ動的リミッター
        # focus_sizeが5なら大体 40〜50 個程度に抑えるのが適正
        # ==========================================
        MAX_LOCAL_NODES = min(250, len(focus_set) * 10) 
        
        # 2. 親が揃っている派生図形（方向ベクトルや角度など）を引き込む
        for _ in range(2): 
            if len(local_nodes) >= MAX_LOCAL_NODES:
                break
                
            added_this_round = False
            candidates = []
            
            for node in self.env.nodes:
                if node in local_nodes or not is_valid_node(node): continue
                rep_n = get_rep(node)
                comp = rep_n.get_best_component()
                if not comp: continue
                
                for d in comp.definitions:
                    # 親がすべて局所グラフ内にあるか？
                    if all(get_rep(p) in local_nodes for p in d.parents):
                        # 角度(AnglePair)より、点や線を優先して引き込む
                        priority = 1 if d.def_type in ["AnglePair", "Direction"] else 0
                        candidates.append((priority, rep_n))
                        break
            
            if not candidates:
                break
                
            candidates.sort(key=lambda x: x[0])
            
            for _, new_node in candidates:
                if len(local_nodes) >= MAX_LOCAL_NODES:
                    break # 上限到達でスパッと切る（Warningスパム防止のためログは消す）
                if new_node not in local_nodes:
                    local_nodes.add(new_node)
                    added_this_round = True
                    
            if not added_this_round: 
                break

        # 3. 必須の定数ノードを追加
        if hasattr(self.env, 'right_angle'): local_nodes.add(get_rep(self.env.right_angle))
        if hasattr(self.env, 'zero_angle'): local_nodes.add(get_rep(self.env.zero_angle))
        
        return list(local_nodes)

    def _prune_theorems(self, local_nodes, theorems):
        # (既存の _prune_theorems と同じ)
        active_theorems = []
        types_in_local = {getattr(n, 'entity_type', '') for n in local_nodes}
        for th in theorems:
            needs_scalar = any(t == "Scalar" for t in th.entities.values())
            if needs_scalar and "Scalar" not in types_in_local: continue
            needs_angle = any(t == "Angle" for t in th.entities.values())
            if needs_angle and "Angle" not in types_in_local: continue
            active_theorems.append(th)
        return active_theorems

    def step(self, theorems):
        # 🌟 修正: スコアの辞書も受け取る
        focus_set, chosen_scores = self._sample_focus_set()
        
        # 🌟 NEW: 図形名と一緒にスコア(評価値)を小数点第1位まで表示する
        focus_log_parts = [f"{n.name}({chosen_scores[n]:.1f})" for n in focus_set]
        logger.info(f"🔍 [局所探索] 注目セット: {', '.join(focus_log_parts)}")
        
        local_nodes = self._extract_local_graph(focus_set)
        active_theorems = self._prune_theorems(local_nodes, theorems)
        
        nodes_before = len(self.env.nodes)
        logger.info(f"   => 局所ノード数: {len(local_nodes)} (全体 {nodes_before}), 適用定理: {len(active_theorems)}/{len(theorems)}")

        # (以下はそのまま)
        self.env.active_search_nodes = local_nodes
        success = self.base_engine.run_all(active_theorems)
        
        nodes_after = len(self.env.nodes)
        new_nodes_count = nodes_after - nodes_before
        if new_nodes_count > 0:
            logger.info(f"   => 📦 [ターン終了] 新規ノードを待機列から合流: +{new_nodes_count} 個 (全体 {nodes_after})")
        
        self.scoring.apply_feedback(focus_set, success)
        self.scoring.decay_global_heat()
        return success

    def run_until_stalled(self, theorems, max_steps=100, target_checker=None):
        import time
        stalled_counter = 0
        logger.info("🚀 局所ヒューリスティック探索を開始します...")
        
        for step in range(1, max_steps + 1):
            start_time = time.time()
            logger.info(f"\n--- ターン {step} ---")
            
            success = self.step(theorems)
            
            if target_checker and target_checker():
                logger.info("🎯 ターゲットの証明を検出しました！局所探索を早期終了します。")
                break
                
            elapsed = time.time() - start_time
            if elapsed > 10.0:
                logger.warning(f"⚠️ ターン処理が重すぎます ({elapsed:.2f}秒)。強制脱出します。")
                break

            if success:
                stalled_counter = 0
            else:
                stalled_counter += 1
                
            if stalled_counter >= 10: 
                break
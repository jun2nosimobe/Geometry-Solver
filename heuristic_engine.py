import random
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
        base_score = getattr(node, 'importance', 1.0)
        heat = min(self.heat_table[node], self.MAX_HEAT)
        cooldown = self.cooldown_table[node]
        
        # 🌟 NEW: 目標図形(Target)に近いほどスコアに下駄を履かせる(引力)
        target_bonus = 0.0
        if target_nodes and node in target_nodes:
            target_bonus = 15.0

        cooldown_penalty = 0.2 ** cooldown # ペナルティを少しマイルドに調整
        
        final_score = (base_score + heat + target_bonus) * cooldown_penalty
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
        """🌟 劇的改善: Graph-Walk (構造的) サンプリング"""
        base_types = {"Point", "Line", "Circle"}
        all_candidates = [get_rep(n) for n in self.env.nodes if getattr(get_rep(n), 'entity_type', '') in base_types and is_valid_node(n)]
        all_candidates = list(set(all_candidates))
        
        if len(all_candidates) <= self.focus_size:
            return all_candidates

        # 1. まず「主役 (Center)」をスコアに基づいて1つだけ選ぶ
        scores = [self.scoring.get_selection_score(c, self.target_nodes) for c in all_candidates]
        total_score = sum(scores)
        probs = [s / total_score for s in scores]
        
        center_node = np.random.choice(all_candidates, p=probs)
        focus_set = {center_node}
        
        # 2. 主役の「近傍 (Neighbors)」を取得し、そこから優先的に残りを選ぶ
        neighbors = self._get_neighbors(center_node)
        # 近傍の中でも基本図形だけをフィルター
        valid_neighbors = [n for n in neighbors if getattr(n, 'entity_type', '') in base_types and n != center_node]
        
        if valid_neighbors:
            num_to_pick = min(len(valid_neighbors), self.focus_size - 1)
            # 近傍からはランダムにピック (スコア計算を省いて高速化)
            chosen_neighbors = np.random.choice(valid_neighbors, size=num_to_pick, replace=False)
            focus_set.update(chosen_neighbors)
            
        # 3. それでもサイズに満たない場合は、全体からランダムに埋める
        remaining_slots = self.focus_size - len(focus_set)
        if remaining_slots > 0:
            remaining_candidates = list(set(all_candidates) - focus_set)
            if remaining_candidates:
                num_to_pick = min(len(remaining_candidates), remaining_slots)
                fillers = np.random.choice(remaining_candidates, size=num_to_pick, replace=False)
                focus_set.update(fillers)

        return list(focus_set)

    def _extract_local_graph(self, focus_set):
        local_nodes = set(focus_set)
        
        # 1. 注目ノードに直接関連する直線と円を確実に追加
        for base_node in focus_set:
            local_nodes.update(get_subentity(base_node, ["Line", "Circle"]))
            
        # ==========================================
        # 🌟 NEW: 局所ノードの爆発を防ぐ絶対防波堤 (Hard Limit)
        # ==========================================
        MAX_LOCAL_NODES = 250  
        
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
                        # 🌟 工夫: 角度(AnglePair)より、点や線を優先して引き込むためのスコア付け
                        priority = 1 if d.def_type in ["AnglePair", "Direction"] else 0
                        candidates.append((priority, rep_n))
                        break
            
            if not candidates:
                break
                
            # 優先度順（重要図形が先、角度が後）にソートして追加
            candidates.sort(key=lambda x: x[0])
            
            for _, new_node in candidates:
                if len(local_nodes) >= MAX_LOCAL_NODES:
                    logger.warning(f"⚠️ 局所グラフが上限({MAX_LOCAL_NODES})に到達。これ以上の波及を打ち切ります。")
                    break
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
        focus_set = self._sample_focus_set()
        logger.info(f"🔍 [局所探索] 注目セット: {', '.join([n.name for n in focus_set])}")
        
        local_nodes = self._extract_local_graph(focus_set)
        active_theorems = self._prune_theorems(local_nodes, theorems)
        logger.info(f"   => 局所ノード数: {len(local_nodes)} (全体 {len(self.env.nodes)}), 適用定理: {len(active_theorems)}/{len(theorems)}")

        self.env.active_search_nodes = local_nodes
        success = self.base_engine.run_all(active_theorems)
        self.env.active_search_nodes = None
        
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
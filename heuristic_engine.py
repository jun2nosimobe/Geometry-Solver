import random
import logging
import itertools
from collections import defaultdict
from logic_core import get_rep, is_valid_node, get_subentity

logger = logging.getLogger("GeometryProver")

# ==========================================
# 🌟 スコアリングとフィードバックの独立モジュール
# (ここを後からいくらでもチューニング・拡張できます)
# ==========================================
class ScoringPolicy:
    """注目ノードを選ぶためのスコア計算と、探索結果のフィードバックを管理するクラス"""
    
    def __init__(self):
        self.cooldown_table = defaultdict(int)  # 探索失敗によるペナルティ(ターン数)
        self.heat_table = defaultdict(float)    # 発見による熱ボーナス

    def get_selection_score(self, node):
        """ノードが「次の注目セット」に選ばれる確率の重みを計算する"""
        base_score = getattr(node, 'importance', 1.0)
        heat = self.heat_table[node]
        cooldown = self.cooldown_table[node]
        
        # クールダウン中はスコアを激減させる (例: 1/10, 1/100...)
        cooldown_penalty = 0.1 ** cooldown 
        
        # 最終スコア: (基本重要度 + 熱) * ペナルティ
        final_score = (base_score + heat) * cooldown_penalty
        return max(0.001, final_score) # 確率が0にならないよう微小値を保証

    def apply_feedback(self, focus_set, success):
        """1ターンの探索結果を受けて、熱とペナルティを更新する"""
        for node in focus_set:
            if success:
                # 🎉 大発見！ 熱を上げ、クールダウンを即座にリセット
                self.heat_table[node] += 2.0
                self.cooldown_table[node] = 0
            else:
                # ❌ 何も出なかった。熱を少し冷まし、クールダウンを増加
                self.heat_table[node] = max(0.0, self.heat_table[node] - 0.5)
                self.cooldown_table[node] += 1

    def decay_global_heat(self):
        """毎ターン、全体の熱を少しずつ冷ます (忘却効果)"""
        for node in list(self.heat_table.keys()):
            self.heat_table[node] *= 0.9
            if self.heat_table[node] < 0.1:
                del self.heat_table[node]


# ==========================================
# 🌟 局所探索エンジン 本体
# ==========================================
class FocusSearchEngine:
    def __init__(self, env, prover, base_engine, focus_size=5):
        self.env = env
        self.prover = prover
        self.base_engine = base_engine # logic_core.py の UniversalRuleEngine
        self.focus_size = focus_size
        
        # スコアリングロジックの注入 (将来的に MLPolicy などに差し替え可能)
        self.scoring = ScoringPolicy()

    def _sample_focus_set(self):
        """基本図形 (Point, Line, Circle) の中から、スコアに従って注目セットを選ぶ"""
        base_types = {"Point", "Line", "Circle"}
        candidates = [n for n in self.env.nodes if getattr(get_rep(n), 'entity_type', '') in base_types and is_valid_node(n)]
        
        # 代表元(Canonical)だけをユニークに集める
        candidates = list(set(get_rep(n) for n in candidates))
        
        if len(candidates) <= self.focus_size:
            return candidates

        scores = [self.scoring.get_selection_score(c) for c in candidates]
        total_score = sum(scores)
        probs = [s / total_score for s in scores]
        
        import numpy as np
        # numpyを使って確率の重み付きランダム抽出 (重複なし)
        chosen = np.random.choice(candidates, size=self.focus_size, replace=False, p=probs)
        return list(chosen)

    def _extract_local_graph(self, focus_set):
        """選ばれた基本図形に「直接」関係する副次図形(方向、角度、長さなど)を掻き集める"""
        local_nodes = set(focus_set)
        
        # Focus Set に含まれる点を通る直線や円をまず追加
        for base_node in focus_set:
            local_nodes.update(get_subentity(base_node, ["Line", "Circle"]))
            
        # 既存のすべてのノードをチェックし、親がすべて local_nodes に含まれるなら局所グラフに入れる
        # (例: AnglePairの親であるDirectionの親であるLineがFocus Setの2点からできている、など)
        # ※深い依存関係を拾うため、数回ループを回して「波及」させる
        for _ in range(2): 
            added_this_round = False
            for node in self.env.nodes:
                if node in local_nodes or not is_valid_node(node): continue
                
                rep_n = get_rep(node)
                comp = rep_n.get_best_component()
                if not comp: continue
                
                # 定義の親が「すべて」local_nodes に入っていれば、このノードも局所グラフに追加
                for d in comp.definitions:
                    if all(get_rep(p) in local_nodes for p in d.parents):
                        local_nodes.add(rep_n)
                        added_this_round = True
                        break # このノードは追加されたので次のノードへ
            
            if not added_this_round: break

        # システムの必須定数 (直角、ゼロ角) は常に局所グラフに混ぜる
        if hasattr(self.env, 'right_angle'): local_nodes.add(get_rep(self.env.right_angle))
        if hasattr(self.env, 'zero_angle'): local_nodes.add(get_rep(self.env.zero_angle))
        
        return list(local_nodes)

    def _prune_theorems(self, local_nodes, theorems):
        """局所グラフの状態を見て、絶対に発火しない定理を枝刈りする"""
        active_theorems = []
        types_in_local = {getattr(n, 'entity_type', '') for n in local_nodes}
        
        for th in theorems:
            needs_scalar = any(t == "Scalar" for t in th.entities.values())
            if needs_scalar and "Scalar" not in types_in_local:
                continue
                
            needs_angle = any(t == "Angle" for t in th.entities.values())
            if needs_angle and "Angle" not in types_in_local:
                continue
                
            active_theorems.append(th)
        return active_theorems

    def step(self, theorems):
        """1ターンの局所探索を実行する"""
        # 1. 注目ノードの決定
        focus_set = self._sample_focus_set()
        logger.info(f"🔍 [局所探索] 注目セット: {', '.join([n.name for n in focus_set])}")
        
        # 2. 局所グラフの抽出と定理の枝刈り
        local_nodes = self._extract_local_graph(focus_set)
        active_theorems = self._prune_theorems(local_nodes, theorems)
        logger.info(f"   => 局所ノード数: {len(local_nodes)} (全体 {len(self.env.nodes)}), 適用定理: {len(active_theorems)}/{len(theorems)}")

        self.env.active_search_nodes = local_nodes
        
        success = self.base_engine.run_all(active_theorems)
        
        # 🌟 探索が終わったらスコープを解除し、全体探索に戻す
        self.env.active_search_nodes = None
        
        self.scoring.apply_feedback(focus_set, success)
        self.scoring.decay_global_heat()
        
        return success

    def run_until_stalled(self, theorems, max_steps=100, target_checker=None):
        """新しい発見が完全に出なくなるまで、またはターゲットが証明されるまで局所探索を繰り返す"""
        stalled_counter = 0
        logger.info("🚀 局所ヒューリスティック探索を開始します...")
        
        for step in range(1, max_steps + 1):
            logger.info(f"\n--- ターン {step} ---")
            success = self.step(theorems)
            
            # 🌟 NEW: 毎ターン終了時にゴール判定を行い、達成していれば即座に打ち切る！
            if target_checker and target_checker():
                logger.info("🎯 ターゲットの証明を検出しました！局所探索を早期終了します。")
                break
            
            if success:
                stalled_counter = 0
            else:
                stalled_counter += 1
                
            if stalled_counter >= 10: 
                logger.info("🛑 連続して新しい発見がなかったため、探索を終了します。")
                break
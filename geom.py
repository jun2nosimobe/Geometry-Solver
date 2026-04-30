# geom.py
import math
import numpy as np
import random
import itertools
import logging
import importlib
import sys
from mmp_core import * 
from logic_core import * 
from theorems import THEOREMS 

# ログの設定: 推論の詳細を proof.log に書き出し、コンソールはスッキリさせる
logger = logging.getLogger("GeometryProver")
logger.setLevel(logging.DEBUG)
if not logger.handlers:
    file_handler = logging.FileHandler('proof.log', mode='w', encoding='utf-8')
    file_handler.setFormatter(logging.Formatter('%(message)s'))
    logger.addHandler(file_handler)


# --- 型判定・ゼロ判定ヘルパー ---
def is_zero_mod(v):
    """ModIntの実装によらず、確実に0を判定する"""
    if hasattr(v, 'value'): return v.value == 0
    if hasattr(v, 'val'): return v.val == 0
    if hasattr(v, 'n'): return v.n == 0
    try: return int(v) == 0
    except: return v == 0
def is_point(obj): return hasattr(obj, 'entity_type') and obj.entity_type == "Point"
def is_line(obj): return hasattr(obj, 'entity_type') and obj.entity_type == "Line"
def is_circle(obj): return hasattr(obj, 'entity_type') and obj.entity_type == "Circle"



# ==========================================
# 2. モンテカルロ木探索 (MCTS) エンジン
# ==========================================
class MCTSNode:
    """MCTSの探索木ノード"""
    def __init__(self, action=None, parent=None):
        self.action = action  # (X, Y, 作図の種類, 名前)
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
        
        # SVD計算用のランダムサンプル(キャッシュ)の初期化などはそのまま残す
        self.t_samples = [ModInt(np.random.randint(1, ModInt.MOD - 1)) for _ in range(400)]
        self.historical_names = set()

    def _discover_all_mmp_relations(self, Z, parents):
        """確定した手(Z)について、ありとあらゆる代数的関係(MMP大発見)を徹底的にテストする"""
        
        # 1. 基本的な Incidence (点と曲線)
        if is_point(Z):
            for c in [n for n in self.env.nodes if (is_line(n) or is_circle(n)) and n not in parents]: 
                self._check_and_add_incidence(Z, c)
        elif is_line(Z) or is_circle(Z):
            for p in [n for n in self.env.nodes if is_point(n) and n not in parents]: 
                self._check_and_add_incidence(p, Z)
                
        # =========================================================
        # 🌟 追加大発見A: 直線の「平行」と「垂直」を徹底テスト
        # =========================================================
        if is_line(Z):
            # ★ 修正: self.env.importance.get(...) ではなく n.importance を直接参照
            hot_lines = [n for n in self.env.nodes if is_line(n) and n not in parents and n.importance >= 3.0]
            
            for ln in hot_lines:
                if Z == ln: continue
                
                valid_para, valid_perp = 0, 0
                for _ in range(5):
                    cache = {}
                    random_t_dict = {v: ModInt(np.random.randint(1, ModInt.MOD - 1)) for v in self.all_vars}
                    try:
                        cZ = Z.calculate(random_t_dict, cache)
                        cln = ln.calculate(random_t_dict, cache)
                        if is_zero_mod(cZ[0]*cln[1] - cZ[1]*cln[0]): valid_para += 1
                        if is_zero_mod(cZ[0]*cln[0] + cZ[1]*cln[1]): valid_perp += 1
                    except: pass
                    
                
                if valid_para == 5:
                    # 🌟 修正: ParallelのFactを発行する
                    fact = Fact("Parallel", [Z, ln], is_proven=False, proof_source="MMP大発見(平行)")
                    if not any(f == fact for f in self.prover.facts):
                        self.prover.add_fact(fact)
                        logger.debug(f"    🌟 MMP大発見(平行): {Z.name} // {ln.name}")
                        Z.importance += 5.0
                        ln.importance += 5.0
                    
                if valid_perp == 5:
                    # 🌟 修正: 垂直は既存のAPIを使って安全に登録する
                    if hasattr(self.env, 'add_right_angle'):
                        self.env.add_right_angle(Z, ln)
                        logger.debug(f"    🌟 MMP大発見(垂直): {Z.name} ⊥ {ln.name}")
                        Z.importance += 5.0
                        ln.importance += 5.0

        # =========================================================
        # 🌟 追加大発見B: 離れた4点の「非自明な共円」を徹底テスト
        # =========================================================
        if is_point(Z):
            # ★ 修正: self.env.importance.get(...) ではなく n.importance を直接参照
            hot_pts = [n for n in self.env.nodes if is_point(n) and n != Z and n not in parents and n.importance >= 8.0]
            
            for p1, p2, p3 in itertools.combinations(hot_pts, 3):
                # ★ 新構造に合わせたダミーの円(GeoEntity)作成
                temp_circle = create_geo_entity("Circumcircle", [p1, p2, p3], name="temp", env=None)
                
                valid_count = 0
                for _ in range(5):
                    cache = {}
                    random_t_dict = {v: ModInt(np.random.randint(1, ModInt.MOD - 1)) for v in self.all_vars}
                    try:
                        c_val = temp_circle.calculate(random_t_dict, cache)
                        Z_val = Z.calculate(random_t_dict, cache)
                        if all(is_zero_mod(v) for v in c_val) or all(is_zero_mod(v) for v in Z_val): continue
                        if is_zero_mod(Z_val[-1]): continue # 無限遠点は除外
                        
                        # 円の方程式への代入チェック
                        cond = EvaluateCircleCondition(temp_circle, Z)
                        if cond.evaluate(random_t_dict, cache) == 0:
                            valid_count += 1
                    except: pass

                if valid_count == 5:
                    # 🌟 修正: 4点(Z, p1, p2, p3)の共円Factを正しく発行する！
                    fact = Fact("Concyclic", [Z, p1, p2, p3], is_proven=False, proof_source="MMP大発見(共円)")
                    if not any(f == fact for f in self.prover.facts):
                        self.prover.add_fact(fact)
                        logger.debug(f"    🌟 MMP大発見(共円): {Z.name}, {p1.name}, {p2.name}, {p3.name}")
                        Z.importance += 5.0
                        p1.importance += 2.0
                        p2.importance += 2.0
                        p3.importance += 2.0

    def _check_and_add_incidence(self, pt, curve):
        # 1. 既に論理的に乗っているかチェック (無駄な計算を省く)
        c_pt = pt.get_best_component()
        if c_pt and curve in c_pt.subobjects: return False
        
        # 2. 既にMMP(代数テスト)で発見済みかチェック
        if curve in pt.mmp_subobjects: return False
        
        valid_count = 0
        for _ in range(5): 
            cache = {}
            random_t_dict = {v: ModInt(np.random.randint(1, ModInt.MOD - 1)) for v in self.all_vars}
            try:
                pt_val = pt.calculate(random_t_dict, cache)
                c_val = curve.calculate(random_t_dict, cache)
                
                if all(is_zero_mod(v) for v in pt_val) or all(is_zero_mod(v) for v in c_val): continue
                if is_zero_mod(pt_val[-1]): continue # 無限遠点は除外
                
                # 退化した異常な直線の除外
                if curve.entity_type == "Line" and is_zero_mod(c_val[0]) and is_zero_mod(c_val[1]): continue

                # 直線の Incidence 判定 (内積=0)
                is_on_curve = False
                if curve.entity_type == "Line":
                    dot = c_val[0]*pt_val[0] + c_val[1]*pt_val[1] + c_val[2]*pt_val[2]
                    if is_zero_mod(dot): is_on_curve = True
                elif curve.entity_type == "Circle":
                    # ★ 古い EvaluateCircleCondition を削除し、直接計算！
                    u, v, w, s = c_val
                    x, y, z = pt_val
                    val = u*(x**2 + y**2) + v*x*z + w*y*z + s*z**2
                    if is_zero_mod(val): is_on_curve = True

                if is_on_curve:
                    valid_count += 1
            except: pass
        
        # 5回すべてで成立した場合のみ「真実」とみなす
        if valid_count == 5: 
            # ★ 新構造: MMP発見リストに双方向で登録
            pt.mmp_subobjects.add(curve)
            curve.mmp_subobjects.add(pt)
            
            fact_type = "Concyclic" if curve.entity_type == "Circle" else "Collinear"
            
            # Factとして論理エンジン(Prover)に投げる
            from logic_core import Fact
            # 曲線を作るのに使われた親の点群を取得
            c_curve = curve.get_best_component()
            curve_pts = [p for p in next(iter(c_curve.definitions)).parents if getattr(p, 'entity_type', '') == "Point"] if c_curve and c_curve.definitions else []
            
            objs = [pt] + curve_pts
            fact = Fact(fact_type, objs, is_proven=False, proof_source="MMP大発見")
            
            if not any(f == fact for f in self.prover.facts):
                self.prover.add_fact(fact)
                logger.debug(f"    🌟 MMP大発見: {pt.name} が {curve.name} 上にある！")
                pt.importance += 10.0
            return True
        return False

    def evaluate_numerical_degree(self, Z, naive_d, target_var, max_samples=None):
        """1変数SVDによる真の次数計算 (軽量化・フリーズ対策版)"""
        t_values, x_values, y_values = [], [], []
        fixed_vars = {v: ModInt(np.random.randint(1, ModInt.MOD - 1)) for v in self.all_vars if v != target_var}
        
        # SVDには最低 2d + 2 のサンプルが必要
        required_samples = 2 * naive_d + 3 
        sample_pool = self.t_samples[:max_samples] if max_samples else self.t_samples
        
        for t in sample_pool:
            cache = {}
            current_t_dict = {**fixed_vars, target_var: t}
            try:
                val = Z.evaluate(current_t_dict, cache)
                if val[-1].value == 0: continue
                x, y = val[0] / val[-1], val[1] / val[-1]
                t_values.append(t); x_values.append(x); y_values.append(y)
                
                # ★ NEW: 必要十分なサンプルが集まったら即座にループを抜ける（計算爆発の防止）
                if len(t_values) >= required_samples:
                    break
            except: continue
            
        if len(t_values) < 2 * naive_d + 2: return naive_d
        return max(get_numerical_degree(t_values, x_values, naive_d, mode='mod'),
                   get_numerical_degree(t_values, y_values, naive_d, mode='mod'))

    def _get_possible_actions(self, nodes: List['GeoEntity'], is_simulation=False):
        """現在のGeoEntity群から可能な合法手をサンプリングして返す(新構造対応版)"""
        if len(nodes) < 2: return []
        
        # 重要度ベースのルーレット選択
        weights = np.array([n.importance for n in nodes])
        probs = weights / weights.sum()
        
        actions = []
        
        existing_names = self.historical_names
        if not is_simulation:
            self.historical_names.update(n.name for n in nodes)
        existing_names = self.historical_names

        
        for _ in range(40): 
            # 2つの実体を選ぶ
            X, Y = np.random.choice(nodes, size=2, replace=False, p=probs)
            
            # 論理コンポーネントの取得
            cx = X.get_best_component()
            cy = Y.get_best_component()
            if not cx or not cy: continue

            # ==========================================
            # 1. 直線 × 直線 -> 交点
            # ==========================================
            if X.entity_type == "Line" and Y.entity_type == "Line":
                # ★ 超高速チェック: 2つの直線の subobjects に共通の「点」がすでにあるか？
                common_pts = [obj for obj in (cx.subobjects & cy.subobjects) if obj.entity_type == "Point"]
                
                # 平行チェック (mmp_subobjects等に平行フラグが入る設計になればそこに置き換えます)
                is_para = any(X in lines and Y in lines for lines in self.env.parallel_classes.values()) if hasattr(self.env, 'parallel_classes') else False
                
                # 共通の交点がなく、平行でもない場合のみ作図！
                if not common_pts and not is_para:
                    name = f"Int_{X.name}_{Y.name}"
                    if name not in existing_names:
                        actions.append(([X, Y], "Intersection", name))
                        
            # ==========================================
            # 2. 点 × 点 -> 直線 / 中点
            # ==========================================
            elif X.entity_type == "Point" and Y.entity_type == "Point":
                # ★ 超高速チェック: すでにこの2点を通る「直線」が存在しているか？
                common_lines = [obj for obj in (cx.subobjects & cy.subobjects) if obj.entity_type == "Line"]
                
                if not common_lines:
                    name_line = f"Line_{X.name}_{Y.name}"
                    if name_line not in existing_names:
                        actions.append(([X, Y], "LineThroughPoints", name_line))
                
                # 中点は重要度が高いペアでのみ許可
                if X.importance + Y.importance >= 10.0:
                    name_mid = f"Mid_{X.name}_{Y.name}"
                    if name_mid not in existing_names:
                        actions.append(([X, Y], "Midpoint", name_mid))
                        
            # ==========================================
            # 3. 点 × 直線 -> 垂線 / 平行線
            # ==========================================
            elif (X.entity_type == "Point" and Y.entity_type == "Line") or (Y.entity_type == "Point" and X.entity_type == "Line"):
                pt, ln = (X, Y) if X.entity_type == "Point" else (Y, X)
                c_pt = cx if X.entity_type == "Point" else cy
                
                name_perp = f"Perp_{pt.name}_{ln.name}"
                if name_perp not in existing_names:
                    actions.append(([ln, pt], "PerpendicularLine", name_perp))
                
                # ★ 超高速チェック: 点がすでにその直線上に乗っているか？ (乗っていれば平行線は引けない)
                if ln not in c_pt.subobjects:
                    name_para = f"Para_{pt.name}_{ln.name}"
                    if name_para not in existing_names:
                        actions.append(([ln, pt], "ParallelLine", name_para))

            # ==========================================
            # 4. 点 × 点 × 点 -> 外接円 (3ノード選ぶ場合)
            # ==========================================
            if len(nodes) >= 3:
                P1, P2, P3 = np.random.choice(nodes, size=3, replace=False, p=probs)
                if P1.entity_type == "Point" and P2.entity_type == "Point" and P3.entity_type == "Point":
                    if P1.importance + P2.importance + P3.importance >= 15.0:
                        cp1, cp2, cp3 = P1.get_best_component(), P2.get_best_component(), P3.get_best_component()
                        if cp1 and cp2 and cp3:
                            # ★ 超高速チェック: この3点を全て通る「円」または「直線(共線)」がすでにあるか？
                            common_curves = cp1.subobjects & cp2.subobjects & cp3.subobjects
                            
                            if not common_curves: # 何も共有していなければ円を描く
                                names = sorted([P1.name, P2.name, P3.name])
                                name_circ = f"Circum_{names[0]}_{names[1]}_{names[2]}"
                                if name_circ not in existing_names:
                                    actions.append(([P1, P2, P3], "Circumcircle", name_circ))

        # 重複排除処理 (タプル化してsetで回す)
        unique_actions = []
        seen = set()
        for act in actions:
            act_tuple = (tuple(p.id for p in act[0]), act[1], act[2])
            if act[2] not in seen:
                seen.add(act[2])
                unique_actions.append(act)
                
        return unique_actions

    def _create_object_from_action(self, action):
        parents, c_type, name = action
        
        # c_type (作図の種類) と self.env をそのままビルダーに渡すだけ！
        return create_geo_entity(c_type, parents, name=name, env=None)
        

    def _playout(self, initial_nodes: List['GeoEntity'], depth: int = 3):
        """シミュレーション: 新データ構造(GeoEntity)を使って盤面のポテンシャルを測る"""
        sim_nodes = list(initial_nodes)
        score = 0.0
        
        for step_idx in range(depth):
            actions = self._get_possible_actions(sim_nodes, is_simulation=True)
            if not actions: break
            
            # 親の重要度でルーレット選択
            action_weights = [sum(p.importance for p in a[0]) for a in actions]
            total_w = sum(action_weights)
            probs = [w / total_w for w in action_weights]
            action = actions[np.random.choice(len(actions), p=probs)]
            
            # ★ NEW: 作図ビルダーを使ってシミュレーション用のエンティティを生成
            parents, def_type, name = action[0], action[1], action[2]
            Z = create_geo_entity(def_type, parents, name)
            
            cZ = Z.get_best_component()
            if not cZ or cZ.depth > 6: 
                score -= 1.0
                continue 
            
            # 評価1: 親の重要度
            parent_imp = sum(p.importance for p in parents) / len(parents)
            score += parent_imp * (0.5 ** step_idx)

            # 評価2: SVDによる次数低下シミュレーション
            for var in self.all_vars:
                nd = cZ.naive_degree
                if nd > 30: continue
                score += max(0.1, 2.0 / (nd + 1))
                if 1 < nd <= 15:
                    td = self.evaluate_numerical_degree(Z, nd, var, max_samples=40)
                    if td <= 15:
                        drop = max(0, nd - td)
                        if drop > 0: score += drop * 20.0 
                            
            # 評価3: Factの重さのシミュレーション (既存の熱い図形とのIncidenceテスト)
            if Z.entity_type == "Point":
                hot_curves = [n for n in sim_nodes if n.entity_type in ["Line", "Circle"] and n.importance >= 5.0 and n not in parents]
                for c in hot_curves:
                    cache = {}
                    random_t_dict = {v: ModInt(np.random.randint(1, ModInt.MOD - 1)) for v in self.all_vars}
                    try:
                        # 計算レジストリを使って座標を評価
                        Z_val = Z.calculate(random_t_dict, cache)
                        c_val = c.calculate(random_t_dict, cache)
                        
                        # (※ EvaluateLineCondition などを関数ベースに置き換えていく過程ですが、
                        #    一旦は代入計算が0になるかどうかのテストとして処理します)
                        score += c.importance * 3.0
                        break # 1つ乗れば十分
                    except: pass

            sim_nodes.append(Z)
            
        return score

    def _check_identical_mmp(self, entity1: 'GeoEntity', entity2: 'GeoEntity') -> bool:
        """2つのGeoEntityが代数的に全く同じ座標(式)を持っているか、厳密に5回テストする"""
        if entity1.entity_type != entity2.entity_type: return False
        
        valid_count = 0
        for _ in range(5):
            cache = {}
            random_t_dict = {v: ModInt(np.random.randint(1, ModInt.MOD - 1)) for v in self.all_vars}
            try:
                val1 = entity1.calculate(random_t_dict, cache)
                val2 = entity2.calculate(random_t_dict, cache)
                
                # 🌟 修正: 3次元(点・線)と4次元(円)の両方に完全対応する「比例判定」
                # 最初の非ゼロ要素を探す
                idx1 = next((i for i, x in enumerate(val1) if not is_zero_mod(x)), -1)
                idx2 = next((i for i, x in enumerate(val2) if not is_zero_mod(x)), -1)
                
                if idx1 == idx2:
                    if idx1 == -1: 
                        valid_count += 1 # 両方ゼロベクトルの異常系
                    else:
                        # 基準となる要素の比率を求める
                        ratio = val2[idx1] / val1[idx1]
                        # すべての要素がその比率と一致するかチェック
                        if all(is_zero_mod(val1[i] * ratio - val2[i]) for i in range(len(val1))):
                            valid_count += 1
            except: pass
            
        return valid_count == 5

    def _run_logic_step(self):
        """新しい事実に基づく局所的推論"""
        new_facts = []
        
        # 🌟 デバッグ用：このステップ内で処理したFactの文字列表現を記録
        processed_fact_strings = getattr(self, '_debug_processed_facts', set())
        self._debug_processed_facts = processed_fact_strings

        # ==========================================
        # 🌟 NEW: E-Graph Entailment Check (最強の重複ストッパー)
        # E-Graphが「すでに知っている」事実なら、文字の順序によらずTrueを返す
        # ==========================================
        def get_representative(obj):
            while hasattr(obj, '_merged_into') and obj._merged_into is not None:
                obj = obj._merged_into
            return obj

        def is_already_in_egraph(fact):
            if any(getattr(obj, '_is_merged_and_dead', False) for obj in fact.objects):
                return True

            if fact.fact_type == "Concyclic" and len(fact.objects) >= 4:
                pts = fact.objects[:4]
                comps = [p.get_best_component() for p in pts]
                if all(comps):
                    common_circles = set.intersection(*(c.subobjects for c in comps))
                    if any(obj.entity_type == "Circle" for obj in common_circles):
                        return True
            elif fact.fact_type == "Collinear" and len(fact.objects) >= 3:
                pts = fact.objects[:3]
                comps = [p.get_best_component() for p in pts]
                if all(comps):
                    common_lines = set.intersection(*(c.subobjects for c in comps))
                    if any(obj.entity_type == "Line" for obj in common_lines):
                        return True
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
                        if has_12 and has_34:
                            return True # すでに同じAngleエンティティ内に統合済み！
            elif fact.fact_type == "Identical" and len(fact.objects) == 2:
                obj1, obj2 = fact.objects
                rep1 = get_representative(obj1)
                rep2 = get_representative(obj2)
                # 既に物理的に同じオブジェクト（マージ済み）なら、推論する必要なし
                if rep1 == rep2:
                    print("!!")
                    return True
                    
            return False

        for theorem in THEOREMS:
            matches = theorem.match_func(self.prover.facts, self.env)
            for match in matches:
                premises, conclusion_template = theorem.apply_func(match)
                
                # --- (通常のチェック処理群) ---
                if is_already_in_egraph(conclusion_template): continue
                actual_premises = [self.prover.get_or_add_fact(p) for p in premises]
                if not all(p.is_proven for p in actual_premises): continue
                actual_conclusion = self.prover.get_or_add_fact(conclusion_template)
                if actual_conclusion.is_proven: continue
                # -----------------------------

                # 🌟 結論の文字列表現を作る
                conclusion_str = str(actual_conclusion)

                # ==========================================
                # 🚨 デバッグトラップ発動！
                # ==========================================
                if actual_conclusion.fact_type == "Identical" and conclusion_str in processed_fact_strings:
                    obj1, obj2 = actual_conclusion.objects
                    logger.error(f"🚨 【重複すり抜け検知】: {conclusion_str}")
                    logger.error(f"  ▶ obj1 ({obj1.name}): id={id(obj1)}, dead={getattr(obj1, '_is_merged_and_dead', False)}, merged_into={getattr(obj1, '_merged_into', None)}")
                    logger.error(f"  ▶ obj2 ({obj2.name}): id={id(obj2)}, dead={getattr(obj2, '_is_merged_and_dead', False)}, merged_into={getattr(obj2, '_merged_into', None)}")
                    
                    rep1 = get_representative(obj1)
                    rep2 = get_representative(obj2)
                    logger.error(f"  ▶ 真の本体比較: rep1={id(rep1)} ({rep1.name}), rep2={id(rep2)} ({rep2.name}) -> 同一? {rep1 == rep2}")
                    
                    # どこで防壁が破られたのか強制停止して確認したければ、ここで raise Exception しても良いです
                    # raise RuntimeError("デバッグ強制停止")
                # ==========================================
                
                # ★ 革命的ストッパー: E-Graphがすでに知っているなら、一切の処理をスキップ！
                if is_already_in_egraph(conclusion_template):
                    continue
                
                
                step_exists = any(getattr(dep, 'conclusion', None) == actual_conclusion and getattr(dep, 'theorem_name', '') == theorem.name 
                                  for p in actual_premises for dep in p.dependents)
                
                if not step_exists:
                    proof_step = ProofStep(theorem.name, actual_premises, actual_conclusion)
                    
                    # ★ 落とし穴②の修正: 前提が揃っているので即座に証明完了状態にする！
                    proof_step.check_if_proven()
                    
                    # check_if_proven によって証明が成功した場合のみ還元処理を行う
                    if actual_conclusion.is_proven:
                        new_facts.append(actual_conclusion)
                        processed_fact_strings.add(conclusion_str) # 🌟 記録する
                        
                        # ログ出力
                        logger.debug(f"  [推論] 🟢 {actual_conclusion} (定理: {theorem.name})")
                        
                        # ==========================================
                        # 🌟 証明された事実をデータ構造(GeoEntity)に還元する
                        # ==========================================
                        if actual_conclusion.fact_type == "Concyclic":
                            pts = actual_conclusion.objects
                            if len(pts) >= 4:
                                p1, p2, p3, p4 = pts[0], pts[1], pts[2], pts[3]
                                c1, c2, c3 = p1.get_best_component(), p2.get_best_component(), p3.get_best_component()
                                
                                if c1 and c2 and c3:
                                    common_circles = [obj for obj in (c1.subobjects & c2.subobjects & c3.subobjects) if obj.entity_type == "Circle"]
                                    if common_circles:
                                        circ = common_circles[0]
                                    else:
                                        circ_name = f"Circum_{p1.name}{p2.name}{p3.name}_(Auto)"
                                        new_circ = create_geo_entity("Circumcircle", [p1, p2, p3], name=circ_name, env=self.env)
                                        self.env.nodes.append(new_circ)
                                        
                                        # 🌟 修正: Auto生成された円も必ずMMP重複チェック＆マージを通す！
                                        merged = False
                                        for node in self.env.nodes:
                                            if node != new_circ and self._check_identical_mmp(new_circ, node):
                                                merged_node = self.env.merge_entities_logically(node, new_circ)
                                                if merged_node: new_circ = merged_node
                                                merged = True
                                                break
                                        circ = new_circ
                                    
                                    link_logical_incidence(circ, p4)
                                    logger.debug(f"    🔄 [データ還元] 論理証明により {p4.name} が {circ.name} 上にある事実を構造化しました。")

                        elif actual_conclusion.fact_type == "Collinear":
                            pts = actual_conclusion.objects
                            if len(pts) >= 3:
                                p1, p2, p3 = pts[0], pts[1], pts[2]
                                c1, c2 = p1.get_best_component(), p2.get_best_component()
                                if c1 and c2:
                                    common_lines = [obj for obj in (c1.subobjects & c2.subobjects) if obj.entity_type == "Line"]
                                    if common_lines:
                                        line_obj = common_lines[0]
                                    else:
                                        line_name = f"Line_{p1.name}{p2.name}_(Auto)"
                                        new_line = create_geo_entity("LineThroughPoints", [p1, p2], name=line_name, env=self.env)
                                        self.env.nodes.append(new_line)
                                        
                                        # 🌟 修正: Auto生成された直線も必ずMMP重複チェック＆マージを通す！
                                        merged = False
                                        for node in self.env.nodes:
                                            if node != new_line and self._check_identical_mmp(new_line, node):
                                                merged_node = self.env.merge_entities_logically(node, new_line)
                                                if merged_node: new_line = merged_node
                                                merged = True
                                                break
                                        line_obj = new_line
                                    
                                    link_logical_incidence(line_obj, p3)
                                    logger.debug(f"    🔄 [データ還元] 論理証明により {p3.name} が {line_obj.name} 上にある事実を構造化しました。")
                        
                        elif actual_conclusion.fact_type == "EqualAngle_Line":
                            L1, L2, L3, L4 = actual_conclusion.objects
                            self.env.add_equal_angle(L1, L2, L3, L4)

                        elif actual_conclusion.fact_type == "Identical":
                            obj1, obj2 = actual_conclusion.objects
                            
                            # 🌟 修正: マージする際も「真の本体（ルート）」同士を取得する！
                            # （※ get_representative は直前で定義した関数を使用）
                            rep1 = get_representative(obj1)
                            rep2 = get_representative(obj2)
                            
                            # 万が一本体が同じならスキップ（上の防壁で弾かれているはずですが念のため）
                            if rep1 == rep2:
                                continue

                            # 🌟 名前が消える前に、ログ用の文字列表現を作成（本体の名前を使う）
                            name1, name2 = rep1.name, rep2.name
                            
                            # 本体同士を確実にマージする
                            merged_node = self.env.merge_entities_logically(rep1, rep2)
                            if merged_node:
                                # マージ後に名前が変わっても、当時の関係性がわかるように記録
                                actual_conclusion.proof_source += f" (対象: {name1} ≡ {name2})"
                                logger.debug(f"    🔄 [同一性還元] {name1} と {name2} を統合しました。")
                        
                        for obj in actual_conclusion.objects:
                            obj.importance = min(getattr(obj, 'importance', 1.0) + 5.0, 50.0)

        # ==========================================
        # 🚨 デバッグ用: E-Graph 健全性チェック (Sanity Check)
        # ==========================================
        
        zombie_found = False
        
        # 1. env.nodes の中に直接ゾンビが混ざっていないか
        for node in self.env.nodes:
            if getattr(node, '_is_merged_and_dead', False):
                logger.error(f"🧟‍♂️ [環境汚染A] nodes 配列自体にゾンビが存在します: {node.name}")
                zombie_found = True
                
            comp = node.get_best_component()
            if not comp: continue
            
            # 2. 各ノードの subobjects がゾンビを握っていないか
            for obj in comp.subobjects:
                if getattr(obj, '_is_merged_and_dead', False):
                    logger.error(f"🧟‍♂️ [環境汚染B] {node.name} の subobjects にゾンビがいます: {obj.name}")
                    zombie_found = True
                    
            # 3. 各ノードの definitions (親) がゾンビを握っていないか
            for d in comp.definitions:
                for p in d.parents:
                    if getattr(p, '_is_merged_and_dead', False):
                        logger.error(f"🧟‍♂️ [環境汚染C] {node.name} の definitions にゾンビがいます: {p.name}")
                        zombie_found = True

        # 4. prover.facts の中にゾンビが混ざっていないか
        for fact in self.prover.facts:
            for obj in fact.objects:
                if getattr(obj, '_is_merged_and_dead', False):
                    logger.error(f"🧟‍♂️ [環境汚染D] 登録済みの Fact ({fact.fact_type}) の中にゾンビがいます: {obj.name}")
                    zombie_found = True
                    
        # 5. 特殊エンティティ (right_angle など) にゾンビがいないか
        # ※ 実装に合わせて、env が持っている怪しいプロパティを列挙してください
        for special_name in ['zero_angle', 'right_angle', 'parallel_classes']:
            special_node = getattr(self.env, special_name, None)
            if special_node and hasattr(special_node, 'get_best_component'):
                comp = special_node.get_best_component()
                if comp:
                    for d in comp.definitions:
                        for p in d.parents:
                            if getattr(p, '_is_merged_and_dead', False):
                                logger.error(f"🧟‍♂️ [特別枠汚染] env.{special_name} にゾンビがいます: {p.name}")
                                zombie_found = True

        if zombie_found:
            logger.error("🚨 警告: 環境内にゾンビ(マージ済みの古いオブジェクト)の参照が残っています！")
            # 状況がひどい場合は、ここで強制終了(raise RuntimeError)させてもよいです
        # ==========================================

    def run_step(self, num_simulations=40):
        """MCTSのエントリポイント。N回のシミュレーションを経て最適な1手を選ぶ"""
        root = MCTSNode()
        root.untried_actions = self._get_possible_actions(self.env.nodes)
        if not root.untried_actions: return

        # === 1. MCTS ループ ===
        for _ in range(num_simulations):
            node = root
            sim_nodes = list(self.env.nodes)
            
            # Selection (選択: 期待値と未開拓度のバランスで選ぶ)
            while node.is_expanded and node.children:
                node = max(node.children, key=lambda c: c.ucb1())
                Z = self._create_object_from_action(node.action)
                if Z: sim_nodes.append(Z)
                
            # Expansion (展開: まだ試していない手を試す)
            if not node.is_expanded and node.untried_actions:
                action = node.untried_actions.pop()
                child = MCTSNode(action=action, parent=node)
                node.children.append(child)
                node = child
                Z = self._create_object_from_action(action)
                if Z: sim_nodes.append(Z)
                if not node.parent.untried_actions: node.parent.is_expanded = True
            
            # Simulation (シミュレーション: 未来を占う)
            score = self._playout(sim_nodes, depth=3)
            
            # Backpropagation (伝播: スコアを親に伝える)
            while node is not None:
                node.visits += 1
                node.total_score += score
                node = node.parent

        # === 2. 確定 (最も訪問された手を採用) ===
        if not root.children: return
        # ★ UCBではなく、最も探索されて信頼できる手を選ぶのが定石
        best_child = max(root.children, key=lambda c: c.visits)
        best_action = best_child.action
        Z = self._create_object_from_action(best_action)
        
        if not Z: return

        # === 3. 確定した作図を実行 ===
        parents, def_type, name = best_action[0], best_action[1], best_action[2]
        
        Z = create_geo_entity(def_type, parents, name, env=self.env)
        cZ = Z.get_best_component()
        
        logger.debug(f"🤖 [MCTS確定手] {Z.name} を採用 (期待スコア: {best_child.total_score/best_child.visits:.2f}, 探索回数: {best_child.visits})")
        
        total_drop = 0
        for var in self.all_vars:
            nd = cZ.naive_degree
            if cZ.depth > 6 or nd > 40: continue 
            if 1 < nd <= 40:
                td = self.evaluate_numerical_degree(Z, nd, var)
                if cZ.depth + td <= 50: total_drop += max(0, nd - td)

        Z.numerical_degree = nd - total_drop # SVDで判明した真の自由度を記録

        # ==========================================
        # 🌟 マージ判定: キメラ図形の吸収
        # ==========================================
        self.env.nodes.append(Z)

        merged = False
        for node in self.env.nodes:
            if node != Z and self._check_identical_mmp(Z, node):
                logger.debug(f"  🔄 [MMP同一実体マージ] {Z.name} は実は {node.name} と同じだった！")
                
                # ★ 単なるポイ捨てではなく、正規の論理マージを使って完全に統合・成仏させる
                merged_node = self.env.merge_entities_logically(node, Z)
                if merged_node:
                    merged_node.importance += total_drop * 3 + 5.0
                    Z = merged_node
                merged = True
                break
                
        if not merged:
            Z.importance = sum(p.importance for p in parents) / len(parents) + total_drop * 3
            if total_drop > 0: logger.debug(f"  🔥 発見: {Z.name} (Drop: {total_drop})")
            
            
        # ==========================================
        # ★ MMP大発見 (Incidence) の徹底テスト
        # ==========================================
        # ※Zが既存ノードだった場合でも、新しい定義(親)が増えたことで
        #   新たな関係性が見つかる可能性があるので必ず実行する
        self._discover_all_mmp_relations(Z, parents) 
        
        # 論理エンジンの起動
        self._run_logic_step()

        # === 重要度の減衰 (忘却) ===
        for node in self.env.nodes:
            node.importance = max(1.0, min(node.importance * 0.95, 50.0))
            

# ==========================================
# 3. メインエンジン
# ==========================================
class HybridEngine:
    # ★ 修正: 第1引数を initial_nodes から env に変更
    def __init__(self, env, all_vars, target_fact, theorems):
        # 外部(prob_simson等)ですでに構築・連携済みの環境をそのまま使う
        self.env = env  
        
        self.all_vars = all_vars
        self.target_fact = target_fact
        self.theorems = theorems
        
        # 論理エンジンとMCTSエンジンに環境を
        self.prover = LogicProver(self.env, self.theorems)
        self.agent = MCTSSearchEngine(self.env, self.all_vars, self.prover)
        
    def check_target_reached(self):
        """目標（target_fact）が物理的または論理的に達成されているか確認する"""
        import logging
        logger = logging.getLogger("GeometryProver")

        # 1. 論理エンジンが「証明済み」とマークしているか確認
        target_f = next((f for f in self.prover.facts if f == self.target_fact), None)
        if target_f and target_f.is_proven:
            return target_f

        # 2. E-Graphの状態を確認（Collinearの場合）
        if self.target_fact.fact_type == "Collinear":
            pts = self.target_fact.objects
            comps = [p.get_best_component() for p in pts]
            
            if len(comps) == len(pts) and all(comps):
                # ★ 堅牢な積集合の計算（*アンパックによるバグを回避）
                # 最初の点の所属ラインを取得
                common_lines = {obj for obj in comps[0].subobjects if getattr(obj, 'entity_type', '') == "Line"}
                
                # 2つ目以降の点と順番に積集合をとる
                for c in comps[1:]:
                    lines_here = {obj for obj in c.subobjects if getattr(obj, 'entity_type', '') == "Line"}
                    common_lines = common_lines.intersection(lines_here)
                
                if common_lines:
                    # 達成されていた場合
                    self.target_fact.is_proven = True
                    self.target_fact.proof_source = f"E-Graph 構造解析 (同一性からの帰結: {list(common_lines)[0].name})"
                    return self.target_fact
                
                # ==========================================
                # 🌟 最後の確認用デバッグログ（原因特定用）
                # もし失敗した場合、各点が「どの直線の上に乗っていると認識しているか」を出力
                # ==========================================
                logger.debug("--- 🔍 ターゲット(Collinear)達成チェック失敗 ---")
                for p, c in zip(pts, comps):
                    lines = [obj.name for obj in c.subobjects if getattr(obj, 'entity_type', '') == "Line"]
                    logger.debug(f"点 {p.name} が所属している直線: {lines}")
                logger.debug("----------------------------------------------")

            # 🌟 NEW: --- Concyclic（共円）のチェックを追加 ---
        elif self.target_fact.fact_type == "Concyclic":
            pts = self.target_fact.objects
            comps = [p.get_best_component() for p in pts]
            
            if len(comps) == len(pts) and all(comps):
                # 全ての点が共通して所属している「円」を探す
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
        
        # ★ NEW: 探索開始前に、前提条件（初期事実）に関わるノードの重要度を底上げする
        for fact in self.prover.facts:
            if fact.is_proven:
                for obj in fact.objects:
                    if hasattr(obj, 'id'):
                        # 初期設定の点は最低でも 8.0 の重みを持たせる
                        self.env.importance[obj.id] = max(self.env.importance.get(obj.id, 1.0), 8.0)
        
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

# ==========================================
# 実行 (geom.py の末尾)
# ==========================================
if __name__ == "__main__":
    import sys
    import importlib
    
    problem_name = "prob_euler"
    if len(sys.argv) > 1:
        problem_name = sys.argv[1]

    print(f"=== ハイブリッド自動定理証明システム 起動 ===")
    print(f"▶ 読み込み中の問題: {problem_name}")

    # 先に環境(ProofEnvironment)を用意する
    env = ProofEnvironment()

    try:
        prob_module = importlib.import_module(f"problems.{problem_name}")
        # ★ 修正: envを渡し、戻り値を新構造に合わせる
        all_vars, target_fact, initial_facts = prob_module.setup_problem(env)
    except Exception as e:
        print(f"❌ エラー: 問題ファイル 'problems/{problem_name}.py' の読み込みに失敗しました。詳細: {e}")
        sys.exit(1)

    # HybridEngine の初期化 (env を渡すように変更)
    # ※ HybridEngine クラスの __init__ も def __init__(self, env, all_vars, target_fact, theorems): となっている前提です
    engine = HybridEngine(env, all_vars, target_fact, THEOREMS)
    
    for fact in initial_facts:
        engine.prover.add_fact(fact)
        # 初期事実に含まれるノードの重要度を底上げ
        for obj in fact.objects:
            obj.importance = max(obj.importance, 8.0)

    # 初期に与えられた直角や平行をMMPで見つけるため、一度全体をテスト
    print("▶ 初期状態のMMP大発見を実行中...")
    for n in list(env.nodes):
        if n.entity_type in ["Point", "Line"]:
            engine.agent._discover_all_mmp_relations(n, [])

    engine.run(max_steps=10)
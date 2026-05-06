import logging
import os
import itertools

logger = logging.getLogger("GeometryProver")
logger.setLevel(logging.DEBUG)

# 🌟 NEW: ロガーを動的にセットアップする関数
def setup_proof_logger(problem_name: str):
    # すでにハンドラがあればクリア（連続実行時の重複防止）
    if logger.hasHandlers():
        logger.handlers.clear()
        
    # "prob_euler" から "prob_" を取り除いて "euler" にする
    base_name = problem_name.replace("prob_", "") if problem_name.startswith("prob_") else problem_name
    
    # result フォルダが存在しなければ自動作成
    os.makedirs("result", exist_ok=True)
    
    # 出力先のパスを生成
    log_path = os.path.join("result", f"proof_{base_name}.log")
    
    file_handler = logging.FileHandler(log_path, mode='w', encoding='utf-8')
    file_handler.setFormatter(logging.Formatter('%(message)s'))
    logger.addHandler(file_handler)
    
    return log_path

# ==========================================
# 🌟 汎用 E-Graph クエリ関数
# ==========================================
def get_rep(obj):
    """オブジェクトの代表元(Canonical Node)を常に取得する"""
    if obj is None: return None
    while hasattr(obj, '_merged_into') and obj._merged_into is not None:
        obj = obj._merged_into
    return obj


def is_valid_node(obj):
    """ゴースト図形を確実に無視するための絶対フィルター"""
    from logic_core import get_rep # 念のため
    rep = get_rep(obj)
    # 属性名は確実に base_importance を参照する
    return getattr(rep, 'base_importance', 1.0) > 0.0

def get_subentity(obj, entity_types):
    comp = obj.get_best_component()
    if not comp: return set()
    if isinstance(entity_types, str): entity_types = [entity_types]
    result_set = set()
    
    for sub_obj in comp.subobjects:
        rep_sub = get_rep(sub_obj)
        # 🌟 修正: is_valid_node を使用
        if is_valid_node(rep_sub) and getattr(rep_sub, 'entity_type', '') in entity_types:
            result_set.add(rep_sub)
            
    for d in comp.definitions:
        for p in d.parents:
            rep_p = get_rep(p)
            # 🌟 修正: is_valid_node を使用
            if is_valid_node(rep_p) and getattr(rep_p, 'entity_type', '') in entity_types:
                result_set.add(rep_p)
    return result_set


# ==========================================
# 🌟 宣言的スキーマ定義
# ==========================================
class FactTemplate:
    """E-Graphの状態に対するクエリ(前提) または コマンド(結論)"""
    def __init__(self, fact_type, args, target_type=None, sub_type=None):
        self.fact_type = fact_type
        self.args = args               
        self.target_type = target_type 
        self.sub_type = sub_type

class ConstructTemplate:
    """定理適用時に自動でノードを生成・取得するコマンド"""
    def __init__(self, def_type, args, target_type, bind_to):
        self.def_type = def_type       # "LineThroughPoints", "AnglePair" など
        self.args = args               # 親となる変数のリスト ["A", "B"]
        self.target_type = target_type # 生成するノードの型 "Line", "Angle"
        self.bind_to = bind_to         # 取得したノードを入れるバインド変数名

class TheoremDef:
    # skip_numeric 引数を削除！
    def __init__(self, name, entities, patterns, conclusions, constructions=None):
        self.name = name
        self.entities = entities          
        self.patterns = patterns          
        self.constructions = constructions or [] 
        self.conclusions = conclusions

# ==========================================
# 🌟 パターンマッチング (クエリ)
# ==========================================
class Pattern:
    def match(self, current_bind, prover, env):
        raise NotImplementedError

class NotPattern(Pattern):
    """否定パターン(Negation as Failure)。内部のパターンがマッチした場合、棄却する"""
    def __init__(self, pattern: Pattern):
        self.pattern = pattern

    def match(self, current_bind, prover, env):
        # 内部パターンが1つでも状態を yield したらアウト
        # ジェネレータから最初の要素を取ろうと試みる
        generator = self.pattern.match(current_bind.copy(), prover, env)
        try:
            next(generator)
            # マッチした (例外が出なかった) ので棄却
            return
        except StopIteration:
            # マッチしなかった (StopIteration) ので、現在の状態をそのまま通過させる
            yield current_bind

class DistinctPattern(Pattern):
    """バインドされた変数がすべて『互いに異なる実体』であることを保証するパターン"""
    def __init__(self, vars_list):
        self.vars_list = vars_list
        
    def match(self, current_bind, prover, env):
        bound_vars = [v for v in self.vars_list if v in current_bind]
        reps = [get_rep(current_bind[v]) for v in bound_vars]
        if len(set(reps)) == len(reps):
            yield current_bind

class FactPattern(Pattern):
    # 🌟 flip_group=None を追加
    def __init__(self, fact_type, args, target_type=None, sub_type=None, allow_flip=False, flip_group=None):
        self.fact_type = fact_type
        self.args = args
        self.target_type = target_type
        self.sub_type = sub_type
        self.allow_flip = allow_flip
        self.flip_group = flip_group # 🌟 保存

    def match(self, current_bind, prover, env):
        """
        DFS用のジェネレータ関数。
        current_bind を直接書き換え、yield した後に状態を巻き戻す (バックトラッキング)。
        """
        # --- 1. 同一性 (Identical) ---
        if self.fact_type == "Identical":
            v1, v2 = self.args[0], self.args[1]
            
            if v1 in current_bind and v2 in current_bind:
                if get_rep(current_bind[v1]) == get_rep(current_bind[v2]):
                    yield current_bind
            elif v1 in current_bind or v2 in current_bind:
                bound_var, unbound_var = (v1, v2) if v1 in current_bind else (v2, v1)
                target_rep = get_rep(current_bind[bound_var])
                
                for n in env.nodes:
                    if get_rep(n) == target_rep and is_valid_node(n):
                        current_bind[unbound_var] = n
                        yield current_bind
                        del current_bind[unbound_var]
            else:
                nodes = [n for n in env.nodes if getattr(get_rep(n), 'entity_type', '') == self.target_type and is_valid_node(n)]
                for rep in set(get_rep(n) for n in nodes):
                    current_bind[v1] = rep
                    current_bind[v2] = rep
                    yield current_bind
                    del current_bind[v1]
                    del current_bind[v2]

       # --- 2. 所属・接続関係 (Connected) ---
        elif self.fact_type == "Connected":
            child_args = self.args[0] if isinstance(self.args[0], (list, tuple)) else [self.args[0]]
            parent_arg = self.args[1] if len(self.args) > 1 else None
            
            parent_nodes = set()
            if parent_arg and parent_arg in current_bind:
                parent_nodes.add(get_rep(current_bind[parent_arg]))
            else:
                # 🌟 型チェックを緩和: "Line" が "LineThroughPoints" 等に含まれていればOKとする
                for n in env.nodes:
                    rep_n = get_rep(n)
                    e_type = getattr(rep_n, 'entity_type', '')
                    if self.target_type and (self.target_type in e_type or e_type in self.target_type) and is_valid_node(rep_n):
                        parent_nodes.add(rep_n)
                
            for p_node in parent_nodes:
                children = set()
                c_comp = p_node.get_best_component()
                if c_comp:
                    for sub in c_comp.subobjects:
                        rep_sub = get_rep(sub)
                        s_type = getattr(rep_sub, 'entity_type', '')
                        # 🌟 子要素の型チェックも緩和
                        if self.sub_type and (self.sub_type in s_type or s_type in self.sub_type) and is_valid_node(rep_sub): 
                            children.add(rep_sub)
                    for d in c_comp.definitions:
                        for p in d.parents:
                            rep_p = get_rep(p)
                            p_type = getattr(rep_p, 'entity_type', '')
                            # 🌟 親要素の型チェックも緩和
                            if self.sub_type and (self.sub_type in p_type or p_type in self.sub_type) and is_valid_node(rep_p): 
                                children.add(rep_p)
                
                children = list(children)
                if len(children) >= len(child_args):
                    for child_comb in itertools.permutations(children, len(child_args)):
                        conflict = False
                        added_vars = []
                        
                        if parent_arg:
                            if parent_arg in current_bind and current_bind[parent_arg] != p_node: conflict = True
                            elif parent_arg not in current_bind:
                                current_bind[parent_arg] = p_node
                                added_vars.append(parent_arg)
                        
                        if not conflict:
                            for arg_name, child_obj in zip(child_args, child_comb):
                                if arg_name in current_bind and current_bind[arg_name] != child_obj: conflict = True; break
                                elif arg_name not in current_bind:
                                    current_bind[arg_name] = child_obj
                                    added_vars.append(arg_name)
                            
                            if not conflict:
                                yield current_bind
                                
                        for v in added_vars:
                            del current_bind[v]
                    
                # --- 3. 関数・定義関係 (DefinedBy) ---
        elif self.fact_type == "DefinedBy":
            arg_vars = self.args[:-1]
            result_var = self.args[-1]
            
            # DirectionPair や AnglePair の両順列展開を自動化
            unordered_types = ["LengthSq", "Intersection", "CirclesIntersection", "Midpoint", "LineThroughPoints"]
            is_unordered = (self.target_type in unordered_types) or (self.sub_type == "Unordered")
            should_permute = is_unordered or getattr(self, 'allow_flip', False)

            # 🌟 NEW: 定義名(def_type)から実体型(entity_type)へのマッピング
            # これにより O(N) の全探索を廃止し、O(1)の get_subentity を使えるようにする
            entity_map = {
                "AnglePair": "Angle", "DirectionOf": "Direction",
                "LengthSq": "Scalar", "AffineRatio": "Scalar", "Constant": "Scalar",
                "Midpoint": "Point", "Intersection": "Point", "CirclesIntersection": "Point",
                "LineThroughPoints": "Line", "Circumcircle": "Circle",
                "PerpendicularLine": "Line", "ParallelLine": "Line"  # 🌟 この1行を追加！
            }
            actual_entity_type = entity_map.get(self.target_type, self.target_type)

            if result_var in current_bind:
                valid_nodes = [get_rep(current_bind[result_var])]
                
            elif all(v in current_bind for v in arg_vars):
                rep_parents = [get_rep(current_bind[v]) for v in arg_vars]
                        
                # 🌟 FIX: first_parent だけ検索する過剰最適化を廃止し、すべての親から確実に拾う
                valid_nodes = set()
                for p in rep_parents:
                    valid_nodes.update(get_subentity(p, actual_entity_type))
                valid_nodes = list(valid_nodes)
            else:
                valid_nodes = [get_rep(n) for n in env.nodes if getattr(get_rep(n), 'entity_type', '') == actual_entity_type and is_valid_node(n)]
                
            for node in set(valid_nodes):
                comp = node.get_best_component()
                if not comp: continue
                
                for d in comp.definitions:
                    if d.def_type == self.target_type and len(d.parents) == len(arg_vars):
                        reps_parents = [get_rep(p) for p in d.parents]
                        
                        perms = list(itertools.permutations(reps_parents)) if should_permute else [reps_parents]
                        
                        for perm in perms:
                            conflict = False
                            added_vars = []
                            
                            # ==========================================
                            # 🌟 NEW: flip_group による有向角の相対フリップ強制
                            # ==========================================
                            if self.target_type == "AnglePair" and len(arg_vars) == 2:
                                is_flipped = (tuple(perm) != tuple(reps_parents))
                                
                                if is_flipped and not getattr(self, 'allow_flip', False):
                                    conflict = True
                                else:
                                    # 1. グループ全体のフリップ状態の照合と記録
                                    if getattr(self, 'flip_group', None):
                                        group_key = f"__flip_group_{self.flip_group}"
                                        if group_key not in current_bind:
                                            current_bind[group_key] = is_flipped
                                            added_vars.append(group_key)
                                        elif current_bind[group_key] != is_flipped:
                                            conflict = True # グループ内でフリップ状態が不一致なら棄却
                                            
                                    # 2. 個別の Angle 変数のフリップ状態を記録（apply_conclusions で使うため）
                                    if not conflict:
                                        indiv_key = f"__flip_{result_var}"
                                        if indiv_key not in current_bind:
                                            current_bind[indiv_key] = is_flipped
                                            added_vars.append(indiv_key)
                                        elif current_bind[indiv_key] != is_flipped:
                                            conflict = True
                                        
                            # ===========================================
                            
                            if result_var in current_bind and current_bind[result_var] != node: conflict = True
                            elif result_var not in current_bind:
                                current_bind[result_var] = node
                                added_vars.append(result_var)
                                
                            if not conflict:
                                for v_name, p_obj in zip(arg_vars, perm):
                                    if v_name in current_bind and current_bind[v_name] != p_obj: conflict = True; break
                                    elif v_name not in current_bind:
                                        current_bind[v_name] = p_obj
                                        added_vars.append(v_name)
                                        
                                if not conflict: 
                                    yield current_bind
                            
                            for v in added_vars:
                                del current_bind[v]

        # --- 4. 共通要素 (CommonEntity) ---
        elif self.fact_type == "CommonEntity":
            p1_var, p2_var, child_var = self.args
            
            if p1_var in current_bind and p2_var in current_bind:
                p1_node = get_rep(current_bind[p1_var])
                p2_node = get_rep(current_bind[p2_var])
                
                def get_sub_points(node):
                    pts = set()
                    comp = node.get_best_component()
                    if comp:
                        for sub in comp.subobjects:
                            rep_sub = get_rep(sub)
                            # 🌟 修正: pts_on_curve ではなく pts.add を使用し、対象は target_type
                            if getattr(rep_sub, 'entity_type', '') == self.target_type and is_valid_node(rep_sub):
                                pts.add(rep_sub)
                        for d in comp.definitions:
                            for p in d.parents:
                                rep_p = get_rep(p)
                                # 🌟 修正: pts_on_curve ではなく pts.add を使用
                                if getattr(rep_p, 'entity_type', '') == self.target_type and is_valid_node(rep_p):
                                    pts.add(rep_p)
                    # 🌟 修正: 集めた pts をしっかり return する
                    return pts
                    
                # 🌟 修正: 消えていた common_pts の計算式を復活！
                common_pts = get_sub_points(p1_node) & get_sub_points(p2_node)
                
                for pt in common_pts:
                    conflict = False
                    added_vars = []
                    if child_var in current_bind and current_bind[child_var] != pt: conflict = True
                    elif child_var not in current_bind:
                        current_bind[child_var] = pt
                        added_vars.append(child_var)
                        
                    if not conflict:
                        yield current_bind
                        
                    for v in added_vars:
                        del current_bind[v]

        # --- 5. 共線 (Collinear) & 共円 (Concyclic) ---
        elif self.fact_type in ["Collinear", "Concyclic"]:
            target_entity = "Line" if self.fact_type == "Collinear" else "Circle"
            
            if all(v in current_bind for v in self.args):
                p_nodes = [get_rep(current_bind[v]) for v in self.args]
                common_curves = None
                for p in p_nodes:
                    curves = get_subentity(p, target_entity) 
                    if common_curves is None:
                        common_curves = set(curves)
                    else:
                        common_curves &= set(curves)
                        
                if common_curves: 
                    yield current_bind
                    
            else:
                curves = [n for n in env.nodes if getattr(get_rep(n), 'entity_type', '') == target_entity and is_valid_node(n)]
                for curve in set(get_rep(n) for n in curves):
                    pts_on_curve = []
                    comp = curve.get_best_component()
                    if comp:
                        for sub in comp.subobjects:
                            rep_sub = get_rep(sub)
                            # 🌟 修正: is_valid_node を追加
                            if getattr(rep_sub, 'entity_type', '') == "Point" and is_valid_node(rep_sub):
                                pts_on_curve.append(rep_sub)
                        for d in comp.definitions:
                            for p in d.parents:
                                rep_p = get_rep(p)
                                # 🌟 修正: is_valid_node を追加
                                if getattr(rep_p, 'entity_type', '') == "Point" and is_valid_node(rep_p):
                                    pts_on_curve.append(rep_p)
                    
                    pts_on_curve = list(set(pts_on_curve))
                    
                    if len(pts_on_curve) >= len(self.args):
                        for perm in itertools.permutations(pts_on_curve, len(self.args)):
                            conflict = False
                            added_vars = []
                            for v_name, pt_obj in zip(self.args, perm):
                                if v_name in current_bind and current_bind[v_name] != pt_obj: conflict = True; break
                                elif v_name not in current_bind:
                                    current_bind[v_name] = pt_obj
                                    added_vars.append(v_name)
                            
                            if not conflict:
                                yield current_bind
                                
                            for v in added_vars:
                                del current_bind[v]

                # 🌟 B. MMP予想などの論理Factリスト(prover.facts)の確認
                valid_facts = []
                if hasattr(prover, 'facts'):
                    for fact in prover.facts:
                        # 🚨 追加: MMPの予想であり、かつ未証明のものは絶対に推論の根拠にしない！
                        if getattr(fact, 'is_mmp_conjecture', False) and not getattr(fact, 'is_proven', False):
                            continue
                        
                        if fact.fact_type == self.fact_type:
                            valid_facts.append([get_rep(a) for a in getattr(fact, 'objects', [])])
                
                for f_args in valid_facts:
                    if len(f_args) >= len(self.args):
                        for perm in itertools.permutations(f_args, len(self.args)):
                            conflict = False
                            added = []
                            for v_name, obj in zip(self.args, perm):
                                if v_name in current_bind and current_bind[v_name] != obj: conflict = True; break
                                elif v_name not in current_bind:
                                    current_bind[v_name] = obj
                                    added.append(v_name)
                            if not conflict:
                                yield current_bind
                            for v in added:
                                del current_bind[v]

        # --- 6. その他のファクト ---
        else:
            if all(v in current_bind for v in self.args):
                reps = [get_rep(current_bind[v]) for v in self.args]
                fact_exists = False
                
                if hasattr(prover, 'facts'):
                    for fact in prover.facts:
                        # 🚨 追加: 未証明の予想を弾く
                        if getattr(fact, 'is_mmp_conjecture', False) and not getattr(fact, 'is_proven', False):
                            continue
                            
                        if fact.fact_type == self.fact_type:
                            fact_reps = [get_rep(n) for n in getattr(fact, 'objects', [])]
                            if set(reps) == set(fact_reps):
                                fact_exists = True; break
                            
                if not fact_exists:
                    for n in env.nodes:
                        comp = get_rep(n).get_best_component()
                        if comp:
                            for d in comp.definitions:
                                if d.def_type == self.fact_type:
                                    d_reps = [get_rep(p) for p in d.parents]
                                    if set(reps).issubset(set(d_reps)):
                                        fact_exists = True; break
                if fact_exists:
                    yield current_bind
            else:
                valid_facts = []
                if hasattr(prover, 'facts'):
                    for fact in prover.facts:
                        # 🚨 追加: 未証明の予想を弾く
                        if getattr(fact, 'is_mmp_conjecture', False) and not getattr(fact, 'is_proven', False):
                            continue
                            
                        if fact.fact_type == self.fact_type:
                            valid_facts.append([get_rep(a) for a in getattr(fact, 'objects', [])])
                            
                for n in env.nodes:
                    comp = get_rep(n).get_best_component()
                    if comp:
                        for d in comp.definitions:
                            if d.def_type == self.fact_type:
                                valid_facts.append([get_rep(p) for p in d.parents])
                                
                for f_args in valid_facts:
                    if len(f_args) >= len(self.args):
                        for perm in itertools.permutations(f_args, len(self.args)):
                            conflict = False
                            added = []
                            for v_name, obj in zip(self.args, perm):
                                if v_name in current_bind and current_bind[v_name] != obj:
                                    conflict = True; break
                                elif v_name not in current_bind:
                                    current_bind[v_name] = obj
                                    added.append(v_name)
                            if not conflict:
                                yield current_bind
                            for v in added:
                                del current_bind[v]

class CustomPattern(Pattern):
    """任意のPython関数で変数を束縛・フィルタするパターン"""
    def __init__(self, match_func):
        self.match_func = match_func

    def match(self, current_bind, prover, env):
        partial_binds = self.match_func(env, current_bind)
        if not partial_binds: return
        
        for pb in partial_binds:
            conflict = False
            added_vars = []
            for k, v in pb.items():
                rep_v = get_rep(v)
                if k in current_bind and current_bind[k] != rep_v:
                    conflict = True; break
                elif k not in current_bind:
                    current_bind[k] = rep_v
                    added_vars.append(k)
                    
            if not conflict:
                yield current_bind
                
            # バックトラッキング
            for k in added_vars:
                del current_bind[k]

# ==========================================
# 🌟 汎用ルールエンジン (UniversalRuleEngine)
# ==========================================
class UniversalRuleEngine:
    def __init__(self, env, prover):
        self.env = env
        self.prover = prover

    def _evaluate_patterns(self, theorem_name, patterns):
        """深さ優先探索 (DFS) とバックトラッキングによる超高速パターンマッチ"""
        initial_bind = {}
        if hasattr(self.env, 'right_angle'):
            from logic_core import get_rep
            initial_bind["Ang90"] = get_rep(self.env.right_angle)
        if hasattr(self.env, 'zero_angle'):
            from logic_core import get_rep
            initial_bind["Ang0"] = get_rep(self.env.zero_angle)
            
        survival_counts = [0] * len(patterns)
        
        # 🌟 追跡したい図形の名前（ミケルの定理なら C, D, E, M など）
        # ここに含まれる文字列がバインドされているルートが消滅した時だけ警告を出します
        TARGET_NAMES = ["C", "D", "E", "M"] 
            
        def dfs(pattern_idx, current_bind):
            if pattern_idx == len(patterns):
                yield current_bind.copy()
                return
            
            pattern = patterns[pattern_idx]
            matched_any = False
            
            # match 関数(ジェネレータ)から次々と候補を受け取る
            for bound_dict in pattern.match(current_bind, self.prover, self.env):
                matched_any = True
                survival_counts[pattern_idx] += 1
                yield from dfs(pattern_idx + 1, bound_dict)
                
            # ==========================================
            # 🚨 デバッグトラップ: 期待ルートの消滅を検知 (完全精密版)
            # ==========================================
            if not matched_any and theorem_name == "円周角の定理の逆":
                # 点の変数名リスト
                point_keys = ["P_Apex1", "P_Apex2", "P_Base1", "P_Base2"]
                
                # 現在バインドされている点オブジェクトの「正確な名前」だけを抽出
                bound_pts = [getattr(current_bind[k], 'name', '') for k in point_keys if k in current_bind]
                
                # 1つ以上点がバインドされており、かつ「ターゲット以外の点（AやFなど）」が混ざっていないかチェック
                if set(bound_pts) == set(TARGET_NAMES):
                    import logging
                    logger = logging.getLogger("GeometryProver")
                    
                    if hasattr(pattern, 'fact_type'):
                        pat_desc = f"{pattern.__class__.__name__}({pattern.fact_type}, {getattr(pattern, 'target_type', '')})"
                    elif hasattr(pattern, 'vars_list'):
                        pat_desc = f"Distinct({pattern.vars_list})"
                    else:
                        pat_desc = pattern.__class__.__name__
                        
                    bound_names = {k: getattr(v, 'name', str(v)) for k, v in current_bind.items()}
                    logger.debug(f"  🚨 [狙撃デバッグ] 条件 {pattern_idx + 1}: {pat_desc} で期待ルートが消滅！")
                    logger.debug(f"       -> 直前のバインド状態: {bound_names}")
            # ==========================================
                
        results = list(dfs(0, initial_bind))
        
        import logging
        logger = logging.getLogger("GeometryProver")
        for i, count in enumerate(survival_counts):
            pat = patterns[i]
            if hasattr(pat, 'fact_type'): pat_desc = f"FactPattern({pat.fact_type}, {getattr(pat, 'target_type', '')})"
            elif hasattr(pat, 'vars_list'): pat_desc = "Distinct"
            elif hasattr(pat, 'pattern'): pat_desc = "Not"
            else: pat_desc = pat.__class__.__name__
                
            logger.debug(f"      [条件 {i+1}: {pat_desc}] 生き残り探索数: {count}")
            if count == 0: break
            
        return results

    def _execute_constructions(self, constructions, bind):
        """宣言的作図の実行 (共通の親を持つか探し、無ければ作る)"""
        from mmp_core import create_geo_entity, link_logical_incidence
        from logic_core import get_subentity
        
        for constr in constructions:
            parents = [bind[arg] for arg in constr.args]
            if len(set(parents)) < len(parents): return False # 自己ループ防止

            # 🌟 修正: 勝手に入れ替えるのをやめ、不正な順序なら定理の適用自体をキャンセル
            if constr.def_type == "AnglePair" and len(parents) == 2:
                from mmp_core import is_canonical_angle_order
                if not is_canonical_angle_order(parents[0], parents[1]):
                    # E-Graphの純粋性を守るため、順序を反転させてCanonicalにする
                    parents = [parents[1], parents[0]]
                    # 🌟 【最重要】反転させたという事実をバインドに「裏タグ」として記録する
                    bind[f"__flip_{constr.bind_to}"] = True
                else:
                    bind[f"__flip_{constr.bind_to}"] = False

            if constr.def_type == "LineThroughPoints" and len(parents) == 2:
                common_lines = get_subentity(parents[0], "Line") & get_subentity(parents[1], "Line")
                if common_lines:
                    bind[constr.bind_to] = list(common_lines)[0]
                    continue
                
            # O(1)の積集合で候補を絞る
            common = get_subentity(parents[0], constr.target_type)
            for p in parents[1:]:
                common &= get_subentity(p, constr.target_type)
                
            found_obj = None
            unordered_types = ["LengthSq", "Intersection", "CirclesIntersection", "Midpoint", "LineThroughPoints"]
            is_unordered = constr.def_type in unordered_types
            
            # 定義の順序まで厳格に照合する
            for obj in common:
                comp = obj.get_best_component()
                if comp:
                    for d in comp.definitions:
                        if d.def_type == constr.def_type:
                            if is_unordered:
                                # 直線や中点などは、親の順序が違っても（A, B と B, A）同一とみなす
                                if set(d.parents) == set(parents):
                                    found_obj = obj; break
                            else:
                                # AnglePair (有向角) などは、親の順序まで完全に一致しないと弾く
                                if d.parents == parents: 
                                    found_obj = obj; break
                if found_obj: break
                
            if found_obj:
                bind[constr.bind_to] = found_obj 
            else:
                name_suffix = "_".join([getattr(p, 'name', str(id(p))[-4:]) for p in parents])
                name = f"{constr.def_type}_{name_suffix}_(Auto)"
                new_obj = create_geo_entity(constr.def_type, parents, name=name, env=self.env)
                self.env.nodes.append(new_obj)
                # 親と自動リンク
                for p in parents: link_logical_incidence(p, new_obj)
                bind[constr.bind_to] = new_obj
        return True

    def apply_conclusions(self, theorem_name, conclusions, bind):
        """結論の実行 (サイレントキラー可視化版)"""
        from mmp_core import link_logical_incidence
        from logic_core import get_rep, get_subentity
        import logging
        logger = logging.getLogger("GeometryProver")
        applied_anything = False
        
        for conc in conclusions:
            objects = [bind[arg] for arg in conc.args]
            reps = [get_rep(o) for o in objects]
            
            if conc.fact_type == "Identical" and len(reps) == 2:
                # 🌟 NEW: Angleマージの場合、フリップ状態（裏タグ）が一致するかチェック
                if getattr(reps[0], 'entity_type', '') == "Angle":
                    flip1 = bind.get(f"__flip_{conc.args[0]}", False)
                    flip2 = bind.get(f"__flip_{conc.args[1]}", False)
                    if flip1 != flip2:
                        logger.debug(f"    ⏭️ フリップ状態の不一致 (θ ≡ -θ) のためマージをスキップ: {reps[0].name}")
                        continue
                        
                if reps[0] == reps[1]:
                    logger.debug(f"    ⏭️ 既に同一ノードのためマージをスキップ: {reps[0].name}")
                    continue

                # 🌟 ログの拡張: 根拠となった共円の点情報を取得
                evidence_str = ""
                if theorem_name == "円周角の定理":
                    # Apex1, Apex2, Base1, Base2 の代表元の名前を抽出
                    p_names = [get_rep(bind[k]).name for k in ["Apex1", "Apex2", "Base1", "Base2"] if k in bind]
                    evidence_str = f" [根拠: 共円({', '.join(p_names)})]"

                # ログ出力時に evidence_str を付加する
                logger.info(f"  🟢 [マージ実行] {reps[0].name} ≡ {reps[1].name} (理由: {theorem_name}){evidence_str}")
                
                merged = self.env.merge_entities_logically(reps[0], reps[1])
                if merged:
                    logger.debug(f"  🟢 [マージ実行] {reps[0].name} ≡ {reps[1].name} (理由: {theorem_name})")
                    applied_anything = True
                    self.prover.record_trace(theorem_name, f"{reps[0].name} ≡ {reps[1].name}")

            elif conc.fact_type == "Connected":
                child_args = conc.args[0] if isinstance(conc.args[0], list) else [conc.args[0]]
                parent_obj = bind[conc.args[1]]
                for c_arg in child_args:
                    child_obj = bind[c_arg]
                    if parent_obj not in get_subentity(child_obj, conc.target_type):
                        link_logical_incidence(parent_obj, child_obj)
                        logger.debug(f"  🟢 [リンク] {child_obj.name} ∈ {parent_obj.name} (理由: {theorem_name})")
                        applied_anything = True
                        self.prover.record_trace(theorem_name, f"{child_obj.name} ∈ {parent_obj.name}")
                    else:
                        # 🌟 NEW: 既にリンク済みの処理を可視化
                        logger.debug(f"    ⏭️ 既にリンク済みのためスキップ: {child_obj.name} ∈ {parent_obj.name}")

            elif conc.fact_type in ["Collinear", "Concyclic"]:
                search_type = "Line" if conc.fact_type == "Collinear" else "Circle"
                def_type = "LineThroughPoints" if conc.fact_type == "Collinear" else "Circumcircle"
                
                common_curves = get_subentity(reps[0], search_type)
                for pt in reps[1:]: common_curves &= get_subentity(pt, search_type)
                
                if not common_curves:
                    from mmp_core import create_geo_entity
                    name = f"{def_type}_(Auto)"
                    new_curve = create_geo_entity(def_type, reps[:3] if search_type=="Circle" else reps[:2], name=name, env=self.env)
                    self.env.nodes.append(new_curve)
                    for pt in reps: link_logical_incidence(pt, new_curve)
                    logger.debug(f"  🟢 [マクロ構築] {', '.join(p.name for p in reps)} ∈ {new_curve.name} (理由: {theorem_name})")
                    applied_anything = True
                    self.prover.record_trace(theorem_name, f"{conc.fact_type}({', '.join(p.name for p in reps)})")
                else:
                    # 🌟 NEW: 既に共円/共線である場合のスキップを可視化
                    curve_name = list(common_curves)[0].name
                    logger.debug(f"    ⏭️ 既に {search_type} ({curve_name}) 上に存在するためスキップ: {', '.join(p.name for p in reps)}")

        return applied_anything

    def run_all(self, theorems):
        import logging
        logger = logging.getLogger("GeometryProver")
        applied_any_in_this_run = False
        
        for theorem in theorems:
            logger.debug(f"  ▶ 評価開始: {theorem.name}")
            bindings = self._evaluate_patterns(theorem.name, theorem.patterns)
            
            if not bindings:
                logger.debug(f"    => ❌ マッチなし")
                continue

            valid_count = 0
            for bind in bindings:
                type_ok = True
                for k, v in bind.items():
                    if k in theorem.entities and theorem.entities[k] != "Any":
                        if getattr(v, 'entity_type', '') != theorem.entities[k]:
                            # 🌟 NEW: 型チェックの失敗を可視化
                            logger.debug(f"    ❌ 型チェックで弾かれました ({k} が {theorem.entities[k]} ではない): {v.name}")
                            type_ok = False; break
                if not type_ok: continue

                if not self._execute_constructions(theorem.constructions, bind): 
                    # 🌟 NEW: 作図の失敗(角度の順序違反など)を可視化
                    logger.debug(f"    ❌ 作図(Constructions)フェーズで拒否されました: { {k: getattr(v, 'name', v) for k, v in bind.items()} }")
                    continue

                if self.apply_conclusions(theorem.name, theorem.conclusions, bind):
                    valid_count += 1
                    applied_any_in_this_run = True

            if valid_count > 0:
                logger.debug(f"    => 🎉 {valid_count} 件の新しい結論を適用！")
                
        return applied_any_in_this_run

# ==========================================
# 🌟 Proof Environment & Prover
# ==========================================
class ProofEnvironment:
    # 🌟 修正1: 引数に enable_numerical_debug=False を追加
    def __init__(self, enable_numerical_debug=False):
        self.nodes = []           
        
        # 🌟 デバッグ用の変数を初期化
        self.enable_numerical_debug = enable_numerical_debug
        self.all_vars = None
        
        from mmp_core import GeoEntity, LogicalComponent
        self.zero_angle = GeoEntity("Angle", "Parallel_0")
        self.zero_angle.components.append(LogicalComponent())
        self.zero_angle.importance = 10.0
        
        self.right_angle = GeoEntity("Angle", "Perpendicular_90")
        self.right_angle.components.append(LogicalComponent())
        self.right_angle.importance = 10.0
        
        self.nodes.extend([self.zero_angle, self.right_angle])

    def merge_entities_logically(self, rep1, rep2):
        entity1, entity2 = get_rep(rep1), get_rep(rep2)
        if entity1 == entity2: return None
        if entity1 not in self.nodes or entity2 not in self.nodes: return None

        # --- 実行時デバッグ ---
        if getattr(self, 'enable_numerical_debug', False) and getattr(self, 'all_vars', None):
            from mmp_core import verify_identical_runtime
            if not verify_identical_runtime(entity1, entity2, self.all_vars):
                v1_val = getattr(entity1, '_debug_v', 'Unknown')
                v2_val = getattr(entity2, '_debug_v', 'Unknown')
                err_trace = getattr(entity1, '_calc_err_trace', '') # 🌟 エラーを取得
                
                err_msg = f"🚨 [FATAL ERROR] 数値検証FAIL: {entity1.name} ≡ {entity2.name}\n   -> v1_coords = {v1_val}\n   -> v2_coords = {v2_val}"
                
                # 🌟 真の原因をコンソールに叩き出す
                if err_trace:
                    err_msg += f"\n\n🔥 [計算中の内部例外 (これが真の原因です!)]:\n{err_trace}"
                    
                print(err_msg)
                raise RuntimeError(err_msg)
                
        # 🌟 修正2: rep1, rep2 を使って get_rep を呼び出す
        entity1, entity2 = get_rep(rep1), get_rep(rep2)
        
        if entity1 == entity2: return None
        if entity1 not in self.nodes or entity2 not in self.nodes: return None
            
        for node in self.nodes:
            for comp in node.components:
                if entity2 in comp.subobjects:
                    comp.subobjects.remove(entity2)
                    comp.subobjects.add(entity1)
                
                new_defs = set()
                for d in comp.definitions:
                    if entity2 in d.parents:
                        new_parents = [entity1 if p == entity2 else p for p in d.parents]
                        from mmp_core import Definition
                        new_defs.add(Definition(d.def_type, new_parents, d.naive_degree, d.depth))
                    else:
                        new_defs.add(d)
                comp.definitions = new_defs

        entity1.merge_numerical(entity2)
        while len(entity1.components) > 1:
            entity1.prove_components_equal(0, 1)
            
        entity1.importance = max(getattr(entity1, 'importance', 1.0), getattr(entity2, 'importance', 1.0))
        self.nodes.remove(entity2)
        entity2._merged_into = entity1
        entity2._is_merged_and_dead = True
        return entity1

class Fact:
    """MMP予想(🟡)を保持するためだけの一時的なラッパー (論理エンジンからは分離)"""
    def __init__(self, fact_type, objects):
        self.fact_type = fact_type
        self.objects = objects
        self.is_proven = False
        self.is_mmp_conjecture = True
        self.conjecture_score = 0.0
        self.proof_source = ""
    def __eq__(self, other):
        if not isinstance(other, Fact) or self.fact_type != other.fact_type: return False
        if self.fact_type in ["Concyclic", "Collinear", "Identical", "Parallel"]: return set(self.objects) == set(other.objects)
        return self.objects == other.objects

class LogicProver:
    """人間のための証明ログ(Trace)の管理とMMP予想の保管"""
    def __init__(self, env, theorems):
        self.env = env
        self.theorems = theorems
        self.trace_log = [] 
        self.facts = [] # MMP予想用
        
    def record_trace(self, theorem_name, conclusion_str):
        log_entry = f"{conclusion_str} <= {theorem_name}"
        if log_entry not in self.trace_log:
            self.trace_log.append(log_entry)

    def print_proof_trace(self, target_fact=None):
        logger.debug("\n【証明のトレース（E-Graph書き換え連鎖）】")
        for i, log in enumerate(self.trace_log):
            logger.debug(f" {i+1}. 🟢 {log}")
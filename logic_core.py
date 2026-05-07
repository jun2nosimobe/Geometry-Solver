import logging
import os
import itertools

logger = logging.getLogger("GeometryProver")

# ==========================================
# 🌟 ロガーのセットアップ (IS_DEBUG 制御対応)
# ==========================================
def setup_proof_logger(problem_name: str, is_debug: bool = False):
    if logger.hasHandlers():
        logger.handlers.clear()
        
    base_name = problem_name.replace("prob_", "") if problem_name.startswith("prob_") else problem_name
    os.makedirs("result", exist_ok=True)
    log_path = os.path.join("result", f"proof_{base_name}.log")
    
    file_handler = logging.FileHandler(log_path, mode='w', encoding='utf-8')
    file_handler.setFormatter(logging.Formatter('%(message)s'))
    logger.addHandler(file_handler)
    
    # 🌟 DEBUG=False の時は INFO のみ出力し、ログスパムを消滅させる
    logger.setLevel(logging.DEBUG if is_debug else logging.INFO)
    
    return log_path

# ==========================================
# 🌟 汎用 E-Graph クエリ関数
# ==========================================
def get_rep(obj):
    if obj is None: return None
    while hasattr(obj, '_merged_into') and obj._merged_into is not None:
        obj = obj._merged_into
    return obj

def is_valid_node(obj):
    rep = get_rep(obj)
    return getattr(rep, 'base_importance', 1.0) > 0.0

def get_subentity(obj, entity_types):
    obj = get_rep(obj) # 🌟 修正: 最初に必ず代表元を取る！これがないと死んだノードを参照します
    comp = obj.get_best_component()
    if not comp: return set()
    if isinstance(entity_types, str): entity_types = [entity_types]
    result_set = set()
    
    for sub_obj in comp.subobjects:
        rep_sub = get_rep(sub_obj)
        if is_valid_node(rep_sub) and getattr(rep_sub, 'entity_type', '') in entity_types:
            result_set.add(rep_sub)
            
    for d in comp.definitions:
        for p in d.parents:
            rep_p = get_rep(p)
            if is_valid_node(rep_p) and getattr(rep_p, 'entity_type', '') in entity_types:
                result_set.add(rep_p)
    return result_set


# ==========================================
# 🌟 宣言的スキーマ定義
# ==========================================
class FactTemplate:
    def __init__(self, fact_type, args, target_type=None, sub_type=None):
        self.fact_type = fact_type
        self.args = args               
        self.target_type = target_type 
        self.sub_type = sub_type

class ConstructTemplate:
    def __init__(self, def_type, args, target_type, bind_to):
        self.def_type = def_type
        self.args = args
        self.target_type = target_type
        self.bind_to = bind_to

class TheoremDef:
    def __init__(self, name, entities, patterns, conclusions, constructions=None):
        self.name = name
        self.entities = entities          
        self.patterns = patterns          
        self.constructions = constructions or [] 
        self.conclusions = conclusions

# ==========================================
# 🌟 パターンマッチング (クエリ基底クラス)
# ==========================================
class Pattern:
    def match(self, current_bind, prover, env):
        raise NotImplementedError

    def _try_bind_and_yield(self, current_bind, new_bindings):
        """🌟 共通化: 変数の束縛とバックトラッキングを一手に引き受けるヘルパー"""
        conflict = False
        added_vars = []
        for k, v in new_bindings.items():
            if k in current_bind and current_bind[k] != v:
                conflict = True
                break
            elif k not in current_bind:
                current_bind[k] = v
                added_vars.append(k)
                
        if not conflict:
            yield current_bind
            
        for k in added_vars:
            del current_bind[k]

class NotPattern(Pattern):
    def __init__(self, pattern: Pattern):
        self.pattern = pattern

    def match(self, current_bind, prover, env):
        generator = self.pattern.match(current_bind.copy(), prover, env)
        try:
            next(generator)
            return
        except StopIteration:
            yield current_bind

class DistinctPattern(Pattern):
    def __init__(self, vars_list):
        self.vars_list = vars_list
        
    def match(self, current_bind, prover, env):
        bound_vars = [v for v in self.vars_list if v in current_bind]
        reps = [get_rep(current_bind[v]) for v in bound_vars]
        if len(set(reps)) == len(reps):
            yield current_bind

class CustomPattern(Pattern):
    def __init__(self, match_func):
        self.match_func = match_func

    def match(self, current_bind, prover, env):
        partial_binds = self.match_func(env, current_bind)
        if not partial_binds: return
        for pb in partial_binds:
            new_binds = {k: get_rep(v) for k, v in pb.items()}
            yield from self._try_bind_and_yield(current_bind, new_binds)

# ==========================================
# 🌟 ディスパッチャ化された FactPattern
# ==========================================
class FactPattern(Pattern):
    def __init__(self, fact_type, args, target_type=None, sub_type=None, allow_flip=False, flip_group=None):
        self.fact_type = fact_type
        self.args = args
        self.target_type = target_type
        self.sub_type = sub_type
        self.allow_flip = allow_flip
        self.flip_group = flip_group

    def match(self, current_bind, prover, env):
        # 🌟 探索スコープの取得
        search_nodes = env.active_search_nodes if getattr(env, 'active_search_nodes', None) is not None else env.nodes
        
        """ディスパッチャ: 種類に応じて専用の検索メソッドに委譲する"""
        if self.fact_type == "Identical":
            yield from self._match_identical(current_bind, prover, env, search_nodes) # 🌟 search_nodes を渡す
        elif self.fact_type == "Connected":
            yield from self._match_connected(current_bind, prover, env, search_nodes)
        elif self.fact_type == "DefinedBy":
            yield from self._match_defined_by(current_bind, prover, env, search_nodes)
        elif self.fact_type == "CommonEntity":
            yield from self._match_common_entity(current_bind, prover, env, search_nodes)
        elif self.fact_type in ["Collinear", "Concyclic"]:
            yield from self._match_curve_macro(current_bind, prover, env, search_nodes)
        else:
            yield from self._match_generic(current_bind, prover, env, search_nodes)

    # ---------------------------------------------------------
    # 処理分割メソッド群
    # ---------------------------------------------------------
    def _match_identical(self, current_bind, prover, env, search_nodes):
        v1, v2 = self.args[0], self.args[1]
        
        if v1 in current_bind and v2 in current_bind:
            if get_rep(current_bind[v1]) == get_rep(current_bind[v2]):
                yield current_bind
        elif v1 in current_bind or v2 in current_bind:
            bound_var, unbound_var = (v1, v2) if v1 in current_bind else (v2, v1)
            target_rep = get_rep(current_bind[bound_var])
            for n in search_nodes: # 🌟 env.nodes を置換
                if get_rep(n) == target_rep and is_valid_node(n):
                    yield from self._try_bind_and_yield(current_bind, {unbound_var: n})
        else:
            nodes = [n for n in search_nodes if getattr(get_rep(n), 'entity_type', '') == self.target_type and is_valid_node(n)] # 🌟 env.nodes を置換
            for rep in set(get_rep(n) for n in nodes):
                yield from self._try_bind_and_yield(current_bind, {v1: rep, v2: rep})

    def _match_connected(self, current_bind, prover, env, search_nodes):
        child_args = self.args[0] if isinstance(self.args[0], (list, tuple)) else [self.args[0]]
        parent_arg = self.args[1] if len(self.args) > 1 else None
        
        parent_nodes = set()
        if parent_arg and parent_arg in current_bind:
            parent_nodes.add(get_rep(current_bind[parent_arg]))
        else:
            for n in search_nodes: # 🌟 env.nodes を置換
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
                    if self.sub_type and (self.sub_type in s_type or s_type in self.sub_type) and is_valid_node(rep_sub): 
                        children.add(rep_sub)
                for d in c_comp.definitions:
                    for p in d.parents:
                        rep_p = get_rep(p)
                        p_type = getattr(rep_p, 'entity_type', '')
                        if self.sub_type and (self.sub_type in p_type or p_type in self.sub_type) and is_valid_node(rep_p): 
                            children.add(rep_p)
            
            children = list(children)
            if len(children) >= len(child_args):
                for child_comb in itertools.permutations(children, len(child_args)):
                    new_binds = {}
                    if parent_arg: new_binds[parent_arg] = p_node
                    for arg_name, child_obj in zip(child_args, child_comb):
                        new_binds[arg_name] = child_obj
                        
                    yield from self._try_bind_and_yield(current_bind, new_binds)

    def _match_defined_by(self, current_bind, prover, env, search_nodes):
        arg_vars = self.args[:-1]
        result_var = self.args[-1]
        
        unordered_types = ["LengthSq", "Intersection", "CirclesIntersection", "Midpoint", "LineThroughPoints", "Circumcircle"]
        is_unordered = (self.target_type in unordered_types) or (self.sub_type == "Unordered")
        should_permute = is_unordered or getattr(self, 'allow_flip', False)

        entity_map = {
            "AnglePair": "Angle", "DirectionOf": "Direction",
            "LengthSq": "Scalar", "AffineRatio": "Scalar", "Constant": "Scalar",
            "Midpoint": "Point", "Intersection": "Point", "CirclesIntersection": "Point",
            "LineThroughPoints": "Line", "Circumcircle": "Circle",
            "PerpendicularLine": "Line", "ParallelLine": "Line"
        }
        actual_entity_type = entity_map.get(self.target_type, self.target_type)

        if result_var in current_bind:
            valid_nodes = [get_rep(current_bind[result_var])]
        elif all(v in current_bind for v in arg_vars):
            rep_parents = [get_rep(current_bind[v]) for v in arg_vars]
            valid_nodes = set()
            for p in rep_parents:
                valid_nodes.update(get_subentity(p, actual_entity_type))
            valid_nodes = list(valid_nodes)
        else:
            # 🌟 env.nodes を置換
            valid_nodes = [get_rep(n) for n in search_nodes if getattr(get_rep(n), 'entity_type', '') == actual_entity_type and is_valid_node(n)]
            
        for node in set(valid_nodes):
            comp = node.get_best_component()
            if not comp: continue
            
            for d in comp.definitions:
                if d.def_type == self.target_type and len(d.parents) == len(arg_vars):
                    reps_parents = [get_rep(p) for p in d.parents]
                    perms = list(itertools.permutations(reps_parents)) if should_permute else [reps_parents]
                    
                    for perm in perms:
                        new_binds = {result_var: node}
                        
                        if self.target_type == "AnglePair" and len(arg_vars) == 2:
                            is_flipped = (tuple(perm) != tuple(reps_parents))
                            if is_flipped and not getattr(self, 'allow_flip', False): continue
                            
                            if getattr(self, 'flip_group', None):
                                group_key = f"__flip_group_{self.flip_group}"
                                if group_key in current_bind and current_bind[group_key] != is_flipped:
                                    continue
                                new_binds[group_key] = is_flipped
                                
                            indiv_key = f"__flip_{result_var}"
                            if indiv_key in current_bind and current_bind[indiv_key] != is_flipped:
                                continue
                            new_binds[indiv_key] = is_flipped
                            
                        for v_name, p_obj in zip(arg_vars, perm):
                            new_binds[v_name] = p_obj
                            
                        yield from self._try_bind_and_yield(current_bind, new_binds)

    def _match_common_entity(self, current_bind, prover, env, search_nodes):
        p1_var, p2_var, child_var = self.args
        if p1_var in current_bind and p2_var in current_bind:
            p1_node, p2_node = get_rep(current_bind[p1_var]), get_rep(current_bind[p2_var])
            
            def get_sub_points(node):
                pts = set()
                comp = node.get_best_component()
                if comp:
                    for sub in comp.subobjects:
                        rep_sub = get_rep(sub)
                        if getattr(rep_sub, 'entity_type', '') == self.target_type and is_valid_node(rep_sub): pts.add(rep_sub)
                    for d in comp.definitions:
                        for p in d.parents:
                            rep_p = get_rep(p)
                            if getattr(rep_p, 'entity_type', '') == self.target_type and is_valid_node(rep_p): pts.add(rep_p)
                return pts
                
            common_pts = get_sub_points(p1_node) & get_sub_points(p2_node)
            for pt in common_pts:
                yield from self._try_bind_and_yield(current_bind, {child_var: pt})

    def _match_curve_macro(self, current_bind, prover, env, search_nodes):
        target_entity = "Line" if self.fact_type == "Collinear" else "Circle"
        
        if all(v in current_bind for v in self.args):
            p_nodes = [get_rep(current_bind[v]) for v in self.args]
            common_curves = None
            for p in p_nodes:
                curves = get_subentity(p, target_entity) 
                if common_curves is None: common_curves = set(curves)
                else: common_curves &= set(curves)
            if common_curves: 
                yield current_bind
        else:
            curves = [n for n in search_nodes if getattr(get_rep(n), 'entity_type', '') == target_entity and is_valid_node(n)]
            for curve in set(get_rep(n) for n in curves):
                pts_on_curve = []
                comp = curve.get_best_component()
                if comp:
                    for sub in comp.subobjects:
                        rep_sub = get_rep(sub)
                        if getattr(rep_sub, 'entity_type', '') == "Point" and is_valid_node(rep_sub): pts_on_curve.append(rep_sub)
                    for d in comp.definitions:
                        for p in d.parents:
                            rep_p = get_rep(p)
                            if getattr(rep_p, 'entity_type', '') == "Point" and is_valid_node(rep_p): pts_on_curve.append(rep_p)
                
                pts_on_curve = list(set(pts_on_curve))
                if len(pts_on_curve) >= len(self.args):
                    for perm in itertools.permutations(pts_on_curve, len(self.args)):
                        new_binds = {v_name: pt_obj for v_name, pt_obj in zip(self.args, perm)}
                        yield from self._try_bind_and_yield(current_bind, new_binds)

            yield from self._match_generic(current_bind, prover, env, search_nodes)

    def _match_generic(self, current_bind, prover, env, search_nodes):
        valid_facts = []
        if hasattr(prover, 'facts'):
            for fact in prover.facts:
                if getattr(fact, 'is_mmp_conjecture', False) and not getattr(fact, 'is_proven', False): continue
                if fact.fact_type == self.fact_type:
                    valid_facts.append([get_rep(a) for a in getattr(fact, 'objects', [])])
                    
        if not all(v in current_bind for v in self.args):
            for n in search_nodes: 
                # 🌟 FIX: ここに is_valid_node のチェックを追加！
                if not is_valid_node(n): continue
                
                comp = get_rep(n).get_best_component()
                if comp:
                    for d in comp.definitions:
                        if d.def_type == self.fact_type:
                            valid_facts.append([get_rep(p) for p in d.parents])
                            
        if all(v in current_bind for v in self.args):
            reps = [get_rep(current_bind[v]) for v in self.args]
            if any(set(reps).issubset(set(f_args)) for f_args in valid_facts):
                yield current_bind
        else:
            for f_args in valid_facts:
                if len(f_args) >= len(self.args):
                    for perm in itertools.permutations(f_args, len(self.args)):
                        new_binds = {v_name: obj for v_name, obj in zip(self.args, perm)}
                        yield from self._try_bind_and_yield(current_bind, new_binds)


# ==========================================
# 🌟 ディスパッチャ化されたルールエンジン
# ==========================================
class UniversalRuleEngine:
    def __init__(self, env, prover):
        self.env = env
        self.prover = prover

    def _evaluate_patterns(self, theorem_name, patterns):
        initial_bind = {}
        if hasattr(self.env, 'right_angle'): initial_bind["Ang90"] = get_rep(self.env.right_angle)
        if hasattr(self.env, 'zero_angle'): initial_bind["Ang0"] = get_rep(self.env.zero_angle)
            
        survival_counts = [0] * len(patterns)
            
        def dfs(pattern_idx, current_bind):
            if pattern_idx == len(patterns):
                yield current_bind.copy()
                return
            
            pattern = patterns[pattern_idx]
            for bound_dict in pattern.match(current_bind, self.prover, self.env):
                survival_counts[pattern_idx] += 1
                yield from dfs(pattern_idx + 1, bound_dict)
                
        results = list(dfs(0, initial_bind))
        
        # DEBUGモードの時だけ詳細な探索数を計算して出力
        if logger.isEnabledFor(logging.DEBUG):
            for i, count in enumerate(survival_counts):
                pat = patterns[i]
                pat_desc = pat.__class__.__name__
                if hasattr(pat, 'fact_type'): pat_desc = f"FactPattern({pat.fact_type}, {getattr(pat, 'target_type', '')})"
                elif hasattr(pat, 'vars_list'): pat_desc = "Distinct"
                elif hasattr(pat, 'pattern'): pat_desc = "Not"
                
                logger.debug(f"      [条件 {i+1}: {pat_desc}] 生き残り探索数: {count}")
                if count == 0: break
            
        return results

    def _execute_constructions(self, theorem_name, constructions, bind):
        from mmp_core import create_geo_entity, link_logical_incidence
        from logic_core import get_rep
        
        for constr in constructions:
            parents = [get_rep(bind[arg]) for arg in constr.args]
            
            if len(set(parents)) < len(parents): return False

            if constr.def_type == "AnglePair" and len(parents) == 2:
                from mmp_core import is_canonical_angle_order
                if not is_canonical_angle_order(parents[0], parents[1]):
                    parents = [parents[1], parents[0]]
                    bind[f"__flip_{constr.bind_to}"] = True
                else:
                    bind[f"__flip_{constr.bind_to}"] = False

            if constr.def_type == "LineThroughPoints" and len(parents) == 2:
                common_lines = get_subentity(parents[0], "Line") & get_subentity(parents[1], "Line")
                if common_lines:
                    bind[constr.bind_to] = list(common_lines)[0]
                    continue
                
            common = get_subentity(parents[0], constr.target_type)
            for p in parents[1:]: common &= get_subentity(p, constr.target_type)
                
            found_obj = None
            is_unordered = constr.def_type in ["LengthSq", "Intersection", "CirclesIntersection", "Midpoint", "LineThroughPoints", "Circumcircle"]
            
            for obj in common:
                comp = obj.get_best_component()
                if comp:
                    for d in comp.definitions:
                        if d.def_type == constr.def_type:
                            # 🌟 修正: 親を必ず最新の代表元に変換してから比較する！
                            rep_d_parents = [get_rep(p) for p in d.parents] 
                            
                            if is_unordered:
                                if set(rep_d_parents) == set(parents):
                                    found_obj = obj; break
                            else:
                                if rep_d_parents == parents: 
                                    found_obj = obj; break
                if found_obj: break
                
            # ==========================================
            # 🌟 絶対フォールバック検索も同様に修正
            # ==========================================
            if not found_obj:
                for node in self.env.nodes:
                    if not is_valid_node(node): continue
                    comp = get_rep(node).get_best_component()
                    if not comp: continue
                    for d in comp.definitions:
                        if d.def_type == constr.def_type:
                            # 🌟 修正: ここでも最新の代表元に変換
                            rep_d_parents = [get_rep(p) for p in d.parents]
                            
                            if (is_unordered and set(rep_d_parents) == set(parents)) or (not is_unordered and rep_d_parents == parents):
                                found_obj = get_rep(node)
                                break
                    if found_obj: break
            if found_obj:
                bind[constr.bind_to] = found_obj 
            else:
                name_suffix = "_".join([getattr(p, 'name', str(id(p))[-4:]) for p in parents])
                new_obj = create_geo_entity(constr.def_type, parents, name=f"{constr.def_type}_{name_suffix}_(Auto)", env=self.env)
                
                # 🌟 修正: theorem_name を使うようにする
                new_obj.created_by_theorem = theorem_name
                
                self.env.nodes.append(new_obj)
                for p in parents: link_logical_incidence(p, new_obj)
                bind[constr.bind_to] = new_obj
        return True

    def apply_conclusions(self, theorem_name, conclusions, bind):
        """ディスパッチャ: 結論の実行を種類ごとに振り分ける"""
        applied_anything = False
        for conc in conclusions:
            if conc.fact_type == "Identical":
                if self._apply_identical(theorem_name, conc, bind): applied_anything = True
            elif conc.fact_type == "Connected":
                if self._apply_connected(theorem_name, conc, bind): applied_anything = True
            elif conc.fact_type in ["Collinear", "Concyclic"]:
                if self._apply_curve_macro(theorem_name, conc, bind): applied_anything = True
        return applied_anything

    def _apply_congruence_closure(self):
        """🌟 E-Graph の究極奥義：親が同じになった子要素たちを自動的にマージする（合同閉包）"""
        from logic_core import get_rep, is_valid_node
        changed = False
        def_map = {}
        
        for node in self.env.nodes:
            if not is_valid_node(node): continue
            rep = get_rep(node)
            comp = rep.get_best_component()
            if not comp: continue
            
            for d in comp.definitions:
                # ==========================================
                # 🌟 NEW: 特異点ガード (Big Crunch 防止)
                # 1. 親がない(独立したGiven図形)場合はデフラグしない
                if not d.parents:
                    continue
                # 2. 関数ではなく単なる「型ラベル」の場合はデフラグしない
                if d.def_type in ["Point", "Line", "Circle", "Given", "Free", "Direction", "Angle", "Scalar"]:
                    continue
                # ==========================================

                # 親を最新の代表元にしてシグネチャ（設計図）を作る
                rep_parents = tuple(get_rep(p) for p in d.parents)
                
                # 順不同図形の場合はソートして同一視する
                unordered_types = ["LengthSq", "Intersection", "CirclesIntersection", "Midpoint", "LineThroughPoints", "Circumcircle"]
                if d.def_type in unordered_types:
                    rep_parents = tuple(sorted(rep_parents, key=lambda x: getattr(x, 'name', str(id(x)))))
                    
                signature = (d.def_type, rep_parents)
                
                # もし全く同じ設計図を持つ別の図形がすでに見つかっていれば、マージ！
                if signature in def_map:
                    existing_node = def_map[signature]
                    if get_rep(existing_node) != rep:
                        logger.debug(f"  🔄 [合同閉包・デフラグ] 同一の親を持つノードを統合: {rep.name} ≡ {get_rep(existing_node).name}")
                        merged = self.env.merge_entities_logically(existing_node, rep)
                        if merged:
                            changed = True
                            break # マージされたらこのノードの処理は終了し次へ
                else:
                    def_map[signature] = rep
                    
        return changed

    # ---------------------------------------------------------
    # 結論適用 メソッド群
    # ---------------------------------------------------------
    def _apply_identical(self, theorem_name, conc, bind):
        reps = [get_rep(bind[arg]) for arg in conc.args]
        if len(reps) != 2: return False
        
        if getattr(reps[0], 'entity_type', '') == "Angle":
            flip1 = bind.get(f"__flip_{conc.args[0]}", False)
            flip2 = bind.get(f"__flip_{conc.args[1]}", False)
            if flip1 != flip2:
                logger.debug(f"    ⏭️ フリップ状態の不一致 (θ ≡ -θ) のためマージをスキップ: {reps[0].name}")
                return False
                
        if reps[0] == reps[1]:
            logger.debug(f"    ⏭️ 既に同一ノードのためマージをスキップ: {reps[0].name}")
            return False

        evidence_str = ""
        if theorem_name == "円周角の定理":
            p_names = [get_rep(bind[k]).name for k in ["Apex1", "Apex2", "Base1", "Base2"] if k in bind]
            evidence_str = f" [根拠: 共円({', '.join(p_names)})]"

        logger.info(f"  🟢 [マージ実行] {reps[0].name} ≡ {reps[1].name} (理由: {theorem_name}){evidence_str}")
        merged = self.env.merge_entities_logically(reps[0], reps[1])
        if merged:
            self.prover.record_trace(theorem_name, f"{reps[0].name} ≡ {reps[1].name}")
            return True
        return False

    def _apply_connected(self, theorem_name, conc, bind):
        from mmp_core import link_logical_incidence
        child_args = conc.args[0] if isinstance(conc.args[0], list) else [conc.args[0]]
        
        # 🌟 修正: 親ノードを必ず最新の代表元にする
        parent_obj = get_rep(bind[conc.args[1]])
        applied = False
        
        for c_arg in child_args:
            # 🌟 修正: 子ノードも必ず最新の代表元にする
            child_obj = get_rep(bind[c_arg])
            
            # 念のための安全装置 (マージの過程でNoneになっていたらスキップ)
            if not parent_obj or not child_obj:
                continue

            if parent_obj not in get_subentity(child_obj, conc.target_type):
                # 🌟 常に最新の代表元同士でリンクを張る
                link_logical_incidence(parent_obj, child_obj)
                logger.info(f"  🟢 [リンク] {child_obj.name} ∈ {parent_obj.name} (理由: {theorem_name})")
                self.prover.record_trace(theorem_name, f"{child_obj.name} ∈ {parent_obj.name}")
                applied = True
            else:
                logger.debug(f"    ⏭️ 既にリンク済みのためスキップ: {child_obj.name} ∈ {parent_obj.name}")
        return applied

    def _apply_curve_macro(self, theorem_name, conc, bind):
        from mmp_core import create_geo_entity, link_logical_incidence
        reps = [get_rep(bind[arg]) for arg in conc.args]
        search_type = "Line" if conc.fact_type == "Collinear" else "Circle"
        def_type = "LineThroughPoints" if conc.fact_type == "Collinear" else "Circumcircle"
        
        base_count = 3 if search_type == "Circle" else 2
        
        # 1. まず、対象の全点がすでに通っている曲線があるかチェック
        common_curves = get_subentity(reps[0], search_type)
        for pt in reps[1:]: 
            common_curves &= get_subentity(pt, search_type)
        
        if common_curves:
            logger.debug(f"    ⏭️ 既に {search_type} ({list(common_curves)[0].name}) 上に存在するためスキップ: {', '.join(p.name for p in reps)}")
            return False
            
        # 2. ベースとなる点を通る曲線が既に存在するかチェック
        base_curves = get_subentity(reps[0], search_type)
        for pt in reps[1:base_count]:
            base_curves &= get_subentity(pt, search_type)
            
        # ==========================================
        # 🌟 NEW: リンク漏れ対策の「絶対フォールバック検索」
        # ==========================================
        if not base_curves:
            for node in self.env.nodes:
                if not is_valid_node(node): continue
                if getattr(get_rep(node), 'entity_type', '') == search_type:
                    comp = get_rep(node).get_best_component()
                    if comp:
                        for d in comp.definitions:
                            if d.def_type == def_type:
                                rep_parents = [get_rep(p) for p in d.parents]
                                # ベース点がすべて親に含まれているか（順不同）
                                if set(reps[:base_count]).issubset(set(rep_parents)):
                                    base_curves = {get_rep(node)}
                                    break
                if base_curves: break
        # ==========================================

        if base_curves:
            # 既存の円(または直線)に残りの点をリンクするだけ！
            target_curve = list(base_curves)[0]
            for pt in reps[base_count:]:
                link_logical_incidence(pt, target_curve)
                
            logger.info(f"  🟢 [マクロ拡張] {', '.join(p.name for p in reps[base_count:])} を既存の {target_curve.name} に追加 (理由: {theorem_name})")
            self.prover.record_trace(theorem_name, f"{conc.fact_type}({', '.join(p.name for p in reps)})")
            return True
            
        # 3. 完全に新規作成する
        new_curve = create_geo_entity(def_type, reps[:base_count], name=f"{def_type}_(Auto)", env=self.env)
        
        # 🌟 NEW: 生成元を正しく記録（Unknownを撲滅）
        new_curve.created_by_theorem = theorem_name 
        
        # 🌟 NEW: env.nodes への二重登録を絶対に防ぐガード
        if new_curve not in self.env.nodes:
            self.env.nodes.append(new_curve)
        
        for pt in reps: 
            link_logical_incidence(pt, new_curve)
            
        logger.info(f"  🟢 [マクロ構築] {', '.join(p.name for p in reps)} ∈ {new_curve.name} (理由: {theorem_name})")
        self.prover.record_trace(theorem_name, f"{conc.fact_type}({', '.join(p.name for p in reps)})")
        return True

    def run_all(self, theorems):
        applied_any_in_this_run = False
        for theorem in theorems:
            logger.info(f"  ▶ 評価開始: {theorem.name}")
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
                            logger.debug(f"    ❌ 型チェック弾き ({k} が {theorem.entities[k]} ではない): {v.name}")
                            type_ok = False; break
                if not type_ok: continue

                # 🌟 修正: 第1引数に theorem.name を追加して渡す！
                if not self._execute_constructions(theorem.name, theorem.constructions, bind): 
                    logger.debug(f"    ❌ 作図フェーズ拒否: { {k: getattr(v, 'name', v) for k, v in bind.items()} }")
                    continue

                if self.apply_conclusions(theorem.name, theorem.conclusions, bind):
                    valid_count += 1
                    applied_any_in_this_run = True

            if valid_count > 0:
                logger.info(f"    => 🎉 {valid_count} 件の新しい結論を適用！")
                
        # ==========================================
        # 🌟 NEW: 定理の適用が一通り終わるたびに、合同閉包でグラフを圧縮(デフラグ)する
        # ==========================================
        if self._apply_congruence_closure():
            applied_any_in_this_run = True
                
        return applied_any_in_this_run

# ==========================================
# 🌟 Proof Environment & Prover
# ==========================================
class ProofEnvironment:
    def __init__(self, enable_numerical_debug=False):
        self.nodes = [] # 🌟 これは常に「グローバルな全図形」を保持する
        self.active_search_nodes = None # 🌟 NEW: 局所探索のスコープ制限用
        
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

    # 🌟 修正案: 基本図形の「宇宙崩壊」をフラグなしでも防ぐ
        is_basic = entity1.entity_type in ["Point", "Line"]
        should_verify = getattr(self, 'enable_numerical_debug', False) or is_basic

        #should_verify=True
        if should_verify and getattr(self, 'all_vars', None):
            from mmp_core import verify_identical_runtime
            # 検証実行
            if not verify_identical_runtime(entity1, entity2, self.all_vars):
            # 💡 ログを詳細に出す
                print(f"❌ [拒否] 数値的に不一致: {entity1.name}({entity1.entity_type}) vs {entity2.name}({entity2.entity_type})")
                logger.info(f"❌ [拒否] 数値的に不一致: {entity1.name}({entity1.entity_type}) vs {entity2.name}({entity2.entity_type})")
                return None # 🌟 修正: raise ではなく、単にマージを拒否して推論を続けさせるのが安全
                
        entity1, entity2 = get_rep(rep1), get_rep(rep2)
        if entity1 == entity2: return None
        if entity1 not in self.nodes or entity2 not in self.nodes: return None
            
        for node in self.nodes:
            for comp in node.components:
                # [既存] 他のノードが entity2 を子として持っていた場合の更新
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

        # ==========================================
        # 🌟 NEW: entity2 自身が持っていた子要素(subobjects)を、すべて entity1 に引き継ぐ！
        # ==========================================
        e1_comp = entity1.get_best_component()
        e2_comp = entity2.get_best_component()
        if e1_comp and e2_comp:
            for child in e2_comp.subobjects:
                e1_comp.subobjects.add(child)
                # 子要素側から見た親のリンクも entity1 に向ける（念のため）
                child_comp = get_rep(child).get_best_component()
                if child_comp:
                    for d in child_comp.definitions:
                        if entity2 in d.parents:
                            d.parents = [entity1 if p == entity2 else p for p in d.parents]
        # ==========================================

        entity1.merge_numerical(entity2)
        while len(entity1.components) > 1:
            entity1.prove_components_equal(0, 1)
            
        entity1.importance = max(getattr(entity1, 'importance', 1.0), getattr(entity2, 'importance', 1.0))
        self.nodes.remove(entity2)
        entity2._merged_into = entity1
        entity2._is_merged_and_dead = True
        return entity1

class Fact:
    def __init__(self, fact_type, objects):
        self.fact_type = fact_type
        self.objects = objects
        self.is_proven = False
        self.is_mmp_conjecture = True
        self.conjecture_score = 0.0
        self.proof_source = ""

    def __str__(self):
        # オブジェクトが名前を持っていれば名前を、なければ文字列表現を使う
        obj_names = ", ".join([getattr(o, 'name', str(o)) for o in self.objects])
        return f"{self.fact_type}({obj_names})"
        
    def __repr__(self):
        return self.__str__()
        
    def __eq__(self, other):
        if not isinstance(other, Fact) or self.fact_type != other.fact_type: return False
        if self.fact_type in ["Concyclic", "Collinear", "Identical", "Parallel"]: return set(self.objects) == set(other.objects)
        return self.objects == other.objects

class LogicProver:
    def __init__(self, env, theorems):
        self.env = env
        self.theorems = theorems
        self.trace_log = [] 
        self.facts = []
        
    def record_trace(self, theorem_name, conclusion_str):
        log_entry = f"{conclusion_str} <= {theorem_name}"
        if log_entry not in self.trace_log:
            self.trace_log.append(log_entry)

    def print_proof_trace(self, target_fact=None):
        logger.info("\n【証明のトレース（E-Graph書き換え連鎖）】")
        for i, log in enumerate(self.trace_log):
            logger.info(f" {i+1}. 🟢 {log}")
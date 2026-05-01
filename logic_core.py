import logging
import itertools

logger = logging.getLogger("GeometryProver")
logger.setLevel(logging.DEBUG)
if not logger.handlers:
    file_handler = logging.FileHandler('proof.log', mode='w', encoding='utf-8')
    file_handler.setFormatter(logging.Formatter('%(message)s'))
    logger.addHandler(file_handler)

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
        # 内部パターンを評価
        matches = self.pattern.match(current_bind, prover, env)
        # もし「現在のバインディングを満たした上で」マッチするものが1つでもあれば、条件不成立(棄却)
        if matches:
            return [] 
        # マッチしなかった場合は、現在のバインディングをそのまま次に流す
        return [current_bind]



class DistinctPattern(Pattern):
    """バインドされた変数がすべて『互いに異なる実体』であることを保証するパターン"""
    def __init__(self, vars_list):
        self.vars_list = vars_list
        
    def match(self, current_bind, prover, env):
        # 🌟 FIX: 「現在バインド済みの変数」だけを抽出してチェックする
        bound_vars = [v for v in self.vars_list if v in current_bind]
        
        reps = [get_rep(current_bind[v]) for v in bound_vars]
        if len(set(reps)) == len(reps):
            return [current_bind]
        return []

class FactPattern(Pattern):
    def __init__(self, fact_type, args, target_type=None, sub_type=None):
        self.fact_type = fact_type
        self.args = args
        self.target_type = target_type
        self.sub_type = sub_type

    def match(self, current_bind, prover, env):
        results = []
        
        # --- 1. 同一性 (Identical) ---
        if self.fact_type == "Identical":
            v1, v2 = self.args[0], self.args[1]
            
            # ケースA: 両方とも既にバインドされている（例: 円周角の逆での確認）
            if v1 in current_bind and v2 in current_bind:
                if get_rep(current_bind[v1]) == get_rep(current_bind[v2]):
                    results.append(current_bind.copy())
            
            # ケースB: 片方だけバインドされている（代入伝播）
            elif v1 in current_bind:
                new_bind = current_bind.copy()
                new_bind[v2] = get_rep(current_bind[v1])
                results.append(new_bind)
            elif v2 in current_bind:
                new_bind = current_bind.copy()
                new_bind[v1] = get_rep(current_bind[v2])
                results.append(new_bind)
            
            # ケースC: 両方とも未バインド（E-Graphから同一ノードを拾って両方に入れる）
            else:
                nodes = [n for n in env.nodes if getattr(get_rep(n), 'entity_type', '') == self.target_type and is_valid_node(n)]
                for rep in set(get_rep(n) for n in nodes):
                    new_bind = current_bind.copy()
                    new_bind[v1] = rep
                    new_bind[v2] = rep
                    results.append(new_bind)

        # --- 2. 所属・接続関係 (Connected) ---
        elif self.fact_type == "Connected":
            child_args = self.args[0] if isinstance(self.args[0], (list, tuple)) else [self.args[0]]
            parent_arg = self.args[1] if len(self.args) > 1 else None
            
            # 🌟 究極の最適化: 親(直線)だけでなく、子(点)がバインド済みならそこから逆引きする！
            parent_nodes = set()
            
            if parent_arg and parent_arg in current_bind:
                parent_nodes.add(get_rep(current_bind[parent_arg]))
            else:
                # バインド済みの子(点)があるか探す
                bound_children = [current_bind[arg] for arg in child_args if arg in current_bind]
                if bound_children:
                    # バインド済みの子を含む直線だけを取得する
                    first_child = get_rep(bound_children[0])
                    # 子の所属先(親)を探す
                    possible_parents = get_subentity(first_child, self.target_type) 
                    for p in possible_parents:
                        parent_nodes.add(get_rep(p))
                else:
                    # 親も子も未バインドなら仕方なく全探索
                    for n in env.nodes:
                        if getattr(get_rep(n), 'entity_type', '') == self.target_type and is_valid_node(n):
                            parent_nodes.add(get_rep(n))
                
            for p_node in parent_nodes:
                # 🌟 安全な要素取得: subobjects と parents の両方から無理やり集める
                children = set()
                c_comp = p_node.get_best_component()
                if c_comp:
                    for sub in c_comp.subobjects:
                        if getattr(get_rep(sub), 'entity_type', '') == self.sub_type: children.add(get_rep(sub))
                    for d in c_comp.definitions:
                        for p in d.parents:
                            if getattr(get_rep(p), 'entity_type', '') == self.sub_type: children.add(get_rep(p))
                
                children = list(children)
                if len(children) >= len(child_args):
                    for child_comb in itertools.permutations(children, len(child_args)):
                        new_bind = current_bind.copy()
                        conflict = False
                        
                        if parent_arg:
                            if parent_arg in new_bind and new_bind[parent_arg] != p_node: conflict = True
                            else: new_bind[parent_arg] = p_node
                        
                        if not conflict:
                            for arg_name, child_obj in zip(child_args, child_comb):
                                if arg_name in new_bind and new_bind[arg_name] != child_obj: conflict = True; break
                                new_bind[arg_name] = child_obj
                            if not conflict: results.append(new_bind)

        # --- 3. 関数・定義関係 (DefinedBy) ---
        elif self.fact_type == "DefinedBy":
            arg_vars = self.args[:-1]
            result_var = self.args[-1]
            
            unordered_types = ["LengthSq", "Intersection", "CirclesIntersection", "Midpoint"]
            is_unordered = (self.target_type in unordered_types) or (self.sub_type == "Unordered")

            # 🌟 劇的最適化 1: ターゲット変数が特定済みなら、O(1) で直撃する (Reverse Search)
            if result_var in current_bind:
                valid_nodes = [get_rep(current_bind[result_var])]
                
            # 🌟 劇的最適化 2: 親変数がすべて特定済みなら、親の所属から O(1) で探す (Forward Search)
            elif all(v in current_bind for v in arg_vars):
                rep_parents = [get_rep(current_bind[v]) for v in arg_vars]
                
                # 🌟 FIX: 検索時も AnglePair の引数を正規化順序に揃える
                if self.target_type == "AnglePair" and len(rep_parents) == 2:
                    from mmp_core import is_canonical_angle_order
                    if not is_canonical_angle_order(parents[0], parents[1]):
                        parents = [parents[1], parents[0]]
                        rep_parents = [rep_parents[1], rep_parents[0]]
                        
                first_parent = rep_parents[0]
                valid_nodes = list(get_subentity(first_parent, self.target_type))
                
            # 両方未特定の場合のみ全探索
            else:
                valid_nodes = [get_rep(n) for n in env.nodes if is_valid_node(n)]
                
            for node in set(valid_nodes):
                comp = node.get_best_component()
                if not comp: continue
                
                for d in comp.definitions:
                    if d.def_type == self.target_type and len(d.parents) == len(arg_vars):
                        reps_parents = [get_rep(p) for p in d.parents]
                        perms = list(itertools.permutations(reps_parents)) if is_unordered else [reps_parents]
                        
                        for perm in perms:
                            new_bind = current_bind.copy()
                            conflict = False
                            
                            if result_var in new_bind and new_bind[result_var] != node: conflict = True
                            else: new_bind[result_var] = node
                                
                            if not conflict:
                                for v_name, p_obj in zip(arg_vars, perm):
                                    if v_name in new_bind and new_bind[v_name] != p_obj: conflict = True; break
                                    new_bind[v_name] = p_obj
                                    
                            if not conflict: results.append(new_bind)

        # --- 4. マクロ (Collinear / Concyclic) ---
        elif self.fact_type in ["Collinear", "Concyclic"]:
            search_type = "Line" if self.fact_type == "Collinear" else "Circle"
            curves = [n for n in env.nodes if getattr(get_rep(n), 'entity_type', '') == search_type and is_valid_node(n)]
            for curve in set(get_rep(c) for c in curves):
                # 🌟 FIX: 直線/円上の点を取得
                pts = list(get_subentity(curve, "Point"))
                if len(pts) >= len(self.args):
                    for pts_comb in itertools.permutations(pts, len(self.args)):
                        new_bind = current_bind.copy()
                        conflict = False
                        for arg_name, pt_obj in zip(self.args, pts_comb):
                            if arg_name in new_bind and new_bind[arg_name] != pt_obj: conflict = True; break
                            new_bind[arg_name] = pt_obj
                        if not conflict: results.append(new_bind)

        # --- 5. 共通要素の取得 (CommonEntity) ---
        elif self.fact_type == "CommonEntity":
            # 例: ["L_CA", "L_CB", "C"] (直線L_CAとL_CBの共通点Cを取得する)
            p1_var, p2_var, child_var = self.args
            
            p1 = current_bind.get(p1_var)
            p2 = current_bind.get(p2_var)
            if not p1 or not p2: return [] # 親が特定されていなければ探索不能
            
            # E-Graph の機能を使って、それぞれの図形が持つ要素を O(1) で取得
            children1 = get_subentity(p1, self.target_type)
            children2 = get_subentity(p2, self.target_type)
            
            # 積集合(&)をとることで、一瞬で「交点」や「共通の直線」が求まる
            common = children1 & children2
            
            for child in common:
                new_bind = current_bind.copy()
                if child_var in new_bind and new_bind[child_var] != child:
                    continue # 矛盾する場合は破棄
                new_bind[child_var] = child
                results.append(new_bind)

        return results

class CustomPattern(Pattern):
    """任意のPython関数で変数を束縛・フィルタするパターン"""
    def __init__(self, match_func):
        self.match_func = match_func

    def match(self, current_bind, prover, env):
        partial_binds = self.match_func(env, current_bind)
        if not partial_binds: return []
        
        results = []
        for pb in partial_binds:
            new_bind = current_bind.copy()
            conflict = False
            for k, v in pb.items():
                rep_v = get_rep(v)
                if k in new_bind and new_bind[k] != rep_v: conflict = True; break
                new_bind[k] = rep_v
            if not conflict: results.append(new_bind)
        return results

# ==========================================
# 🌟 汎用ルールエンジン (UniversalRuleEngine)
# ==========================================
class UniversalRuleEngine:
    def __init__(self, env, prover):
        self.env = env
        self.prover = prover

    def _evaluate_patterns(self, theorem_name, patterns):
        bindings = [{}] 
        for idx, pattern in enumerate(patterns):
            new_bindings = []
            for bind in bindings:
                new_bindings.extend(pattern.match(bind, self.prover, self.env))
            
            # 重複排除
            unique = []
            for b in new_bindings:
                if b not in unique: unique.append(b)
            bindings = unique
            
            # 🌟 DEBUG: 各条件ごとの生き残りバインディング数をログ出力
            if hasattr(pattern, 'fact_type'):
                logger.debug(f"      [条件 {idx+1}: {pattern.fact_type}] 生き残り: {len(bindings)}件")
            elif isinstance(pattern, NotPattern):
                logger.debug(f"      [条件 {idx+1}: NotPattern] 生き残り: {len(bindings)}件")
            else:
                logger.debug(f"      [条件 {idx+1}: Custom] 生き残り: {len(bindings)}件")

            if not bindings: 
                break # この時点で0件なら、以降の条件は評価しない
                
        return bindings

    def _execute_constructions(self, constructions, bind):
        """宣言的作図の実行 (共通の親を持つか探し、無ければ作る)"""
        from mmp_core import create_geo_entity, link_logical_incidence
        import itertools
        
        for constr in constructions:
            parents = [bind[arg] for arg in constr.args]
            if len(set(parents)) < len(parents): return False # 自己ループ防止

            if constr.def_type == "AnglePair" and len(parents) == 2:
                from mmp_core import is_canonical_angle_order
                if not is_canonical_angle_order(parents[0], parents[1]):
                    parents = [parents[1], parents[0]]

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
            # 🌟 FIX: AnglePair は除外し、LineThroughPoints を追加！
            unordered_types = ["LengthSq", "Intersection", "CirclesIntersection", "Midpoint", "LineThroughPoints"]
            is_unordered = constr.def_type in unordered_types
            
            # 🌟 究極の修正: 適当に list(common)[0] を拾うのをやめ、定義の順序まで厳格に照合する
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
        """結論の実行"""
        from mmp_core import link_logical_incidence
        applied_anything = False
        
        for conc in conclusions:
            objects = [bind[arg] for arg in conc.args]
            reps = [get_rep(o) for o in objects]
            
            if conc.fact_type == "Identical" and len(reps) == 2:
                if reps[0] == reps[1]: continue
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

        return applied_anything


    def run_all(self, theorems):
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
                            type_ok = False; break
                if not type_ok: continue

                if not self._execute_constructions(theorem.constructions, bind): continue

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
    def __init__(self):
        self.nodes = []           
        
        from mmp_core import GeoEntity, LogicalComponent
        self.zero_angle = GeoEntity("Angle", "Parallel_0")
        self.zero_angle.components.append(LogicalComponent())
        self.zero_angle.importance = 10.0
        
        self.right_angle = GeoEntity("Angle", "Perpendicular_90")
        self.right_angle.components.append(LogicalComponent())
        self.right_angle.importance = 10.0
        
        self.nodes.extend([self.zero_angle, self.right_angle])

    def merge_entities_logically(self, entity1, entity2):
        entity1, entity2 = get_rep(entity1), get_rep(entity2)
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
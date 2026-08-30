import logging
import os
import sys
import itertools
import time
import heapq
from enum import Enum
from collections import deque
from proof_manager import Fact
from mmp_core import Definition, GeoEntity, LogicalComponent

logger = logging.getLogger("GeometryProver")

class RelativeTimeFormatter(logging.Formatter):
    def __init__(self, fmt):
        super().__init__(fmt)
        self.start_time = time.time()  # ロガー初期化時を0秒とする

    def format(self, record):
        elapsed = time.time() - self.start_time
        mins, secs = divmod(elapsed, 60)
        # 00:00.000 の形式で relative_time 属性を作成
        record.relative_time = f"{int(mins):02d}:{secs:06.3f}"
        return super().format(record)

def setup_proof_logger(problem_name: str, is_debug: bool = False):
    if logger.hasHandlers(): logger.handlers.clear()
    base_name = problem_name.replace("prob_", "") if problem_name.startswith("prob_") else problem_name
    os.makedirs("result", exist_ok=True)
    log_path = os.path.join("result", f"proof_{base_name}.log")
    
    # 🌟 FIX: ミリ秒付きのタイムスタンプを付与するフォーマッタ
    formatter = RelativeTimeFormatter('[%(relative_time)s] %(message)s')
    
    file_handler = logging.FileHandler(log_path, mode='w', encoding='utf-8')
    file_handler.setFormatter(formatter)
    logger.addHandler(file_handler)
    stream_handler = logging.StreamHandler(sys.stdout)
    stream_handler.setFormatter(formatter)
    logger.addHandler(stream_handler)
    logger.setLevel(logging.DEBUG if is_debug else logging.INFO)
    return log_path

def get_subentity(node, target_type=None):
    res = set()
    rep_node = node.get_rep() if hasattr(node, 'get_rep') else node
    def is_match(obj):
        if not target_type: return True
        e_type = getattr(obj, 'entity_type', '')
        if not e_type: return False
        if isinstance(target_type, (list, tuple)): return any(t in e_type for t in target_type)
        return target_type in e_type

    for comp in getattr(rep_node, 'components', []):
        for sub in comp.subobjects:
            sub_rep = sub.get_rep() if hasattr(sub, 'get_rep') else sub
            if is_match(sub_rep) and getattr(sub_rep, 'is_valid', lambda: True)(): res.add(sub_rep)
        for d in comp.definitions:
            for p in d.parents:
                p_rep = p.get_rep() if hasattr(p, 'get_rep') else p
                if is_match(p_rep) and getattr(p_rep, 'is_valid', lambda: True)(): res.add(p_rep)
    return res

class FactTemplate:
    def __init__(self, fact_type, args, target_type=None, sub_type=None):
        self.fact_type = fact_type; self.args = args; self.target_type = target_type; self.sub_type = sub_type

class ConstructTemplate:
    def __init__(self, def_type, args, target_type, bind_to):
        self.def_type = def_type; self.args = args; self.target_type = target_type; self.bind_to = bind_to

class TheoremDef:
    def __init__(self, name, entities, patterns, conclusions, constructions=None):
        self.name = name; self.entities = entities; self.patterns = patterns; self.constructions = constructions or []; self.conclusions = conclusions

class Pattern:
    def match(self, current_bind, prover, env): raise NotImplementedError
    def _try_bind_and_yield(self, current_bind, new_bindings, used_fact=None):
        conflict = False
        added_vars = []
        for k, v in new_bindings.items():
            if k in current_bind and current_bind[k] != v:
                conflict = True; break
            elif k not in current_bind:
                current_bind[k] = v; added_vars.append(k)
        if not conflict:
            added_fact = False
            if used_fact:
                if '__facts__' not in current_bind: current_bind['__facts__'] = []  
                if used_fact not in current_bind['__facts__']:
                    current_bind['__facts__'].append(used_fact); added_fact = True
            yield current_bind
            if added_fact:
                current_bind['__facts__'].remove(used_fact)
                if not current_bind['__facts__']: del current_bind['__facts__']
        for k in added_vars: del current_bind[k]

class NotPattern(Pattern):
    def __init__(self, pattern: Pattern): self.pattern = pattern
    def match(self, current_bind, prover, env):
        generator = self.pattern.match(current_bind.copy(), prover, env)
        try: next(generator); return
        except StopIteration: yield current_bind

class DistinctPattern(Pattern):
    def __init__(self, vars_list): self.vars_list = vars_list
    def match(self, current_bind, prover, env):
        bound_vars = [v for v in self.vars_list if v in current_bind]
        reps = [current_bind[v].get_rep() if hasattr(current_bind[v], 'get_rep') else current_bind[v] for v in bound_vars]
        if len(set(reps)) == len(reps): yield current_bind

class CustomPattern(Pattern):
    def __init__(self, match_func): self.match_func = match_func
    def match(self, current_bind, prover, env):
        partial_binds = self.match_func(env, current_bind)
        if not partial_binds: return
        for pb in partial_binds:
            new_binds = {k: v.get_rep() for k, v in pb.items()}
            yield from self._try_bind_and_yield(current_bind, new_binds)

class FactPattern(Pattern):
    def __init__(self, fact_type, args, target_type=None, sub_type=None, allow_flip=False, flip_group=None):
        self.fact_type = fact_type; self.args = args; self.target_type = target_type; self.sub_type = sub_type; self.allow_flip = allow_flip; self.flip_group = flip_group

    def match(self, current_bind, prover, env):
        search_nodes = env.active_search_nodes if getattr(env, 'active_search_nodes', None) is not None else env.nodes
        if self.fact_type == "Identical": yield from self._match_identical(current_bind, prover, env, search_nodes)
        elif self.fact_type == "Connected": yield from self._match_connected(current_bind, prover, env, search_nodes)
        elif self.fact_type == "DefinedBy": yield from self._match_defined_by(current_bind, prover, env, search_nodes)
        elif self.fact_type == "CommonEntity": yield from self._match_common_entity(current_bind, prover, env, search_nodes)
        elif self.fact_type in ["Collinear", "Concyclic"]: yield from self._match_curve_macro(current_bind, prover, env, search_nodes)
        else: yield from self._match_generic(current_bind, prover, env, search_nodes)

    def _match_identical(self, current_bind, prover, env, search_nodes):
        v1, v2 = self.args[0], self.args[1]
        if v1 in current_bind and v2 in current_bind:
            if current_bind[v1].get_rep() == current_bind[v2].get_rep(): yield current_bind
        elif v1 in current_bind or v2 in current_bind:
            bound_var, unbound_var = (v1, v2) if v1 in current_bind else (v2, v1)
            target_rep = current_bind[bound_var].get_rep()
            for n in search_nodes:
                if n.get_rep() == target_rep and n.is_valid(): yield from self._try_bind_and_yield(current_bind, {unbound_var: n})
        else:
            nodes = [n for n in search_nodes if getattr(n.get_rep(), 'entity_type', '') == self.target_type and n.is_valid()]
            for rep in set(n.get_rep() for n in nodes): yield from self._try_bind_and_yield(current_bind, {v1: rep, v2: rep})
            
        yield from self._match_generic(current_bind, prover, env, search_nodes)
        
        if self.fact_type == "Identical" and len(self.args) == 2:
            for n in search_nodes:
                if not n.is_valid(): continue
                rep = n.get_rep()
                if getattr(rep, 'entity_type', '') == "Angle":
                    for c in getattr(rep, 'components', []):
                        for d in list(c.definitions):
                            if d.def_type == "AnglePair" and len(d.parents) == 2:
                                d1, d2 = d.parents[0].get_rep(), d.parents[1].get_rep()
                                for n2 in search_nodes:
                                    if not n2.is_valid() or getattr(n2.get_rep(), 'entity_type', '') != "Angle": continue
                                    if n2.get_rep() == rep: continue
                                    for c2 in getattr(n2.get_rep(), 'components', []):
                                        for d_flip in list(c2.definitions):
                                            if d_flip.def_type == "AnglePair" and len(d_flip.parents) == 2:
                                                if d_flip.parents[0].get_rep() == d2 and d_flip.parents[1].get_rep() == d1:
                                                    yield from self._try_bind_and_yield(current_bind, {self.args[0]: rep, self.args[1]: n2.get_rep()})

    def _match_connected(self, current_bind, prover, env, search_nodes):
        child_args = self.args[0] if isinstance(self.args[0], (list, tuple)) else [self.args[0]]
        parent_arg = self.args[1] if len(self.args) > 1 else None
        def is_type_match(expected_type, actual_type):
            if not expected_type: return True
            if not actual_type: return False
            if isinstance(expected_type, (list, tuple)): return any(t in actual_type for t in expected_type)
            return expected_type in actual_type or actual_type in expected_type

        parent_nodes = set()
        if parent_arg and parent_arg in current_bind: parent_nodes.add(current_bind[parent_arg].get_rep())
        else:
            for n in search_nodes: 
                rep_n = n.get_rep()
                if is_type_match(self.target_type, getattr(rep_n, 'entity_type', '')) and rep_n.is_valid(): parent_nodes.add(rep_n)
            
        for p_node in parent_nodes:
            children = set()
            for c_comp in getattr(p_node, 'components', []):
                for sub in c_comp.subobjects:
                    rep_sub = sub.get_rep()
                    if is_type_match(self.sub_type, getattr(rep_sub, 'entity_type', '')) and rep_sub.is_valid(): children.add(rep_sub)
                for d in c_comp.definitions:
                    for p in d.parents:
                        rep_p = p.get_rep() if hasattr(p, 'get_rep') else p
                        if is_type_match(self.sub_type, getattr(rep_p, 'entity_type', '')) and getattr(rep_p, 'is_valid', lambda: True)(): children.add(rep_p)
            children = list(children)
            if len(children) >= len(child_args):
                for child_comb in itertools.permutations(children, len(child_args)):
                    new_binds = {}
                    if parent_arg: new_binds[parent_arg] = p_node
                    for arg_name, child_obj in zip(child_args, child_comb): new_binds[arg_name] = child_obj
                    yield from self._try_bind_and_yield(current_bind, new_binds)

    def _match_defined_by(self, current_bind, prover, env, search_nodes):
        arg_vars = self.args[:-1]; result_var = self.args[-1]
        unordered_types = ["LengthSq", "Intersection", "CirclesIntersection", "Midpoint", "LineThroughPoints", "Circumcircle"]
        is_unordered = (self.target_type in unordered_types) or (self.sub_type == "Unordered")
        should_permute = is_unordered or getattr(self, 'allow_flip', False)
        entity_map = {
            "AnglePair": "Angle", "DirectionOf": "Direction", "LengthSq": "Scalar", "AffineRatio": "Scalar", "Constant": "Scalar",
            "Midpoint": "Point", "Intersection": "Point", "CirclesIntersection": "Point", "LineThroughPoints": "Line", "Circumcircle": "Circle",
            "PerpendicularLine": "Line", "ParallelLine": "Line"
        }
        actual_entity_type = entity_map.get(self.target_type, self.target_type)

        if result_var in current_bind:
            valid_nodes = [current_bind[result_var].get_rep()]
        elif all(v in current_bind for v in arg_vars):
            rep_parents = [current_bind[v].get_rep() for v in arg_vars]
            valid_set = set()
            for p in rep_parents: valid_set.update(get_subentity(p, actual_entity_type))
            valid_nodes = [n for n in valid_set if n.is_valid()]
            
            exact_exists = False
            for node in valid_nodes:
                for comp in getattr(node.get_rep(), 'components', []):
                    for d in comp.definitions:
                        if d.def_type == self.target_type and len(d.parents) == len(arg_vars):
                            reps_d_parents = [p.get_rep() if hasattr(p, 'get_rep') else p for p in d.parents]
                            if should_permute:
                                if set(reps_d_parents) == set(rep_parents): exact_exists = True
                            else:
                                if tuple(reps_d_parents) == tuple(rep_parents): exact_exists = True
                            if exact_exists: break
                    if exact_exists: break
                if exact_exists: break
                
            if not exact_exists and self.target_type in ["AnglePair", "DirectionOf"]:
                from mmp_core import create_geo_entity
                name_parts = [getattr(p, 'name', str(id(p))[-4:]) for p in rep_parents]
                new_node = create_geo_entity(self.target_type, rep_parents, name=f"{self.target_type}_{'_'.join(name_parts)}_(Auto)", env=env)
                if new_node: valid_nodes.append(new_node)
        else:
            bound_args = [current_bind[v].get_rep() for v in arg_vars if v in current_bind]
            if bound_args:
                valid_nodes = set()
                for p in bound_args: valid_nodes.update(get_subentity(p, actual_entity_type))
                search_reps = {n.get_rep() for n in search_nodes}
                valid_nodes = [n for n in valid_nodes if n.get_rep() in search_reps and n.is_valid()]
            else:
                valid_nodes = [n.get_rep() for n in search_nodes if getattr(n.get_rep(), 'entity_type', '') == actual_entity_type and n.is_valid()]
            
        valid_nodes = sorted(list(valid_nodes), key=lambda n: getattr(n, 'importance', 0.0), reverse=True)
            
        for node in valid_nodes:
            for comp in getattr(node.get_rep(), 'components', []):
                for d in list(comp.definitions):
                    if d.def_type == self.target_type and len(d.parents) == len(arg_vars):
                        reps_parents = [p.get_rep() if hasattr(p, 'get_rep') else p for p in d.parents]
                        if any(not getattr(p, 'is_valid', lambda: True)() for p in reps_parents): continue
                        perms = list(itertools.permutations(reps_parents)) if should_permute else [reps_parents]
                        for perm in perms:
                            new_binds = {result_var: node}
                            if self.target_type == "AnglePair" and len(arg_vars) == 2:
                                is_flipped = (tuple(perm) != tuple(reps_parents))
                                if is_flipped and not getattr(self, 'allow_flip', False): continue
                                if getattr(self, 'flip_group', None):
                                    group_key = f"__flip_group_{self.flip_group}"
                                    if group_key in current_bind and current_bind[group_key] != is_flipped: continue
                                    new_binds[group_key] = is_flipped
                                indiv_key = f"__flip_{result_var}"
                                if indiv_key in current_bind and current_bind[indiv_key] != is_flipped: continue
                                new_binds[indiv_key] = is_flipped
                            for v_name, p_obj in zip(arg_vars, perm): new_binds[v_name] = p_obj
                            yield from self._try_bind_and_yield(current_bind, new_binds)

    def _match_common_entity(self, current_bind, prover, env, search_nodes):
        p1_var, p2_var, child_var = self.args
        if p1_var in current_bind and p2_var in current_bind:
            p1_node, p2_node = current_bind[p1_var].get_rep(), current_bind[p2_var].get_rep()
            def get_sub_points(node):
                pts = set()
                for comp in getattr(node, 'components', []):
                    for sub in comp.subobjects:
                        rep_sub = sub.get_rep()
                        if getattr(rep_sub, 'entity_type', '') == self.target_type and rep_sub.is_valid(): pts.add(rep_sub)
                    for d in comp.definitions:
                        for p in d.parents:
                            rep_p = p.get_rep()
                            if getattr(rep_p, 'entity_type', '') == self.target_type and rep_p.is_valid(): pts.add(rep_p)
                return pts
            common_pts = get_sub_points(p1_node) & get_sub_points(p2_node)
            for pt in common_pts: yield from self._try_bind_and_yield(current_bind, {child_var: pt})

    def _match_curve_macro(self, current_bind, prover, env, search_nodes):
        target_entity = "Line" if self.fact_type == "Collinear" else "Circle"
        if all(v in current_bind for v in self.args):
            p_nodes = [current_bind[v].get_rep() for v in self.args]
            common_curves = None
            for p in p_nodes:
                curves = get_subentity(p, target_entity) 
                if common_curves is None: common_curves = set(curves)
                else: common_curves &= set(curves)
            if common_curves: 
                yield current_bind; return 
            yield from self._match_generic(current_bind, prover, env, search_nodes)
        else:
            curves = [n for n in search_nodes if getattr(n.get_rep(), 'entity_type', '') == target_entity and n.is_valid()]
            for curve in set(n.get_rep() for n in curves):
                pts_on_curve = set()
                for comp in getattr(curve, 'components', []):
                    for sub in comp.subobjects:
                        rep_sub = sub.get_rep()
                        if getattr(rep_sub, 'entity_type', '') == "Point" and rep_sub.is_valid(): pts_on_curve.add(rep_sub)
                    for d in comp.definitions:
                        for p in d.parents:
                            rep_p = p.get_rep()
                            if getattr(rep_p, 'entity_type', '') == "Point" and rep_p.is_valid(): pts_on_curve.add(rep_p)
                pts_on_curve = list(pts_on_curve)
                if len(pts_on_curve) >= len(self.args):
                    import itertools
                    for perm in itertools.permutations(pts_on_curve, len(self.args)):
                        new_binds = {v_name: pt_obj for v_name, pt_obj in zip(self.args, perm)}
                        yield from self._try_bind_and_yield(current_bind, new_binds)
            yield from self._match_generic(current_bind, prover, env, search_nodes)

    def _match_generic(self, current_bind, prover, env, search_nodes=None):
        for fact in reversed(prover.facts):
            if getattr(fact, 'is_proven', False):
                if fact.fact_type == self.fact_type:
                    yield from self._try_bind_and_yield(current_bind, {k: v for k, v in zip(self.args, fact.objects)})
        if env is not None:
            safe_nodes = list(env.nodes)
            if self.fact_type == "Connected" and len(self.args) == 2:
                c_var, p_var = self.args[0], self.args[1]
                for n in safe_nodes:
                    if not n.is_valid(): continue
                    rep = n.get_rep()
                    if getattr(rep, 'entity_type', '') in ["Line", "Circle"]:
                        pts = set()
                        for comp in getattr(rep, 'components', []):
                            for sub in comp.subobjects:
                                if getattr(sub.get_rep(), 'entity_type', '') == "Point": pts.add(sub.get_rep())
                            for d in comp.definitions:
                                for p in d.parents:
                                    if getattr(p.get_rep(), 'entity_type', '') == "Point": pts.add(p.get_rep())
                        for pt in pts: yield from self._try_bind_and_yield(current_bind, {c_var: pt, p_var: rep})
            elif self.fact_type in ["Collinear", "Concyclic"]:
                target_type = "Line" if self.fact_type == "Collinear" else "Circle"
                for n in safe_nodes:
                    if not n.is_valid() or getattr(n.get_rep(), 'entity_type', '') != target_type: continue
                    rep = n.get_rep()
                    pts = set()
                    for comp in getattr(rep, 'components', []):
                        for sub in comp.subobjects:
                            if getattr(sub.get_rep(), 'entity_type', '') == "Point": pts.add(sub.get_rep())
                        for d in comp.definitions:
                            for p in d.parents:
                                if getattr(p.get_rep(), 'entity_type', '') == "Point": pts.add(p.get_rep())
                    if len(pts) >= len(self.args):
                        import itertools
                        for perm in itertools.permutations(list(pts), len(self.args)):
                            yield from self._try_bind_and_yield(current_bind, {k: v for k, v in zip(self.args, perm)})
            elif self.fact_type == "Identical" and len(self.args) == 2:
                for n in safe_nodes:
                    if not n.is_valid(): continue
                    rep = n.get_rep()
                    yield from self._try_bind_and_yield(current_bind, {self.args[0]: rep, self.args[1]: rep})
                    if getattr(rep, 'entity_type', '') == "Angle":
                        for c in getattr(rep, 'components', []):
                            for d in list(c.definitions):
                                if d.def_type == "AnglePair" and len(d.parents) == 2:
                                    d1, d2 = d.parents[0].get_rep(), d.parents[1].get_rep()
                                    for n2 in safe_nodes:
                                        if not n2.is_valid() or getattr(n2.get_rep(), 'entity_type', '') != "Angle": continue
                                        if n2.get_rep() == rep: continue
                                        for c2 in getattr(n2.get_rep(), 'components', []):
                                            for d_flip in list(c2.definitions):
                                                if d_flip.def_type == "AnglePair" and len(d_flip.parents) == 2:
                                                    if d_flip.parents[0].get_rep() == d2 and d_flip.parents[1].get_rep() == d1:
                                                        yield from self._try_bind_and_yield(current_bind, {self.args[0]: rep, self.args[1]: n2.get_rep()})

class OrderPattern(Pattern):
    """
    対称性破壊パターン (Symmetry Breaking)
    変数のバインド結果に対して辞書順(ID順)の制約を課し、無駄な順列探索を N! 分の1に刈り取る。
    （例：2本の直線を選ぶとき、A-B のみを通し B-A を弾く）
    """
    def __init__(self, vars_list):
        self.vars_list = vars_list

    def match(self, current_bind, prover, env):
        bound_vars = [current_bind[v] for v in self.vars_list if v in current_bind]
        # まだ全てバインドされていない場合は一旦パス
        if len(bound_vars) < len(self.vars_list):
            yield current_bind
            return
            
        reps = [v.get_rep() if hasattr(v, 'get_rep') else v for v in bound_vars]
        ids = [id(r) for r in reps]
        
        # IDが単調増加(A < B < C...)になっている順列だけを許可する
        if all(ids[i] < ids[i+1] for i in range(len(ids)-1)):
            yield current_bind


class EventType(Enum):
    NEW_CONJECTURE = 1
    FACT_PROVEN = 2
    NODE_MERGED = 3

class PendingMatch:
    def __init__(self, theorem, bind, required_facts):
        self.theorem = theorem
        self.theorem_name = theorem.name
        self.bind = bind.copy()
        self.required_facts = required_facts
        self.constructions = theorem.constructions
        self.conclusions = theorem.conclusions

    def get_unmet_conditions(self, env):
        unmet = []
        for f in self.required_facts:
            if getattr(f, 'is_proven', False): continue
            raw_args = getattr(f, 'objects', getattr(f, 'args', []))
            bound_objs = [self.bind.get(a, a) for a in raw_args]
            reps = [o.get_rep() if hasattr(o, 'get_rep') else o for o in bound_objs]
            
            if f.fact_type == "Identical":
                if len(reps) == 2 and reps[0] == reps[1]: continue
                if len(reps) == 2 and getattr(reps[0], 'entity_type', '') == "Angle" and getattr(reps[1], 'entity_type', '') == "Angle":
                    def get_flip_rep(ang_rep):
                        c = ang_rep.get_best_component()
                        if not c: return None
                        for d in c.definitions:
                            if d.def_type == "AnglePair" and len(d.parents) == 2:
                                d1, d2 = d.parents[0].get_rep(), d.parents[1].get_rep()
                                for n in env.nodes:
                                    if not n.is_valid() or getattr(n.get_rep(), 'entity_type', '') != "Angle": continue
                                    c2 = n.get_rep().get_best_component()
                                    if c2:
                                        for d_flip in c2.definitions:
                                            if d_flip.def_type == "AnglePair" and len(d_flip.parents) == 2:
                                                if d_flip.parents[0].get_rep() == d2 and d_flip.parents[1].get_rep() == d1:
                                                    return n.get_rep()
                        return None
                    flip0, flip1 = get_flip_rep(reps[0]), get_flip_rep(reps[1])
                    if flip0 and flip1 and flip0 == flip1: continue
                    if flip0 and flip0 == reps[1]: continue
                    if flip1 and flip1 == reps[0]: continue

            elif f.fact_type in ["Collinear", "Concyclic"]:
                target_type = "Line" if f.fact_type == "Collinear" else "Circle"
                found = False
                for n in env.nodes:
                    if not n.is_valid() or getattr(n.get_rep(), 'entity_type', '') != target_type: continue
                    c_rep = n.get_rep()
                    pts_on_curve = set()
                    comp = c_rep.get_best_component()
                    if comp:
                        for sub in comp.subobjects:
                            if getattr(sub.get_rep(), 'entity_type', '') == "Point": pts_on_curve.add(sub.get_rep())
                        for d in comp.definitions:
                            for p in d.parents:
                                if getattr(p.get_rep(), 'entity_type', '') == "Point": pts_on_curve.add(p.get_rep())
                    if all(pt in pts_on_curve for pt in reps):
                        found = True; break
                if found: continue

            elif f.fact_type == "Connected":
                if len(reps) == 2:
                    child, parent = reps[0], reps[1]
                    connected = False
                    comp = parent.get_best_component() if hasattr(parent, 'get_best_component') else None
                    if comp:
                        sub_reps = [s.get_rep() for s in comp.subobjects]
                        parent_reps = [p.get_rep() if hasattr(p, 'get_rep') else p for d in comp.definitions for p in d.parents]
                        if child in sub_reps or child in parent_reps: connected = True
                    comp_c = child.get_best_component() if hasattr(child, 'get_best_component') else None
                    if comp_c:
                        for d in comp_c.definitions:
                            if parent in [p.get_rep() if hasattr(p, 'get_rep') else p for p in d.parents]: connected = True
                    if connected: continue

            elif f.fact_type == "DefinedBy":
                if all(a in self.bind for a in raw_args): continue

            unmet.append(f)
        return unmet

    def is_ready(self, env) -> bool:
        return len(self.get_unmet_conditions(env)) == 0

class TaskCounter:
    _id = 0
    @classmethod
    def next(cls): cls._id += 1; return cls._id

class ParallelBlackboardEngine:
    def __init__(self, env, prover):
        self.env = env; self.prover = prover; self.prover_queue = deque(); self.matcher_queue = []
        self.pending_matches = []; self.processed_signatures = set(); self.start_time = time.time()
        self.construction_demands = {}
        
        # 🌟 NEW: プロファイリング用の統計データ
        self.stats = {
            'time_in_prover': 0.0,
            'time_in_matcher': 0.0,
            'dfs_calls': {},
            'theorem_success': {},
            'theorem_empty_fires': {}
        }

    def emit(self, event_type: EventType, payload: any=None):
        if payload and hasattr(payload, 'objects'):
            obj_names = [getattr(o, 'name', str(o)) for o in payload.objects]
            payload_desc = f"{payload.fact_type}({', '.join(obj_names)})"
        else:
            payload_desc = getattr(payload, 'fact_type', str(payload)) if payload else "None"
            
        # 🌟 FIX: print から logger.info に変更し、タイムスタンプを統一
        logger.info(f"📥 [イベント受信] Type: {event_type.name}, Payload: {payload_desc}")
        
        if event_type == EventType.NEW_CONJECTURE:
            if payload is not None: self._schedule_matcher_task(payload)
        elif event_type == EventType.FACT_PROVEN:
            self.prover_queue.append((event_type, payload))
            if payload is not None: self._schedule_matcher_task(payload)
        elif event_type == EventType.NODE_MERGED:
            self.prover_queue.append((event_type, payload))

    def print_bottlenecks(self):
        # 🌟 NEW: Stall時にプロファイリングレポートを自動出力
        self.print_profiling_report()
        
        if not self.pending_matches:
            logger.info("  -> リーチ状態の定理はありません。")
            return
        logger.info(f"  -> 【ボトルネック分析】現在 {len(self.pending_matches)} 件の定理が待機中です。")
        for i, pm in enumerate(self.pending_matches[:20]):
            unmet = pm.get_unmet_conditions(self.env)
            unmet_desc = []
            for f in unmet:
                if hasattr(f, 'fact_type'):
                    args_str = ', '.join(getattr(o, 'name', str(o)) for o in getattr(f, 'objects', getattr(f, 'args', [])))
                    desc = f"{f.fact_type}({args_str})"
                    
                    if f.fact_type == "Identical" and len(getattr(f, 'objects', [])) == 2:
                        rep0 = f.objects[0].get_rep() if hasattr(f.objects[0], 'get_rep') else f.objects[0]
                        rep1 = f.objects[1].get_rep() if hasattr(f.objects[1], 'get_rep') else f.objects[1]
                        group0 = [n.get_rep().name for n in self.env.nodes if n.is_valid() and n.get_rep() == rep0]
                        group1 = [n.get_rep().name for n in self.env.nodes if n.is_valid() and n.get_rep() == rep1]
                        desc += f"\n      🔍 [推論の断絶] {getattr(rep0, 'name', 'Unknown')} の同値類: {len(group0)}個"
                        desc += f"\n      🔍 [推論の断絶] {getattr(rep1, 'name', 'Unknown')} の同値類: {len(group1)}個"
                else:
                    desc = str(f)
                unmet_desc.append(desc)
            if not unmet_desc:
                logger.info(f"    [{i+1}] ⚠️ 異常検知: {pm.theorem_name} はis_ready=Falseなのに待機理由が見つかりません。")
            else:
                logger.info(f"    [{i+1}] {pm.theorem_name} は次の証明を待機中: {', '.join(unmet_desc)}")

    def _is_conclusion_already_true(self, conc, bind):
        try:
            reps = [bind[arg].get_rep() if hasattr(bind[arg], 'get_rep') else bind[arg] for arg in conc.args]
        except (KeyError, TypeError):
            return False

        if conc.fact_type == "Identical" and len(reps) == 2:
            if reps[0] == reps[1]: return True
            if getattr(reps[0], 'entity_type', '') == "Angle" and getattr(reps[1], 'entity_type', '') == "Angle":
                def get_flip_rep(ang_rep):
                    for c in getattr(ang_rep, 'components', []):
                        for d in c.definitions:
                            if d.def_type == "AnglePair" and len(d.parents) == 2:
                                d1, d2 = d.parents[0].get_rep(), d.parents[1].get_rep()
                                for n in self.env.nodes:
                                    if not n.is_valid() or getattr(n.get_rep(), 'entity_type', '') != "Angle": continue
                                    for c2 in getattr(n.get_rep(), 'components', []):
                                        for d_flip in c2.definitions:
                                            if d_flip.def_type == "AnglePair" and len(d_flip.parents) == 2:
                                                if d_flip.parents[0].get_rep() == d2 and d_flip.parents[1].get_rep() == d1:
                                                    return n.get_rep()
                    return None
                flip0, flip1 = get_flip_rep(reps[0]), get_flip_rep(reps[1])
                if flip0 and flip1 and flip0 == flip1: return True
                if flip0 and flip0 == reps[1]: return True
                if flip1 and flip1 == reps[0]: return True
            return False
        elif conc.fact_type in ["Collinear", "Concyclic"]:
            target_type = "Line" if conc.fact_type == "Collinear" else "Circle"
            for n in self.env.nodes:
                if not n.is_valid() or getattr(n.get_rep(), 'entity_type', '') != target_type: continue
                c_rep = n.get_rep()
                pts_on_curve = set()
                for comp in getattr(c_rep, 'components', []):
                    for sub in comp.subobjects:
                        if getattr(sub.get_rep(), 'entity_type', '') == "Point": pts_on_curve.add(sub.get_rep())
                    for d in comp.definitions:
                        for p in d.parents:
                            if getattr(p.get_rep(), 'entity_type', '') == "Point": pts_on_curve.add(p.get_rep())
                if all(pt in pts_on_curve for pt in reps): return True
        elif conc.fact_type == "Connected" and len(reps) == 2:
            child, parent = reps[0], reps[1]
            for comp in getattr(parent, 'components', []):
                sub_reps = [s.get_rep() for s in comp.subobjects]
                parent_reps = [p.get_rep() if hasattr(p, 'get_rep') else p for d in comp.definitions for p in d.parents]
                if child in sub_reps or child in parent_reps: return True
            for comp_c in getattr(child, 'components', []):
                for d in comp_c.definitions:
                    if parent in [p.get_rep() if hasattr(p, 'get_rep') else p for p in d.parents]: return True
        t_obj_set = set(reps)
        for fact in self.prover.facts:
            if getattr(fact, 'is_proven', False) and fact.fact_type == conc.fact_type:
                f_objs = [o.get_rep() if hasattr(o, 'get_rep') else o for o in fact.objects]
                if conc.fact_type in ["Concyclic", "Collinear", "Identical", "Parallel"]:
                    if set(f_objs) == t_obj_set: return True
                else:
                    if f_objs == reps: return True
        return False

    def _schedule_matcher_task(self, fact):
        heat = getattr(fact, 'conjecture_score', 10.0)
        priority = -heat
        for theorem in self.prover.theorems:
            if not any(hasattr(p, 'fact_type') and p.fact_type == fact.fact_type for p in theorem.patterns): continue
            gen = self._evaluate_patterns_with_seed_gen(theorem.name, theorem.patterns, fact)
            heapq.heappush(self.matcher_queue, (priority, TaskCounter.next(), gen, theorem))

    def schedule_full_sweep(self):
        import heapq
        import logging
        logger = logging.getLogger("GeometryProver")
        
        new_queue = []
        for item in self.matcher_queue:
            # 優先度が負の値(個別タスク)のものは残す
            if item[0] < 0:  
                new_queue.append(item)
                
        self.matcher_queue = new_queue
        heapq.heapify(self.matcher_queue)
        
        logger.info("  🔄 [Full Sweep] 構造的真実からの定理起動をスケジュールしました (最新の状態で探索リセット)")
        
        for theorem in self.prover.theorems:
            gen = self._evaluate_patterns_dfs_wrapper(theorem.name, theorem.patterns, {})
            # 🌟 FIX: プロファイリングの成功回数を優先度(ヒープは小さい順なのでマイナス)に変換！
            # 過去に役立った実績のある定理ほど先に評価される
            succ_count = self.stats.get('theorem_success', {}).get(theorem.name, 0)
            priority = -succ_count  
            
            heapq.heappush(self.matcher_queue, (priority, TaskCounter.next(), gen, theorem))

    def run_parallel_loop(self, matcher_budget=100000):
        applied_anything = False
        if self._run_prover_agent(): applied_anything = True
        if self._run_matcher_agent(matcher_budget): applied_anything = True
        return applied_anything

    def print_profiling_report(self):
        """🌟 NEW: どこに無駄があるのかを一目で可視化するレポート機能"""
        logger.info("\n" + "="*50)
        logger.info(" 📊 探索アーキテクチャ プロファイリングレポート")
        logger.info("="*50)
        logger.info(f"⏱️ 累計処理時間: Matcher(探索)={self.stats['time_in_matcher']:.3f}s | Prover(適用)={self.stats['time_in_prover']:.3f}s")
        
        logger.info("\n🔍 空間探索の重さ (DFS呼び出し回数 ワースト):")
        for th, calls in sorted(self.stats['dfs_calls'].items(), key=lambda x: x[1], reverse=True):
            logger.info(f"  - {th}: {calls:,} 回")
            
        logger.info("\n✅ 発火の精度 (成功 vs ⚠️ 空振り):")
        all_ths = set(self.stats['theorem_success'].keys()) | set(self.stats['theorem_empty_fires'].keys())
        for th in sorted(all_ths):
            succ = self.stats['theorem_success'].get(th, 0)
            fail = self.stats['theorem_empty_fires'].get(th, 0)
            logger.info(f"  - {th}: 成功 {succ} 回 / 空振り {fail} 回")
        logger.info("="*50 + "\n")

    def _run_prover_agent(self):
        t_start = time.time()  
        applied = False
        still_pending = []
        for match in self.pending_matches:
            if match.is_ready(self.env):
                already_proven = True
                for conc in match.conclusions:
                    if not self._is_conclusion_already_true(conc, match.bind):
                        already_proven = False; break
                if already_proven: continue

                logger.info(f"  ⚡ [準備完了] {match.theorem_name} を発火します...")
                if not self._execute_constructions(match.theorem_name, match.constructions, match.bind):
                    logger.warning(f"  ❌ [発火失敗] {match.theorem_name} の作図・バインドに失敗しました。")
                    continue
                
                applied_now = self.apply_conclusions(match.theorem_name, match.conclusions, match.bind)
                if applied_now:
                    logger.info(f"  ✅ [発火成功] {match.theorem_name} が結論を適用しました。")
                    self.stats['theorem_success'][match.theorem_name] = self.stats['theorem_success'].get(match.theorem_name, 0) + 1
                    applied = True
                else:
                    logger.info(f"  ⚠️ [発火空振り] {match.theorem_name} は新しい事実を生み出しませんでした。")
                    self.stats['theorem_empty_fires'][match.theorem_name] = self.stats['theorem_empty_fires'].get(match.theorem_name, 0) + 1
            else:
                still_pending.append(match)
        self.pending_matches = still_pending

        # 🌟 FIX: 重複した更新イベントをまとめ、フルスキャンを1回だけ呼び出す
        needs_full_sweep = False
        while self.prover_queue:
            ev_type, payload = self.prover_queue.popleft()
            if ev_type == EventType.NODE_MERGED:
                if self._apply_congruence_closure(): applied = True
                needs_full_sweep = True  # ループ内ではフラグを立てるだけ
                
        if needs_full_sweep:
            self.schedule_full_sweep()  # まとめて1回だけスケジュール！
                
        if applied:
            still_pending_2 = []
            for match in self.pending_matches:
                if match.is_ready(self.env):
                    already_proven = True
                    for conc in match.conclusions:
                        if not self._is_conclusion_already_true(conc, match.bind):
                            already_proven = False; break
                    if already_proven: continue
                    logger.info(f"  ⚡ [準備完了(追撃)] {match.theorem_name} を発火します...")
                    if not self._execute_constructions(match.theorem_name, match.constructions, match.bind): continue
                    
                    if self.apply_conclusions(match.theorem_name, match.conclusions, match.bind): 
                        self.stats['theorem_success'][match.theorem_name] = self.stats['theorem_success'].get(match.theorem_name, 0) + 1
                        applied = True
                    else:
                        self.stats['theorem_empty_fires'][match.theorem_name] = self.stats['theorem_empty_fires'].get(match.theorem_name, 0) + 1
                else:
                    still_pending_2.append(match)
            self.pending_matches = still_pending_2

        self.stats['time_in_prover'] += (time.time() - t_start)
        return applied

    def _run_matcher_agent(self, budget):
        t_start = time.time()
        if not self.matcher_queue: return False
        calls = 0
        applied = False  
        initial_node_count = len(self.env.nodes)
        
        while self.matcher_queue and calls < budget:
            priority, task_id, gen, theorem = heapq.heappop(self.matcher_queue)
            try:
                bind = next(gen)
                calls += 1
                
                # 🌟 NEW: "PAUSE" 信号を受け取ったら、新しいタスクIDを振って最後尾に並べ直す(ラウンドロビン)
                if bind == "PAUSE":
                    heapq.heappush(self.matcher_queue, (priority, TaskCounter.next(), gen, theorem))
                    continue
                
                type_ok = True
                for k, v in bind.items():
                    if k in theorem.entities and theorem.entities[k] != "Any" and k != "__facts__":
                        expected_type = theorem.entities[k]
                        actual_type = getattr(v, 'entity_type', '')
                        if actual_type != expected_type:
                            if expected_type == "Angle" and actual_type == "Direction": pass
                            else: type_ok = False; break
                            
                if type_ok:
                    sig = self._make_signature(theorem.name, bind)
                    if sig not in self.processed_signatures:
                        self.processed_signatures.add(sig)
                        
                        already_proven = True
                        for conc in theorem.conclusions:
                            if not self._is_conclusion_already_true(conc, bind):
                                already_proven = False; break
                        if already_proven: continue
                        
                        required_facts = list(bind.get('__facts__', []))
                        pm = PendingMatch(theorem, bind, required_facts)
                        self.pending_matches.append(pm)
                        logger.info(f"  🔍 [発見] {theorem.name} のリーチフォーマットをストックしました！")
                        applied = True 
                        
                        if pm.is_ready(self.env):
                            self.emit(EventType.FACT_PROVEN, None)
                
                # 🌟 NEW: 次の探索のために、必ず新しいTaskIDで再キューイングし、他の定理にターンを譲る
                heapq.heappush(self.matcher_queue, (priority, TaskCounter.next(), gen, theorem))
                
            except StopIteration:
                pass
                
        if len(self.env.nodes) > initial_node_count:
            applied = True
            
        self.stats['time_in_matcher'] += (time.time() - t_start)
        return applied

    def _evaluate_patterns_with_seed_gen(self, theorem_name, patterns, seed_fact):
        for pat in patterns:
            if not hasattr(pat, 'fact_type') or pat.fact_type != seed_fact.fact_type: continue
            reps = [obj.get_rep() if hasattr(obj, 'get_rep') else obj for obj in seed_fact.objects]
            if len(reps) >= len(pat.args):
                for perm in itertools.permutations(reps, len(pat.args)):
                    bind = {"__facts__": [seed_fact]}
                    if hasattr(self.env, 'right_angle'): bind["Ang90"] = self.env.right_angle.get_rep()
                    if hasattr(self.env, 'zero_angle'): bind["Ang0"] = self.env.zero_angle.get_rep()
                    for v_name, obj in zip(pat.args, perm): bind[v_name] = obj
                    self.env.active_search_nodes = self.env.nodes
                    yield from self._evaluate_patterns_dfs_wrapper(theorem_name, patterns, bind)

    def _evaluate_patterns_dfs_wrapper(self, theorem_name, patterns, initial_bind):
        MAX_DFS_CALLS = 100000  # 🌟 上限を緩和(他のタスクをブロックしなくなったため)
        state = {'calls': 0, 'limit_hit': False}
        failed_paths_cache = set()
        
        def dfs(pattern_idx, current_bind):
            state['calls'] += 1
            self.stats['dfs_calls'][theorem_name] = self.stats['dfs_calls'].get(theorem_name, 0) + 1
            
            if state['calls'] > MAX_DFS_CALLS:
                if not state['limit_hit']:
                    logger.warning(f"    ⚠️ [{theorem_name}] 探索空間が大きすぎるため打ち切り (上限: {MAX_DFS_CALLS})")
                    state['limit_hit'] = True
                return
                
            # 🌟 NEW (プリエンプション): 100手探索しても結果が出なければ息継ぎ
            if state['calls'] % 100 == 0:
                focus_targets = [v.get_rep() for k, v in current_bind.items() if hasattr(v, 'get_rep')]
                if hasattr(self.env, 'visualizer'):
                    # 🌟 FIX: ここで定理名をビジュアライザに渡す
                    self.env.visualizer.broadcast_state(focus_nodes=focus_targets, current_theorem=theorem_name)
                yield "PAUSE"
                
            if pattern_idx == len(patterns):
                yield current_bind.copy()
                return

            bind_ids = []
            for k, v in sorted(current_bind.items()):
                if k == '__facts__': continue
                bind_ids.append(f"{k}:{id(v.get_rep() if hasattr(v, 'get_rep') else v)}")
            state_sig = f"{pattern_idx}_" + "_".join(bind_ids)

            if state_sig in failed_paths_cache:
                return

            matched_any = False
            for bound_dict in patterns[pattern_idx].match(current_bind, self.prover, self.env):
                matched_any = True
                yield from dfs(pattern_idx + 1, bound_dict)
                
            if not matched_any:
                failed_paths_cache.add(state_sig)
                bound_points = [v.get_rep() for k, v in current_bind.items() if k != '__facts__' and hasattr(v, 'get_rep') and getattr(v.get_rep(), 'entity_type', '') == 'Point']
                if len(bound_points) >= 2:
                    for p1, p2 in itertools.combinations(set(bound_points), 2):
                        c1, c2 = p1.get_best_component(), p2.get_best_component()
                        if c1 and c2 and not any(getattr(obj, 'entity_type', '') == "Line" for obj in (c1.subobjects & c2.subobjects)):
                            demand_sig = frozenset([p1, p2])
                            self.construction_demands[demand_sig] = self.construction_demands.get(demand_sig, 0) + 1.0

        yield from dfs(0, initial_bind)

    def _make_signature(self, theorem_name, bind):
        bind_ids = []
        for k, v in sorted(bind.items()):
            if k == '__facts__': continue
            if hasattr(v, 'get_rep'): bind_ids.append(f"{k}:{id(v.get_rep())}")
            else: bind_ids.append(f"{k}:{str(v)}")
        return f"{theorem_name}-" + "-".join(bind_ids)

    def _execute_constructions(self, theorem_name, constructions, bind):
        from mmp_core import create_geo_entity, link_logical_incidence
        for constr in constructions:
            parents = [bind[arg].get_rep() if hasattr(bind[arg], 'get_rep') else bind[arg] for arg in constr.args]
            if len(set(parents)) < len(parents): return False

            if constr.def_type == "AnglePair" and len(parents) == 2:
                if not self.env.tester.is_canonical_angle_order(parents[0], parents[1]):
                    parents = [parents[1], parents[0]]
                    bind[f"__flip_{constr.bind_to}"] = True
                else:
                    bind[f"__flip_{constr.bind_to}"] = False

            if constr.def_type == "LineThroughPoints" and len(parents) == 2:
                common_lines = get_subentity(parents[0], "Line") & get_subentity(parents[1], "Line")
                if common_lines:
                    bind[constr.bind_to] = list(common_lines)[0]; continue
                
            common = get_subentity(parents[0], constr.target_type)
            for p in parents[1:]: common &= get_subentity(p, constr.target_type)
                
            found_obj = None
            is_unordered = constr.def_type in ["LengthSq", "Intersection", "CirclesIntersection", "Midpoint", "LineThroughPoints", "Circumcircle"]
            
            for obj in common:
                comp = obj.get_best_component()
                if comp:
                    for d in comp.definitions:
                        if d.def_type == constr.def_type:
                            rep_d_parents = [p.get_rep() for p in d.parents] 
                            if is_unordered:
                                if set(rep_d_parents) == set(parents): found_obj = obj; break
                            else:
                                if rep_d_parents == parents: found_obj = obj; break
                if found_obj: break
                
            if not found_obj:
                for node in self.env.nodes:
                    if not node.is_valid(): continue
                    comp = node.get_rep().get_best_component()
                    if not comp: continue
                    for d in comp.definitions:
                        if d.def_type == constr.def_type:
                            rep_d_parents = [p.get_rep() for p in d.parents]
                            if (is_unordered and set(rep_d_parents) == set(parents)) or (not is_unordered and rep_d_parents == parents):
                                found_obj = node.get_rep(); break
                    if found_obj: break

            if found_obj:
                bind[constr.bind_to] = found_obj 
            else:
                name_suffix = "_".join([getattr(p, 'name', str(id(p))[-4:]) for p in parents])
                new_obj = create_geo_entity(constr.def_type, parents, name=f"{constr.def_type}_{name_suffix}_(Auto)", env=self.env)
                if new_obj is None: return False
                new_obj.created_by_theorem = theorem_name
                for p in parents: link_logical_incidence(p, new_obj)
                bind[constr.bind_to] = new_obj
        return True

    def apply_conclusions(self, theorem_name, conclusions, bind):
        current_premises = list(bind.values())
        applied_anything = False
        structural_changed = False
        
        for conc in conclusions:
            if isinstance(conc, FactTemplate):
                reps = [bind[arg].get_rep() if hasattr(bind[arg], 'get_rep') else bind[arg] for arg in conc.args]
                new_fact = Fact(fact_type=conc.fact_type, objects=reps, source_theorem=theorem_name, premises=current_premises)
                if new_fact not in self.prover.facts:
                    new_fact.is_proven = True
                    self.prover.facts.append(new_fact)
                    self.emit(EventType.FACT_PROVEN, new_fact)
                    applied_anything = True
                else:
                    existing = self.prover.facts[self.prover.facts.index(new_fact)]
                    if not getattr(existing, 'is_proven', False):
                        existing.is_proven = True; existing.proof_source = theorem_name
                        self.emit(EventType.FACT_PROVEN, existing)
                        applied_anything = True

            if conc.fact_type == "Identical":
                if self._apply_identical(theorem_name, conc, bind): 
                    applied_anything = True
                    structural_changed = True
            elif conc.fact_type == "Connected":
                if self._apply_connected(theorem_name, conc, bind): 
                    applied_anything = True
                    structural_changed = True
            elif conc.fact_type in ["Collinear", "Concyclic"]:
                if self._apply_curve_macro(theorem_name, conc, bind): 
                    applied_anything = True
                    structural_changed = True
                    
        if structural_changed:
            self.emit(EventType.NODE_MERGED, None)
        return applied_anything

    def _apply_congruence_closure(self):
        start_time = time.time()
        changed = False; def_map = {}; merge_count = 0
        for node in list(self.env.nodes):
            if not node.is_valid(): continue
            rep = node.get_rep()
            comp = rep.get_best_component()
            if not comp: continue
            for d in comp.definitions:
                if not d.parents: continue
                if d.def_type in ["Point", "Line", "Circle", "Given", "Free", "GivenPoint", "FreePoint", "Direction", "Angle", "Scalar", "Constant"]: continue
                rep_parents = tuple(p.get_rep() for p in d.parents)
                unordered_types = ["LengthSq", "Intersection", "CirclesIntersection", "Midpoint", "LineThroughPoints", "Circumcircle", "OtherLineCircleIntersection"]
                if d.def_type in unordered_types:
                    rep_parents = tuple(p.get_rep() if hasattr(p, 'get_rep') else p for p in d.parents)
                    rep_parents = tuple(sorted(rep_parents, key=lambda x: getattr(x, 'name', str(id(x)))))
                signature = (d.def_type, rep_parents)
                if signature in def_map:
                    existing_node = def_map[signature]
                    rep_existing = existing_node.get_rep()
                    rep_current = rep.get_rep()
                    if rep_existing != rep_current:
                        logger.debug(f"  🔄 [合同閉包] 同一の親を持つノードを統合: {rep_current.name} ≡ {rep_existing.name}")
                        merged = self.env.merge_entities_logically(rep_existing, rep_current, force_bypass_verify=True)
                        if merged: changed = True; merge_count += 1; break
                else: def_map[signature] = rep.get_rep()
        return changed

    def _apply_identical(self, theorem_name, conc, bind):
        reps = [bind[arg].get_rep() for arg in conc.args]
        if len(reps) != 2: return False
        if getattr(reps[0], 'entity_type', '') == "Angle":
            flip1 = bind.get(f"__flip_{conc.args[0]}", False)
            flip2 = bind.get(f"__flip_{conc.args[1]}", False)
            if flip1 != flip2: return False
        if reps[0] == reps[1]: return False
        evidence_str = f" [根拠: 共円({', '.join([bind[k].get_rep().name for k in ['Apex1', 'Apex2', 'Base1', 'Base2'] if k in bind])})]" if theorem_name == "円周角の定理" else ""
        logger.info(f"  🟢 [マージ実行] {reps[0].name} ≡ {reps[1].name} (理由: {theorem_name}){evidence_str}")
        merged = self.env.merge_entities_logically(reps[0], reps[1])
        if merged:
            self.prover.record_trace(theorem_name, f"{reps[0].name} ≡ {reps[1].name}")
            return True
        return False

    def _apply_connected(self, theorem_name, conc, bind):
        from mmp_core import link_logical_incidence
        child_args = conc.args[0] if isinstance(conc.args[0], list) else [conc.args[0]]
        parent_obj = bind[conc.args[1]].get_rep() if hasattr(bind[conc.args[1]], 'get_rep') else bind[conc.args[1]]
        applied = False
        for c_arg in child_args:
            child_obj = bind[c_arg].get_rep() if hasattr(bind[c_arg], 'get_rep') else bind[c_arg]
            if not parent_obj or not child_obj: continue
            p_type = getattr(parent_obj, 'entity_type', '')
            if parent_obj not in get_subentity(child_obj, p_type):
                link_logical_incidence(parent_obj, child_obj)
                logger.info(f"  🟢 [リンク] {child_obj.name} ∈ {parent_obj.name} (理由: {theorem_name})")
                self.prover.record_trace(theorem_name, f"{child_obj.name} ∈ {parent_obj.name}")
                applied = True
        return applied
    
    def _apply_curve_macro(self, theorem_name, conc, bind):
        from mmp_core import create_geo_entity, link_logical_incidence
        reps = [bind[arg].get_rep() if hasattr(bind[arg], 'get_rep') else bind[arg] for arg in conc.args]
        search_type = "Line" if conc.fact_type == "Collinear" else "Circle"
        def_type = "LineThroughPoints" if conc.fact_type == "Collinear" else "Circumcircle"
        base_count = 3 if search_type == "Circle" else 2
        common_curves = get_subentity(reps[0], search_type)
        for pt in reps[1:]: common_curves &= get_subentity(pt, search_type)
        if common_curves: return False
        base_curves = get_subentity(reps[0], search_type)
        for pt in reps[1:base_count]: base_curves &= get_subentity(pt, search_type)
        if not base_curves:
            for node in self.env.nodes:
                if not node.is_valid(): continue
                if getattr(node.get_rep(), 'entity_type', '') == search_type:
                    comp = node.get_rep().get_best_component()
                    if comp:
                        for d in comp.definitions:
                            if d.def_type == def_type:
                                rep_parents = [p.get_rep() for p in d.parents]
                                if set(reps[:base_count]).issubset(set(rep_parents)): base_curves = {node.get_rep()}; break
                if base_curves: break
        if base_curves:
            target_curve = list(base_curves)[0]
            for pt in reps[base_count:]: link_logical_incidence(pt, target_curve)
            logger.info(f"  🟢 [マクロ拡張] {', '.join(p.name for p in reps[base_count:])} を既存の {target_curve.name} に追加 (理由: {theorem_name})")
            self.prover.record_trace(theorem_name, f"{conc.fact_type}({', '.join(p.name for p in reps)})")
            return True
        new_curve = create_geo_entity(def_type, reps[:base_count], name=f"{def_type}_(Auto)", env=self.env)
        if new_curve is None: return False
        new_curve.created_by_theorem = theorem_name 
        for pt in reps: link_logical_incidence(pt, new_curve)
        logger.info(f"  🟢 [マクロ構築] {', '.join(p.name for p in reps)} ∈ {new_curve.name} (理由: {theorem_name})")
        self.prover.record_trace(theorem_name, f"{conc.fact_type}({', '.join(p.name for p in reps)})")
        return True
# ==========================================
# 🌟 NEW: AttentionManager (動的パラメータ管理)
# ==========================================
class AttentionManager:
    def __init__(self, env):
        self.env = env
        self.decay_rate = 0.85

    def inject_heat(self, node, amount):
        """特定のノードに熱を注入し、O(1)キャッシュのソート順をリセットする"""
        if getattr(node, 'base_importance', 1.0) <= 0.0: return
        node.heat_bonus = getattr(node, 'heat_bonus', 0.0) + amount
        self.env._type_cache_version = -1  # キャッシュを無効化して再ソートを強制

    def cool_down_all(self):
        """ターン終了時にシステム全体の熱を冷ます"""
        for n in self.env.nodes:
            if hasattr(n, 'heat_bonus'):
                n.heat_bonus *= self.decay_rate
        self.env._type_cache_version = -1

    def get_heuristic_score(self, node):
        """3つのパラメータを合成して探索の優先度(有望さ)を算出する"""
        imp = getattr(node, 'base_importance', 1.0)
        heat = getattr(node, 'heat_bonus', 0.0)
        deg = getattr(node, 'numerical_degree', 10)
        if deg is None: deg = 10
        return imp + heat - (deg * 0.1)

# ==========================================
# ProofEnvironment (環境)
# ==========================================
class ProofEnvironment:
    def __init__(self, enable_numerical_debug=False):
        self.nodes = []; self.active_search_nodes = None; self.enable_numerical_debug = enable_numerical_debug; self.all_vars = None
        
        # 🌟 FIX: AttentionManager を環境にマウント
        self.attention = AttentionManager(self)
        
        self.zero_angle = GeoEntity("Angle", "Parallel_0"); self.zero_angle.components.append(LogicalComponent()); self.zero_angle.importance = 10.0
        self.right_angle = GeoEntity("Angle", "Perpendicular_90"); self.right_angle.components.append(LogicalComponent()); self.right_angle.importance = 10.0
        self.nodes.extend([self.zero_angle, self.right_angle])

    def merge_entities_logically(self, rep1, rep2, force_bypass_verify=False, reason_fact=None):
        entity1, entity2 = rep1.get_rep(), rep2.get_rep()
        if entity1 == entity2: return None
        if entity1 not in self.nodes or entity2 not in self.nodes: return None
        should_verify = (getattr(self, 'enable_numerical_debug', False)) and not force_bypass_verify
        if should_verify and getattr(self, 'all_vars', None):
            if not self.tester.verify_identical(entity1, entity2): return None
        entity2.merge_into(entity1, reason_fact=reason_fact)
        entity2.base_importance = 0.0 
        for n in self.nodes:
            if not getattr(n, 'is_valid', lambda: True)(): continue
            comp = n.get_best_component()
            if not comp: continue
            needs_update = False
            for d in comp.definitions:
                if entity2 in d.parents: needs_update = True; break
            if needs_update:
                new_defs = set()
                for d in comp.definitions:
                    new_parents = [entity1 if p == entity2 else p for p in d.parents]
                    if new_parents != d.parents: new_defs.add(Definition(d.def_type, new_parents, d.naive_degree, d.depth))
                    else: new_defs.add(d)
                comp.definitions = new_defs 
        return entity1.get_rep()

    def get_valid_nodes_by_type(self, target_type):
        if not hasattr(self, '_type_cache_version') or getattr(self, '_type_cache_version', -1) != len(self.nodes):
            self._type_index = {}
            for n in self.nodes:
                if not n.is_valid(): continue
                rep = n.get_rep()
                e_type = getattr(rep, 'entity_type', '')
                if e_type not in self._type_index:
                    self._type_index[e_type] = set()
                self._type_index[e_type].add(rep)
                
            self._sorted_type_index = {}
            for k, v in self._type_index.items():
                # 🌟 FIX: AttentionManager を使ってスコア計算
                self._sorted_type_index[k] = sorted(list(v), key=self.attention.get_heuristic_score, reverse=True)
                
            self._type_cache_version = len(self.nodes)
            
        return self._sorted_type_index.get(target_type, [])
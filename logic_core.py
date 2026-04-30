# logic_core.py
import logging

# ログの設定（ファイルに出力し、コンソールには出さない設定）
logger = logging.getLogger("GeometryProver")
logger.setLevel(logging.DEBUG)
if not logger.handlers:
    file_handler = logging.FileHandler('proof.log', mode='w', encoding='utf-8')
    file_handler.setFormatter(logging.Formatter('%(message)s'))
    logger.addHandler(file_handler)

class Fact:
    def __init__(self, fact_type, objects, is_proven=False, proof_source=""):
        self.fact_type = fact_type  
        self.objects = objects
        self.is_proven = is_proven
        self.proof_source = proof_source
        self.dependents = [] 

    def mark_as_proven(self, source_description):
        if not self.is_proven:
            self.is_proven = True
            self.proof_source = source_description
            logger.debug(f"  🟢 [証明完了] {self} が証明されました！ (理由: {source_description})")
            for step in self.dependents:
                step.check_if_proven()

    def __eq__(self, other):
        if not isinstance(other, Fact) or self.fact_type != other.fact_type:
            return False
        # 🌟 修正: 順序に依存しないFactタイプの拡張 (Identical, Parallel を追加)
        if self.fact_type in ["Concyclic", "Collinear", "Identical", "Parallel"]:
            return set(self.objects) == set(other.objects)
        return self.objects == other.objects
        
    def __repr__(self):
        status = "🟢" if self.is_proven else "🟡"
        names = [getattr(o, 'name', str(o)) for o in self.objects]
        return f"{status} [{self.fact_type}] {', '.join(names)}"

class ProofStep:
    def __init__(self, theorem_name, premises, conclusion):
        self.theorem_name = theorem_name
        self.premises = premises
        self.conclusion = conclusion
        for p in self.premises:
            if self not in p.dependents:
                p.dependents.append(self)

    def check_if_proven(self):
        if self.conclusion.is_proven:
            return 
        if all(p.is_proven for p in self.premises):
            premise_strs = ", ".join([str(p) for p in self.premises])
            self.conclusion.mark_as_proven(f"{self.theorem_name} (前提: {premise_strs})")

class GeometryTheorem:
    def __init__(self, name, match_func, apply_func):
        self.name = name
        self.match_func = match_func
        self.apply_func = apply_func


# ==========================================
# 1. 包含と等価関係のグラフ構造 (E-Graph)
# ==========================================
class ProofEnvironment:
    """現在の幾何学的な「状態」と「重要度」を管理する世界"""
    def __init__(self):
        self.nodes = []           
        self.importance = {}      
        self.affinity = {}        
        
        from mmp_core import GeoEntity, LogicalComponent
        
        # 角度の基底エンティティ(e-class)の初期化
        self.zero_angle = GeoEntity("Angle", "Parallel_0")
        self.zero_angle.components.append(LogicalComponent())
        self.zero_angle.importance = 10.0
        
        self.right_angle = GeoEntity("Angle", "Perpendicular_90")
        self.right_angle.components.append(LogicalComponent())
        self.right_angle.importance = 10.0
        
        self.nodes.extend([self.zero_angle, self.right_angle])

    def add_equal_angle(self, L1, L2, L3, L4):
        from mmp_core import GeoEntity, Definition, LogicalComponent
        angle1, angle2 = None, None
        for node in self.nodes:
            if getattr(node, 'entity_type', '') == "Angle":
                comp = node.get_best_component()
                if not comp: continue
                for d in comp.definitions:
                    if d.def_type == "AnglePair" and len(d.parents) == 2:
                        p_set = {d.parents[0].id, d.parents[1].id}
                        if {L1.id, L2.id} == p_set: angle1 = node
                        if {L3.id, L4.id} == p_set: angle2 = node

        if angle1 and angle2 and angle1 != angle2:
            angle1.merge_numerical(angle2)
            if len(angle1.components) > 1: angle1.prove_components_equal(0, 1)
            if angle2 in self.nodes: self.nodes.remove(angle2)
        elif angle1:
            angle1.get_best_component().definitions.add(Definition("AnglePair", [L3, L4]))
        elif angle2:
            angle2.get_best_component().definitions.add(Definition("AnglePair", [L1, L2]))
        else:
            new_angle = GeoEntity("Angle", f"Angle_{L1.name}{L2.name}_{L3.name}{L4.name}")
            new_angle.components.append(LogicalComponent())
            new_angle.get_best_component().definitions.add(Definition("AnglePair", [L1, L2]))
            new_angle.get_best_component().definitions.add(Definition("AnglePair", [L3, L4]))
            new_angle.importance = 5.0 
            self.nodes.append(new_angle)

    def merge_entities_logically(self, entity1, entity2):
        """論理推論によって2つの実体が同一であると証明された場合、完全に融合する"""
        
        # 渡されたのがゾンビだった場合、自力で本体(ルート)まで遡る
        while hasattr(entity1, '_merged_into') and entity1._merged_into is not None:
            entity1 = entity1._merged_into
        while hasattr(entity2, '_merged_into') and entity2._merged_into is not None:
            entity2 = entity2._merged_into

        # マージが中断された場合の理由を明確にロギングする
        if entity1 == entity2:
            logger.debug(f"    [マージ中断] {entity1.name} と {entity2.name} は既に同じ本体です。")
            return None
        if entity1 not in self.nodes:
            logger.debug(f"    [マージ中断] 統合先 {entity1.name} が環境(nodes)に存在しません。")
            return None
        if entity2 not in self.nodes:
            logger.debug(f"    [マージ中断] 統合元(消去対象) {entity2.name} が環境(nodes)に存在しません。")
            return None
            
        # 1. 全てのノードの「定義」と「所属図形」の中にある entity2 を entity1 に置換
        for node in self.nodes:
            for comp in node.components:
                # 所属図形(subobjects)の更新
                if entity2 in comp.subobjects:
                    comp.subobjects.remove(entity2)
                    comp.subobjects.add(entity1)
                
                # 定義(definitions)の更新
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
            # 🌟 NEW: Shape(相似クラス) が持つ shape_members の参照更新
            # もし entity2 が「点」または「Triangle」だった場合、ここで本体に書き換える
            # ==========================================
            if getattr(node, 'shape_members', None):
                new_shape_members = {}
                for tri, pts in node.shape_members.items():
                    # Triangle自身がマージされた場合はキーを差し替え
                    new_tri = entity1 if tri == entity2 else tri
                    # Triangleの頂点がマージされた場合はタプル内を差し替え
                    new_pts = tuple(entity1 if p == entity2 else p for p in pts)
                    new_shape_members[new_tri] = new_pts
                node.shape_members = new_shape_members

        # 2. 既に証明された事実(Fact)リストの中の参照も更新（重複判定を狂わせないため）
        if hasattr(self, 'prover'):
            for fact in self.prover.facts:
                # is (メモリ一致) だけでなく、id が同じもの、または同じ名前のゾンビも容赦なく置換する
                new_objects = []
                for obj in fact.objects:
                    if obj is entity2 or getattr(obj, 'id', None) == getattr(entity2, 'id', None):
                        new_objects.append(entity1)
                    else:
                        new_objects.append(obj)
                fact.objects = new_objects
            
            # 重複の排除
            unique_facts = []
            for fact in self.prover.facts:
                if fact not in unique_facts:
                    unique_facts.append(fact)
            self.prover.facts = unique_facts

        # 3. entity2 の知識を entity1 に吸収させて削除
        entity1.merge_numerical(entity2)
        while len(entity1.components) > 1:
            entity1.prove_components_equal(0, 1)
            
        entity1.importance = max(getattr(entity1, 'importance', 1.0), getattr(entity2, 'importance', 1.0))

        self.nodes.remove(entity2)
        entity2._merged_into = entity1
        entity2._is_merged_and_dead = True
        return entity1

class LogicProver:
    def __init__(self, env, theorems):
        self.env = env
        self.theorems = theorems
        self.facts = []
        
    def get_or_add_fact(self, new_fact):
        for existing in self.facts:
            if existing == new_fact: return existing
        self.facts.append(new_fact)
        return new_fact

    def add_fact(self, fact):
        return self.get_or_add_fact(fact)

    def print_proof_trace(self, target_fact):
        logger.debug("\n【証明のトレース（証明された事実の連鎖）】")
        proven_facts = [f for f in self.facts if f.is_proven]
        for i, f in enumerate(proven_facts):
            logger.debug(f" {i+1}. {f}")
            logger.debug(f"      <= {f.proof_source}")
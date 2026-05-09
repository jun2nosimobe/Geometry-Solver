# proof_manager.py
# 証明の記録、Factの管理、および証明ツリーの抽出・可視化を担当するモジュール

import logging

logger = logging.getLogger("GeometryProver")

class Fact:
    def __init__(self, fact_type, objects, source_theorem=None, premises=None):
        self.fact_type = fact_type
        self.objects = objects
        self.is_proven = False
        self.is_mmp_conjecture = True
        self.conjecture_score = 0.0
        self.proof_source = ""
        
        # 🌟 証明ツリー構築のためのメタデータ
        self.source_theorem = source_theorem
        self.premises = premises or []

    def __str__(self):
        obj_names = ", ".join([getattr(o, 'name', str(o)) for o in self.objects])
        return f"{self.fact_type}({obj_names})"
        
    def __repr__(self):
        return self.__str__()
        
    def __eq__(self, other):
        if not isinstance(other, Fact) or self.fact_type != other.fact_type: return False
        if self.fact_type in ["Concyclic", "Collinear", "Identical", "Parallel"]: 
            return set(self.objects) == set(other.objects)
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


# ==========================================
# 🌟 証明ツリーの抽出・可視化ロジック
# ==========================================
def format_target(target):
    """ターゲット（FactやGeoEntity）を文字列化するヘルパー"""
    if hasattr(target, 'fact_type'):
        args_str = ", ".join(getattr(a, 'name', str(a)) for a in target.objects)
        return f"{target.fact_type}({args_str})"
    elif hasattr(target, 'name'):
        return target.name
    return str(target)

def print_proof_tree(target, visited=None, indent="", is_last=True):
    """
    証明ツリーをコンソールに美しく可視化する再帰関数
    """
    if visited is None:
        visited = set()

    # 枝の記号（見た目を綺麗にするためのASCIIアート）
    branch = "└── " if is_last else "├── "
    next_indent = indent + ("    " if is_last else "│   ")

    # 1. 循環参照の防止 (E-Graphの無限ループを防ぐ)
    node_id = id(target)
    if node_id in visited:
        logger.info(f"{indent}{branch}🔄 {format_target(target)} (既出のため省略)")
        return
    visited.add(node_id)

    # 2. 現在のノードの出力
    source_theorem = getattr(target, 'source_theorem', None)
    if source_theorem:
        logger.info(f"{indent}{branch}🎯 {format_target(target)} <= [{source_theorem}]")
    else:
        # 定理がない場合（初期条件や Given な図形）
        logger.info(f"{indent}{branch}🌱 {format_target(target)} (初期条件 / 定義)")
        return

    # 3. 前提条件（Premises）を再帰的に辿る
    premises = getattr(target, 'premises', [])
    for i, premise in enumerate(premises):
        is_last_child = (i == len(premises) - 1)
        print_proof_tree(premise, visited, next_indent, is_last_child)
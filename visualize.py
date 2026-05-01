# visualize.py
import graphviz
from logic_core import get_rep
from mmp_core import GeoEntity

def draw_egraph(env, filename="egraph_output", view=True):
    """
    E-Graphの現在の状態をGraphvizで可視化し、見やすく出力する。
    """
    # エンジンを 'dot' から 'sfdp' または 'neato' に変更すると
    # 横長になりすぎるのを防げますが、論理の流れを見るなら dot が一番です。
    # 代わりに dot のレイアウトパラメータを調整します。
    dot = graphviz.Digraph(comment='Geometry E-Graph')
    
    # 🌟 NEW: 超横長を防ぐための Graphviz チューニング
    dot.attr(rankdir='LR')          # 左から右へ流す (BTやTBより横長になりにくい)
    dot.attr(nodesep='0.3')         # 兄弟ノード間の隙間を詰める (デフォルト0.25)
    dot.attr(ranksep='0.8')         # 階層間の隙間
    dot.attr(splines='polyline')    # 矢印を曲線ではなく折れ線にして見やすく
    dot.attr(concentrate='true')    # 共通の矢印を束ねてスッキリさせる
    dot.attr('node', fontname='Helvetica, Arial, sans-serif', margin='0.1')

    drawn_nodes = set()
    
    def safe_id(obj):
        if isinstance(obj, GeoEntity): return str(id(get_rep(obj)))
        return str(id(obj))
        
    def safe_label(obj):
        if isinstance(obj, GeoEntity):
            rep = get_rep(obj)
            return f"{rep.name}\n[{rep.entity_type}]"
        if hasattr(obj, 'value'):
            return f"Const:\n{obj.value}"
        return str(obj)

    # 1. アクティブな代表元(Canonical Nodes)を描画
    for node in env.nodes:
        rep = get_rep(node)
        n_id = safe_id(rep)
        if getattr(rep, 'importance', 1.0) <= 0.0:
            continue    

        n_id = safe_id(rep)
        if n_id in drawn_nodes:
            continue
            
        color = 'lightblue'
        if rep.entity_type == 'Point': color = 'lightpink'
        elif rep.entity_type == 'Line': color = 'lightgreen'
        elif rep.entity_type == 'Circle': color = 'plum'
        elif rep.entity_type == 'Angle': color = 'gold'
        elif rep.entity_type == 'Scalar': color = 'wheat'
        elif rep.entity_type == 'Direction': color = 'lightcyan'

        dot.node(n_id, safe_label(rep), style='filled', fillcolor=color, shape='ellipse')
        drawn_nodes.add(n_id)

        comp = rep.get_best_component()
        if not comp: continue

        # 2. 定義 (Definitions) を四角いノードで描画
        for d in comp.definitions:
            if d.def_type == "Given": continue

            if any(getattr(get_rep(p), 'importance', 1.0) <= 0.0 for p in d.parents):
                continue
                
            def_node_id = f"def_{id(d)}"
            dot.node(def_node_id, d.def_type, shape='box', style='filled', fillcolor='lightgrey', fontsize='10')
            
            for parent in d.parents:
                p_id = safe_id(parent)
                if p_id not in drawn_nodes:
                    dot.node(p_id, safe_label(parent), shape='plaintext')
                    drawn_nodes.add(p_id)
                dot.edge(p_id, def_node_id, color='dimgrey')
                
            dot.edge(def_node_id, n_id, color='black', style='bold')

        # 3. リンク・所属関係 (Connected) を破線で描画
        for sub in comp.subobjects:
            sub_rep = get_rep(sub)
            
            if getattr(sub_rep, 'importance', 1.0) <= 0.0:
                continue

            sub_id = safe_id(sub_rep)
            if sub_id != n_id:
                # arrowhead='vee' を追加して方向を明確に
                dot.edge(n_id, sub_id, color='blue', style='dashed', arrowhead='vee')

    dot.render(filename, format='png', view=view, cleanup=True)
    print(f"📊 E-Graphの可視化画像を保存しました: {filename}.png")
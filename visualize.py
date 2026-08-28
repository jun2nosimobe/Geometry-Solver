import graphviz
from mmp_core import GeoEntity

def draw_egraph(env, filename="egraph_output", view=True):
    dot = graphviz.Digraph(comment='Geometry E-Graph')
    dot.attr(rankdir='LR', nodesep='0.3', ranksep='0.8', splines='polyline', concentrate='true')
    dot.attr('node', fontname='Helvetica, Arial, sans-serif', margin='0.1')

    drawn_nodes = set()
    
    def safe_id(obj):
        if isinstance(obj, GeoEntity): return str(id(obj.get_rep()))
        return str(id(obj))
        
    def safe_label(obj):
        if isinstance(obj, GeoEntity):
            rep = obj.get_rep()
            return f"{rep.name}\n[{rep.entity_type}]"
        if hasattr(obj, 'value'):
            return f"Const:\n{obj.value}"
        return str(obj)

    for node in env.nodes:
        rep = node.get_rep()
        n_id = safe_id(rep)
        if getattr(rep, 'importance', 1.0) <= 0.0 or n_id in drawn_nodes:
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

        for d in comp.definitions:
            if d.def_type == "Given": continue

            if any(getattr(p.get_rep() if hasattr(p, 'get_rep') else p, 'importance', 1.0) <= 0.0 for p in d.parents):
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

        for sub in comp.subobjects:
            sub_rep = sub.get_rep()
            if getattr(sub_rep, 'importance', 1.0) <= 0.0:
                continue

            sub_id = safe_id(sub_rep)
            if sub_id != n_id:
                dot.edge(n_id, sub_id, color='blue', style='dashed', arrowhead='vee')

    dot.render(filename, format='png', view=view, cleanup=True)
    print(f"📊 E-Graphの可視化画像を保存しました: {filename}.png")
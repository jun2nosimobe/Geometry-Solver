# action_space.py
import numpy as np
import itertools
import random

class ActionGenerator:
    def __init__(self, historical_names, tester):
        self.historical_names = historical_names
        self.tester = tester 

    def _is_collinear_mmp(self, P1, P2, P3):
        valid_count = 0
        samples = getattr(self.tester, 't_samples', [])
        if not samples: return False
        
        for t in samples[:3]: 
            cache = {}
            t_dict = {v: np.random.choice(self.tester.t_samples) for v in self.tester.all_vars}
            try:
                v1 = P1.calculate(t_dict, cache)
                v2 = P2.calculate(t_dict, cache)
                v3 = P3.calculate(t_dict, cache)
                
                x1, y1 = v1[0]/v1[-1], v1[1]/v1[-1]
                x2, y2 = v2[0]/v2[-1], v2[1]/v2[-1]
                x3, y3 = v3[0]/v3[-1], v3[1]/v3[-1]
                
                area = x1*(y2 - y3) + x2*(y3 - y1) + x3*(y1 - y2)
                
                if hasattr(area, 'value') and area.value == 0:
                    valid_count += 1
                elif not hasattr(area, 'value') and area == 0:
                    valid_count += 1
            except: pass
            
        return valid_count >= 2

    def get_possible_actions(self, nodes, is_simulation=False):
        if len(nodes) < 2: return []
        
        weights = np.array([getattr(n, 'importance', 1.0) for n in nodes])
        probs = weights / weights.sum()
        
        actions = []
        
        if not is_simulation:
            self.historical_names.update(n.name for n in nodes)
        existing_names = self.historical_names

        num_samples = 20 if is_simulation else 40

        for _ in range(num_samples): 
            X, Y = np.random.choice(nodes, size=2, replace=False, p=probs)
            
            cx = X.get_best_component()
            cy = Y.get_best_component()
            if not cx or not cy: continue

            if X.entity_type == "Line" and Y.entity_type == "Line":
                common_pts = [obj for obj in (cx.subobjects & cy.subobjects) if obj.entity_type == "Point"]
                is_para = any(X in lines and Y in lines for lines in self.tester.env.parallel_classes.values()) if hasattr(self.tester.env, 'parallel_classes') else False
                
                if not common_pts and not is_para:
                    name = f"Int_{X.name}_{Y.name}"
                    if name not in existing_names:
                        actions.append(([X, Y], "Intersection", name))
                        
            elif X.entity_type == "Point" and Y.entity_type == "Point":
                common_lines = [obj for obj in (cx.subobjects & cy.subobjects) if obj.entity_type == "Line"]
                
                if not common_lines:
                    name_line = f"Line_{X.name}_{Y.name}"
                    if name_line not in existing_names:
                        actions.append(([X, Y], "LineThroughPoints", name_line))
                
                if getattr(X, 'importance', 1.0) + getattr(Y, 'importance', 1.0) >= 10.0:
                    name_mid = f"Mid_{X.name}_{Y.name}"
                    if name_mid not in existing_names:
                        actions.append(([X, Y], "Midpoint", name_mid))
                        
            elif (X.entity_type == "Point" and Y.entity_type == "Line") or (Y.entity_type == "Point" and X.entity_type == "Line"):
                pt, ln = (X, Y) if X.entity_type == "Point" else (Y, X)
                c_pt = cx if X.entity_type == "Point" else cy
                
                name_perp = f"Perp_{pt.name}_{ln.name}"
                if name_perp not in existing_names:
                    actions.append(([ln, pt], "PerpendicularLine", name_perp))
                
                if ln not in c_pt.subobjects:
                    name_para = f"Para_{pt.name}_{ln.name}"
                    if name_para not in existing_names:
                        actions.append(([ln, pt], "ParallelLine", name_para))

            if len(nodes) >= 3:
                P1, P2, P3 = np.random.choice(nodes, size=3, replace=False, p=probs)
                if P1.entity_type == "Point" and P2.entity_type == "Point" and P3.entity_type == "Point":
                    cp1, cp2, cp3 = P1.get_best_component(), P2.get_best_component(), P3.get_best_component()
                    if cp1 and cp2 and cp3:
                        imp_sum = getattr(P1, 'importance', 1.0) + getattr(P2, 'importance', 1.0) + getattr(P3, 'importance', 1.0)
                        
                        if imp_sum >= 10.0 and not self._is_collinear_mmp(P1, P2, P3):
                            
                            if imp_sum >= 15.0:
                                common_curves = cp1.subobjects & cp2.subobjects & cp3.subobjects
                                if not common_curves: 
                                    names = sorted([P1.name, P2.name, P3.name])
                                    name_circ = f"Circum_{names[0]}_{names[1]}_{names[2]}"
                                    if name_circ not in existing_names:
                                        actions.append(([P1, P2, P3], "Circumcircle", name_circ))

                            common_lines = [obj for obj in (cp1.subobjects & cp2.subobjects & cp3.subobjects) if obj.entity_type == "Line"]
                            if not common_lines:
                                true_deg = self.tester.evaluate_triangle_numerical_degree(P1, P2, P3)
                                
                                if true_deg <= 30: 
                                    sorted_pts = sorted([P1, P2, P3], key=lambda x: x.name)
                                    name_tri = f"Tri_{sorted_pts[0].name}{sorted_pts[1].name}{sorted_pts[2].name}"
                                    if name_tri not in existing_names:
                                        actions.append((sorted_pts, "Triangle", name_tri))

        if not is_simulation:
            lines = [n for n in nodes if n.entity_type == "Line"]
            if lines:
                L = random.choice(lines)
                c_L = L.get_best_component()
                if c_L:
                    pts_on_L = [p for p in c_L.subobjects if p.entity_type == "Point"]
                    if len(pts_on_L) >= 3:
                        pts_weights = [getattr(p, 'importance', 1.0) for p in pts_on_L]
                        p_probs = np.array(pts_weights) / sum(pts_weights)
                        
                        A, B, C = np.random.choice(pts_on_L, size=3, replace=False, p=p_probs)
                        name_ratio = f"Ratio_{A.name}{B.name}_{B.name}{C.name}_(Auto)"
                        if name_ratio not in existing_names:
                            actions.append(([A, B, C], "AffineRatio", name_ratio))

            triangles = [n for n in nodes if n.entity_type == "Triangle"]
            if triangles:
                T = random.choice(triangles)
                c_T = T.get_best_component()
                if c_T and hasattr(c_T, 'triangle_points'):
                    pts = c_T.triangle_points
                    if len(pts) == 3:
                        A, B, C = pts
                        for p1, p2 in [(A, B), (B, C), (C, A)]:
                            name_len = f"LenSq_{p1.name}{p2.name}_(Auto)"
                            if name_len not in existing_names:
                                actions.append(([p1, p2], "LengthSq", name_len))

        unique_actions = []
        seen = set()
        for act in actions:
            if act[2] not in seen:
                seen.add(act[2])
                unique_actions.append(act)
                
        return unique_actions
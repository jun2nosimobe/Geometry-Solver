# action_space.py
import numpy as np
import itertools
import random

class ActionGenerator:
    """MCTSの「合法手（次に可能な作図）」を生成するジェネレータ"""
    
    def __init__(self, historical_names, tester):
        self.historical_names = historical_names
        # MMPTesterのインスタンス（次数の計算や環境へのアクセスに使用）
        self.tester = tester 

    def get_possible_actions(self, nodes, is_simulation=False):
        """現在のGeoEntity群から可能な合法手をサンプリングして返す"""
        if len(nodes) < 2: return []
        
        # 重要度(Importance)ベースのルーレット選択
        weights = np.array([n.importance for n in nodes])
        probs = weights / weights.sum()
        
        actions = []
        
        # シミュレーション中でなければ、現在の盤面にある名前を歴史に刻む
        if not is_simulation:
            self.historical_names.update(n.name for n in nodes)
        existing_names = self.historical_names

        # 40回サンプリングして有望な作図を探す
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
                # 超高速チェック: 2つの直線の subobjects に共通の「点」がすでにあるか？
                common_pts = [obj for obj in (cx.subobjects & cy.subobjects) if obj.entity_type == "Point"]
                
                # 平行チェック (平行クラスが定義されていれば)
                is_para = any(X in lines and Y in lines for lines in self.tester.env.parallel_classes.values()) if hasattr(self.tester.env, 'parallel_classes') else False
                
                # 共通の交点がなく、平行でもない場合のみ作図
                if not common_pts and not is_para:
                    name = f"Int_{X.name}_{Y.name}"
                    if name not in existing_names:
                        actions.append(([X, Y], "Intersection", name))
                        
            # ==========================================
            # 2. 点 × 点 -> 直線 / 中点
            # ==========================================
            elif X.entity_type == "Point" and Y.entity_type == "Point":
                # 超高速チェック: すでにこの2点を通る「直線」が存在しているか？
                common_lines = [obj for obj in (cx.subobjects & cy.subobjects) if obj.entity_type == "Line"]
                
                if not common_lines:
                    name_line = f"Line_{X.name}_{Y.name}"
                    if name_line not in existing_names:
                        actions.append(([X, Y], "LineThroughPoints", name_line))
                
                # 中点は重要度が高いペアでのみ許可 (計算爆発を防ぐため)
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
                
                # 超高速チェック: 点がすでにその直線上に乗っているか？ (乗っていれば平行線は引けない)
                if ln not in c_pt.subobjects:
                    name_para = f"Para_{pt.name}_{ln.name}"
                    if name_para not in existing_names:
                        actions.append(([ln, pt], "ParallelLine", name_para))

            # ==========================================
            # 4. 点 × 点 × 点 -> 外接円 ＆ 三角形(Shape)
            # ==========================================
            if len(nodes) >= 3:
                P1, P2, P3 = np.random.choice(nodes, size=3, replace=False, p=probs)
                if P1.entity_type == "Point" and P2.entity_type == "Point" and P3.entity_type == "Point":
                    cp1, cp2, cp3 = P1.get_best_component(), P2.get_best_component(), P3.get_best_component()
                    if cp1 and cp2 and cp3:
                        # --- 4-A. 外接円の作図 ---
                        if P1.importance + P2.importance + P3.importance >= 15.0:
                            # 超高速チェック: この3点を全て通る「円」または「直線(共線)」がすでにあるか？
                            common_curves = cp1.subobjects & cp2.subobjects & cp3.subobjects
                            if not common_curves: 
                                names = sorted([P1.name, P2.name, P3.name])
                                name_circ = f"Circum_{names[0]}_{names[1]}_{names[2]}"
                                if name_circ not in existing_names:
                                    actions.append(([P1, P2, P3], "Circumcircle", name_circ))

                        # --- 4-B. 三角形(Shapeコンテナ)の作図 ---
                        common_lines = [obj for obj in (cp1.subobjects & cp2.subobjects & cp3.subobjects) if obj.entity_type == "Line"]
                        # 共線ではなく、重要度が十分高いペアを抽出
                        if not common_lines and (P1.importance + P2.importance + P3.importance >= 10.0):
                            # 🌟 MMPTester に委譲: SVDで真の次数を評価して足切り
                            true_deg = self.tester.evaluate_triangle_numerical_degree(P1, P2, P3)
                            
                            # 次数が30以下(退化してない/複雑すぎない)綺麗な三角形だけを登録
                            if true_deg <= 30: 
                                sorted_pts = sorted([P1, P2, P3], key=lambda x: x.name)
                                name_tri = f"Tri_{sorted_pts[0].name}{sorted_pts[1].name}{sorted_pts[2].name}"
                                if name_tri not in existing_names:
                                    actions.append((sorted_pts, "Triangle", name_tri))

        # 重複排除処理 (同じ名前の作図を2回提案しないようにする)
        unique_actions = []
        seen = set()
        for act in actions:
            if act[2] not in seen:
                seen.add(act[2])
                unique_actions.append(act)
                
        return unique_actions
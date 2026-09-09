# problems/prob_orthocenter.py
from mmp_core import *
from logic_core import Fact

def setup_problem():
    # ★ 多変数による問題定義
    # A は変数 tA に依存して水平移動。P は変数 tP に依存して水平移動。
    A = MovingPoint(lambda tA, **kwargs: (tA, 4, 1), var_degrees={'tA': 1}, name="A")
    B = PointFixed(0, 0, 1, name="B")
    C = PointFixed(6, 0, 1, name="C")
    D = PointFixed(4, 0, 1, name="D")
    
    LineBC = LineThroughPoints(B, C, name="LineBC")
    LineAC = LineThroughPoints(A, C, name="LineAC")
    LineAB = LineThroughPoints(A, B, name="LineAB")
    
    AltA = PerpendicularLine(LineBC, A, name="AltA")
    AltB = PerpendicularLine(LineAC, B, name="AltB")
    H = Intersection(AltA, AltB, name="H")
    
    P = MovingPoint(lambda tP, **kwargs: (tP, 0, 1), var_degrees={'tP': 1}, name="P")
    
    Circum_ABC = Circle(A, B, C, name="Circum_ABC")
    LineBH = LineThroughPoints(B, H, name="LineBH")
    E = CircleLineOtherIntersection(Circum_ABC, LineBH, B, name="E")
    
    Circum_ABD = Circle(A, B, D, name="Circum_ABD")
    Circum_DHP = Circle(D, H, P, name="Circum_DHP")
    RadAxis_Q = RadicalAxis(Circum_ABD, Circum_DHP, name="RadAxis_Q")
    Q = CircleLineOtherIntersection(Circum_ABD, RadAxis_Q, D, name="Q")
    Q_prime = Reflection(Q, LineAB, name="Q'")
    
    all_nodes = [A, B, C, D, LineBC, LineAC, LineAB, AltA, AltB, H, P, 
                 Circum_ABC, LineBH, E, Circum_ABD, Circum_DHP, RadAxis_Q, Q, Q_prime]

    target_fact = Fact("Concyclic", [B, E, P, Q_prime])

    initial_facts = [
        Fact("Concyclic", [A, B, C, E], is_proven=True, proof_source="問題の仮定: Eは外接円ABC上の点"),
        Fact("Concyclic", [A, B, D, Q], is_proven=True, proof_source="問題の仮定: Qは外接円ABD上の点"),
        Fact("Concyclic", [D, H, P, Q], is_proven=True, proof_source="問題の仮定: Qは外接円DHP上の点")
    ]
    
    initial_right_angles = [
        (LineBC, AltA),
        (LineAC, AltB)
    ]
    
    # ★ この問題空間に存在するすべての独立変数（MMPが偏微分する対象）
    all_vars = ['tA', 'tP']
    
    return all_nodes, all_vars, target_fact, initial_facts, initial_right_angles
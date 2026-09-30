//! 🌟 HAGeo-409(https://huggingface.co/datasets/HAGeo-IMO/HAGeo-409)の作図スクリプトを、そのまま問題として読む。
//!
//! 問題は `hageo:<Problem_ID>`(例: `hageo:2019SilkRoadp1`)で指定する。データは `data/hageo409.tsv`
//! (ID・難易度・スクリプト)で、手で写した bench_*.rs と違って、写し間違いが入らず、調整に使っていない問題を
//! 機械的に増やせる(汎化を測る保留問題)。
//!
//! 読めるのは、このエンジンの作図語彙で有理的に書けるものだけ。円の定義(circle_center_point など)や、内心・角の二等分線・
//! 弧の中点のように平方根を要る作図、円と直線の交点は、理由を付けて「読めない」と返す(`geom_solver hageo-list`)。
//! 経緯と語彙の被覆率: docs/notes/diagnostics.md「HAGeo-409 の取り込み」。

use std::collections::HashMap;

use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};
use crate::problems::geo_helpers::{circumcenter, foot};
use crate::problems::ProblemSetup;

const DATA: &str = include_str!("../data/hageo409.tsv");

/// (Problem_ID, 難易度, スクリプト)。
pub fn all() -> Vec<(&'static str, &'static str, &'static str)> {
    DATA.lines()
        .filter_map(|l| {
            let mut f = l.splitn(3, '\t');
            Some((f.next()?, f.next()?, f.next()?))
        })
        .collect()
}

pub fn script_of(id: &str) -> Option<&'static str> {
    all().into_iter().find(|(i, _, _)| *i == id).map(|(_, _, s)| s)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind { Point, Line, Circle }

struct Builder<'a> {
    eg: &'a mut EGraph,
    env: HashMap<String, (ClassId, Kind)>,
    aux: usize,
    /// 円ごとの中心(分かっているもの)。
    centers: HashMap<usize, ClassId>,
    /// 内接円から作る三角形の頂点の名前(内心・角の二等分線を使う三角形)と、作った内心。
    incircle_for: Option<[String; 3]>,
    incenter: Option<ClassId>,
}

impl<'a> Builder<'a> {
    fn fresh(&mut self, base: &str) -> String {
        self.aux += 1;
        format!("{}_h{}", base, self.aux)
    }

    fn get(&self, name: &str, kind: Kind) -> Result<ClassId, String> {
        match self.env.get(name) {
            Some((id, k)) if *k == kind => Ok(*id),
            Some(_) => Err(format!("「{}」の種類(点/直線)が合わない", name)),
            None => Err(format!("「{}」が未定義", name)),
        }
    }

    fn point(&mut self, name: &str, def: Definition) -> ClassId {
        let id = self.eg.create_entity(name.to_string(), def, EntityType::Point);
        self.env.insert(name.to_string(), (id, Kind::Point));
        id
    }

    fn line(&mut self, name: &str, def: Definition) -> ClassId {
        let id = self.eg.create_entity(name.to_string(), def, EntityType::Line);
        self.env.insert(name.to_string(), (id, Kind::Line));
        id
    }

    fn free_point(&mut self, name: &str) -> ClassId { self.point(name, Definition::FreePoint) }

    /// 名前を付けずに(環境に入れずに)補助の実体を作る。
    fn hidden(&mut self, base: &str, def: Definition, ty: EntityType) -> ClassId {
        let n = self.fresh(base);
        self.eg.create_entity(n, def, ty)
    }

    fn line_through_points(&mut self, a: ClassId, b: ClassId, base: &str) -> ClassId {
        let n = self.fresh(base);
        let id = self.eg.create_entity(n.clone(), Definition::new_line(a, b), EntityType::Line);
        self.env.insert(n, (id, Kind::Line));
        id
    }

    fn circle(&mut self, name: &str, def: Definition, center: Option<ClassId>) -> ClassId {
        let id = self.eg.create_entity(name.to_string(), def, EntityType::Conic);
        self.env.insert(name.to_string(), (id, Kind::Circle));
        if let Some(o) = center { self.centers.insert(id.0, o); }
        id
    }

    /// 名前の種類(点・直線・円)。
    fn kind_of(&self, name: &str) -> Result<(ClassId, Kind), String> {
        self.env.get(name).copied().ok_or_else(|| format!("「{}」が未定義", name))
    }

    /// 点 P の、点 M に関する対称点(M が PP′ の中点)。P′ は調和共役 (M, ∞; P, P′) = −1 で作り、中点の実体を M と
    /// 合流させる(作図の定義なので前提として)。
    fn point_reflection(&mut self, name: &str, p: ClassId, m: ClassId, line: Option<ClassId>) -> ClassId {
        let l = match line { Some(l) => l, None => self.line_through_points(p, m, "Rl") };
        let inf = self.hidden("Rinf", Definition::DirectionOf(l), EntityType::Point);
        let q = self.point(name, Definition::HarmonicConjugateOf(m, inf, p));
        let mid = self.hidden("Rmid", Definition::Midpoint(p, q), EntityType::Point);
        self.eg.apply_congruence_closure();
        self.eg.merge_entities_justified(mid, m, crate::mmp_core::Justification::Given);
        q
    }

    /// 図にある有限の点のうち、2つの曲線の両方に(乱数座標で)乗っているもの。
    fn common_point(&mut self, a: ClassId, b: ClassId) -> Option<ClassId> {
        self.eg.apply_congruence_closure();
        let linf = self.eg.line_infinity;
        let mut pts: Vec<ClassId> = self.env.values().filter(|v| v.1 == Kind::Point).map(|v| self.eg.get_rep(v.0)).collect();
        pts.sort_by_key(|p| p.0);
        pts.dedup();
        // 構造上も両方に乗っている点を優先する(数値で同じ位置の別の点を選ぶと、「直線と円の交点は2つまで」の規則が
        // 新しい点をその点と合流させてしまう)。
        let on_both: Vec<ClassId> = pts.into_iter().filter(|&p| !self.eg.is_connected(p, linf)
            && self.eg.numeric_incidence_check(p, a, 4) == Some(true) && self.eg.numeric_incidence_check(p, b, 4) == Some(true)).collect();
        on_both.iter().copied().max_by_key(|&p| (self.eg.is_connected(p, a) as u8 + self.eg.is_connected(p, b) as u8, std::cmp::Reverse(p.0)))
    }

    /// 円の中心(外接円なら外心を作る)。
    fn center_of(&mut self, c: ClassId, name: &str) -> Result<ClassId, String> {
        if let Some(&o) = self.centers.get(&c.0) { return Ok(o); }
        let defs = self.eg.entities[c.0].components.first().map(|comp| comp.definitions.clone()).unwrap_or_default();
        for d in defs {
            if let Definition::Circumcircle(a, b, cc) = d {
                let o = circumcenter(self.eg, a, b, cc, name);
                self.centers.insert(c.0, o);
                return Ok(o);
            }
        }
        Err("円の中心が分からない".into())
    }

    /// 1つの文 `名前... = 作図 引数...` を図に足す。
    fn statement(&mut self, lhs: &[&str], prim: &str, args: &[&str]) -> Result<(), String> {
        let need = |n: usize| -> Result<(), String> {
            if args.len() == n && !lhs.is_empty() { Ok(()) } else { Err(format!("{} の引数の数が合わない", prim)) }
        };
        match prim {
            "triangle" | "acute_triangle" | "obtuse_triangle" => {
                if lhs.len() != 3 { return Err("三角形の頂点が3つでない".into()); }
                if self.incircle_for.as_ref().is_some_and(|t| t.iter().zip(lhs).all(|(a, b)| a == b)) {
                    // 内心は平方根が要るので、三角形を内接円から作る: 中心 I と円周上の3点(接点)を置き、接線どうしの交点を頂点にする。
                    let (inn, t0n) = (self.fresh("Inc"), self.fresh("Tin"));
                    let (i, t0) = (self.free_point(&inn), self.free_point(&t0n));
                    let w = self.hidden("Incircle", Definition::CircleCenterPoint(i, t0), EntityType::Conic);
                    self.centers.insert(w.0, i);
                    let mut t = vec![t0];
                    for _ in 0..2 {
                        let n = self.fresh("Tin");
                        let q = self.free_point(&n);
                        self.eg.link_logical_incidence(q, w);
                        t.push(q);
                    }
                    let tl: Vec<ClassId> = t.iter().map(|&q| self.hidden("Tan", Definition::TangentLine(w, q), EntityType::Line)).collect();
                    // 頂点 k は、接点 k の向かい(接線 k 以外の2本の交点)。
                    for (k, n) in lhs.iter().enumerate() {
                        self.point(n, Definition::Intersection(tl[(k + 1) % 3], tl[(k + 2) % 3]));
                    }
                    self.incenter = Some(i);
                } else {
                    for n in lhs { self.free_point(n); }
                }
            }
            "incenter" | "excenter" | "angle_bisector" | "angle_exbisector" => {
                need(3)?;
                let (Some(i), Some(t)) = (self.incenter, self.incircle_for.clone()) else { return Err(format!("作図「{}」は平方根が要る", prim)) };
                let mut sorted: Vec<&str> = args.to_vec();
                sorted.sort_unstable();
                let mut tri: Vec<&str> = t.iter().map(|x| x.as_str()).collect();
                tri.sort_unstable();
                if sorted != tri { return Err(format!("作図「{}」は平方根が要る(内接円から作った三角形のものでない)", prim)); }
                match prim {
                    "incenter" => { self.env.insert(lhs[0].to_string(), (i, Kind::Point)); }
                    // 傍心(最初の頂点の向かい): 他の2頂点での外角の二等分線(内角の二等分線に垂直)の交点。
                    "excenter" => {
                        let mut ext = Vec::new();
                        for n in &args[1..] {
                            let v = self.get(n, Kind::Point)?;
                            let vi = self.line_through_points(v, i, "Bis");
                            ext.push(self.hidden("ExBis", Definition::PerpendicularLine(vi, v), EntityType::Line));
                        }
                        self.point(lhs[0], Definition::Intersection(ext[0], ext[1]));
                    }
                    // 角の二等分線(真ん中の頂点での内角・外角)。
                    _ => {
                        let v = self.get(args[1], Kind::Point)?;
                        if prim == "angle_bisector" {
                            self.line(lhs[0], Definition::new_line(v, i));
                        } else {
                            let vi = self.line_through_points(v, i, "Bis");
                            self.line(lhs[0], Definition::PerpendicularLine(vi, v));
                        }
                    }
                }
            }
            "quadrilateral" => {
                if lhs.len() != 4 { return Err("四角形の頂点が4つでない".into()); }
                for n in lhs { self.free_point(n); }
            }
            "point" => { need(0)?; self.free_point(lhs[0]); }
            "line" if args.is_empty() => {
                // 任意の直線: 自由点2つを通る直線。
                let p = self.fresh("Lp"); let q = self.fresh("Lq");
                let (p, q) = (self.free_point(&p), self.free_point(&q));
                self.line(lhs[0], Definition::new_line(p, q));
            }
            "line_through" => {
                need(1)?;
                let h = self.get(args[0], Kind::Point)?;
                let q = self.fresh("Lq");
                let q = self.free_point(&q);
                self.line(lhs[0], Definition::new_line(h, q));
            }
            "line" => {
                need(2)?;
                let (a, b) = (self.get(args[0], Kind::Point)?, self.get(args[1], Kind::Point)?);
                self.line(lhs[0], Definition::new_line(a, b));
            }
            "intersection" => {
                need(2)?;
                if lhs.len() != 1 { return Err("2つの交点を同時に作る(平方根が要る)".into()); }
                let (a, b) = (self.kind_of(args[0])?, self.kind_of(args[1])?);
                match (a.1, b.1) {
                    (Kind::Line, Kind::Line) => { self.point(lhs[0], Definition::Intersection(a.0, b.0)); }
                    // 円との交点は、既に図にある点が両方に乗っていれば「もう一方の交点」として有理的に作れる。
                    (Kind::Line, Kind::Circle) | (Kind::Circle, Kind::Line) | (Kind::Circle, Kind::Circle) => {
                        let Some(k) = self.common_point(a.0, b.0) else { return Err("円との交点(既知の共有点が無く、平方根が要る)".into()) };
                        let def = match (a.1, b.1) {
                            (Kind::Line, _) => Definition::SecondIntersectionOfLineAndConic(k, a.0, b.0),
                            (_, Kind::Line) => Definition::SecondIntersectionOfLineAndConic(k, b.0, a.0),
                            _ => Definition::SecondIntersectionOfCircles(k, a.0, b.0),
                        };
                        self.point(lhs[0], def);
                    }
                    _ => return Err("交点の引数が直線・円でない".into()),
                }
            }
            "circle_center_point" => {
                need(2)?;
                let (o, p) = (self.get(args[0], Kind::Point)?, self.get(args[1], Kind::Point)?);
                self.circle(lhs[0], Definition::CircleCenterPoint(o, p), Some(o));
            }
            "circle" | "circumcircle" if args.len() == 3 => {
                let p: Result<Vec<ClassId>, String> = args.iter().map(|n| self.get(n, Kind::Point)).collect();
                let p = p?;
                self.circle(lhs[0], Definition::Circumcircle(p[0], p[1], p[2]), None);
            }
            "circle" if args.is_empty() => {
                // 任意の円: 中心と円周上の1点を自由点にする。
                let (on, pn) = (self.fresh("Co"), self.fresh("Cp"));
                let (o, p) = (self.free_point(&on), self.free_point(&pn));
                self.circle(lhs[0], Definition::CircleCenterPoint(o, p), Some(o));
            }
            "circle_diameter" => {
                need(2)?;
                let (a, b) = (self.get(args[0], Kind::Point)?, self.get(args[1], Kind::Point)?);
                let m = self.hidden("Dm", Definition::Midpoint(a, b), EntityType::Point);
                self.circle(lhs[0], Definition::CircleCenterPoint(m, a), Some(m));
            }
            "on_circle" => {
                need(1)?;
                let c = self.get(args[0], Kind::Circle)?;
                let p = self.free_point(lhs[0]);
                self.eg.link_logical_incidence(p, c);
            }
            "outside" => { need(1)?; self.get(args[0], Kind::Circle)?; self.free_point(lhs[0]); }
            "tangent" | "tangent_line" if lhs.len() == 1 => {
                need(2)?;
                let (p, c) = (self.get(args[0], Kind::Point)?, self.get(args[1], Kind::Circle)?);
                self.eg.apply_congruence_closure();
                // 円の外の点からの接線は平方根が要る。
                if self.eg.numeric_incidence_check(p, c, 4) != Some(true) { return Err("円の外の点からの接線(平方根が要る)".into()); }
                self.line(lhs[0], Definition::TangentLine(c, p));
            }
            "reflect_point_wrt_point" => {
                need(2)?;
                let (p, m) = (self.get(args[0], Kind::Point)?, self.get(args[1], Kind::Point)?);
                self.point_reflection(lhs[0], p, m, None);
            }
            "reflect_point_wrt_line" | "reflect" => {
                need(2)?;
                let p = self.get(args[0], Kind::Point)?;
                match self.kind_of(args[1])? {
                    (m, Kind::Point) => { self.point_reflection(lhs[0], p, m, None); }
                    (l, Kind::Line) => {
                        let perp = self.hidden("Rperp", Definition::PerpendicularLine(l, p), EntityType::Line);
                        let f = self.hidden("Rfoot", Definition::Intersection(l, perp), EntityType::Point);
                        self.point_reflection(lhs[0], p, f, Some(perp));
                    }
                    _ => return Err(format!("鏡映の軸「{}」が点でも直線でもない", args[1])),
                }
            }
            "right_triangle" => {
                // 最初の頂点が直角。
                if lhs.len() != 3 { return Err("三角形の頂点が3つでない".into()); }
                let (a, b) = (self.free_point(lhs[0]), self.free_point(lhs[1]));
                let ab = self.line_through_points(a, b, "RTab");
                let perp = self.hidden("RTperp", Definition::PerpendicularLine(ab, a), EntityType::Line);
                let c = self.free_point(lhs[2]);
                self.eg.link_logical_incidence(c, perp);
            }
            "isos_triangle" => {
                // 最初の頂点が頂角(OA = OB)。
                if lhs.len() != 3 { return Err("三角形の頂点が3つでない".into()); }
                let (o, a) = (self.free_point(lhs[0]), self.free_point(lhs[1]));
                let c = self.hidden("ITc", Definition::CircleCenterPoint(o, a), EntityType::Conic);
                let b = self.free_point(lhs[2]);
                self.eg.link_logical_incidence(b, c);
            }
            "parallelogram" => {
                // `A B C D = parallelogram`(A, B, C は自由)か `D = parallelogram A B C`: ABCD が平行四辺形になる D。
                let (a, b, c, d) = match (lhs.len(), args.len()) {
                    (4, 0) => { let (a, b, c) = (self.free_point(lhs[0]), self.free_point(lhs[1]), self.free_point(lhs[2])); (a, b, c, lhs[3]) }
                    (1, 3) => (self.get(args[0], Kind::Point)?, self.get(args[1], Kind::Point)?, self.get(args[2], Kind::Point)?, lhs[0]),
                    _ => return Err("平行四辺形の引数の数が合わない".into()),
                };
                let (bc, ab) = (self.line_through_points(b, c, "PGbc"), self.line_through_points(a, b, "PGab"));
                let (la, lc) = (self.hidden("PGa", Definition::ParallelLine(bc, a), EntityType::Line), self.hidden("PGc", Definition::ParallelLine(ab, c), EntityType::Line));
                self.point(d, Definition::Intersection(la, lc));
            }
            "midpoint" => {
                need(2)?;
                let (a, b) = (self.get(args[0], Kind::Point)?, self.get(args[1], Kind::Point)?);
                self.point(lhs[0], Definition::Midpoint(a, b));
            }
            "foot" => {
                need(2)?;
                let (p, l) = (self.get(args[0], Kind::Point)?, self.get(args[1], Kind::Line)?);
                let f = foot(self.eg, p, l, lhs[0]);
                self.env.insert(lhs[0].to_string(), (f, Kind::Point));
            }
            "perpendicular_line" => {
                need(2)?;
                let (p, l) = (self.get(args[0], Kind::Point)?, self.get(args[1], Kind::Line)?);
                self.line(lhs[0], Definition::PerpendicularLine(l, p));
            }
            "parallel_line" => {
                need(2)?;
                let (p, l) = (self.get(args[0], Kind::Point)?, self.get(args[1], Kind::Line)?);
                self.line(lhs[0], Definition::ParallelLine(l, p));
            }
            "on_line" => {
                need(1)?;
                let l = self.get(args[0], Kind::Line)?;
                let p = self.free_point(lhs[0]);
                self.eg.link_logical_incidence(p, l);
            }
            "perpendicular_bisector" => {
                need(2)?;
                let (a, b) = (self.get(args[0], Kind::Point)?, self.get(args[1], Kind::Point)?);
                let ab = self.line_through_points(a, b, "PBab");
                let m = self.hidden("PBm", Definition::Midpoint(a, b), EntityType::Point);
                self.line(lhs[0], Definition::PerpendicularLine(ab, m));
            }
            "circumcenter" if args.len() == 1 => {
                let c = self.get(args[0], Kind::Circle)?;
                let o = self.center_of(c, lhs[0])?;
                self.env.insert(lhs[0].to_string(), (o, Kind::Point));
            }
            "circumcenter" => {
                need(3)?;
                let p: Result<Vec<ClassId>, String> = args.iter().map(|n| self.get(n, Kind::Point)).collect();
                let p = p?;
                let o = circumcenter(self.eg, p[0], p[1], p[2], lhs[0]);
                self.env.insert(lhs[0].to_string(), (o, Kind::Point));
            }
            "orthocenter" => {
                need(3)?;
                let p: Result<Vec<ClassId>, String> = args.iter().map(|n| self.get(n, Kind::Point)).collect();
                let p = p?;
                let bc = self.line_through_points(p[1], p[2], "Hbc");
                let ac = self.line_through_points(p[0], p[2], "Hac");
                let alt_a = self.hidden("Ha", Definition::PerpendicularLine(bc, p[0]), EntityType::Line);
                let alt_b = self.hidden("Hb", Definition::PerpendicularLine(ac, p[1]), EntityType::Line);
                self.point(lhs[0], Definition::Intersection(alt_a, alt_b));
            }
            "centroid" => {
                // `G M1 M2 M3 = centroid A B C`: 重心と、BC・CA・AB の中点。
                need(3)?;
                let p: Result<Vec<ClassId>, String> = args.iter().map(|n| self.get(n, Kind::Point)).collect();
                let p = p?;
                let mids = [(p[1], p[2]), (p[2], p[0]), (p[0], p[1])];
                let mut m = Vec::new();
                for (i, (a, b)) in mids.iter().enumerate() {
                    let name = if lhs.len() == 4 { lhs[i + 1].to_string() } else { self.fresh("Gm") };
                    m.push(self.point(&name, Definition::Midpoint(*a, *b)));
                }
                let med_a = self.line_through_points(p[0], m[0], "Gma");
                let med_b = self.line_through_points(p[1], m[1], "Gmb");
                self.point(lhs[0], Definition::Intersection(med_a, med_b));
            }
            other => return Err(format!("作図「{}」はこのエンジンの語彙に無い", other)),
        }
        Ok(())
    }

    /// 「直線2本」か「点4つ(AB と CD)」を2本の直線にする。
    fn two_lines(&mut self, objs: &[(ClassId, Kind)]) -> Result<(ClassId, ClassId), String> {
        if objs.len() == 2 && objs.iter().all(|o| o.1 == Kind::Line) {
            return Ok((objs[0].0, objs[1].0));
        }
        if objs.len() == 4 && objs.iter().all(|o| o.1 == Kind::Point) {
            let l1 = self.line_through_points(objs[0].0, objs[1].0, "Gl");
            let l2 = self.line_through_points(objs[2].0, objs[3].0, "Gl");
            return Ok((l1, l2));
        }
        Err("目標の引数が直線2本でも点4つでもない".into())
    }

    fn goal(&mut self, kind: &str, names: &[&str]) -> Result<(String, Vec<ClassId>), String> {
        let objs: Result<Vec<(ClassId, Kind)>, String> = names.iter()
            .map(|n| self.env.get(*n).copied().ok_or_else(|| format!("「{}」が未定義", n))).collect();
        let objs = objs?;
        let all_points = objs.iter().all(|o| o.1 == Kind::Point);
        let p: Vec<ClassId> = objs.iter().map(|o| o.0).collect();
        match kind {
            "collinear" if all_points && (p.len() == 3 || p.len() == 4) => {
                // 3点なら PQ と PR、4点なら PQ と RS が同じ直線。
                let (l1, l2) = if p.len() == 3 {
                    (self.line_through_points(p[0], p[1], "Gl"), self.line_through_points(p[0], p[2], "Gl"))
                } else {
                    (self.line_through_points(p[0], p[1], "Gl"), self.line_through_points(p[2], p[3], "Gl"))
                };
                Ok(("Identical".into(), vec![l1, l2]))
            }
            "concyclic" if all_points && p.len() == 4 => Ok(("Concyclic".into(), p)),
            "midpoint" if all_points && p.len() == 3 => {
                // p0 が p1 p2 の中点。
                let m = self.hidden("Gm", Definition::Midpoint(p[1], p[2]), EntityType::Point);
                Ok(("Identical".into(), vec![p[0], m]))
            }
            "cong" if all_points && p.len() == 4 => {
                let a = self.hidden("GlenA", Definition::LengthSq(p[0], p[1]), EntityType::Scalar);
                let b = self.hidden("GlenB", Definition::LengthSq(p[2], p[3]), EntityType::Scalar);
                Ok(("Identical".into(), vec![a, b]))
            }
            "parallel" => {
                let (l1, l2) = self.two_lines(&objs)?;
                let d1 = self.hidden("Gd", Definition::DirectionOf(l1), EntityType::Point);
                let d2 = self.hidden("Gd", Definition::DirectionOf(l2), EntityType::Point);
                Ok(("Identical".into(), vec![d1, d2]))
            }
            "perpendicular" => {
                let (l1, l2) = self.two_lines(&objs)?;
                let d1 = self.hidden("Gd", Definition::DirectionOf(l1), EntityType::Point);
                let d2 = self.hidden("Gd", Definition::DirectionOf(l2), EntityType::Point);
                let ang = self.hidden("Ga", Definition::AnglePair(d1, d2), EntityType::Scalar);
                Ok(("Identical".into(), vec![ang, self.eg.ang90]))
            }
            "equal_angle" if all_points && p.len() == 6 => {
                // ∠(p0 p1 p2) = ∠(p3 p4 p5): 頂点は真ん中。向きは、乱数座標で成り立つほうを選ぶ。
                let (a1, a2) = (self.line_through_points(p[1], p[0], "Gl"), self.line_through_points(p[1], p[2], "Gl"));
                let (b1, b2) = (self.line_through_points(p[4], p[3], "Gl"), self.line_through_points(p[4], p[5], "Gl"));
                let mut dirs = Vec::new();
                for l in [a1, a2, b1, b2] { dirs.push(self.hidden("Gd", Definition::DirectionOf(l), EntityType::Point)); }
                let e1 = self.hidden("Ga", Definition::AnglePair(dirs[0], dirs[1]), EntityType::Scalar);
                let e2 = self.hidden("Gb", Definition::AnglePair(dirs[2], dirs[3]), EntityType::Scalar);
                let e2r = self.hidden("Gc", Definition::AnglePair(dirs[3], dirs[2]), EntityType::Scalar);
                self.eg.apply_congruence_closure();
                if self.eg.numeric_plausibility_check(e1, e2, 4) == Some(false) {
                    if self.eg.numeric_plausibility_check(e1, e2r, 4) == Some(false) {
                        return Err("等角が有向角(mod π)でどちらの向きでも成り立たない".into());
                    }
                    return Ok(("Identical".into(), vec![e1, e2r]));
                }
                Ok(("Identical".into(), vec![e1, e2]))
            }
            k => Err(format!("目標「{} ×{}」はこのエンジンの語彙に無い", k, objs.len())),
        }
    }
}

/// 内心・傍心・角の二等分線を使う三角形(スクリプトの最初の三角形で、その3頂点について使うもの)の頂点の名前。
/// この三角形は内接円から作る(内心を有理的に置くため)。
fn incircle_triangle(script: &str) -> Option<[String; 3]> {
    let stmts: Vec<(Vec<&str>, Vec<&str>)> = script.split(';').map(str::trim).filter(|s| !s.starts_with("Prove:"))
        .filter_map(|s| { let (l, r) = s.split_once('=')?; Some((l.split_whitespace().collect(), r.split_whitespace().collect())) }).collect();
    let (tri, _) = stmts.iter().find(|(l, r)| l.len() == 3 && matches!(r.first(), Some(&("triangle" | "acute_triangle" | "obtuse_triangle"))))?;
    let mut t = tri.clone();
    t.sort_unstable();
    let uses = stmts.iter().any(|(_, r)| {
        let Some((prim, args)) = r.split_first() else { return false };
        if !matches!(*prim, "incenter" | "excenter" | "angle_bisector" | "angle_exbisector") || args.len() != 3 { return false; }
        let mut a = args.to_vec();
        a.sort_unstable();
        a == t
    });
    uses.then(|| [tri[0].to_string(), tri[1].to_string(), tri[2].to_string()])
}

/// スクリプトを図に読み込む。読めなければ理由を返す。
pub fn build(script: &str, eg: &mut EGraph) -> Result<ProblemSetup, String> {
    let mut b = Builder { eg, env: HashMap::new(), aux: 0, centers: HashMap::new(), incircle_for: incircle_triangle(script), incenter: None };
    let mut target = None;
    for stmt in script.split(';').map(str::trim).filter(|s| !s.is_empty()) {
        if let Some(rest) = stmt.strip_prefix("Prove:") {
            let t: Vec<&str> = rest.split_whitespace().collect();
            let (kind, names) = t.split_first().ok_or("目標が空")?;
            target = Some(b.goal(kind, names)?);
            continue;
        }
        let (l, r) = stmt.split_once('=').ok_or_else(|| format!("読めない文: {}", stmt))?;
        let lhs: Vec<&str> = l.split_whitespace().collect();
        let rhs: Vec<&str> = r.split_whitespace().collect();
        let (prim, args) = rhs.split_first().ok_or_else(|| format!("読めない文: {}", stmt))?;
        b.statement(&lhs, prim, args)?;
    }
    b.eg.apply_congruence_closure();
    Ok(ProblemSetup { target_fact: Some(target.ok_or("目標が無い")?), initial_facts: vec![] })
}

/// `hageo:<ID>` の問題を読む。読めないものは(ベンチの対象外なので)明示して止める。
pub fn setup(id: &str, eg: &mut EGraph) -> ProblemSetup {
    println!("=== 問題(HAGeo-409): {} ===", id);
    let script = script_of(id).unwrap_or_else(|| panic!("HAGeo-409 に「{}」は無い", id));
    build(script, eg).unwrap_or_else(|e| panic!("HAGeo-409「{}」はこのエンジンでは読めない: {}", id, e))
}

/// `geom_solver hageo-list`: 各問題が読めるか。読めない理由も出す。
pub fn list() {
    let mut ok = 0;
    let mut reasons: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    for (id, diff, script) in all() {
        let mut eg = EGraph::new();
        match build(script, &mut eg) {
            Ok(_) => { ok += 1; println!("読める\t{}\t{}", id, diff); }
            Err(e) => { *reasons.entry(e.clone()).or_default() += 1; println!("読めない\t{}\t{}\t{}", id, diff, e); }
        }
    }
    println!("--- 読める {} / {}", ok, all().len());
    let mut r: Vec<_> = reasons.into_iter().collect();
    r.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (why, n) in r.iter().take(15) { println!("  {:>4}  {}", n, why); }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// データが読めて、読める問題の目標が乱数座標で偽になっていないこと(写し間違いの検出)。
    /// 判定不能(None)の数も出す ― 制約で置かれる点があるとここが None になり、検算が素通しになる。
    #[test]
    fn importable_targets_do_not_fail_numeric_check() {
        let mut ok = 0;
        let mut none = 0;
        let mut bad = Vec::new();
        for (id, _, script) in all() {
            let mut eg = EGraph::new();
            let Ok(setup) = build(script, &mut eg) else { continue };
            ok += 1;
            let Some((kind, a)) = setup.target_fact else { continue };
            let verdict = match kind.as_str() {
                "Identical" => eg.numeric_plausibility_check(a[0], a[1], 4),
                "Concyclic" => {
                    let c1 = eg.create_entity("__c1".into(), Definition::Circumcircle(a[0], a[1], a[2]), EntityType::Conic);
                    let c2 = eg.create_entity("__c2".into(), Definition::Circumcircle(a[0], a[1], a[3]), EntityType::Conic);
                    eg.numeric_plausibility_check(c1, c2, 4)
                }
                _ => None,
            };
            match verdict { Some(false) => bad.push(id), None => none += 1, Some(true) => {} }
        }
        println!("HAGeo 読める {} 件、うち検算が判定不能 {} 件", ok, none);
        assert!(ok >= 20, "読める問題が少なすぎる({}件)", ok);
        assert!(bad.is_empty(), "目標が乱数座標で成り立たない(写しの誤り、または向きの取り違え): {:?}", bad);
    }
}


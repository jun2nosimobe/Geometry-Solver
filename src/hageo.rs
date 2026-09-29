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
enum Kind { Point, Line }

struct Builder<'a> {
    eg: &'a mut EGraph,
    env: HashMap<String, (ClassId, Kind)>,
    aux: usize,
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

    /// 1つの文 `名前... = 作図 引数...` を図に足す。
    fn statement(&mut self, lhs: &[&str], prim: &str, args: &[&str]) -> Result<(), String> {
        let need = |n: usize| -> Result<(), String> {
            if args.len() == n && !lhs.is_empty() { Ok(()) } else { Err(format!("{} の引数の数が合わない", prim)) }
        };
        match prim {
            "triangle" | "acute_triangle" | "obtuse_triangle" => {
                if lhs.len() != 3 { return Err("三角形の頂点が3つでない".into()); }
                for n in lhs { self.free_point(n); }
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
                let (a, b) = (self.get(args[0], Kind::Line), self.get(args[1], Kind::Line));
                match (a, b) {
                    (Ok(a), Ok(b)) => { self.point(lhs[0], Definition::Intersection(a, b)); }
                    _ => return Err("円との交点(平方根が要る)".into()),
                }
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

/// スクリプトを図に読み込む。読めなければ理由を返す。
pub fn build(script: &str, eg: &mut EGraph) -> Result<ProblemSetup, String> {
    let mut b = Builder { eg, env: HashMap::new(), aux: 0 };
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

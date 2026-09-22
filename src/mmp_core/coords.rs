//! 🌟 図を座標で評価するときの、数の表現によらない部分。
//!
//! 数値評価は3通りある: 健全性チェックと次数の測定(有限体、eval.rs)、退化による関連の検出
//! (p進、padic_eval.rs)、発見の図示(実数、discover_viz.rs)。数の表現と計算式はそれぞれ違うが、
//! 次の2つは表現によらず同じで、ここに1つだけ置く(別々に持っていた頃は、同じバグを3か所で直していた):
//!
//! - 同値類の評価(evaluate): マージで1つの同値類に複数の定義が同居するので、計算できるものが見つかる
//!   まで順に試す。互いを参照し合う定義への再突入は in_progress で検出してその定義を諦め、成功した値だけを
//!   キャッシュする。
//! - 自由点の置き方(EGraph::place_free_points): 問題文は「Dは辺BC上」のような前提を座標ではなく接続で
//!   与えるので、そういう自由点はその曲線の上に置く。前提の相手の曲線が先に評価できるよう、置ける点から
//!   順に置き、全員が互いを待って進まなければ1点を自由に置いて循環を解く。最後に前提が本当に満たされたかを
//!   確かめる。

use std::collections::HashSet;
use rustc_hash::FxHashMap;
use super::{ClassId, Definition, EGraph, EntityType};

/// 数の表現ごとの計算式。
pub(crate) trait Geometry {
    type Shape: Clone;
    /// FreePoint / GivenPoint の値(置いた座標)。まだ置いていなければ None。
    fn free(&self, eg: &EGraph, rep: ClassId, def: &Definition) -> Option<Self::Shape>;
    /// それ以外の定義の値。親などの値は get で必要な順に取る。
    fn construct(&self, eg: &EGraph, def: &Definition, get: &mut dyn FnMut(ClassId) -> Option<Self::Shape>) -> Option<Self::Shape>;
}

/// 自由点を置くための操作(Geometry と同じ表現で)。
pub(crate) trait Placement: Geometry {
    fn is_placed(&self, eg: &EGraph, point: ClassId) -> bool;
    fn place_randomly(&mut self, eg: &EGraph, point: ClassId);
    fn unplace(&mut self, eg: &EGraph, point: ClassId);
    /// 2直線の交点に置く。置けなければ false。
    fn place_on_two_lines(&mut self, eg: &EGraph, point: ClassId, l1: &Self::Shape, l2: &Self::Shape) -> bool;
    fn place_on_line(&mut self, eg: &EGraph, point: ClassId, line: &Self::Shape) -> bool;
    /// この値の二次曲線の上に点を取れるか(既知の点を評価する前に確かめる)。
    fn conic_usable(&self, conic: &Self::Shape) -> bool;
    /// 二次曲線の上に置く。known はその曲線に定義上乗っている点の値。
    fn place_on_conic(&mut self, eg: &EGraph, point: ClassId, conic: &Self::Shape, known: &Self::Shape) -> bool;
    fn lies_on(&self, point: &Self::Shape, curve: &Self::Shape, curve_type: EntityType) -> bool;
}

/// 同値類 id の値。
pub(crate) fn evaluate<G: Geometry>(eg: &EGraph, g: &G, id: ClassId,
    cache: &mut FxHashMap<usize, G::Shape>, in_progress: &mut HashSet<usize>) -> Option<G::Shape>
{
    let rep = eg.get_rep(id);
    if let Some(v) = cache.get(&rep.0) { return Some(v.clone()); }
    if !in_progress.insert(rep.0) { return None; }
    let definitions = match eg.entities[rep.0].components.first() {
        Some(c) => c.definitions.clone(),
        None => { in_progress.remove(&rep.0); return None; }
    };
    let mut result = None;
    for def in &definitions {
        let v = match def {
            Definition::FreePoint | Definition::GivenPoint => g.free(eg, rep, def),
            _ => g.construct(eg, def, &mut |p| evaluate(eg, g, p, cache, in_progress)),
        };
        if v.is_some() { result = v; break; }
    }
    in_progress.remove(&rep.0);
    if let Some(v) = &result { cache.insert(rep.0, v.clone()); }
    result
}

/// 構造だけで決まる結果のキャッシュ。EGraph::structure_generation が変わったら丸ごと捨てる。
/// 健全性チェックは二次曲線の一致判定などから頻繁に呼ばれ、そのたびに図全体を辿り直すと、実体が数百個の図では
/// 仕事量(dfs_match の回数)に表れない時間の大半をここで使っていた。
#[derive(Clone, Default)]
pub(crate) struct StructureCache {
    generation: u64,
    extraneous: FxHashMap<usize, std::rc::Rc<Vec<ClassId>>>,
    ancestors: FxHashMap<usize, std::rc::Rc<Vec<ClassId>>>,
}

impl StructureCache {
    fn sync(&mut self, generation: u64) {
        if self.generation != generation {
            self.generation = generation;
            self.extraneous.clear();
            self.ancestors.clear();
        }
    }
}

/// place_free_points の結果。
pub(crate) enum Placed {
    /// 全員を置き、前提も満たした。
    All,
    /// 全員を置いたが、前提を満たさない点がある(all_violations が偽なら最初の1点だけ)。
    Violated(Vec<ClassId>),
    /// 置けないまま残った点がある。
    Stuck,
}

impl EGraph {
    /// 自由点 points を置く(既に置いてある点はそのまま)。前提(問題文が接続で与えた曲線)を持たない点は
    /// 乱数で、持つ点はその曲線の上に置く。
    pub(crate) fn place_free_points<P: Placement>(&self, points: &[ClassId], p: &mut P, all_violations: bool) -> Placed {
        // 図は置いている間に変わらないので、前提の曲線は点ごとに1回だけ求める。
        let mut constraints: FxHashMap<usize, Vec<ClassId>> = FxHashMap::default();
        let mut pending: Vec<ClassId> = Vec::new();
        for &fp in points {
            if p.is_placed(self, fp) { continue; }
            let curves = constraints.entry(self.get_rep(fp).0).or_insert_with(|| self.find_extraneous_incidences(fp));
            if !curves.is_empty() {
                pending.push(fp);
            } else {
                p.place_randomly(self, fp);
            }
        }

        let constrained: Vec<ClassId> = pending.clone();
        let mut cache: FxHashMap<usize, P::Shape> = FxHashMap::default();
        loop {
            if pending.is_empty() {
                // サンプリングは前提を1つしか満たさないことがあり(直線と円の両方に乗る点)、循環の解消で自由に
                // 置いた点も前提を外れうる。そういう座標で比べると正しい結合を「別物」と誤って却下するので確かめる。
                let mut violated = Vec::new();
                for &fp in &constrained {
                    if !self.incidences_hold(fp, &constraints[&self.get_rep(fp).0], p, &mut cache) {
                        violated.push(fp);
                        if !all_violations { break; }
                    }
                }
                return if violated.is_empty() { Placed::All } else { Placed::Violated(violated) };
            }
            let mut progressed = false;
            let mut still_pending = Vec::new();
            for fp in pending.drain(..) {
                if self.place_on_constraint(fp, &constraints[&self.get_rep(fp).0], p, &mut cache) {
                    progressed = true;
                } else {
                    still_pending.push(fp);
                }
            }
            pending = still_pending;
            if !progressed {
                // 全員が互いの座標を待って進まない(円 Omega=Circumcircle(A,B,C) の上の点Dがあり、Omega に
                // Circumcircle(B,C,D) が同居すると、A,B,C にも Omega への接続が制約として現れる)。必要なのは
                // 「どの点を自由に置くか」の順序だけなので、前提の曲線のどれかの定義がその点を必要とする
                // (その定義で評価すれば自動的に乗る)点のうち、最も古い1つを自由に置いて続ける。
                let pick = pending.iter().copied()
                    .filter(|&fp| constraints[&self.get_rep(fp).0].iter()
                        .all(|&c| self.some_definition_requires(fp, c)))
                    .min_by_key(|fp| fp.0);
                match pick {
                    Some(fp) => {
                        p.place_randomly(self, fp);
                        pending.retain(|&q| q != fp);
                    }
                    None => return Placed::Stuck,
                }
            }
        }
    }

    /// 前提を持つ自由点 fp を、その曲線の上に置く。評価できる直線が2本以上あれば、1本だけ選ばずに交点を取る
    /// (1本しか満たさない座標では、もう1本との正しい合流を数値チェックが却下してしまう)。
    fn place_on_constraint<P: Placement>(&self, fp: ClassId, extraneous: &[ClassId], p: &mut P, cache: &mut FxHashMap<usize, P::Shape>) -> bool {
        let rep = self.get_rep(fp);
        let ready_lines: Vec<ClassId> = extraneous.iter().copied()
            .filter(|&c| self.entities[c.0].entity_type == EntityType::Line && self.placed_enough(c, p))
            .collect();
        if ready_lines.len() >= 2 {
            let Some(v1) = evaluate(self, p, ready_lines[0], cache, &mut HashSet::new()) else { return false };
            let Some(v2) = evaluate(self, p, ready_lines[1], cache, &mut HashSet::new()) else { return false };
            return p.place_on_two_lines(self, rep, &v1, &v2);
        }
        // 置ける曲線(直線を先に)のうち最初のもの。
        let ready = |ty: EntityType| extraneous.iter().copied()
            .find(|&c| self.entities[c.0].entity_type == ty && self.placed_enough(c, p));
        let Some(curve) = ready(EntityType::Line).or_else(|| ready(EntityType::Conic)) else { return false };
        match self.entities[curve.0].entity_type {
            EntityType::Line => {
                let Some(v) = evaluate(self, p, curve, cache, &mut HashSet::new()) else { return false };
                p.place_on_line(self, rep, &v)
            }
            EntityType::Conic => {
                let Some(v) = evaluate(self, p, curve, cache, &mut HashSet::new()) else { return false };
                if !p.conic_usable(&v) { return false; }
                let Some(known) = self.conic_definition_known_point(curve) else { return false };
                // known は conic の生成元なので、placed_enough(conic) が真ならその祖先も置いてある。
                let Some(k) = evaluate(self, p, known, cache, &mut HashSet::new()) else { return false };
                p.place_on_conic(self, rep, &v, &k)
            }
            _ => false,
        }
    }

    /// 自由点 fp が、自身の定義からは従わない全ての接続を、いまの座標で実際に満たしているか。
    fn incidences_hold<P: Placement>(&self, fp: ClassId, extraneous: &[ClassId], p: &P, cache: &mut FxHashMap<usize, P::Shape>) -> bool {
        let Some(point) = evaluate(self, p, fp, cache, &mut HashSet::new()) else { return false };
        extraneous.iter().all(|&curve| {
            let Some(v) = evaluate(self, p, curve, cache, &mut HashSet::new()) else { return false };
            p.lies_on(&point, &v, self.entities[curve.0].entity_type)
        })
    }

    /// id を、置き済みの自由点だけで評価できる定義が(再帰的に)少なくとも1つあるか。まだ置いていない自由点に
    /// 依存する評価を先に弾く。同居する定義のどれか1つで評価できれば十分。
    fn placed_enough<P: Placement>(&self, id: ClassId, p: &P) -> bool {
        let mut stack = HashSet::new();
        let mut memo = FxHashMap::default();
        self.node_ready(id, p, &mut stack, &mut memo)
    }

    /// 循環に当たった経路は「評価できない」とみなす。循環の影響を受けた偽は経路に依存するので、真だけをメモ化する。
    fn node_ready<P: Placement>(&self, id: ClassId, p: &P, stack: &mut HashSet<usize>, memo: &mut FxHashMap<usize, bool>) -> bool {
        let rep = self.get_rep(id);
        if memo.contains_key(&rep.0) { return true; }
        if !stack.insert(rep.0) { return false; }
        let defs = self.entities[rep.0].components.first()
            .map(|c| c.definitions.clone()).unwrap_or_default();
        let ready = defs.iter().any(|d| match d {
            Definition::FreePoint => p.is_placed(self, rep),
            Definition::GivenPoint => true,
            _ => d.get_parents().iter().all(|&q| self.node_ready(q, p, stack, memo)),
        });
        stack.remove(&rep.0);
        if ready { memo.insert(rep.0, true); }
        ready
    }

    /// 🌟 このFreePointが、自身の座標では裏付けられない接続(incidence)を1つでも持っているか。
    pub(crate) fn has_extraneous_incidence(&self, free_point: ClassId) -> bool {
        !self.find_extraneous_incidences(free_point).is_empty()
    }

    /// 自由点の前提の曲線を全て(代表元で重複を除き、ClassId 順)。subobjects はマージ前の生のIDを持ち続けるので、
    /// 重複を落とさないと「2本の直線に乗っているなら交点」が同じ直線どうしの交点を計算して退化する。
    /// 依存判定(is_natural_incidence)は曲線ごとにメモを作り直す: そのメモは循環に当たった経路の結果も覚えてしまい、
    /// 曲線をまたいで使い回すと辿る順序で判定が変わる(一度使い回したら solve の結果が1問変わった)。
    pub(crate) fn find_extraneous_incidences(&self, free_point: ClassId) -> Vec<ClassId> {
        let rep = self.get_rep(free_point);
        {
            let mut cache = self.structure_cache.borrow_mut();
            cache.sync(self.structure_generation);
            if let Some(v) = cache.extraneous.get(&rep.0) { return v.as_ref().clone(); }
        }
        let out = self.compute_extraneous_incidences(rep);
        self.structure_cache.borrow_mut().extraneous.insert(rep.0, std::rc::Rc::new(out.clone()));
        out
    }

    fn compute_extraneous_incidences(&self, rep: ClassId) -> Vec<ClassId> {
        let Some(comp) = self.entities[rep.0].components.first() else { return Vec::new() };
        let mut out: Vec<ClassId> = comp.subobjects.iter()
            .map(|&s| self.get_rep(s))
            .filter(|&s| matches!(self.entities[s.0].entity_type, EntityType::Line | EntityType::Conic))
            .collect();
        out.sort_unstable_by_key(|c| c.0);
        out.dedup();
        out.retain(|&s| !self.is_natural_incidence(rep, s));
        out
    }

    /// curve の定義のうち少なくとも1つが point を必要とするか(= その定義で評価する限り、point が curve に
    /// 乗っていることは自動的に満たされる)。
    fn some_definition_requires(&self, point: ClassId, curve: ClassId) -> bool {
        let (point, curve) = (self.get_rep(point), self.get_rep(curve));
        let defs = match self.entities[curve.0].components.first() {
            Some(c) => c.definitions.clone(),
            None => return false,
        };
        let mut memo = FxHashMap::default();
        defs.iter().any(|d| d.get_parents().iter().any(|&q| {
            let mut stack = HashSet::new();
            self.evaluation_requires_point(point, q, &mut stack, &mut memo)
        }))
    }

    /// 🌟 Circumcircle/ConicThrough5Points の定義から、その二次曲線に乗っていることが保証された点を1つ返す
    /// (円もこの経路)。無限遠点(z=0)は二次曲線上のサンプリングに使えないので避ける。
    fn conic_definition_known_point(&self, conic: ClassId) -> Option<ClassId> {
        let rep = self.get_rep(conic);
        let comp = self.entities[rep.0].components.first()?;
        comp.definitions.iter().find_map(|def| match def {
            Definition::Circumcircle(p1, _, _) => Some(*p1),
            Definition::ConicThrough5Points(p1, p2, p3, p4, p5) => [*p1, *p2, *p3, *p4, *p5].into_iter()
                .find(|&q| !self.is_connected(q, self.line_infinity)),
            _ => None,
        })
    }

    /// 🌟 idの祖先(Definitionの親を再帰的に辿った先)にあるFreePointを全て集める。定数(GivenPoint)はそこで
    /// 打ち切る。マージ後は1つの実体が複数の定義を持ちうるので、安全側に倒して全ての定義の親を辿る。
    /// ids それぞれの祖先の自由点を、ids の順に1つの列にまとめる(同じ visited を共有して順に集めたのと同じ結果)。
    /// 根ごとの結果は構造が変わるまでキャッシュする。
    pub(crate) fn free_point_ancestors_of(&self, ids: &[ClassId]) -> Vec<ClassId> {
        let mut out: Vec<ClassId> = Vec::new();
        for &id in ids {
            let rep = self.get_rep(id);
            let cached = {
                let mut cache = self.structure_cache.borrow_mut();
                cache.sync(self.structure_generation);
                cache.ancestors.get(&rep.0).cloned()
            };
            let list = match cached {
                Some(v) => v,
                None => {
                    let mut visited = HashSet::new();
                    let mut v = Vec::new();
                    self.collect_free_point_ancestors(rep, &mut visited, &mut v);
                    let v = std::rc::Rc::new(v);
                    self.structure_cache.borrow_mut().ancestors.insert(rep.0, v.clone());
                    v
                }
            };
            // 先の根で辿った節点の子孫は全て先の根の結果に入っているので、既に入っている点だけを除けば共有 visited と同じ。
            let before = out.len();
            for &fp in list.iter() {
                if !out[..before].contains(&fp) { out.push(fp); }
            }
        }
        out
    }

    fn collect_free_point_ancestors(&self, id: ClassId, visited: &mut HashSet<usize>, out: &mut Vec<ClassId>) {
        let rep = self.get_rep(id);
        if !visited.insert(rep.0) { return; }
        let Some(c) = self.entities[rep.0].components.first() else { return };
        for def in &c.definitions.clone() {
            match def {
                Definition::FreePoint => out.push(rep),
                Definition::GivenPoint => {}
                _ => for q in def.get_parents() { self.collect_free_point_ancestors(q, visited, out); },
            }
        }
    }

    /// 図の全ての自由点(FreePoint として作られた実体の代表元、作られた順)。マージが進むと自由点が代表元で
    /// なくなるのは普通なので、代表元かどうかではなく作られた定義で拾う。
    pub(crate) fn all_free_points(&self) -> Vec<ClassId> {
        let mut seen = HashSet::new();
        self.entities.iter()
            .filter(|e| matches!(e.original_definition, Definition::FreePoint) && e.entity_type == EntityType::Point)
            .map(|e| self.get_rep(e.id))
            .filter(|r| seen.insert(r.0))
            .collect()
    }
}

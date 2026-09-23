//! 定理マッチングの「見積もりと枝刈り」。
//!
//! どのパターンを次に評価すると安いか(estimate_cost)、そして候補が多すぎるときに
//! 熱(heat)でどこまで絞るか(*_candidates / heat_capped_*)を集めてある。探索そのもの
//! (matcher.rs)からこの方針だけを切り離しておくと、「遅い・届かない」の原因が探索の構造の
//! 側なのか、絞り方の側なのかを分けて考えられる。

use std::rc::Rc;

use crate::mmp_core::{ClassId, DefKind, EntityType};
use super::*;

impl ProverEngine {
    /// 順序・相異の制約が、いま束縛されている変数の範囲だけで既に破れているか。
    ///
    /// estimate_cost はこれらの制約に「全変数が束縛されるまで INFINITY」を返すので、
    /// DFS は最後まで選ばない。それを待たずに、束縛済みの範囲で破れた枝を最も早い時点で
    /// 切る。未束縛の変数が絡む部分は通すので、通る解は減らない(マッチング中は e-graph を
    /// 書き換えないので、いま破れている制約が深いところで満たされることは無い)。
    pub(crate) fn violates_bound_part(&self, pat: &Pattern, bind: &Bind) -> bool {
        match pat {
            Pattern::Order(vars) | Pattern::OrderNonStrict(vars) => {
                let strict = matches!(pat, Pattern::Order(_));
                for i in 0..vars.len().saturating_sub(1) {
                    if let (Some(a), Some(b)) = (bind.get(&vars[i]), bind.get(&vars[i + 1])) {
                        let (ra, rb) = (self.egraph.get_rep(*a).0, self.egraph.get_rep(*b).0);
                        if (strict && ra >= rb) || (!strict && ra > rb) { return true; }
                    }
                }
                false
            }
            Pattern::Distinct(vars) => {
                let mut seen = rustc_hash::FxHashSet::default();
                for v in vars {
                    if let Some(&id) = bind.get(v)
                        && !seen.insert(self.egraph.get_rep(id).0) { return true; }
                }
                false
            }
            _ => false,
        }
    }

    pub(crate) fn calc_bind_heat(&self, bind: &Bind) -> f64 {
        let mut heat = 0.0;
        for &id in bind.values() {
            let rep = self.egraph.get_rep(id);
            heat += self.egraph.entities[rep.0].heat_with_degree();
        }
        heat
    }

    pub(crate) fn estimate_cost(&self, pat: &Pattern, bind: &Bind, theorem: &TheoremDef) -> f64 {
        let args = match pat {
            Pattern::Order(vars) | Pattern::Distinct(vars) | Pattern::OrderNonStrict(vars) => {
                return if vars.iter().any(|v| !bind.contains_key(v)) { f64::INFINITY } else { 0.0 };
            }
            // 中の変数がそろう前に評価すると「どの割り当てでも中身が成り立たない」という
            // 別の(ほぼ常に偽になる)主張になるので、順序・相異の制約と同じく最後まで待たせる。
            Pattern::Not(inner_pat) => {
                let mut vars = Vec::new();
                collect_pattern_vars(inner_pat, &mut vars);
                return if vars.iter().any(|v| !bind.contains_key(*v)) { f64::INFINITY } else { 0.0 };
            }
            _ => pat.fact_args().unwrap_or_default(),
        };
        let unbound_count = args.iter().filter(|v| !bind.contains_key(v.as_str())).count();
        if unbound_count == 0 { return 0.0; }

        let base_cost = match pat {
            Pattern::Identical { .. } => if unbound_count == 1 { 1.0 } else { 15.0 },
            Pattern::Connected { child, parent, .. } => {
                if unbound_count == 1 {
                    // 束縛済みの側から実際に伸びる枝の数そのもの(固定値だと、2本しか直線が
                    // 通らない点と12本通るハブの点が同じ安さに見えてしまう)。
                    let (bound_var, free_var) = if bind.contains_key(child) { (child, parent) } else { (parent, child) };
                    match (bind.get(bound_var), theorem.entities.get(free_var)) {
                        (Some(&id), Some(&want)) => self.egraph.count_neighbors_of_type(id, want) as f64 + 1.0,
                        _ => 5.0,
                    }
                } else {
                    // 親の型の実体数で見積もる(円のように少ない型なら安い)。
                    match theorem.entities.get(parent) {
                        Some(&expected_type) => (self.egraph.count_of_type(expected_type) as f64) * 5.0 + 10.0,
                        None => 10000.0,
                    }
                }
            }
            Pattern::DefinedBy { kind, .. } => {
                if unbound_count == args.len() {
                    let penalty = match kind {
                        DefKind::Midpoint | DefKind::LengthSq | DefKind::Intersection => 0.0,
                        DefKind::LineThroughPoints | DefKind::PerpendicularLine | DefKind::TangentLine => 10.0,
                        DefKind::DirectionOf | DefKind::AnglePair | DefKind::Circumcircle => 20.0,
                        _ => 5.0,
                    };
                    100.0 + (unbound_count as f64) + penalty
                } else {
                    10.0 + (unbound_count as f64) * 20.0
                }
            }
            _ => unreachable!("制約と Not は上で返している"),
        };

        // 束縛済みの変数が熱いほど安くする。ただし割引は基本コストの半分まで
        // (でないと「40分岐のパターンが2分岐より安く見える」ことが起きる)。
        let mut heat = 0.0;
        for v in &args {
            if let Some(&id) = bind.get(v.as_str()) {
                let rep = self.egraph.get_rep(id);
                heat += self.egraph.entities[rep.0].heat_with_degree();
            }
        }
        (base_cost - heat.min(base_cost * 0.5)).max(0.1)
    }

    /// Connected の局所スキャン((Some,None)/(None,Some))向けの熱量駆動cap。普段は候補が
    /// 少ないので全件試し、多くの点が乗る円のような「ハブ」のときだけ熱の高い順に絞る。
    pub(crate) fn heat_capped_connected_candidates(&mut self, candidates: rustc_hash::FxHashSet<ClassId>) -> Vec<ClassId> {
        let cap = if self.fanout_connected { self.fanout_heat_cap } else { self.heat_cap };
        let mut v: Vec<ClassId> = candidates.into_iter().collect();
        if v.len() > cap {
            // 数えるのは狭い方(fanout_heat_cap)で切ったときだけ。heat_cap で切った分を数えると、
            // きれいな図でも条件が成立してしまい「cap を広げても候補が増えない場面」で広げることになる。
            if self.fanout_connected { self.fanout_truncations += 1; }
            v.sort_by(|&a, &b| {
                let ha = self.egraph.entities[a.0].heat();
                let hb = self.egraph.entities[b.0].heat();
                hb.partial_cmp(&ha).unwrap_or(std::cmp::Ordering::Equal)
            });
            v.truncate(cap);
        }
        v
    }

    /// Identical 自己束縛の候補(型だけで決まるので定理をまたいで共有する)。
    /// 熱での並べ替えと cap は、熱が刻々変わるので呼び出し側が毎回行う。
    pub(crate) fn identical_self_bind_candidates(&mut self, et: EntityType) -> Rc<Vec<ClassId>> {
        let cur_gen = self.egraph.type_generation.get(&et).copied().unwrap_or(0);
        if let Some((cached, cached_gen)) = self.identical_self_bind_cache.get(&et)
            && *cached_gen == cur_gen { return cached.clone(); }
        let reps: Vec<ClassId> = self.egraph.iter_reps_of_type(et)
            .filter(|id| self.egraph.entities[id.0].is_active())
            .collect();
        let result = Rc::new(reps);
        self.identical_self_bind_cache.insert(et, (result.clone(), cur_gen));
        result
    }

    /// Scalar のうち角度だけの自己束縛候補。角度側の変化(angle_generation)でだけ作り直す。
    pub(crate) fn identical_self_bind_angle_candidates(&mut self) -> Rc<Vec<ClassId>> {
        let cur_gen = self.egraph.angle_generation;
        if let Some((cached, cached_gen)) = &self.identical_self_bind_angle_cache
            && *cached_gen == cur_gen { return cached.clone(); }
        let reps: Vec<ClassId> = self.egraph.iter_reps_of_type(EntityType::Scalar)
            .filter(|&id| self.egraph.entities[id.0].is_active() && self.egraph.is_angle_value(id))
            .collect();
        let result = Rc::new(reps);
        self.identical_self_bind_angle_cache = Some((result.clone(), cur_gen));
        result
    }

    /// Scalar のうち角度以外(長さ・積・複比)の自己束縛候補。非角度側の変化でだけ作り直す。
    pub(crate) fn identical_self_bind_plain_scalar_candidates(&mut self) -> Rc<Vec<ClassId>> {
        let cur_gen = self.egraph.plain_scalar_generation;
        if let Some((cached, cached_gen)) = &self.identical_self_bind_plain_scalar_cache
            && *cached_gen == cur_gen { return cached.clone(); }
        let reps: Vec<ClassId> = self.egraph.iter_reps_of_type(EntityType::Scalar)
            .filter(|&id| self.egraph.entities[id.0].is_active() && !self.egraph.is_angle_value(id))
            .collect();
        let result = Rc::new(reps);
        self.identical_self_bind_plain_scalar_cache = Some((result.clone(), cur_gen));
        result
    }

    /// DefinedBy で親も結果も未束縛のときの候補(結果の型の全代表元、定理をまたいで共有)。
    /// Identical の候補と違い is_active で絞らない。
    pub(crate) fn defined_by_type_scan_candidates(&mut self, et: EntityType) -> Rc<Vec<ClassId>> {
        let cur_gen = self.egraph.type_generation.get(&et).copied().unwrap_or(0);
        if let Some((cached, cached_gen)) = self.defined_by_full_scan_cache.get(&et)
            && *cached_gen == cur_gen { return cached.clone(); }
        let result = Rc::new(self.egraph.iter_reps_of_type(et).collect::<Vec<_>>());
        self.defined_by_full_scan_cache.insert(et, (result.clone(), cur_gen));
        result
    }

    /// Connected の両方未束縛のジョイン(型の組だけで決まるので定理をまたいで共有する)。
    pub(crate) fn connected_pairs_for_types(&mut self, c_type: EntityType, p_type: EntityType) -> Rc<Vec<(ClassId, ClassId)>> {
        let cur_c_gen = self.egraph.type_generation.get(&c_type).copied().unwrap_or(0);
        let cur_p_gen = self.egraph.type_generation.get(&p_type).copied().unwrap_or(0);
        if let Some((cached, gen_c, gen_p)) = self.connected_join_cache.get(&(c_type, p_type))
            && *gen_c == cur_c_gen && *gen_p == cur_p_gen {
                return cached.clone();
            }
        let mut pairs = Vec::new();
        for p_rep in self.egraph.iter_reps_of_type(p_type) {
            if !self.egraph.entities[p_rep.0].is_active() { continue; }
            if let Some(comp) = self.egraph.entities[p_rep.0].components.first() {
                for &sub in &comp.subobjects {
                    let c_rep = self.egraph.get_rep(sub);
                    if c_rep == p_rep { continue; }
                    if !self.egraph.entities[c_rep.0].is_active() { continue; }
                    if self.egraph.entities[c_rep.0].entity_type != c_type { continue; }
                    pairs.push((c_rep, p_rep));
                }
            }
        }
        let result = Rc::new(pairs);
        self.connected_join_cache.insert((c_type, p_type), (result.clone(), cur_c_gen, cur_p_gen));
        result
    }
}

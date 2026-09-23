//! 定理マッチングの探索本体(DFS)。
//!
//! パターン列を1本ずつ消費しながら変数を束縛していく深さ優先探索と、パターンの種類ごとの
//! 候補の展開。次にどのパターンを選ぶか・候補をどこまで見るかの方針は cost.rs にある。
//!
//! 失敗キャッシュ(failed_paths)の依存マスク(dep_mask)の規約:
//!   - 各 dfs_match は自分の探索用に新しいマスクを作り、子にはそれを渡す。
//!   - 候補プールを列挙した分岐は、列挙した型のビットをマスクに立てる。束縛済みの代表元を
//!     直接見るだけの検査は立てない。ただし incidence や定義の集合のように、署名(束縛の
//!     代表元)に現れない状態を見る検査は、その型のビットを立てる。
//!   - 失敗したら (マスク, 型世代) を記録し、成否に関わらずマスクを親へ OR する。

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::mmp_core::{ClassId, DefKind, Definition, EntityType, ParentSymmetry};
use super::*;

/// 🌟 いま束縛しようとしている変数に、まだ残っている他のパターンが課している制約のうち、
/// 候補1つを見るだけで判定できるもの。関係の言葉でいう semi-join に使う。
enum SemiConstraint {
    /// 束縛済みの図形と接続していること。
    ConnectedTo(ClassId),
    /// 束縛済みの図形と同じ代表元であること。
    SameAs(ClassId),
    /// 束縛済みの図形と異なる代表元であること。
    NotSameAs(ClassId),
}

/// active に残っているパターンが見る変数のビット集合。
fn core_mask(pattern_masks: &[u64], active: u64) -> u64 {
    let mut core = 0u64;
    for (i, m) in pattern_masks.iter().enumerate() {
        if active & (1u64 << i) != 0 { core |= *m; }
    }
    core
}

/// 1つの定理に対する探索の文脈。
pub(crate) struct Search<'a> {
    pub theorem: &'a TheoremDef,
    /// いま消費しているパターン列(Not の中身を調べるときはその1本だけ)。
    pub patterns: &'a [Pattern],
    /// patterns がどの列か。0 は定理のパターン列そのもの。Not の中身は別の値にして、
    /// 同じ失敗キャッシュの中で本体の状態と取り違えないようにする。
    pub scope: usize,
    pub failed_paths: &'a mut FailedPaths,
    pub on_match: &'a mut dyn FnMut(&Bind, &FlipStates),
    /// 定理の変数のビット索引(patterns と同じ添字で引く per_pattern を持つ)。
    pub var_index: &'a PatternVarIndex,
    /// patterns の各本が見る変数のビット集合。Not の中身を調べるときは1本分だけ渡す。
    pub pattern_masks: &'a [u64],
}

/// DefinedBy で親が全部そろっていて定義がまだ無いとき、その場で作ってよい種類。
pub(crate) fn created_on_demand(kind: DefKind) -> bool {
    matches!(kind, DefKind::AnglePair | DefKind::DirectionOf | DefKind::LengthSq
        | DefKind::CrossRatio | DefKind::CrossRatioOfLines | DefKind::Product)
}

impl ProverEngine {
    /// 失敗キャッシュのキー。どのパターン列の、どのパターンが残っているか・束縛(代表元に
    /// 直したもの)・フリップ状態から作る。
    ///
    /// 残りパターンは数ではなく集合で入れること。数だけだと、同じ束縛で別のパターンが
    /// 残っている状態(タスクの初期束縛が違えば消費の順序も変わる)や、Not の中身を調べた
    /// ときの失敗(残り1本)を、本体の「残り1本」の状態の失敗と取り違えて正しい枝を刈る。
    fn state_signature(&self, s: &Search<'_>, active: u64, bind: &Bind, flip_states: &FlipStates) -> u64 {
        if self.nogood_core && s.var_index.exact {
            return self.core_signature(s, active, bind, flip_states);
        }
        self.full_signature(s.scope, active, bind, flip_states)
    }

    /// 🌟 残っているパターンが実際に見る変数(核)だけで作る署名。
    ///
    /// 失敗した枝の理由は、たいてい束縛のうち数個しか使っていない。束縛を全部鍵に入れると、
    /// 無関係な変数の値の組み合わせの数だけ同じ失敗を別物として作り直すことになり、図が
    /// 大きいほど(= 無関係な作図が増えるほど)その数が掛け算で増える。
    ///
    /// 失敗する枝が見る束縛は、残っているパターンに現れる変数に限られる
    /// (パターンの選び方も、破れの早期検査も、候補の展開も、すべて残っているパターンの
    /// 引数しか見ない)。核に入らない変数は、この部分木の答えを変えられない。
    ///
    /// ただし枝の打ち切り(dfs_cap)は探索の順序に依存するので、核が同じでも「予算切れで
    /// 失敗した」かどうかまでは一致しない。そこは既存の失敗キャッシュと同じ近似。
    fn core_signature(&self, s: &Search<'_>, active: u64, bind: &Bind, flip_states: &FlipStates) -> u64 {
        let core = core_mask(s.pattern_masks, active);
        let mut hasher = rustc_hash::FxHasher::default();
        (s.scope, active).hash(&mut hasher);
        for (i, name) in s.var_index.vars.iter().enumerate() {
            if core & (1u64 << i) == 0 { continue; }
            i.hash(&mut hasher);
            match bind.get(name) {
                Some(&id) => (1u8, self.egraph.get_rep(id).0).hash(&mut hasher),
                None => (0u8, 0usize).hash(&mut hasher),
            }
            match flip_states.get(name) {
                Some(&f) => (2u8 + u8::from(f)).hash(&mut hasher),
                None => 0u8.hash(&mut hasher),
            }
        }
        hasher.finish()
    }

    fn full_signature(&self, scope: usize, active: u64, bind: &Bind, flip_states: &FlipStates) -> u64 {
        // 定理の変数は多くても20個程度なので、確保を避けてスタック上で並べる。
        // 順序に依らない畳み込み(wrapping_add)は FxHash の撹拌が弱く衝突が増えたので使わない。
        const SIG_CAP: usize = 48;
        let mut hasher = rustc_hash::FxHasher::default();
        (scope, active).hash(&mut hasher);
        let mut pairs: [(&str, usize); SIG_CAP] = [("", 0); SIG_CAP];
        let mut np = 0usize;
        for (k, v) in bind.iter() {
            if np == SIG_CAP { break; }
            pairs[np] = (k.as_str(), self.egraph.get_rep(*v).0);
            np += 1;
        }
        pairs[..np].sort_unstable_by_key(|p| p.0);
        for (k, v) in &pairs[..np] {
            k.hash(&mut hasher);
            v.hash(&mut hasher);
        }
        let mut flips: [(&str, bool); SIG_CAP] = [("", false); SIG_CAP];
        let mut nf = 0usize;
        for (k, v) in flip_states.iter() {
            if nf == SIG_CAP { break; }
            flips[nf] = (k.as_str(), *v);
            nf += 1;
        }
        flips[..nf].sort_unstable_by_key(|p| p.0);
        for (k, v) in &flips[..nf] {
            k.hash(&mut hasher);
            v.hash(&mut hasher);
        }
        hasher.finish()
    }

    /// active のビットが立っているパターンを全部満たす割り当てを探し、見つかるたびに
    /// on_match を呼ぶ。1つでも見つかれば true。
    pub(crate) fn dfs_match(
        &mut self,
        s: &mut Search<'_>,
        active: u64,
        bind: Bind,
        flip_states: FlipStates,
        dep_mask: &mut u8,
    ) -> bool {
        self.dfs_calls += 1;
        self.profile.branch_counts[self.branch_tag as usize] += 1;
        if self.dfs_calls > self.dfs_cap { return false; }

        let state_sig = self.state_signature(s, active, &bind, &flip_states);
        if let Some(&(cached_mask, cached_gens)) = s.failed_paths.get(&state_sig) {
            let still_valid = (0..4).all(|i| {
                (cached_mask & (1 << i)) == 0
                    || self.egraph.type_generation.get(&ALL_ENTITY_TYPES[i]).copied().unwrap_or(0) == cached_gens[i]
            });
            if still_valid {
                self.profile.cache_hits += 1;
                *dep_mask |= cached_mask;
                return false;
            }
            self.profile.cache_stale += 1;
        }

        let theorem = s.theorem;
        if active == 0 {
            for (v_name, id) in &bind {
                if let Some(expected_type) = theorem.entities.get(v_name) {
                    let actual_type = self.egraph.entities[self.egraph.get_rep(*id).0].entity_type;
                    if *expected_type != actual_type { return false; }
                }
            }
            (s.on_match)(&bind, &flip_states);
            return true;
        }

        // 一番安く見積もられたパターンを選ぶ。同じ1周で、束縛済みの範囲だけで既に破れている
        // 順序・相異の制約も検査して枝を早く切る(マスク0 = 型が変化しても有効な失敗)。
        let patterns = s.patterns;
        let var_sizes = if self.var_order { Some(self.constrained_var_sizes(patterns, theorem, active, &bind)) } else { None };
        let mut best_idx = 0;
        let mut best_cost = f64::INFINITY;
        for (i, pat) in patterns.iter().enumerate() {
            if active & (1u64 << i) == 0 { continue; }
            if self.violates_bound_part(pat, &bind) {
                s.failed_paths.insert(state_sig, (0, snapshot_type_generations(&self.egraph)));
                return false;
            }
            let mut cost = self.estimate_cost(pat, &bind, theorem);
            // 他のパターンがその変数を縛っているなら、交差後の候補数はその上界を超えない。
            if let Some(sizes) = var_sizes.as_ref()
                && let Some(args) = pat.fact_args() {
                    let bound = args.iter()
                        .filter(|v| !bind.contains_key(v.as_str()))
                        .filter_map(|v| sizes.iter().find(|(k, _)| *k == v.as_str()).map(|(_, n)| *n))
                        .min();
                    if let Some(n) = bound { cost = cost.min(n as f64 + 1.0); }
                }
            if cost < best_cost { best_cost = cost; best_idx = i; }
        }
        let next_active = active & !(1u64 << best_idx);
        let mut my_mask: u8 = 0;

        let matched_any = match &patterns[best_idx] {
            // 破れていれば上の1周で既に切っているので、ここでは消費するだけ。
            Pattern::Order(_) | Pattern::OrderNonStrict(_) | Pattern::Distinct(_) => {
                self.branch_tag = 0;
                self.dfs_match(s, next_active, bind, flip_states, &mut my_mask)
            }
            Pattern::Identical { a, b, pool } => {
                self.match_identical(s, a, b, *pool, next_active, &bind, flip_states, &mut my_mask)
            }
            Pattern::Connected { child, parent, child_ref, parent_ref } => {
                self.match_connected(s, child, parent, *child_ref, *parent_ref, next_active, &bind, flip_states, &mut my_mask)
            }
            Pattern::DefinedBy { kind, parents, result, flip } => {
                self.match_defined_by(s, *kind, parents, result, flip, next_active, &bind, flip_states, &mut my_mask)
            }
            Pattern::Not(inner) => {
                self.branch_tag = 0;
                let inner_masks = [s.var_index.mask_of(inner)];
                let inner_matched = {
                    let mut ignore = |_: &Bind, _: &FlipStates| {};
                    let mut inner_search = Search {
                        theorem,
                        patterns: std::slice::from_ref(&**inner),
                        scope: s.scope * 65 + best_idx + 1,
                        failed_paths: &mut *s.failed_paths,
                        on_match: &mut ignore,
                        var_index: s.var_index,
                        pattern_masks: &inner_masks,
                    };
                    self.dfs_match(&mut inner_search, 1, bind.clone(), flip_states.clone(), &mut my_mask)
                };
                if inner_matched {
                    false
                } else {
                    self.branch_tag = 0;
                    self.dfs_match(s, next_active, bind, flip_states, &mut my_mask)
                }
            }
        };

        if !matched_any {
            self.profile.dep_mask_bits[my_mask.count_ones() as usize] += 1;
            s.failed_paths.insert(state_sig, (my_mask, snapshot_type_generations(&self.egraph)));
        }
        *dep_mask |= my_mask;
        matched_any
    }

    /// Identical(a, b): 両方束縛済みなら一致の検査、片方だけなら同じ代表元で束縛、
    /// どちらも未束縛なら候補プールから a = b の自己束縛。
    #[allow(clippy::too_many_arguments)]
    fn match_identical(
        &mut self,
        s: &mut Search<'_>,
        v1: &String,
        v2: &String,
        pool: SelfBindPool,
        active: u64,
        bind: &Bind,
        flip_states: FlipStates,
        dep_mask: &mut u8,
    ) -> bool {
        let theorem = s.theorem;
        let expected_type = theorem.entities.get(v1).copied();

        match (bind.get(v1).copied(), bind.get(v2).copied()) {
            (Some(id1), Some(id2)) => {
                if self.egraph.get_rep(id1) != self.egraph.get_rep(id2) { return false; }
                self.branch_tag = 1;
                self.dfs_match(s, active, bind.clone(), flip_states.clone(), dep_mask)
            }
            (Some(id), None) | (None, Some(id)) => {
                let unbound_var = if bind.get(v1).is_none() { v1 } else { v2 };
                let mut next_bind = bind.clone();
                next_bind.insert(unbound_var.clone(), self.egraph.get_rep(id));
                self.branch_tag = 2;
                self.dfs_match(s, active, next_bind, flip_states.clone(), dep_mask)
            }
            (None, None) => {
                // 代表元ごとに1回だけ a = b を試す(同値類の中のペアを全列挙すると N² になる)。
                // Scalar は角度・長さ・積・複比が同じ型に同居しているので、プールを分けて持つ。
                let mut reps: Vec<ClassId> = match expected_type {
                    Some(EntityType::Scalar) => match pool {
                        SelfBindPool::Angle => (*self.identical_self_bind_angle_candidates()).clone(),
                        SelfBindPool::CrossRatioOfLines => self.identical_self_bind_plain_scalar_candidates().iter()
                            .copied()
                            .filter(|&id| self.egraph.is_cross_ratio_of_lines_value(id))
                            .collect(),
                        SelfBindPool::Any => (*self.identical_self_bind_plain_scalar_candidates()).clone(),
                    },
                    Some(et) => (*self.identical_self_bind_candidates(et)).clone(),
                    None => (0..self.egraph.entities.len())
                        .map(ClassId)
                        .filter(|&id| self.egraph.get_rep(id) == id && self.egraph.entities[id.0].is_active())
                        .collect(),
                };
                // 直前にマージされた(熱い)代表元が、この定理の欲しがっている候補である可能性が高い。
                reps.sort_by(|&a, &b| {
                    let ha = self.egraph.entities[a.0].heat();
                    let hb = self.egraph.entities[b.0].heat();
                    hb.partial_cmp(&ha).unwrap_or(Ordering::Equal)
                });
                // 自己束縛の候補数がそのまま下流の分岐係数に掛かる定理(同じ型の自己束縛を
                // 2つ以上持つ、または自己束縛の両側に同種の DefinedBy がぶら下がる)は狭く絞る。
                let self_bind_pattern_count = theorem.patterns.iter().filter(|p| {
                    matches!(p, Pattern::Identical { a, .. } if theorem.entities.get(a).copied() == expected_type)
                }).count();
                let squared_fanout = self_bind_pattern_count >= 2
                    || has_paired_defined_by_fanout(theorem, v1, v2);
                if self.semijoin {
                    let (mut cs, mut m) = self.semijoin_constraints(s, active, v1, bind);
                    let (cs2, m2) = self.semijoin_constraints(s, active, v2, bind);
                    cs.extend(cs2);
                    m |= m2;
                    *dep_mask |= m;
                    if !cs.is_empty() { reps.retain(|&c| self.semijoin_ok(&cs, c)); }
                }
                let cap = if squared_fanout { self.fanout_heat_cap } else { self.heat_cap };
                if squared_fanout && reps.len() > cap { self.fanout_truncations += 1; }
                reps.truncate(cap);
                *dep_mask |= expected_type.map_or(ALL_TYPES_MASK, entity_type_bit);

                let mut any = false;
                for rep in reps {
                    let mut next_bind = bind.clone();
                    next_bind.insert(v1.clone(), rep);
                    next_bind.insert(v2.clone(), rep);
                    self.branch_tag = 3;
                    any |= self.dfs_match(s, active, next_bind, flip_states.clone(), dep_mask);
                }
                any
            }
        }
    }

    /// Connected(child, parent): 束縛状況の4通りで分岐する。点と二次曲線は Refinement で
    /// 「方向か有限点か」「円かそれ以外か」を絞る。
    #[allow(clippy::too_many_arguments)]
    fn match_connected(
        &mut self,
        s: &mut Search<'_>,
        child_var: &String,
        parent_var: &String,
        child_ref: Refinement,
        parent_ref: Refinement,
        active: u64,
        bind: &Bind,
        flip_states: FlipStates,
        dep_mask: &mut u8,
    ) -> bool {
        let theorem = s.theorem;
        let expected_c_type = theorem.entities.get(child_var).copied();
        let expected_p_type = theorem.entities.get(parent_var).copied();

        match (bind.get(child_var).copied(), bind.get(parent_var).copied()) {
            (Some(c_id), Some(p_id)) => {
                // incidence は署名に現れないので、後から接続されたときに無効化できるよう型に依存させる。
                let c_type = self.egraph.entities[self.egraph.get_rep(c_id).0].entity_type;
                let p_type = self.egraph.entities[self.egraph.get_rep(p_id).0].entity_type;
                *dep_mask |= entity_type_bit(c_type) | entity_type_bit(p_type);
                if !self.egraph.is_connected(c_id, p_id) { return false; }
                self.branch_tag = 4;
                self.dfs_match(s, active, bind.clone(), flip_states.clone(), dep_mask)
            }
            (Some(c_id), None) => {
                // link_logical_incidence は常に双方向に張るので、child 自身の subobjects だけ見ればよい。
                let c_rep = self.egraph.get_rep(c_id);
                let mut candidates = rustc_hash::FxHashSet::default();
                for comp in &self.egraph.entities[c_rep.0].components {
                    for &sub in &comp.subobjects {
                        let p_rep = self.egraph.get_rep(sub);
                        if p_rep == c_rep || !self.egraph.entities[p_rep.0].is_active() { continue; }
                        if let Some(et) = expected_p_type
                            && !self.accepts(p_rep, et, parent_ref) { continue; }
                        candidates.insert(p_rep);
                    }
                }
                *dep_mask |= expected_p_type.map_or(ALL_TYPES_MASK, entity_type_bit);
                if self.semijoin {
                    let (cs, m) = self.semijoin_constraints(s, active, parent_var, bind);
                    *dep_mask |= m;
                    if !cs.is_empty() { candidates.retain(|&c| self.semijoin_ok(&cs, c)); }
                }
                let mut any = false;
                for p_rep in self.heat_capped_connected_candidates(candidates) {
                    let mut next_bind = bind.clone();
                    next_bind.insert(parent_var.clone(), p_rep);
                    self.branch_tag = 5;
                    any |= self.dfs_match(s, active, next_bind, flip_states.clone(), dep_mask);
                }
                any
            }
            (None, Some(p_id)) => {
                let p_rep = self.egraph.get_rep(p_id);
                let mut child_candidates = rustc_hash::FxHashSet::default();
                for comp in &self.egraph.entities[p_rep.0].components {
                    for &sub in &comp.subobjects {
                        let s_rep = self.egraph.get_rep(sub);
                        if self.egraph.entities[s_rep.0].is_active() { child_candidates.insert(s_rep); }
                    }
                }
                child_candidates.retain(|&c_rep| {
                    expected_c_type.is_none_or(|et| self.accepts(c_rep, et, child_ref))
                });
                *dep_mask |= expected_c_type.map_or(ALL_TYPES_MASK, entity_type_bit);
                if self.semijoin {
                    let (cs, m) = self.semijoin_constraints(s, active, child_var, bind);
                    *dep_mask |= m;
                    if !cs.is_empty() { child_candidates.retain(|&c| self.semijoin_ok(&cs, c)); }
                }
                let mut any = false;
                for c_rep in self.heat_capped_connected_candidates(child_candidates) {
                    let mut next_bind = bind.clone();
                    next_bind.insert(child_var.clone(), c_rep);
                    self.branch_tag = 6;
                    any |= self.dfs_match(s, active, next_bind, flip_states.clone(), dep_mask);
                }
                any
            }
            (None, None) => {
                *dep_mask |= match (expected_c_type, expected_p_type) {
                    (Some(ct), Some(pt)) => entity_type_bit(ct) | entity_type_bit(pt),
                    _ => ALL_TYPES_MASK,
                };
                let mut any = false;
                if let (Some(ct), Some(pt)) = (expected_c_type, expected_p_type) {
                    // 型の組だけで決まるジョインは定理をまたいで共有し、Refinement はその後でふるう。
                    let raw_pairs = self.connected_pairs_for_types(ct, pt);
                    let needs_filter = matches!(ct, EntityType::Point | EntityType::Conic)
                        || matches!(pt, EntityType::Point | EntityType::Conic);
                    let pairs: Rc<Vec<(ClassId, ClassId)>> = if needs_filter {
                        Rc::new(raw_pairs.iter().copied()
                            .filter(|&(c, p)| self.accepts(c, ct, child_ref) && self.accepts(p, pt, parent_ref))
                            .collect())
                    } else {
                        raw_pairs
                    };
                    if pairs.len() <= self.heat_cap {
                        for &(c_rep, p_rep) in pairs.iter() {
                            let mut next_bind = bind.clone();
                            next_bind.insert(child_var.clone(), c_rep);
                            next_bind.insert(parent_var.clone(), p_rep);
                            self.branch_tag = 7;
                            any |= self.dfs_match(s, active, next_bind, flip_states.clone(), dep_mask);
                        }
                    } else {
                        let mut ordered: Vec<(ClassId, ClassId)> = (*pairs).clone();
                        let heat_of = |id: ClassId| self.egraph.entities[id.0].heat();
                        ordered.sort_by(|&(c1, p1), &(c2, p2)| {
                            (heat_of(c2) + heat_of(p2)).partial_cmp(&(heat_of(c1) + heat_of(p1))).unwrap_or(Ordering::Equal)
                        });
                        ordered.truncate(self.heat_cap);
                        for (c_rep, p_rep) in ordered {
                            let mut next_bind = bind.clone();
                            next_bind.insert(child_var.clone(), c_rep);
                            next_bind.insert(parent_var.clone(), p_rep);
                            self.branch_tag = 8;
                            any |= self.dfs_match(s, active, next_bind, flip_states.clone(), dep_mask);
                        }
                    }
                } else {
                    let parent_candidates: Vec<ClassId> = match expected_p_type {
                        Some(et) => self.egraph.iter_reps_of_type(et)
                            .filter(|&p| self.egraph.entities[p.0].is_active() && self.accepts(p, et, parent_ref))
                            .collect(),
                        None => (0..self.egraph.entities.len())
                            .map(ClassId)
                            .filter(|&p| self.egraph.get_rep(p) == p && self.egraph.entities[p.0].is_active())
                            .collect(),
                    };
                    for p_rep in parent_candidates {
                        let child_candidates: Vec<ClassId> = match self.egraph.entities[p_rep.0].components.first() {
                            Some(comp) => comp.subobjects.iter()
                                .map(|&id| self.egraph.get_rep(id))
                                .filter(|&id| self.egraph.entities[id.0].is_active()
                                    && expected_c_type.is_none_or(|et| self.accepts(id, et, child_ref)))
                                .collect(),
                            None => vec![],
                        };
                        for c_rep in child_candidates {
                            let mut next_bind = bind.clone();
                            next_bind.insert(child_var.clone(), c_rep);
                            next_bind.insert(parent_var.clone(), p_rep);
                            self.branch_tag = 9;
                            any |= self.dfs_match(s, active, next_bind, flip_states.clone(), dep_mask);
                        }
                    }
                }
                any
            }
        }
    }

    /// 🌟 var をこれから束縛するとき、まだ残っているパターンのうち「相手が束縛済みで、
    /// 候補1つを見るだけで判定できる」ものを集める。あわせて、その判定が読む型の
    /// 依存ビットを返す(失敗キャッシュの無効化に必要)。
    ///
    /// ここで落ちる候補は、どのみち後でそのパターンに当たって落ちるものなので、解は減らない。
    /// 効くのは cap との順番で、今までは熱の順に cap で切ってから深いところで他のパターンに
    /// 当てていたため、他の前提を満たす「正しい候補」が cap の外に落ちることがあった。
    fn semijoin_constraints(&self, s: &Search<'_>, active: u64, var: &str, bind: &Bind) -> (Vec<SemiConstraint>, u8) {
        let mut out = Vec::new();
        let mut mask = 0u8;
        for (i, pat) in s.patterns.iter().enumerate() {
            if active & (1u64 << i) == 0 { continue; }
            match pat {
                Pattern::Connected { child, parent, .. } => {
                    let other = if child == var { parent } else if parent == var { child } else { continue };
                    if let Some(&oid) = bind.get(other) {
                        let o_rep = self.egraph.get_rep(oid);
                        mask |= entity_type_bit(self.egraph.entities[o_rep.0].entity_type);
                        out.push(SemiConstraint::ConnectedTo(o_rep));
                    }
                }
                Pattern::Identical { a, b, .. } => {
                    let other = if a == var { b } else if b == var { a } else { continue };
                    if let Some(&oid) = bind.get(other) {
                        out.push(SemiConstraint::SameAs(self.egraph.get_rep(oid)));
                    }
                }
                Pattern::Distinct(vars) => {
                    if !vars.iter().any(|v| v == var) { continue; }
                    for v in vars {
                        if v == var { continue; }
                        if let Some(&oid) = bind.get(v) {
                            out.push(SemiConstraint::NotSameAs(self.egraph.get_rep(oid)));
                        }
                    }
                }
                _ => {}
            }
        }
        (out, mask)
    }

    /// 🌟 いま残っているパターンから、各変数の候補数の上界を集める(generic join の
    /// 「次に束縛する変数の選び方」にあたる)。
    ///
    /// 「相手が束縛済みのパターン」はその変数の候補を直接生成できる(接続先の subobjects、
    /// 同一なら1個、親が全部そろった DefinedBy なら memo の1個)。交差した集合はその中で
    /// いちばん小さいものより大きくならないので、これが上界になる。見積もり(estimate_cost)は
    /// パターン1本だけを見るので、他のパターンがきつく縛っていても高く見えてしまう。
    fn constrained_var_sizes<'p>(&self, patterns: &'p [Pattern], theorem: &TheoremDef, active: u64, bind: &Bind) -> Vec<(&'p str, usize)> {
        let mut out: Vec<(&'p str, usize)> = Vec::new();
        fn note<'p>(name: &'p str, size: usize, out: &mut Vec<(&'p str, usize)>) {
            match out.iter_mut().find(|(k, _)| *k == name) {
                Some((_, v)) => *v = (*v).min(size),
                None => out.push((name, size)),
            }
        }
        for (i, pat) in patterns.iter().enumerate() {
            if active & (1u64 << i) == 0 { continue; }
            match pat {
                Pattern::Connected { child, parent, .. } => {
                    for (v, other) in [(child, parent), (parent, child)] {
                        if bind.contains_key(v) { continue; }
                        let Some(&oid) = bind.get(other) else { continue };
                        let n = match theorem.entities.get(v).copied() {
                            Some(t) => self.egraph.count_neighbors_of_type(oid, t),
                            None => self.egraph.entities[self.egraph.get_rep(oid).0]
                                .components.first().map_or(0, |c| c.subobjects.len()),
                        };
                        note(v.as_str(), n, &mut out);
                    }
                }
                Pattern::Identical { a, b, .. } => {
                    if !bind.contains_key(a) && bind.contains_key(b) { note(a.as_str(), 1, &mut out); }
                    if !bind.contains_key(b) && bind.contains_key(a) { note(b.as_str(), 1, &mut out); }
                }
                Pattern::DefinedBy { parents, result, .. } => {
                    if !bind.contains_key(result) && parents.iter().all(|p| bind.contains_key(p)) {
                        note(result.as_str(), 1, &mut out);
                    }
                }
                _ => {}
            }
        }
        out
    }

    fn semijoin_ok(&self, cs: &[SemiConstraint], cand: ClassId) -> bool {
        cs.iter().all(|c| match c {
            SemiConstraint::ConnectedTo(o) => self.egraph.is_connected(cand, *o),
            SemiConstraint::SameAs(o) => self.egraph.get_rep(cand) == *o,
            SemiConstraint::NotSameAs(o) => self.egraph.get_rep(cand) != *o,
        })
    }

    /// 候補 id が宣言型 et の Connected 変数として受理できるか。
    pub(crate) fn accepts(&self, id: ClassId, et: EntityType, refinement: Refinement) -> bool {
        let eg = &self.egraph;
        if eg.entities[id.0].entity_type != et { return false; }
        match et {
            EntityType::Point => eg.is_connected(id, eg.line_infinity) == (refinement == Refinement::Direction),
            EntityType::Conic => {
                let is_circle = eg.is_connected(id, eg.circ_i) && eg.is_connected(id, eg.circ_j);
                is_circle == (refinement == Refinement::Circle)
            }
            _ => true,
        }
    }

    /// DefinedBy(kind, parents → result): 候補ノードを絞り込み、実際に kind の定義を持つものを
    /// 親変数との整合を取りながら展開する。空振りしたら補助作図の需要として記録する。
    #[allow(clippy::too_many_arguments)]
    fn match_defined_by(
        &mut self,
        s: &mut Search<'_>,
        kind: DefKind,
        parent_vars: &[String],
        result_var: &String,
        flip: &Flip,
        active: u64,
        bind: &Bind,
        flip_states: FlipStates,
        dep_mask: &mut u8,
    ) -> bool {
        let expected_r_type = s.theorem.entities.get(result_var).copied();
        let mut valid_nodes = self.defined_by_valid_nodes(kind, result_var, parent_vars, expected_r_type, bind, dep_mask);
        // 🌟 結果が未束縛なら、定義を展開する前に他のパターンで候補を絞る。型の全代表元を
        // 舐める分岐(defined_by_type_scan_candidates)では、ここで落ちる数がそのまま効く。
        if self.semijoin && !bind.contains_key(result_var) {
            let (cs, m) = self.semijoin_constraints(s, active, result_var, bind);
            *dep_mask |= m;
            if !cs.is_empty() { valid_nodes.retain(|&c| self.semijoin_ok(&cs, c)); }
        }
        let mut matches = self.defined_by_collect_matches(kind, flip, parent_vars, result_var, &valid_nodes, bind, &flip_states);
        // 🌟 親側もここで絞る。定義から取れた親の組が他の前提と食い違っていれば、
        // 熱と次数で並べ替える前に落としておく(並べ替えは候補ごとに次数を測るので重い)。
        if self.semijoin && !matches.is_empty() {
            let mut per_var: Vec<(&String, Vec<SemiConstraint>)> = Vec::new();
            for v in parent_vars {
                if bind.contains_key(v) { continue; }
                let (cs, m) = self.semijoin_constraints(s, active, v, bind);
                *dep_mask |= m;
                if !cs.is_empty() { per_var.push((v, cs)); }
            }
            if !per_var.is_empty() {
                matches.retain(|(b, _)| per_var.iter().all(|(v, cs)| {
                    b.get(*v).is_none_or(|&id| self.semijoin_ok(cs, id))
                }));
            }
        }

        if matches.is_empty() && parent_vars.len() == 2
            && let (Some(&x), Some(&y)) = (bind.get(&parent_vars[0]), bind.get(&parent_vars[1])) {
                let (r1, r2) = (self.egraph.get_rep(x), self.egraph.get_rep(y));
                match kind {
                    // 2点はあるのに結ぶ直線が無い。
                    DefKind::LineThroughPoints if r1 != r2 => {
                        *self.construction_demands.entry((r1, r2)).or_insert(0.0) += 1.0;
                    }
                    // 2直線はあるのに交点が無い。
                    DefKind::Intersection if r1 != r2
                        && self.egraph.entities[r1.0].entity_type == EntityType::Line
                        && self.egraph.entities[r2.0].entity_type == EntityType::Line => {
                        let key = if r1.0 < r2.0 { (r1, r2) } else { (r2, r1) };
                        *self.point_construction_demands.entry(key).or_insert(0.0) += 1.0;
                    }
                    _ => {}
                }
            }

        // 熱の高い候補から試す。候補が多いときだけ、次数の低い(単純な構成の)候補を優先する
        // (次数の測定は重いので少数のときは省く。MAX_D は乱数サンプリングで順位がぶれない大きさ)。
        const DEGREE_HEURISTIC_THRESHOLD: usize = 10;
        const DEGREE_MAX_D_FOR_ORDERING: usize = 4;
        const DEGREE_WEIGHT: f64 = 3.0;
        let use_degree_heuristic = matches.len() > DEGREE_HEURISTIC_THRESHOLD;
        let degree_score = |b: &Bind| -> f64 {
            if !use_degree_heuristic { return 0.0; }
            b.get(result_var)
                .and_then(|&id| self.egraph.cached_degree(id, DEGREE_MAX_D_FOR_ORDERING))
                .unwrap_or(0) as f64
        };
        // 並べ替えのキー(熱と、同点のときの決定的な順序・重複除去に使う束縛の文字列)は
        // 候補ごとに1回だけ作る。
        let mut keyed: Vec<(f64, String, Bind, FlipStates)> = matches.into_iter().map(|(b, f)| {
            let score = self.calc_bind_heat(&b) - DEGREE_WEIGHT * degree_score(&b);
            let mut keys: Vec<_> = b.iter().collect();
            keys.sort_by_key(|k| k.0);
            let key = format!("{:?}", keys);
            (score, key, b, f)
        }).collect();
        keyed.sort_by(|x, y| y.0.partial_cmp(&x.0).unwrap_or(Ordering::Equal).then_with(|| x.1.cmp(&y.1)));
        keyed.dedup_by(|later, earlier| later.1 == earlier.1);
        let mut any = false;
        for (_, _, new_bind, new_flip) in keyed {
            self.branch_tag = 10;
            any |= self.dfs_match(s, active, new_bind, new_flip, dep_mask);
        }
        any
    }

    /// DefinedBy の候補ノード: 結果が束縛済みならそれ1つ、親が全部束縛済みなら memo から
    /// (無ければ created_on_demand の種類に限り作る)、親の一部だけなら束縛済みの親の uses、
    /// どれでもなければ結果の型の全代表元。
    fn defined_by_valid_nodes(
        &mut self,
        kind: DefKind,
        result_var: &String,
        parent_vars: &[String],
        expected_r_type: Option<EntityType>,
        bind: &Bind,
        dep_mask: &mut u8,
    ) -> Vec<ClassId> {
        let mut valid_nodes = Vec::new();

        if let Some(&res_id) = bind.get(result_var) {
            // 結果の実体は後からマージで定義を吸収しうるので、その型に依存させる。
            let res_rep = self.egraph.get_rep(res_id);
            *dep_mask |= entity_type_bit(self.egraph.entities[res_rep.0].entity_type);
            valid_nodes.push(res_rep);
        } else if parent_vars.iter().all(|v| bind.contains_key(v)) {
            *dep_mask |= expected_r_type.map_or(ALL_TYPES_MASK, entity_type_bit);
            let parent_ids: Vec<ClassId> = parent_vars.iter().map(|v| self.egraph.get_rep(bind[v])).collect();
            let Some(temp_def) = self.egraph.build_definition(kind, &parent_ids) else { return valid_nodes };

            if let Some(&existing) = self.egraph.memo.get(&temp_def) {
                valid_nodes.push(self.egraph.get_rep(existing));
            } else if created_on_demand(kind) {
                // 無関係な4点・4直線の複比は次数が積み上がるので、高すぎるものは作らない。
                if let Definition::CrossRatio(a, b, c, d) | Definition::CrossRatioOfLines(a, b, c, d) = temp_def {
                    const CR_DEGREE_CAP: usize = 8;
                    const CR_MAX_D: usize = 6;
                    if let Some((da, db, dc, dd, d_cr)) = self.egraph.measure_cross_ratio_affinity(a, b, c, d, CR_MAX_D)
                        && d_cr > CR_DEGREE_CAP {
                            println!("  🚫 [複比の生成を制限] 次数{}(次数{}+{}+{}+{})が高すぎるため、{}の生成を見送りました", d_cr, da, db, dc, dd, kind.name());
                            return valid_nodes;
                        }
                }

                let p_names: Vec<String> = parent_ids.iter()
                    .map(|&id| self.egraph.entities[id.0].name.clone())
                    .collect();
                let name = format!("{}_{}_(Auto)", kind.label(), p_names.join("_"));
                let prev_origin = self.egraph.set_origin(crate::mmp_core::EntityOrigin::DefinedBy);
                let new_id = self.egraph.create_entity(name, temp_def.clone(), temp_def.default_entity_type());
                self.egraph.apply_trivial_relations(new_id, &temp_def);
                self.egraph.set_origin(prev_origin);
                if matches!(kind, DefKind::CrossRatio | DefKind::CrossRatioOfLines) {
                    self.egraph.detect_cross_ratio_coincidences(new_id);
                }
                valid_nodes.push(new_id);
            }
        } else if let Some(&anchor_raw) = parent_vars.iter().find_map(|v| bind.get(v)) {
            // 真に有効な結果は必ず anchor を親に持つ(= anchor の uses に登録済み)ので、取りこぼさない。
            *dep_mask |= expected_r_type.map_or(ALL_TYPES_MASK, entity_type_bit);
            let anchor = self.egraph.get_rep(anchor_raw);
            let mut seen = rustc_hash::FxHashSet::default();
            for &used_id in &self.egraph.entities[anchor.0].uses {
                let u_rep = self.egraph.get_rep(used_id);
                if let Some(et) = expected_r_type
                    && self.egraph.entities[u_rep.0].entity_type != et { continue; }
                if seen.insert(u_rep) {
                    valid_nodes.push(u_rep);
                }
            }
        } else if let Some(et) = expected_r_type {
            *dep_mask |= entity_type_bit(et);
            let cached = self.defined_by_type_scan_candidates(et);
            valid_nodes.extend(cached.iter().copied());
        } else {
            *dep_mask |= ALL_TYPES_MASK;
            valid_nodes.extend((0..self.egraph.entities.len()).map(ClassId).filter(|&id| self.egraph.get_rep(id) == id));
        }

        valid_nodes
    }

    /// 候補ノードのうち kind の定義を持つものについて、親変数への割り当て(親の対称性と
    /// 有向角の向きの分だけ)を展開する。e-graph は変更しない。
    #[allow(clippy::too_many_arguments)]
    fn defined_by_collect_matches(
        &self,
        kind: DefKind,
        flip: &Flip,
        parent_vars: &[String],
        result_var: &String,
        valid_nodes: &[ClassId],
        bind: &Bind,
        flip_states: &FlipStates,
    ) -> Vec<(Bind, FlipStates)> {
        let group = match flip { Flip::Grouped(g) => Some(g), _ => None };
        let mut matches = Vec::new();
        for &node_id in valid_nodes {
            for comp in &self.egraph.entities[node_id.0].components {
                for d in &comp.definitions {
                    if d.kind() != Some(kind) { continue; }
                    let p = d.get_parents();
                    if p.len() != parent_vars.len() { continue; }

                    let perms: Vec<(Vec<ClassId>, Option<bool>)> = match kind.parent_symmetry() {
                        ParentSymmetry::Unordered if p.len() == 2 => vec![
                            (vec![p[0], p[1]], None), (vec![p[1], p[0]], None),
                        ],
                        ParentSymmetry::Unordered if p.len() == 3 => vec![
                            (vec![p[0], p[1], p[2]], None), (vec![p[0], p[2], p[1]], None),
                            (vec![p[1], p[0], p[2]], None), (vec![p[1], p[2], p[0]], None),
                            (vec![p[2], p[0], p[1]], None), (vec![p[2], p[1], p[0]], None),
                        ],
                        ParentSymmetry::KleinFour if p.len() == 4 => vec![
                            (vec![p[0], p[1], p[2], p[3]], None), (vec![p[1], p[0], p[3], p[2]], None),
                            (vec![p[2], p[3], p[0], p[1]], None), (vec![p[3], p[2], p[1], p[0]], None),
                        ],
                        ParentSymmetry::Ordered if kind == DefKind::AnglePair && *flip != Flip::Fixed && p.len() == 2 => {
                            let state = group.and_then(|g| flip_states.get(g).copied());
                            let mut v = Vec::new();
                            if state != Some(true) { v.push((vec![p[0], p[1]], Some(false))); }
                            if state != Some(false) { v.push((vec![p[1], p[0]], Some(true))); }
                            v
                        }
                        _ => vec![(p.clone(), None)],
                    };

                    for (p_ids, flip_val) in perms {
                        let mut next_bind = bind.clone();
                        let mut conflict = false;
                        for (v_name, &p_id) in parent_vars.iter().zip(p_ids.iter()) {
                            if let Some(&existing) = next_bind.get(v_name)
                                && self.egraph.get_rep(existing) != self.egraph.get_rep(p_id) { conflict = true; break; }
                            next_bind.insert(v_name.clone(), p_id);
                        }
                        if let Some(&existing) = next_bind.get(result_var)
                            && self.egraph.get_rep(existing) != node_id { conflict = true; }
                        next_bind.insert(result_var.clone(), node_id);
                        if conflict { continue; }

                        let mut next_flip = flip_states.clone();
                        if let Some(val) = flip_val {
                            if let Some(g) = group { next_flip.insert(g.clone(), val); }
                            next_flip.insert(result_var.clone(), val);
                        }
                        matches.push((next_bind, next_flip));
                    }
                }
            }
        }
        matches
    }

    pub fn is_already_proven(&self, conclusions: &[Conclusion], bind: &Bind, flips: &FlipStates) -> bool {
        conclusions.iter().all(|conc| match conc {
            Conclusion::Identical(a, b) => match (bind.get(a), bind.get(b)) {
                // 向き(フリップ)が違う角どうしは同じ値ではない。角以外はフリップ状態を持たない。
                (Some(&id1), Some(&id2)) => self.egraph.get_rep(id1) == self.egraph.get_rep(id2)
                    && flips.get(a).copied().unwrap_or(false) == flips.get(b).copied().unwrap_or(false),
                _ => false,
            },
            Conclusion::Connected(c, p) => match (bind.get(c), bind.get(p)) {
                (Some(&child), Some(&parent)) => self.egraph.is_connected(child, parent),
                _ => false,
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mmp_core::EGraph;

    /// Not の中身が成り立たなかった(= Not が通った)ときの記録が、同じ束縛で残り1本になった
    /// 本体の状態の失敗と取り違えられないこと。取り違えると、Not の直後に最後のパターンが
    /// 残る定理は決してマッチしない。
    #[test]
    fn a_passed_not_does_not_block_the_last_pattern() {
        let mut eg = EGraph::new();
        let a = eg.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let b = eg.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let line_def = Definition::new_line(a, b);
        let l = eg.create_entity("L".into(), line_def.clone(), EntityType::Line);
        eg.apply_trivial_relations(l, &line_def);

        let s = |x: &str| x.to_string();
        let on = |c: &str, p: &str| Pattern::Connected {
            child: s(c), parent: s(p), child_ref: Refinement::Default, parent_ref: Refinement::Default,
        };
        let theorem = TheoremDef {
            name: s("2点が相異なる直線上の点"),
            entities: [("A", EntityType::Point), ("B", EntityType::Point), ("L", EntityType::Line)]
                .iter().map(|(k, v)| (s(k), *v)).collect(),
            patterns: vec![
                on("A", "L"),
                on("B", "L"),
                Pattern::Not(Box::new(Pattern::Identical { a: s("A"), b: s("B"), pool: SelfBindPool::Any })),
                Pattern::Distinct(vec![s("A"), s("B")]),
            ],
            constructions: vec![],
            conclusions: vec![],
        };

        let mut prover = ProverEngine::new(eg);
        let mut failed_paths = FailedPaths::default();
        let mut found = 0;
        let mut count = |_: &Bind, _: &FlipStates| found += 1;
        let var_index = PatternVarIndex::build(&theorem);
        let mut search = Search {
            theorem: &theorem,
            patterns: &theorem.patterns,
            scope: 0,
            failed_paths: &mut failed_paths,
            on_match: &mut count,
            var_index: &var_index,
            pattern_masks: &var_index.per_pattern,
        };
        let mut dep_mask = 0;
        prover.dfs_match(&mut search, 0b1111, Bind::default(), FlipStates::default(), &mut dep_mask);
        assert_eq!(found, 2, "(A, B) と (B, A) の2通りが見つかるはず");
    }
}

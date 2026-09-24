//! 🌟 関係マッチング(generic join)の試作。既定は無効(`--generic-join`)。
//!
//! 既存の matcher.rs は「パターンを1本選んで候補を出し、次のパターンへ」という
//! 入れ子ループ結合で、中間結果の爆発を熱cap(heat_cap / fanout_heat_cap)で抑えている。
//! こちらは順番が逆で、「次に束縛する変数」を選び、その変数に触れる全パターンの
//! 候補集合を交差させてから束縛する。交差で抑えるので cap を使わない。
//!
//! 扱えないパターン(現状 Not だけ)を含む定理は、呼び出し側で従来の探索に回す。

use crate::mmp_core::{ClassId, DefKind, Definition, EntityType, ParentSymmetry};
use super::*;
use super::matcher::created_on_demand;

/// 1つの変数の候補をどこから出すか。Any は「このパターンからは絞れない」。
enum Cands {
    Set(Vec<ClassId>),
    /// 親がそろっていて図形がまだ無いが、作ってよい種類。作れば候補はちょうど1個。
    /// 見積もりの段階では作らず、その変数に決めたときだけ作る(図を無駄に膨らませないため)。
    Creatable,
    Any,
}

pub(crate) struct GenJoin<'a> {
    pub theorem: &'a TheoremDef,
    /// 前提に現れる変数(束縛の順序はここから毎回選び直す)。
    pub vars: Vec<String>,
    pub on_match: &'a mut dyn FnMut(&Bind, &FlipStates),
    pub matched: bool,
    /// 通知したマッチの数。上限に達したら探索を打ち切る。
    pub emitted: usize,
}

/// この定理を generic join で扱えるか。
pub(crate) fn supported(theorem: &TheoremDef) -> bool {
    !theorem.patterns.iter().any(|p| matches!(p, Pattern::Not(_)))
}

impl ProverEngine {
    /// theorem の前提を全部満たす割り当てを探し、見つかるたびに on_match を呼ぶ。
    pub(crate) fn genjoin_match(
        &mut self,
        theorem: &TheoremDef,
        seed: Bind,
        on_match: &mut dyn FnMut(&Bind, &FlipStates),
    ) -> bool {
        let mut names: Vec<&str> = Vec::new();
        for pat in &theorem.patterns {
            collect_pattern_vars(pat, &mut names);
        }
        let mut vars: Vec<String> = Vec::new();
        for n in names {
            if !vars.iter().any(|v| v == n) { vars.push(n.to_string()); }
        }
        let mut gj = GenJoin { theorem, vars, on_match, matched: false, emitted: 0 };
        self.gj_solve(&mut gj, seed, FlipStates::default());
        gj.matched
    }

    fn gj_solve(&mut self, gj: &mut GenJoin, bind: Bind, flips: FlipStates) {
        self.dfs_calls += 1;
        if self.dfs_calls > self.dfs_cap || gj.emitted >= self.heat_cap { return; }

        // 次に束縛する変数は、交差した候補集合がいちばん小さいもの。
        let theorem = gj.theorem;
        let vars = gj.vars.clone();
        // 🌟 その場生成は「候補が1個」だが、図そのものを増やす副作用がある。cap を外すと
        // これに歯止めが無くなり、図が膨らんで探索が重くなる(来歴 #58 で実測)。
        // 従来の見積もり(estimate_cost)が親のそろった DefinedBy に付けている値と同じ重みで
        // 扱い、他に安く束縛できる変数があればそちらを先にする。
        const CREATE_COST: usize = 0;
        let mut best: Option<(String, Vec<ClassId>)> = None;
        let mut best_len = usize::MAX;
        let mut creatable: Option<String> = None;
        for v in vars {
            if bind.contains_key(&v) { continue; }
            let (cands, can_create) = self.gj_candidates(theorem, &v, &bind, false);
            if can_create {
                if CREATE_COST < best_len {
                    best_len = CREATE_COST;
                    creatable = Some(v);
                    best = None;
                }
                continue;
            }
            let Some(c) = cands else { return };
            if c.is_empty() { return; }
            if c.len() < best_len {
                best_len = c.len();
                best = Some((v, c));
                creatable = None;
            }
        }
        if let Some(v) = creatable {
            // ここで初めて作る。
            let (cands, _) = self.gj_candidates(theorem, &v, &bind, true);
            let Some(c) = cands else { return };
            if c.is_empty() { return; }
            best = Some((v, c));
        }

        let Some((var, cands)) = best else {
            // 全部束縛できた。前提を1本ずつ検査する。
            self.gj_verify(gj, &bind, flips, 0);
            return;
        };

        for c in cands {
            let mut next = bind.clone();
            next.insert(var.clone(), c);
            self.gj_solve(gj, next, flips.clone());
            // 🌟 絞るのは中間結果ではなく出力の方。従来の探索は候補を cap で切るので
            // 「どの候補が落ちるか」が順序に左右されるが、こちらは全部の解を同じ順で
            // 出しつつ、適用する数だけを上限で止める。
            if self.dfs_calls > self.dfs_cap || gj.emitted >= self.heat_cap { return; }
        }
    }

    /// 変数 v の候補。戻り値は (候補 / None は交差が空, その場生成が必要か)。
    /// allow_create が false のあいだは図形を作らない ― 見積もりのたびに作ると図が膨らむ。
    fn gj_candidates(&mut self, theorem: &TheoremDef, v: &str, bind: &Bind, allow_create: bool)
        -> (Option<Vec<ClassId>>, bool) {
        let want = theorem.entities.get(v).copied();
        let mut acc: Option<Vec<ClassId>> = None;
        for pat in &theorem.patterns {
            let set = match self.gj_gen_for(theorem, pat, v, bind, allow_create) {
                Cands::Any => continue,
                Cands::Creatable => return (None, true),
                Cands::Set(s) => s,
            };
            acc = Some(match acc {
                None => set,
                Some(prev) => {
                    let (small, big) = if prev.len() <= set.len() { (prev, set) } else { (set, prev) };
                    small.into_iter().filter(|x| big.contains(x)).collect()
                }
            });
            if acc.as_ref().is_some_and(|a| a.is_empty()) { return (None, false); }
        }
        let mut out = match acc {
            Some(a) => a,
            // どのパターンからも絞れない変数は、型の全代表元から取る。Scalar は角度・長さ・
            // 複比が同居しているので、Identical が指定しているプールがあればそれに合わせる
            // (従来の探索と同じ候補集合にそろえる)。
            None => match want {
                Some(EntityType::Scalar) => {
                    let pool = theorem.patterns.iter().find_map(|p| match p {
                        Pattern::Identical { a, b, pool } if a == v || b == v => Some(*pool),
                        _ => None,
                    });
                    self.egraph.iter_reps_of_type(EntityType::Scalar)
                        .filter(|&id| self.egraph.entities[id.0].is_active())
                        .filter(|&id| match pool {
                            Some(SelfBindPool::Angle) => self.egraph.is_angle_value(id),
                            Some(SelfBindPool::CrossRatioOfLines) => self.egraph.is_cross_ratio_of_lines_value(id),
                            Some(SelfBindPool::Any) => !self.egraph.is_angle_value(id),
                            None => true,
                        })
                        .collect()
                }
                Some(et) => self.egraph.iter_reps_of_type(et)
                    .filter(|&id| self.egraph.entities[id.0].is_active())
                    .collect(),
                None => (0..self.egraph.entities.len()).map(ClassId)
                    .filter(|&id| self.egraph.get_rep(id) == id && self.egraph.entities[id.0].is_active())
                    .collect(),
            },
        };
        let refinement = theorem.patterns.iter().find_map(|p| match p {
            Pattern::Connected { child, parent, child_ref, parent_ref } => {
                if child == v { Some(*child_ref) } else if parent == v { Some(*parent_ref) } else { None }
            }
            _ => None,
        });
        out.retain(|&c| {
            let rep = self.egraph.get_rep(c);
            if rep != c || !self.egraph.entities[rep.0].is_active() { return false; }
            if let Some(et) = want {
                match refinement {
                    Some(r) => if !self.accepts(rep, et, r) { return false },
                    None => if self.egraph.entities[rep.0].entity_type != et { return false },
                }
            }
            self.gj_ok_constraints(theorem, v, rep, bind)
        });
        out.sort_unstable_by_key(|c| c.0);
        out.dedup();
        // 🌟 出す順は熱の高い順。上限(heat_cap)で打ち切るのは候補ではなくマッチの方なので、
        // 「直近のマージに関わった図形から先に試す」という従来の優先順をここで効かせないと、
        // 上限に入るのが図形IDの若い順という無意味な選び方になる。同点は ID 順で決定的にする。
        out.sort_by(|&a, &b| {
            let (ha, hb) = (self.egraph.entities[a.0].heat(), self.egraph.entities[b.0].heat());
            hb.partial_cmp(&ha).unwrap_or(std::cmp::Ordering::Equal).then(a.0.cmp(&b.0))
        });
        (Some(out), false)
    }

    /// 親がそろった DefinedBy の図形がまだ無いとき、作ってよい種類ならその場で作る。
    /// 従来の探索(defined_by_valid_nodes)と同じ条件・同じ副作用にそろえてある。
    fn gj_create_on_demand(&mut self, kind: DefKind, parent_ids: &[ClassId], def: Definition) -> Option<ClassId> {
        if !created_on_demand(kind) { return None; }
        // 無関係な4点・4直線の複比は次数が積み上がるので、高すぎるものは作らない。
        if let Definition::CrossRatio(a, b, c, d) | Definition::CrossRatioOfLines(a, b, c, d) = def {
            const CR_DEGREE_CAP: usize = 8;
            const CR_MAX_D: usize = 6;
            if let Some((da, db, dc, dd, d_cr)) = self.egraph.measure_cross_ratio_affinity(a, b, c, d, CR_MAX_D)
                && d_cr > CR_DEGREE_CAP {
                    println!("  🚫 [複比の生成を制限] 次数{}(次数{}+{}+{}+{})が高すぎるため、{}の生成を見送りました", d_cr, da, db, dc, dd, kind.name());
                    return None;
                }
        }
        let p_names: Vec<String> = parent_ids.iter()
            .map(|&id| self.egraph.entities[id.0].name.clone())
            .collect();
        let name = format!("{}_{}_(Auto)", kind.label(), p_names.join("_"));
        let prev_origin = self.egraph.set_origin(crate::mmp_core::EntityOrigin::DefinedBy);
        let new_id = self.egraph.create_entity(name, def.clone(), def.default_entity_type());
        self.egraph.apply_trivial_relations(new_id, &def);
        self.egraph.set_origin(prev_origin);
        if matches!(kind, DefKind::CrossRatio | DefKind::CrossRatioOfLines) {
            self.egraph.detect_cross_ratio_coincidences(new_id);
        }
        Some(new_id)
    }

    /// 「2点はあるのに結ぶ直線が無い」「2直線はあるのに交点が無い」を需要として記録する。
    fn gj_note_demand(&mut self, kind: DefKind, ids: &[ClassId]) {
        if ids.len() != 2 { return; }
        let (r1, r2) = (ids[0], ids[1]);
        match kind {
            DefKind::LineThroughPoints if r1 != r2 => {
                *self.construction_demands.entry((r1, r2)).or_insert(0.0) += 1.0;
            }
            DefKind::Intersection if r1 != r2
                && self.egraph.entities[r1.0].entity_type == EntityType::Line
                && self.egraph.entities[r2.0].entity_type == EntityType::Line => {
                let key = if r1.0 < r2.0 { (r1, r2) } else { (r2, r1) };
                *self.point_construction_demands.entry(key).or_insert(0.0) += 1.0;
            }
            _ => {}
        }
    }

    /// v に候補 cand を入れたとき、束縛済みの範囲だけで破れる制約が無いか。
    fn gj_ok_constraints(&self, theorem: &TheoremDef, v: &str, cand: ClassId, bind: &Bind) -> bool {
        for pat in &theorem.patterns {
            match pat {
                Pattern::Distinct(vars) => {
                    if !vars.iter().any(|x| x == v) { continue; }
                    for x in vars {
                        if x == v { continue; }
                        if let Some(&id) = bind.get(x)
                            && self.egraph.get_rep(id) == cand { return false; }
                    }
                }
                Pattern::Order(vars) | Pattern::OrderNonStrict(vars) => {
                    let strict = matches!(pat, Pattern::Order(_));
                    let Some(pos) = vars.iter().position(|x| x == v) else { continue };
                    if pos > 0 && let Some(&id) = bind.get(&vars[pos - 1]) {
                        let r = self.egraph.get_rep(id).0;
                        if (strict && r >= cand.0) || (!strict && r > cand.0) { return false; }
                    }
                    if pos + 1 < vars.len() && let Some(&id) = bind.get(&vars[pos + 1]) {
                        let r = self.egraph.get_rep(id).0;
                        if (strict && cand.0 >= r) || (!strict && cand.0 > r) { return false; }
                    }
                }
                _ => {}
            }
        }
        true
    }

    /// パターン1本が変数 v に出せる候補。
    fn gj_gen_for(&mut self, theorem: &TheoremDef, pat: &Pattern, v: &str, bind: &Bind, allow_create: bool) -> Cands {
        match pat {
            Pattern::Identical { a, b, .. } => {
                let other = if a == v { b } else if b == v { a } else { return Cands::Any };
                match bind.get(other) {
                    Some(&id) => Cands::Set(vec![self.egraph.get_rep(id)]),
                    None => Cands::Any,
                }
            }
            Pattern::Connected { child, parent, .. } => {
                let other = if child == v { parent } else if parent == v { child } else { return Cands::Any };
                let Some(&oid) = bind.get(other) else { return Cands::Any };
                let o_rep = self.egraph.get_rep(oid);
                let mut out = Vec::new();
                for comp in &self.egraph.entities[o_rep.0].components {
                    for &sub in &comp.subobjects {
                        let r = self.egraph.get_rep(sub);
                        if r != o_rep { out.push(r); }
                    }
                }
                Cands::Set(out)
            }
            Pattern::DefinedBy { kind, parents, result, flip } => {
                if result == v {
                    if parents.iter().all(|p| bind.contains_key(p)) {
                        let ids: Vec<ClassId> = parents.iter().map(|p| self.egraph.get_rep(bind[p])).collect();
                        let Some(def) = self.egraph.build_definition(*kind, &ids) else { return Cands::Set(vec![]) };
                        // 🌟 AnglePair は正規化で順序が入れ替わらない(normalize_definition 参照)ので、
                        // ∠(d1,d2) と ∠(d2,d1) は別のエントリになる。向きが固定でない限り、従来の
                        // 探索は反転した向きでも同じ角として拾うので、memo も両方を引く。
                        // これを片方しか引かないと、既にある角の半分を見落として定理が発火しない。
                        let mut hits = Vec::new();
                        if let Some(&e) = self.egraph.memo.get(&def) {
                            hits.push(self.egraph.get_rep(e));
                        }
                        if *kind == DefKind::AnglePair && *flip != Flip::Fixed && ids.len() == 2
                            && let Some(rev) = self.egraph.build_definition(*kind, &[ids[1], ids[0]])
                            && let Some(&e) = self.egraph.memo.get(&rev) {
                                let r = self.egraph.get_rep(e);
                                if !hits.contains(&r) { hits.push(r); }
                            }
                        if !hits.is_empty() { return Cands::Set(hits); }
                        // 親がそろっているのに図形が無い。作ってよい種類ならその場で作り、
                        // そうでなければ補助作図の需要として記録する(従来の探索と同じ扱い)。
                        if !created_on_demand(*kind) {
                            // 🌟 需要は見積もりの段階で記録する。ここで記録しないと、作れない
                            // 種類(補助線・交点)の枝は候補が空のまま即座に死ぬので、回復
                            // フェーズに「2点はあるのに結ぶ直線が無い」が一度も伝わらない。
                            self.gj_note_demand(*kind, &ids);
                            return Cands::Set(vec![]);
                        }
                        if !allow_create { return Cands::Creatable; }
                        if let Some(id) = self.gj_create_on_demand(*kind, &ids, def) {
                            return Cands::Set(vec![id]);
                        }
                        return Cands::Set(vec![]);
                    }
                    if let Some(&anchor) = parents.iter().find_map(|p| bind.get(p)) {
                        let a = self.egraph.get_rep(anchor);
                        let want = theorem.entities.get(v).copied();
                        let mut out = Vec::new();
                        for &u in &self.egraph.entities[a.0].uses {
                            let r = self.egraph.get_rep(u);
                            if want.is_none_or(|t| self.egraph.entities[r.0].entity_type == t) { out.push(r); }
                        }
                        return Cands::Set(out);
                    }
                    return Cands::Any;
                }
                let Some(pos) = parents.iter().position(|p| p == v) else { return Cands::Any };
                if let Some(&rid) = bind.get(result) {
                    // 🌟 定義の読み方(親の並べ替え・AnglePair の向き)のうち、既に束縛済みの親と
                    // 食い違わないものだけを残してから v の位置を読む。全位置をそのまま候補に
                    // すると、後で検査に落ちるだけの枝を大量に作ることになる。
                    let r = self.egraph.get_rep(rid);
                    let bound: Vec<Option<ClassId>> = parents.iter()
                        .map(|p| bind.get(p).map(|&id| self.egraph.get_rep(id)))
                        .collect();
                    let mut out = Vec::new();
                    for comp in &self.egraph.entities[r.0].components {
                        for d in &comp.definitions {
                            if d.kind() != Some(*kind) { continue; }
                            let ps: Vec<ClassId> = d.get_parents().iter()
                                .map(|&x| self.egraph.get_rep(x)).collect();
                            if ps.len() != parents.len() { continue; }
                            for (perm, _) in gj_perms(*kind, &ps, flip) {
                                if bound.iter().zip(perm.iter())
                                    .any(|(b, q)| b.is_some_and(|b| b != *q)) { continue; }
                                out.push(perm[pos]);
                            }
                        }
                    }
                    return Cands::Set(out);
                }
                // 結果が未束縛でも、別の親が束縛済みならその uses から定義を拾える。
                let anchor = parents.iter().enumerate()
                    .filter(|(i, _)| *i != pos)
                    .find_map(|(_, p)| bind.get(p).copied());
                if let Some(anchor) = anchor {
                    let a = self.egraph.get_rep(anchor);
                    let mut out = Vec::new();
                    for &u in &self.egraph.entities[a.0].uses {
                        let r = self.egraph.get_rep(u);
                        for comp in &self.egraph.entities[r.0].components {
                            for d in &comp.definitions {
                                if d.kind() != Some(*kind) { continue; }
                                let ps = d.get_parents();
                                if ps.len() != parents.len() { continue; }
                                out.extend(ps.iter().map(|&x| self.egraph.get_rep(x)));
                            }
                        }
                    }
                    return Cands::Set(out);
                }
                Cands::Any
            }
            _ => Cands::Any,
        }
    }

    /// 全部束縛できた割り当てについて、前提を1本ずつ検査する。
    /// AnglePair の向き(Flip)はここで決める ― グループが未決なら両方の向きを試す。
    ///
    /// 🌟 通知するのは<b>束縛1つにつき1回だけ</b>。同じ束縛が別の向きでも成り立つことは
    /// (∠(d1,d2) と ∠(d2,d1) が併合されている等で)普通に起きるが、従来の探索も
    /// 束縛の文字列で重複除去して1件にしている。ここを1件に絞らないと、同じ結論を
    /// 何度も適用することになり、有向角の加法性では60件が784件に膨れた。
    /// 戻り値は「この呼び出しで通知したか」。
    fn gj_verify(&mut self, gj: &mut GenJoin, bind: &Bind, flips: FlipStates, idx: usize) -> bool {
        self.dfs_calls += 1;
        if self.dfs_calls > self.dfs_cap { return false; }
        if idx >= gj.theorem.patterns.len() {
            gj.matched = true;
            gj.emitted += 1;
            (gj.on_match)(bind, &flips);
            return true;
        }
        let pat = gj.theorem.patterns[idx].clone();
        match &pat {
            Pattern::Identical { a, b, .. } => {
                if self.egraph.get_rep(bind[a]) != self.egraph.get_rep(bind[b]) { return false; }
                self.gj_verify(gj, bind, flips, idx + 1)
            }
            Pattern::Connected { child, parent, .. } => {
                if !self.egraph.is_connected(bind[child], bind[parent]) { return false; }
                self.gj_verify(gj, bind, flips, idx + 1)
            }
            Pattern::Distinct(vars) => {
                let mut seen = rustc_hash::FxHashSet::default();
                for x in vars {
                    if !seen.insert(self.egraph.get_rep(bind[x])) { return false; }
                }
                self.gj_verify(gj, bind, flips, idx + 1)
            }
            Pattern::Order(vars) | Pattern::OrderNonStrict(vars) => {
                let strict = matches!(pat, Pattern::Order(_));
                for w in vars.windows(2) {
                    let (l, r) = (self.egraph.get_rep(bind[&w[0]]).0, self.egraph.get_rep(bind[&w[1]]).0);
                    if (strict && l >= r) || (!strict && l > r) { return false; }
                }
                self.gj_verify(gj, bind, flips, idx + 1)
            }
            Pattern::DefinedBy { kind, parents, result, flip } => {
                let r = self.egraph.get_rep(bind[result]);
                let want: Vec<ClassId> = parents.iter().map(|p| self.egraph.get_rep(bind[p])).collect();
                let group = match flip { Flip::Grouped(g) => Some(g.clone()), _ => None };
                let mut defs: Vec<Vec<ClassId>> = Vec::new();
                for comp in &self.egraph.entities[r.0].components {
                    for d in &comp.definitions {
                        if d.kind() == Some(*kind) && d.get_parents().len() == want.len() {
                            defs.push(d.get_parents().iter().map(|&x| self.egraph.get_rep(x)).collect());
                        }
                    }
                }
                for ps in defs {
                    for (perm, flip_val) in gj_perms(*kind, &ps, flip) {
                        if perm != want { continue; }
                        let mut next = flips.clone();
                        if let (Some(g), Some(fv)) = (group.as_ref(), flip_val) {
                            match next.get(g) {
                                Some(&cur) if cur != fv => continue,
                                Some(_) => {}
                                None => { next.insert(g.clone(), fv); }
                            }
                        }
                        // 1つ通ればこの束縛は通知済み。別の向きや別の定義で重ねて通知しない。
                        if self.gj_verify(gj, bind, next, idx + 1) { return true; }
                        if self.dfs_calls > self.dfs_cap { return false; }
                    }
                }
                false
            }
            Pattern::Not(_) => false,
        }
    }
}

/// 定義の親の並びから、この kind と flip で許される読み方を全部出す。
fn gj_perms(kind: DefKind, p: &[ClassId], flip: &Flip) -> Vec<(Vec<ClassId>, Option<bool>)> {
    match kind.parent_symmetry() {
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
        ParentSymmetry::Ordered if kind == DefKind::AnglePair && *flip != Flip::Fixed && p.len() == 2 => vec![
            (vec![p[0], p[1]], Some(false)), (vec![p[1], p[0]], Some(true)),
        ],
        _ => vec![(p.to_vec(), None)],
    }
}

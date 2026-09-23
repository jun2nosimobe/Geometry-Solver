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
        let mut gj = GenJoin { theorem, vars, on_match, matched: false };
        self.gj_solve(&mut gj, seed, FlipStates::default());
        gj.matched
    }

    fn gj_solve(&mut self, gj: &mut GenJoin, bind: Bind, flips: FlipStates) {
        self.dfs_calls += 1;
        if self.dfs_calls > self.dfs_cap { return; }

        // 次に束縛する変数は、交差した候補集合がいちばん小さいもの。
        let theorem = gj.theorem;
        let vars = gj.vars.clone();
        let mut best: Option<(String, Vec<ClassId>)> = None;
        let mut creatable: Option<String> = None;
        for v in vars {
            if bind.contains_key(&v) { continue; }
            let (cands, can_create) = self.gj_candidates(theorem, &v, &bind, false);
            if can_create {
                // 親がそろっていて図形がまだ無い変数は、作れば候補が1個に決まるので先に決める。
                if creatable.is_none() { creatable = Some(v); }
                continue;
            }
            let Some(c) = cands else { return };
            if c.is_empty() { return; }
            if best.as_ref().is_none_or(|(_, b)| c.len() < b.len()) {
                best = Some((v, c));
            }
        }
        if let Some(v) = creatable {
            // ここで初めて作る(需要の記録も commit のときだけ)。
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
            if self.dfs_calls > self.dfs_cap { return; }
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
            // どのパターンからも絞れない変数は、型の全代表元から取る。
            None => match want {
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
            Pattern::DefinedBy { kind, parents, result, .. } => {
                if result == v {
                    if parents.iter().all(|p| bind.contains_key(p)) {
                        let ids: Vec<ClassId> = parents.iter().map(|p| self.egraph.get_rep(bind[p])).collect();
                        let Some(def) = self.egraph.build_definition(*kind, &ids) else { return Cands::Set(vec![]) };
                        if let Some(&e) = self.egraph.memo.get(&def) {
                            return Cands::Set(vec![self.egraph.get_rep(e)]);
                        }
                        // 親がそろっているのに図形が無い。作ってよい種類ならその場で作り、
                        // そうでなければ補助作図の需要として記録する(従来の探索と同じ扱い)。
                        if !allow_create {
                            return if created_on_demand(*kind) { Cands::Creatable } else { Cands::Set(vec![]) };
                        }
                        if let Some(id) = self.gj_create_on_demand(*kind, &ids, def) {
                            return Cands::Set(vec![id]);
                        }
                        self.gj_note_demand(*kind, &ids);
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
                    let r = self.egraph.get_rep(rid);
                    let mut out = Vec::new();
                    for comp in &self.egraph.entities[r.0].components {
                        for d in &comp.definitions {
                            if d.kind() != Some(*kind) { continue; }
                            let ps = d.get_parents();
                            if ps.len() != parents.len() { continue; }
                            match kind.parent_symmetry() {
                                ParentSymmetry::Unordered | ParentSymmetry::KleinFour => {
                                    out.extend(ps.iter().map(|&x| self.egraph.get_rep(x)));
                                }
                                ParentSymmetry::Ordered => {
                                    // AnglePair は向きを反転して読むことがあるので、両方の位置を許す。
                                    if *kind == DefKind::AnglePair && ps.len() == 2 {
                                        out.push(self.egraph.get_rep(ps[0]));
                                        out.push(self.egraph.get_rep(ps[1]));
                                    } else {
                                        out.push(self.egraph.get_rep(ps[pos]));
                                    }
                                }
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
    fn gj_verify(&mut self, gj: &mut GenJoin, bind: &Bind, flips: FlipStates, idx: usize) {
        self.dfs_calls += 1;
        if self.dfs_calls > self.dfs_cap { return; }
        if idx >= gj.theorem.patterns.len() {
            gj.matched = true;
            (gj.on_match)(bind, &flips);
            return;
        }
        let pat = gj.theorem.patterns[idx].clone();
        match &pat {
            Pattern::Identical { a, b, .. } => {
                if self.egraph.get_rep(bind[a]) != self.egraph.get_rep(bind[b]) { return; }
                self.gj_verify(gj, bind, flips, idx + 1);
            }
            Pattern::Connected { child, parent, .. } => {
                if !self.egraph.is_connected(bind[child], bind[parent]) { return; }
                self.gj_verify(gj, bind, flips, idx + 1);
            }
            Pattern::Distinct(vars) => {
                let mut seen = rustc_hash::FxHashSet::default();
                for x in vars {
                    if !seen.insert(self.egraph.get_rep(bind[x])) { return; }
                }
                self.gj_verify(gj, bind, flips, idx + 1);
            }
            Pattern::Order(vars) | Pattern::OrderNonStrict(vars) => {
                let strict = matches!(pat, Pattern::Order(_));
                for w in vars.windows(2) {
                    let (l, r) = (self.egraph.get_rep(bind[&w[0]]).0, self.egraph.get_rep(bind[&w[1]]).0);
                    if (strict && l >= r) || (!strict && l > r) { return; }
                }
                self.gj_verify(gj, bind, flips, idx + 1);
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
                        self.gj_verify(gj, bind, next, idx + 1);
                        if self.dfs_calls > self.dfs_cap { return; }
                    }
                }
            }
            Pattern::Not(_) => {}
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

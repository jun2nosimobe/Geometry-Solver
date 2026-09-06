use crate::mmp_core::{ClassId, Definition, EGraph, EntityType, GeoEntity};
use rustc_hash::FxHashSet;

/// 🌟 MCTSが1手として選べる「作図アクション」。
/// 単純に1つのDefinitionを作れば済むものはConstructで表すが、
/// 調和共役点は「補助点P,Qを含む完全四辺形」という複合作図(construct_harmonic_conjugate)
/// なので、単一のDefinitionでは表現しきれず専用のバリアントにしてある。
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Action {
    Construct(Definition),
    HarmonicConjugate(ClassId, ClassId, ClassId),
}

pub struct ActionGenerator {
    // 名前ではなく「定義」で重複を完全に防ぐ
    pub historical_defs: FxHashSet<Definition>,
    pub historical_harmonic: FxHashSet<(ClassId, ClassId, ClassId)>,
}

impl ActionGenerator {
    pub fn new() -> Self {
        Self {
            historical_defs: FxHashSet::default(),
            historical_harmonic: FxHashSet::default(),
        }
    }

    /// 🌟 図形1つの「重要度」。既存のcalc_bind_heat(logic_core.rs)と
    /// 全く同じ式(基本重要度+熱+依存度)を使い回すことで、DFSのbind順序付けと
    /// MCTSの行動サンプリング・報酬評価とで「何が面白い図形か」の基準を
    /// 1つに統一する(代数的な次数計算は一切使わない)。
    pub fn entity_weight(e: &GeoEntity) -> f64 {
        e.base_importance + e.heat_bonus + (e.uses.len() as f64 * 0.5)
    }

    fn weighted_pick(&self, candidates: &[ClassId], egraph: &EGraph, n: usize) -> Vec<ClassId> {
        if candidates.len() <= n {
            return candidates.to_vec();
        }
        let weights: Vec<f64> = candidates.iter()
            .map(|&id| Self::entity_weight(&egraph.entities[id.0]).max(0.01))
            .collect();
        let mut pool: Vec<(ClassId, f64)> = candidates.iter().copied().zip(weights).collect();
        let mut picked = Vec::new();
        for _ in 0..n {
            if pool.is_empty() { break; }
            let total: f64 = pool.iter().map(|(_, w)| w).sum();
            let mut r = rand::random::<f64>() * total;
            let mut idx = 0;
            for (i, (_, w)) in pool.iter().enumerate() {
                r -= w;
                if r <= 0.0 { idx = i; break; }
            }
            picked.push(pool.remove(idx).0);
        }
        picked
    }

    /// E-Graph上の有効なエンティティから、ランダムに可能な作図アクションを列挙する。
    /// Python版 action_space.py の考え方(点×点→直線/中点、直線×直線→交点、
    /// 点×直線→垂線/平行線、3点→外接円)を踏襲しつつ、調和共役点の完全四辺形
    /// 作図も候補に加えた。
    pub fn get_possible_actions(&mut self, egraph: &EGraph, is_simulation: bool) -> Vec<Action> {
        let points: Vec<ClassId> = self.entities_of_type(egraph, EntityType::Point);
        let lines: Vec<ClassId> = self.entities_of_type(egraph, EntityType::Line);

        let mut actions = Vec::new();
        let num_samples = if is_simulation { 12 } else { 30 };

        // 1. 点×点 -> 直線 / 中点
        for _ in 0..num_samples {
            let pair = self.weighted_pick(&points, egraph, 2);
            if pair.len() < 2 { continue; }
            let (x, y) = (egraph.get_rep(pair[0]), egraph.get_rep(pair[1]));
            if x == y { continue; }

            let def_line = Definition::new_line(x, y);
            self.try_push_def(&mut actions, egraph, def_line, is_simulation);

            let (a, b) = if x.0 > y.0 { (y, x) } else { (x, y) };
            let def_mid = Definition::Midpoint(a, b);
            self.try_push_def(&mut actions, egraph, def_mid, is_simulation);
        }

        // 2. 直線×直線 -> 交点
        for _ in 0..num_samples {
            let pair = self.weighted_pick(&lines, egraph, 2);
            if pair.len() < 2 { continue; }
            let (x, y) = (egraph.get_rep(pair[0]), egraph.get_rep(pair[1]));
            if x == y { continue; }
            let (a, b) = if x.0 > y.0 { (y, x) } else { (x, y) };
            let def_int = Definition::Intersection(a, b);
            self.try_push_def(&mut actions, egraph, def_int, is_simulation);
        }

        // 3. 点×直線 -> 垂線 / 平行線
        for _ in 0..(num_samples / 2) {
            let p_pick = self.weighted_pick(&points, egraph, 1);
            let l_pick = self.weighted_pick(&lines, egraph, 1);
            if p_pick.is_empty() || l_pick.is_empty() { continue; }
            let (p, l) = (egraph.get_rep(p_pick[0]), egraph.get_rep(l_pick[0]));

            self.try_push_def(&mut actions, egraph, Definition::PerpendicularLine(l, p), is_simulation);
            if !egraph.is_connected(p, l) {
                self.try_push_def(&mut actions, egraph, Definition::ParallelLine(l, p), is_simulation);
            }
        }

        // 4. 3点 -> 外接円 (共線でなさそうな組だけ; 判定は構造的な共通直線の有無のみ)
        if points.len() >= 3 {
            for _ in 0..(num_samples / 2) {
                let triple = self.weighted_pick(&points, egraph, 3);
                if triple.len() < 3 { continue; }
                let mut reps: Vec<ClassId> = triple.iter().map(|&id| egraph.get_rep(id)).collect();
                reps.sort_unstable_by_key(|id| id.0);
                reps.dedup();
                if reps.len() < 3 { continue; }
                if egraph.find_common_line(&reps).is_some() { continue; } // 共線なら外接円は無意味
                self.try_push_def(&mut actions, egraph, Definition::Circumcircle(reps[0], reps[1], reps[2]), is_simulation);
            }
        }

        // 5. 直線 -> 方向 (AnglePair探索の種を増やす)
        for &l in self.weighted_pick(&lines, egraph, (num_samples / 4).max(1)).iter() {
            let l = egraph.get_rep(l);
            self.try_push_def(&mut actions, egraph, Definition::DirectionOf(l), is_simulation);
        }

        // 6. 調和共役点: 既に共線であることが構造的にわかっている3点があれば、
        // その第4調和点を作る完全四辺形作図を候補にする(円錐曲線は使わない)。
        for &l in &lines {
            let l = egraph.get_rep(l);
            let pts_on_l: Vec<ClassId> = egraph.entities[l.0].components.first()
                .map(|c| c.subobjects.iter().map(|&s| egraph.get_rep(s))
                    .filter(|&s| egraph.entities[s.0].entity_type == EntityType::Point)
                    .collect())
                .unwrap_or_default();
            if pts_on_l.len() < 3 { continue; }
            let triple = self.weighted_pick(&pts_on_l, egraph, 3);
            if triple.len() < 3 { continue; }
            let (a, b) = if triple[0].0 > triple[1].0 { (triple[1], triple[0]) } else { (triple[0], triple[1]) };
            let c = triple[2];
            if a == c || b == c { continue; }
            let key = (a, b, c);
            if self.historical_harmonic.contains(&key) { continue; }
            if egraph.memo.contains_key(&egraph.normalize_definition(&Definition::HarmonicConjugateOf(a, b, c))) { continue; }
            actions.push(Action::HarmonicConjugate(a, b, c));
            if !is_simulation { self.historical_harmonic.insert(key); }
        }

        actions
    }

    fn entities_of_type(&self, egraph: &EGraph, ty: EntityType) -> Vec<ClassId> {
        (0..egraph.entities.len())
            .map(ClassId)
            .filter(|&id| {
                egraph.get_rep(id) == id
                    && egraph.entities[id.0].entity_type == ty
                    && egraph.entities[id.0].base_importance > 0.0
            })
            .collect()
    }

    fn try_push_def(&mut self, actions: &mut Vec<Action>, egraph: &EGraph, def: Definition, is_simulation: bool) {
        let norm = egraph.normalize_definition(&def);
        if self.historical_defs.contains(&norm) || egraph.memo.contains_key(&norm) { return; }
        actions.push(Action::Construct(norm.clone()));
        if !is_simulation { self.historical_defs.insert(norm); }
    }
}

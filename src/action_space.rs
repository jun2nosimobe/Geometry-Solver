use crate::mmp_core::{ClassId, Definition, EGraph, EntityType, GeoEntity};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
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
    /// 候補の重み付き抽選に使う。シード固定なので --mcts の実行も再現する。
    rng: StdRng,
}

impl ActionGenerator {
    pub fn new() -> Self {
        Self {
            historical_defs: FxHashSet::default(),
            historical_harmonic: FxHashSet::default(),
            rng: StdRng::seed_from_u64(0xAC71_0115),
        }
    }

    /// 🌟 図形1つの「重要度」。GeoEntity::heat_with_degree(mmp_core/mod.rs)を
    /// 使い回すことで、DFSのbind順序付けとMCTSの行動サンプリング・報酬評価とで
    /// 「何が面白い図形か」の基準を1つに統一する(代数的な次数計算は一切使わない)。
    pub fn entity_weight(e: &GeoEntity) -> f64 {
        e.heat_with_degree()
    }

    /// 🌟 証明目標の図形への構造的な近さによる重みボーナス。mcts.rs の target_bonus(行動の後の報酬評価)と
    /// 同じ考え方で、こちらは行動の候補をサンプリングする段階で目標寄りに偏らせる(限られたサンプル数を、
    /// 目標と無関係な組み合わせに使い切らないように)。代数は使わず、直接一致と is_connected だけを見る。
    fn target_weight_bonus(egraph: &EGraph, id: ClassId, target: &Option<(String, Vec<ClassId>)>) -> f64 {
        let Some((_, targets)) = target else { return 0.0; };
        let rep = egraph.get_rep(id);
        let mut bonus = 0.0;
        for &t in targets {
            let t_rep = egraph.get_rep(t);
            if t_rep == rep { bonus += 20.0; }
            else if egraph.is_connected(rep, t_rep) { bonus += 5.0; }
        }
        bonus
    }

    fn weighted_pick(&mut self, candidates: &[ClassId], egraph: &EGraph, n: usize, target: &Option<(String, Vec<ClassId>)>) -> Vec<ClassId> {
        if candidates.len() <= n {
            return candidates.to_vec();
        }
        let weights: Vec<f64> = candidates.iter()
            .map(|&id| (Self::entity_weight(&egraph.entities[id.0]) + Self::target_weight_bonus(egraph, id, target)).max(0.01))
            .collect();
        let mut pool: Vec<(ClassId, f64)> = candidates.iter().copied().zip(weights).collect();
        let mut picked = Vec::new();
        for _ in 0..n {
            if pool.is_empty() { break; }
            let total: f64 = pool.iter().map(|(_, w)| w).sum();
            let mut r = self.rng.r#gen::<f64>() * total;
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
    pub fn get_possible_actions(&mut self, egraph: &EGraph, is_simulation: bool, target: &Option<(String, Vec<ClassId>)>) -> Vec<Action> {
        let points: Vec<ClassId> = self.entities_of_type(egraph, EntityType::Point);
        let lines: Vec<ClassId> = self.entities_of_type(egraph, EntityType::Line);

        let mut actions = Vec::new();
        let num_samples = if is_simulation { 12 } else { 30 };

        // 1. 点×点 -> 直線 / 中点
        for _ in 0..num_samples {
            let pair = self.weighted_pick(&points, egraph, 2, target);
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
            let pair = self.weighted_pick(&lines, egraph, 2, target);
            if pair.len() < 2 { continue; }
            let (x, y) = (egraph.get_rep(pair[0]), egraph.get_rep(pair[1]));
            if x == y { continue; }
            // 🌟 2直線が既に平行だと分かっているなら、その交点は既存の方向(無限遠点)そのもので、作っても統合される
            // だけなので候補にしない。両方向がまだ実体化されていなければ判定できないので通す。
            if let (Some(&dx), Some(&dy)) = (
                egraph.memo.get(&egraph.normalize_definition(&Definition::DirectionOf(x))),
                egraph.memo.get(&egraph.normalize_definition(&Definition::DirectionOf(y))),
            )
                && egraph.get_rep(dx) == egraph.get_rep(dy) { continue; }
            let (a, b) = if x.0 > y.0 { (y, x) } else { (x, y) };
            let def_int = Definition::Intersection(a, b);
            self.try_push_def(&mut actions, egraph, def_int, is_simulation);
        }

        // 3. 点×直線 -> 垂線 / 平行線
        for _ in 0..(num_samples / 2) {
            let p_pick = self.weighted_pick(&points, egraph, 1, target);
            let l_pick = self.weighted_pick(&lines, egraph, 1, target);
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
                let triple = self.weighted_pick(&points, egraph, 3, target);
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
        for &l in self.weighted_pick(&lines, egraph, (num_samples / 4).max(1), target).iter() {
            let l = egraph.get_rep(l);
            self.try_push_def(&mut actions, egraph, Definition::DirectionOf(l), is_simulation);
        }

        // 6. 調和共役点: 既に共線だと分かっている3点があれば、第4調和点を作る完全四辺形作図を候補にする
        // (円錐曲線は使わない)。他の候補と同じく重み付きサンプリングで直線を絞る ― 全直線に積むと、作図が作る
        // 補助直線がさらに候補を増やす正のフィードバックで、入れ子の調和共役ばかりになる。
        for &l in self.weighted_pick(&lines, egraph, (num_samples / 4).max(1), target).iter() {
            let l = egraph.get_rep(l);
            // subobjects は同じ代表元を指す別の ClassId を重複して持ちうるので、rep 化して重複を除いてから選ぶ
            // (しないと HarmonicConjugate(B,B,B) のような退化した作図ができる)。
            let mut pts_on_l: Vec<ClassId> = egraph.entities[l.0].components.first()
                .map(|c| c.subobjects.iter().map(|&s| egraph.get_rep(s))
                    .filter(|&s| egraph.entities[s.0].entity_type == EntityType::Point)
                    // HarmonicConjugate は try_push_def を通らないので、mcts_depth の上限と無限遠点・内部定数の除外をここでも課す。
                    .filter(|&s| egraph.entities[s.0].mcts_depth <= Self::MAX_MCTS_CHAIN_DEPTH)
                    .filter(|&s| !Self::is_special_constant(egraph, s))
                    .filter(|&s| !egraph.is_connected(s, egraph.line_infinity))
                    .collect())
                .unwrap_or_default();
            pts_on_l.sort_unstable_by_key(|id| id.0);
            pts_on_l.dedup();
            if pts_on_l.len() < 3 { continue; }
            let triple = self.weighted_pick(&pts_on_l, egraph, 3, target);
            if triple.len() < 3 { continue; }
            let (a, b) = if triple[0].0 > triple[1].0 { (triple[1], triple[0]) } else { (triple[0], triple[1]) };
            let c = triple[2];
            if a == b || a == c || b == c { continue; }
            let key = (a, b, c);
            if self.historical_harmonic.contains(&key) { continue; }
            if egraph.memo.contains_key(&egraph.normalize_definition(&Definition::HarmonicConjugateOf(a, b, c))) { continue; }
            actions.push(Action::HarmonicConjugate(a, b, c));
            if !is_simulation { self.historical_harmonic.insert(key); }
        }

        // 7. 直線×二次曲線 -> もう一方の交点(「AOの延長が外接円と再び交わる点」など)。
        // SecondIntersectionOfLineAndConic は両方に乗っている既知の点を要求するので、二次曲線ごとに「その曲線に
        // 乗っている点」→「その点を通る既存の直線」の2段階で候補を絞る(is_connected だけで判定でき、数値計算は要らない)。
        let conics: Vec<ClassId> = self.entities_of_type(egraph, EntityType::Conic);
        for &c in &conics {
            let c = egraph.get_rep(c);
            let mut pts_on_c: Vec<ClassId> = egraph.entities[c.0].components.first()
                .map(|comp| comp.subobjects.iter().map(|&s| egraph.get_rep(s))
                    .filter(|&s| egraph.entities[s.0].entity_type == EntityType::Point)
                    .collect())
                .unwrap_or_default();
            pts_on_c.sort_unstable_by_key(|id| id.0);
            pts_on_c.dedup();
            if pts_on_c.is_empty() { continue; }

            for &p in self.weighted_pick(&pts_on_c, egraph, (num_samples / 4).max(1), target).iter() {
                let p = egraph.get_rep(p);
                let mut lines_on_p: Vec<ClassId> = egraph.entities[p.0].components.first()
                    .map(|comp| comp.subobjects.iter().map(|&s| egraph.get_rep(s))
                        // 🌟 L∞との「もう一方の交点」は無限遠点の相方(円ならI/Jの
                        // どちらか)にしかならず、補助構成として意味を持たないので
                        // 除外する(resolve_angle_demandsのL∞除外と同じ理由)。
                        .filter(|&s| s != egraph.line_infinity
                            && egraph.entities[s.0].entity_type == EntityType::Line)
                        .collect())
                    .unwrap_or_default();
                lines_on_p.sort_unstable_by_key(|id| id.0);
                lines_on_p.dedup();
                if lines_on_p.is_empty() { continue; }

                for &l in self.weighted_pick(&lines_on_p, egraph, 2, target).iter() {
                    let l = egraph.get_rep(l);
                    let def = Definition::SecondIntersectionOfLineAndConic(p, l, c);
                    self.try_push_def(&mut actions, egraph, def, is_simulation);
                }
            }
        }

        actions
    }

    // 🌟 MCTS の産物の上に MCTS の産物を積む連鎖(GeoEntity::mcts_depth)の深さの上限。base_importance を
    // 下げるだけでは確率的に0にならず、「中点のまた中点…」のような入れ子が積み上がる(entity_weight の uses 項
    // による正のフィードバックもある)。2段(補助構成とその交点)までは典型的な証明で要るが、3段目以降は価値を
    // 生まずに組み合わせだけが増える。問題文の図形や需要駆動の補助線は mcts_depth=0 なので影響を受けない。
    const MAX_MCTS_CHAIN_DEPTH: usize = 2;

    /// 🌟 Line_infinity/CircI/CircJ/Ang0/Ang90 は有向角・複比を計算するための内部的な定数で、補助構成の材料には
    /// しない(「Line_infinity への垂線」のような意味の無い作図案を出さない)。
    fn is_special_constant(egraph: &EGraph, id: ClassId) -> bool {
        id == egraph.line_infinity || id == egraph.circ_i || id == egraph.circ_j
            || id == egraph.ang0 || id == egraph.ang90
    }

    /// 🌟 方向も Point なので、Point を要求する候補からは無限遠点を除く(中点・外接円・垂線の点引数などは
    /// 有限点だけが意味を持つ)。
    fn entities_of_type(&self, egraph: &EGraph, ty: EntityType) -> Vec<ClassId> {
        (0..egraph.entities.len())
            .map(ClassId)
            .filter(|&id| {
                egraph.get_rep(id) == id
                    && egraph.entities[id.0].entity_type == ty
                    && egraph.entities[id.0].is_active()
                    && egraph.entities[id.0].mcts_depth <= Self::MAX_MCTS_CHAIN_DEPTH
                    && !Self::is_special_constant(egraph, egraph.get_rep(id))
                    && (ty != EntityType::Point || !egraph.is_connected(id, egraph.line_infinity))
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

#[cfg(test)]
mod tests {
    use super::*;

    /// 🌟 target_weight_bonusが、目標そのもの/目標に構造的に直接接続している
    /// 図形/無関係な図形をそれぞれ正しく区別できることを確認する
    /// (weighted_pickは乱数を使うため、その土台となるこの重み計算自体を
    /// 決定的にテストする)。
    #[test]
    fn test_target_weight_bonus_distinguishes_proximity() {
        let mut egraph = EGraph::new();
        let connected = egraph.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
        let target_pt = egraph.create_entity("T".into(), Definition::FreePoint, EntityType::Point);
        let unrelated = egraph.create_entity("U".into(), Definition::FreePoint, EntityType::Point);

        // connectedは目標(target_pt)と直接接続(is_connected)している。
        // unrelatedはどこにも繋がっていない。
        egraph.link_logical_incidence(connected, target_pt);

        let target: Option<(String, Vec<ClassId>)> = Some(("Identical".to_string(), vec![target_pt, target_pt]));

        let bonus_target = ActionGenerator::target_weight_bonus(&egraph, target_pt, &target);
        let bonus_connected = ActionGenerator::target_weight_bonus(&egraph, connected, &target);
        let bonus_unrelated = ActionGenerator::target_weight_bonus(&egraph, unrelated, &target);

        // 目標そのもの > 目標に直接接続している図形 > 無関係な図形、の順に高いべき
        assert!(bonus_target > bonus_connected, "目標そのものは接続している図形よりボーナスが高いべき");
        assert!(bonus_connected > bonus_unrelated, "目標に接続している図形は無関係な図形よりボーナスが高いべき");
        assert_eq!(bonus_unrelated, 0.0, "目標と無関係な図形のボーナスは0であるべき");

        // targetがNoneの場合は常に0(従来の目標非依存の挙動と完全に一致する)
        assert_eq!(ActionGenerator::target_weight_bonus(&egraph, target_pt, &None), 0.0);
    }

    /// 🌟 目標指向ヒューリスティックの効果を、orthocenter の初期状態(探索は進めない)で直接測る回帰テスト。
    /// get_possible_actions が出す候補のうち、目標(またはそれに直接接続する垂線)を参照するものの割合を、
    /// 目標バイアスの有無で比べる。MCTS を実際に走らせて比べる方法は、探索の分岐でばらつきが大きすぎて指標にならない。
    #[test]
    fn measure_target_bias_effect_on_orthocenter() {
        let mut egraph = EGraph::new();
        let problem = crate::problems::load_problem("orthocenter", &mut egraph);
        let target = problem.target_fact.clone();
        let Some((_, target_ids)) = &target else { panic!("orthocenterはtarget_factを持つはず"); };

        let touches_target = |egraph: &EGraph, action: &Action| -> bool {
            let ids: Vec<ClassId> = match action {
                Action::Construct(def) => def.get_parents(),
                Action::HarmonicConjugate(a, b, c) => vec![*a, *b, *c],
            };
            ids.iter().any(|&id| {
                let rep = egraph.get_rep(id);
                target_ids.iter().any(|&t| {
                    let t_rep = egraph.get_rep(t);
                    rep == t_rep || egraph.is_connected(rep, t_rep)
                })
            })
        };

        let trials = 300;
        let mut with_bias_hits = 0usize;
        let mut with_bias_total = 0usize;
        let mut gen_on = ActionGenerator::new();
        for _ in 0..trials {
            let actions = gen_on.get_possible_actions(&egraph, true, &target);
            with_bias_total += actions.len();
            with_bias_hits += actions.iter().filter(|a| touches_target(&egraph, a)).count();
        }

        let mut without_bias_hits = 0usize;
        let mut without_bias_total = 0usize;
        let mut gen_off = ActionGenerator::new();
        for _ in 0..trials {
            let actions = gen_off.get_possible_actions(&egraph, true, &None);
            without_bias_total += actions.len();
            without_bias_hits += actions.iter().filter(|a| touches_target(&egraph, a)).count();
        }

        let with_ratio = with_bias_hits as f64 / with_bias_total.max(1) as f64;
        let without_ratio = without_bias_hits as f64 / without_bias_total.max(1) as f64;
        println!(
            "目標バイアス有効: {}/{} ({:.1}%)  無効: {}/{} ({:.1}%)",
            with_bias_hits, with_bias_total, with_ratio * 100.0,
            without_bias_hits, without_bias_total, without_ratio * 100.0
        );
        assert!(with_ratio > without_ratio, "目標バイアス有効時の方が目標関連の候補割合が高いはず");
    }
}

//! 🌟 数値評価環境(MMPテスト用)と、それを土台にした健全性チェック。
//! ここでの数値計算はあくまでテスト・事後検証のためのものであり、
//! メインの証明導出(合同閉包・定理適用)は一切これに依存しない。

use std::collections::HashSet;
use rustc_hash::FxHashMap;
use crate::mmp_math::ModInt;
use crate::mmp_calculators;
use super::{ClassId, ConjectureEntry, ConjectureValue, Definition, EntityType, EGraph, Justification};
use super::coords::{self, Geometry, Placed, Placement};

/// 数値チェックが使う「図全体に座標を置いた標本」と、その座標での評価結果。構造が変わるまで使い回す。
/// 一意性の伝播は同じ図の上で何度も検算するので、そのたびに座標を置き直して根から評価し直すと、実体が数百個の
/// 図では時間の大半をここで使う。
#[derive(Clone)]
pub(crate) struct NumericSamples {
    generation: u64,
    /// 図全体に座標を置けたか(置けない図ではペアごとに置く従来の経路を使う)。
    usable: bool,
    vars: Vec<FxHashMap<String, ModInt>>,
    cache: Vec<FxHashMap<usize, Vec<ModInt>>>,
}

impl Default for NumericSamples {
    fn default() -> Self {
        // まだどの世代の標本も持っていないことを表す番兵。
        Self { generation: u64::MAX, usable: true, vars: Vec::new(), cache: Vec::new() }
    }
}


impl EGraph {
    /// 🌟 数値評価。自由点の座標は vars に名前で入れておく(`{名前}_x`, `{名前}_y`)。
    pub fn evaluate_node(
        &self,
        node_id: ClassId,
        vars: &FxHashMap<String, ModInt>,
        cache: &mut FxHashMap<usize, Vec<ModInt>>,
    ) -> Option<Vec<ModInt>> {
        coords::evaluate(self, &ModIntVars { vars }, node_id, cache, &mut HashSet::new())
    }

    /// 🌟 calc_* が退化した入力(一致した2点、同一の2直線など)に返す値を、一箇所で「計算不能」(None)に
    /// 変換する。空 Vec と、射影平面の点として定義できない全成分0(normalize は全0をそのまま返す)の両方を
    /// 弾く。通すと後続の cross_product などが範囲外アクセスで panic する。
    fn to_option(v: Vec<ModInt>) -> Option<Vec<ModInt>> {
        if v.is_empty() || v.iter().all(|x| x.0 == 0) { None } else { Some(v) }
    }

    /// 🔮 記号的にはまだ別物の a, b が、ランダムな座標で数値的に一致したことを予想(conjectures)として記録する。
    /// 独立な一様乱数(法 998244353)が偶然一致する確率は約10億分の1なので、ほぼ確実に構造的な同一性がある
    /// (Schwartz-Zippel の逆読み)。証明ではなく、調べる価値の高い候補の提示にとどまる。
    pub(crate) fn log_conjecture_candidate(&self, a: ClassId, b: ClassId, hypothesis: &str) {
        let rep_a = self.get_rep(a);
        let rep_b = self.get_rep(b);
        if rep_a == rep_b { return; } // 既に記号的に証明済みなら予想ではない
        let key = if rep_a.0 < rep_b.0 { (rep_a.0, rep_b.0) } else { (rep_b.0, rep_a.0) };

        // 🌟 同じペアは何百回も検出されるので、ログは初回だけにし、以降は occurrences を増やすだけにする。
        // 代表元はマージで変わるので、既存のキーを今の get_rep で解決し直して一致するものがあれば、そのエントリを
        // 今のキーへ付け替える(しないと同じ関係が別々のエントリとして大量に溜まる)。
        let mut map = self.conjectures.borrow_mut();
        let canonical_existing = map.keys().copied().find(|&(ka, kb)| {
            let (ra, rb) = (self.get_rep(ClassId(ka)), self.get_rep(ClassId(kb)));
            let (ra, rb) = if ra.0 < rb.0 { (ra.0, rb.0) } else { (rb.0, ra.0) };
            (ra, rb) == key
        });
        let is_first = match canonical_existing {
            Some(old_key) => {
                if old_key != key
                    && let Some(entry) = map.remove(&old_key) { map.insert(key, entry); }
                if let Some(entry) = map.get_mut(&key) { entry.occurrences += 1; }
                false
            }
            None => {
                map.insert(key, ConjectureEntry {
                    hypothesis: hypothesis.to_string(),
                    occurrences: 1,
                    tested: false,
                });
                true
            }
        };
        drop(map);

        if is_first {
            let name_a = &self.entities[rep_a.0].name;
            let name_b = &self.entities[rep_b.0].name;
            println!(
                "  🔮 [予想候補] {} と {} は独立な乱数サンプルで数値的に一致しました(仮説: {})。\
                 まだ証明はされていませんが、偶然の確率は約10億分の1なので実在する関係の可能性が高いです。",
                name_a, name_b, hypothesis
            );
        }
    }

    /// 🌟 予想(a≡b)を実際に真だと仮定した場合、合同閉包だけでどれだけの
    /// 追加的な帰結(マージ)が即座に得られるかを、使い捨てのクローン上で
    /// 見積もる。証明の健全性には一切影響しない(現実のegraphは一切変更
    /// しない)、あくまで探索の優先度付け(heat_bonus)のためのヒューリスティックな
    /// 価値推定であり、これ自体が新しい事実を証明するわけではない。
    ///
    /// 🌟 組み合わせ爆発対策: 意図的に定理マッチング(dfs_match)までは行わず、
    /// 合同閉包(apply_congruence_closure、直線/点の一意性の局所伝播)だけに
    /// 留める。定理マッチングまで踏み込み、その結論をさらに新しい予想として
    /// 連鎖的に評価し始めると、組み合わせが指数的に増える恐れがある。
    /// まず最も安価でよく効く一段階の構造的伝播だけで価値を見積もり、
    /// 効果が薄ければそれ以上深追いしない設計にすることで、1つの予想を
    /// 評価するコストを「クローン1回+合同閉包1回」に固定している。
    pub fn estimate_conjecture_value(&self, a: ClassId, b: ClassId, target: &Option<(String, Vec<ClassId>)>) -> ConjectureValue {
        let mut sim = self.clone();
        let classes_before = sim.count_active_classes();
        sim.merge_entities_justified(a, b, Justification::Trivial {
            reason: "予想(数値的根拠のみ、未証明)を価値評価のため一時的に仮定".to_string(),
        });
        sim.apply_congruence_closure();
        let classes_after = sim.count_active_classes();
        let additional_merges = classes_before.saturating_sub(classes_after);

        let target_reached = match target {
            Some((ftype, targets)) if ftype == "Identical" && targets.len() == 2 => {
                sim.get_rep(targets[0]) == sim.get_rep(targets[1])
            }
            Some((ftype, targets)) if ftype == "Concyclic" => {
                let reps: Vec<ClassId> = targets.iter().map(|&t| sim.get_rep(t)).collect();
                sim.points_share_a_circle(&reps)
            }
            _ => false,
        };

        ConjectureValue { additional_merges, target_reached }
    }

    /// 🌟 使い捨てクローン(MCTS の sim_egraph など)で検出された予想を、現実の EGraph の予想マップへ合流させる。
    /// conjectures は RefCell ごと複製されるので、合流しないとクローンと一緒に捨てられる。クローンで新しく
    /// 作られた実体(現実の egraph に無い ClassId)を参照する予想は除き、現実の egraph の今の代表元で正規化し直す。
    pub fn absorb_conjectures_from(&self, other: &EGraph) {
        let real_len = self.entities.len();
        let incoming: Vec<((usize, usize), ConjectureEntry)> = {
            let other_map = other.conjectures.borrow();
            other_map.iter()
                .filter(|&(&(a, b), _)| a < real_len && b < real_len)
                .map(|(&k, v)| (k, v.clone()))
                .collect()
        };
        if incoming.is_empty() { return; }

        let mut map = self.conjectures.borrow_mut();
        for ((a, b), entry) in incoming {
            let (ra, rb) = (self.get_rep(ClassId(a)), self.get_rep(ClassId(b)));
            if ra == rb { continue; } // 現実のegraph側では既に証明済み
            let key = if ra.0 < rb.0 { (ra.0, rb.0) } else { (rb.0, ra.0) };
            match map.get_mut(&key) {
                Some(existing) => existing.occurrences += entry.occurrences,
                None => { map.insert(key, entry); }
            }
        }
    }

    /// 🌟 溜まった予想を処理する。未評価の予想ごとに estimate_conjecture_value で価値を見積もり、一定以上なら
    /// 2つの実体の heat_bonus を上げて探索をそちらへ向ける。証明状態(union-find/memo/facts)は変えない。
    /// MCTS の run_step からも同じ呼び出しの中で使うので、BlackboardEngine ではなく EGraph に置く
    /// (BlackboardEngine::process_pending_conjectures は委譲するだけ)。
    /// 組み合わせ爆発の対策:
    /// 1. 評価は合同閉包1回だけの浅い見積もりにし、定理マッチングや予想の連鎖はしない。
    /// 2. 同じペアは ConjectureEntry.tested で一度しか評価しない。
    /// 3. 1回の呼び出しで新しく評価するのは MAX_PER_CALL 件まで。
    pub fn process_pending_conjectures(&mut self, target: &Option<(String, Vec<ClassId>)>) -> usize {
        const MAX_PER_CALL: usize = 3;
        const MERGE_THRESHOLD: usize = 3;
        const HEAT_BOOST: f64 = 2.0;
        const HEAT_BOOST_TARGET: f64 = 10.0;

        let pending: Vec<(usize, usize, String, u32)> = {
            let map = self.conjectures.borrow();
            map.iter()
                .filter(|(_, e)| !e.tested)
                .take(MAX_PER_CALL)
                .map(|(&(a, b), e)| (a, b, e.hypothesis.clone(), e.occurrences))
                .collect()
        };
        if pending.is_empty() { return 0; }

        for (a_idx, b_idx, hypothesis, occurrences) in &pending {
            let (a, b) = (ClassId(*a_idx), ClassId(*b_idx));
            let name_a = self.entities[*a_idx].name.clone();
            let name_b = self.entities[*b_idx].name.clone();

            println!("  🔍 [予想の検証開始] {} ≡ {} (仮説: {}, これまでに{}回観測) を一時的に仮定して検証します。\
                以下は使い捨ての複製上での仮想的な帰結であり、実際の証明状態には反映されません:",
                name_a, name_b, hypothesis, occurrences);
            let value = self.estimate_conjecture_value(a, b, target);
            println!("  🔍 [予想の検証終了] 合同閉包だけで{}件の追加的な帰結{}",
                value.additional_merges, if value.target_reached { "、さらに証明目標にも到達" } else { "" });

            if let Some(entry) = self.conjectures.borrow_mut().get_mut(&(*a_idx, *b_idx)) {
                entry.tested = true;
            }

            if value.target_reached {
                // 🌟 "🎯"は既存のリーチ通知(健全に完全マッチした定理の通知)で使われて
                // いるため紛らわしい。こちらは未証明の仮定に基づく評価なので"🏆"を使う。
                println!("  🏆 [予想の評価] {} ≡ {} を仮定するだけで証明目標に到達しました！この2点への注目度を大きく引き上げます。", name_a, name_b);
                self.bump_heat_bonus(a, HEAT_BOOST_TARGET);
                self.bump_heat_bonus(b, HEAT_BOOST_TARGET);
            } else if value.additional_merges >= MERGE_THRESHOLD {
                println!("  📈 [予想の評価] {} ≡ {} は仮定するだけで{}件の追加的な帰結を生むため、この2点への注目度を引き上げます。",
                    name_a, name_b, value.additional_merges);
                self.bump_heat_bonus(a, HEAT_BOOST);
                self.bump_heat_bonus(b, HEAT_BOOST);
            }
        }
        pending.len()
    }

    /// 🌟 同次座標(2要素または3要素)としての比例判定。normalize()の正規化
    /// 方式が定義の種類によって異なる(FreePointは[x,y,1]のまま、他の多くは
    /// 「最初の非ゼロ成分を1にする」方式)ため、単純な要素比較ではなく
    /// 外積(クロス積)がゼロかどうかで比較する。
    fn numeric_values_proportional(v1: &[ModInt], v2: &[ModInt]) -> bool {
        if v1.len() != v2.len() || v1.is_empty() { return false; }
        if v1.len() == 3 {
            let z1 = v1[0] * v2[1] - v1[1] * v2[0];
            let z2 = v1[1] * v2[2] - v1[2] * v2[1];
            let z3 = v1[2] * v2[0] - v1[0] * v2[2];
            return z1.0 == 0 && z2.0 == 0 && z3.0 == 0;
        }
        if v1.len() == 2 {
            let cross = v1[0] * v2[1] - v1[1] * v2[0];
            return cross.0 == 0;
        }
        v1.iter().zip(v2.iter()).all(|(a, b)| a.0 == b.0)
    }

    /// 🌟 点 point の曲線 curve への接続が、curve 自身の定義から座標的に自動で従うか(従うなら制約付き
    /// サンプリングは要らない)。例: LineThroughPoints(A,B) への A の接続は自然。問題文が link_logical_incidence
    /// で直接与えた「D はこの円の上」は自然ではない(座標の裏付けが無い、構造だけの前提)。
    /// 基準は「その点なしで curve を評価できるか」(evaluation_requires_point)。評価できるなら接続は本物の制約。
    pub(crate) fn is_natural_incidence(&self, point: ClassId, curve: ClassId) -> bool {
        let point_rep = self.get_rep(point);
        let curve_rep = self.get_rep(curve);
        if self.entities[curve_rep.0].components.first().is_none() { return false; }
        let mut memo = rustc_hash::FxHashMap::default();
        let mut stack = HashSet::new();
        self.evaluation_requires_point(point_rep, curve_rep, &mut stack, &mut memo)
    }

    /// 🌟 node を数値評価するのに point_rep の座標が不可欠か。node が point 自身なら不可欠。そうでなければ、
    /// node の全ての定義が親のどれかを通じて point を必要とするときだけ不可欠(point を使わない評価経路が
    /// 1本でもあれば不可欠ではない。親を持たない FreePoint/GivenPoint はそれ自体がそういう経路)。
    /// 循環に出会ったら「不可欠」側に倒す(制約付きサンプリングが循環すると座標が決まらなくなる)。
    /// 定義グラフは DAG なのでメモ化が必須。⚠️ 循環に当たった節点そのものはメモしないが、その結果を使った親の結果は
    /// メモされるので、同じ memo で別の節点から辿り直すと答えが変わりうる。呼び出しごとに memo を作り直すこと。
    pub(crate) fn evaluation_requires_point(&self, point_rep: ClassId, node: ClassId,
        stack: &mut HashSet<usize>, memo: &mut rustc_hash::FxHashMap<usize, bool>) -> bool
    {
        let rep = self.get_rep(node);
        if rep == point_rep { return true; }
        if let Some(&v) = memo.get(&rep.0) { return v; }
        if !stack.insert(rep.0) { return true; }
        let defs = match self.entities[rep.0].components.first() {
            Some(c) => c.definitions.clone(),
            None => { stack.remove(&rep.0); memo.insert(rep.0, false); return false; }
        };
        let requires = !defs.is_empty() && defs.iter().all(|d| {
            let parents = d.get_parents();
            !parents.is_empty()
                && parents.iter().any(|&p| self.evaluation_requires_point(point_rep, p, stack, memo))
        });
        stack.remove(&rep.0);
        memo.insert(rep.0, requires);
        requires
    }

    /// 祖先の自由点に座標を置く(coords の place_free_points の有限体版)。置けない点や前提を満たさない点が
    /// 残れば false(呼び出し側は判定不能に倒す)。
    fn assign_free_point_coords(&self, ancestors: &[ClassId], vars: &mut FxHashMap<String, ModInt>) -> bool {
        self.assign_free_point_coords_with(ancestors, vars, RngSource::Numeric)
    }

    fn assign_free_point_coords_with(&self, ancestors: &[ClassId], vars: &mut FxHashMap<String, ModInt>, rng: RngSource) -> bool {
        matches!(self.place_free_points(ancestors, &mut ModIntPlacer { vars, rng }, false), Placed::All)
    }

    /// 🌟 マージを確定する前の数値的な裏付け。祖先の自由点にランダムな座標を割り当て(前提のある点は前提を
    /// 満たすように)、a と b が本当に同じ値になるかを trials 回検算する。明確に矛盾すれば Some(false)、
    /// 座標を組み立てられないか評価できなければ None(判定不能)。
    /// congruence.rs の構造的な伝播(propagate_*_uniqueness)が偶然の一致で誤った同一視をしないためのゲートで、
    /// これ自体は何も証明しない。
    pub(crate) fn numeric_plausibility_check(&self, a: ClassId, b: ClassId, trials: usize) -> Option<bool> {
        let (ra, rb) = (self.get_rep(a), self.get_rep(b));
        let key = if ra.0 <= rb.0 { (ra.0, rb.0) } else { (rb.0, ra.0) };
        {
            let mut cache = self.structure_cache.borrow_mut();
            cache.sync(self.structure_generation);
            if let Some(&v) = cache.verdicts.get(&key) { return v; }
        }
        let verdict = self.numeric_plausibility_check_uncached(a, b, trials);
        self.structure_cache.borrow_mut().verdicts.insert(key, verdict);
        verdict
    }

    /// 図の全ての自由点に座標を置いた標本を trials 個ぶん用意する(構造が変わるまで使い回す)。
    /// 置けない図(前提が平方根を要する等)では None を返し、呼び出し側はペアごとに置く従来の経路に落ちる。
    fn shared_samples(&self, trials: usize) -> bool {
        let mut samples = self.numeric_samples.borrow_mut();
        if samples.generation != self.structure_generation {
            *samples = NumericSamples { generation: self.structure_generation, usable: true, vars: Vec::new(), cache: Vec::new() };
        }
        if !samples.usable { return false; }
        while samples.vars.len() < trials {
            let mut vars: FxHashMap<String, ModInt> = FxHashMap::default();
            if !self.assign_free_point_coords(&self.all_free_points(), &mut vars) {
                samples.usable = false;
                return false;
            }
            samples.vars.push(vars);
            samples.cache.push(FxHashMap::default());
        }
        true
    }

    fn numeric_plausibility_check_uncached(&self, a: ClassId, b: ClassId, trials: usize) -> Option<bool> {
        if self.shared_samples(trials) {
            let mut samples = self.numeric_samples.borrow_mut();
            for i in 0..trials {
                let NumericSamples { vars, cache, .. } = &mut *samples;
                let (va, vb) = (self.evaluate_node(a, &vars[i], &mut cache[i]), self.evaluate_node(b, &vars[i], &mut cache[i]));
                match (va, vb) {
                    (Some(va), Some(vb)) => if !Self::numeric_values_proportional(&va, &vb) { return Some(false); },
                    _ => return None,
                }
            }
            return Some(true);
        }
        self.numeric_plausibility_check_per_pair(a, b, trials)
    }

    fn numeric_plausibility_check_per_pair(&self, a: ClassId, b: ClassId, trials: usize) -> Option<bool> {
        // 🐛 問題文は「P はこの円の上」のような前提を座標ではなく link_logical_incidence で与えることが多い。
        // そういう自由点に完全な乱数座標を置くと前提を満たさず、正しいマージまで却下してしまうので、
        // assign_free_point_coords は前提を満たす座標を取る。取れないときだけ None に倒す。
        let ancestors = self.free_point_ancestors_of(&[a, b]);
        if ancestors.is_empty() { return None; }

        for _ in 0..trials {
            let mut vars: FxHashMap<String, ModInt> = FxHashMap::default();
            if !self.assign_free_point_coords(&ancestors, &mut vars) { return None; }

            let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
            match (self.evaluate_node(a, &vars, &mut cache), self.evaluate_node(b, &vars, &mut cache)) {
                (Some(va), Some(vb)) => {
                    if !Self::numeric_values_proportional(&va, &vb) { return Some(false); }
                }
                _ => return None,
            }
        }
        Some(true)
    }

    /// 乱数の状態を戻して f を実行する。診断(--audit-merges)の検算が、探索が使う乱数の列を変えないように。
    pub(crate) fn without_consuming_rng<T>(&self, f: impl FnOnce(&Self) -> T) -> T {
        let saved = self.rng_state.get();
        let out = f(self);
        self.rng_state.set(saved);
        out
    }

    /// 点 point が曲線 curve(直線・二次曲線)に乗っているかの数値的な裏付け(numeric_plausibility_check の接続版)。
    /// 判定できなければ None。
    pub(crate) fn numeric_incidence_check(&self, point: ClassId, curve: ClassId, trials: usize) -> Option<bool> {
        let (point, curve) = (self.get_rep(point), self.get_rep(curve));
        let curve_type = self.entities[curve.0].entity_type;
        if self.entities[point.0].entity_type != EntityType::Point
            || !matches!(curve_type, EntityType::Line | EntityType::Conic) { return None; }
        let ancestors = self.free_point_ancestors_of(&[point, curve]);
        if ancestors.is_empty() { return None; }
        for _ in 0..trials {
            let mut vars: FxHashMap<String, ModInt> = FxHashMap::default();
            if !self.assign_free_point_coords(&ancestors, &mut vars) { return None; }
            let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
            let (Some(p), Some(c)) = (self.evaluate_node(point, &vars, &mut cache), self.evaluate_node(curve, &vars, &mut cache))
                else { return None };
            if !(ModIntPlacer { vars: &mut vars, rng: RngSource::Numeric }).lies_on(&p, &c, curve_type) { return Some(false); }
        }
        Some(true)
    }

    /// 探索を始める前にマージ済みの組(問題文の前提)が、乱数座標で数値的に成り立つか。マージ済みの2つは同じ同値類として
    /// 評価されてしまうので、それぞれの元の定義(original_definition)を個別に評価して比べる。成り立たない組があるなら、
    /// その問題の前提は座標への制約(「OP = OA」など)で、乱数座標による検算は前提を満たさない図で行われている。
    pub fn hypotheses_hold_numerically(&self) -> bool {
        self.without_consuming_rng(|eg| {
            let points = eg.all_free_points();
            for _ in 0..2 {
                let mut vars: FxHashMap<String, ModInt> = FxHashMap::default();
                if !eg.assign_free_point_coords(&points, &mut vars) { return true; } // 判定できない
                let geometry = ModIntVars { vars: &vars };
                let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
                for (i, e) in eg.entities.iter().enumerate() {
                    let rep = eg.get_rep(ClassId(i));
                    if rep.0 == i { continue; }
                    let own = |id: usize, def: &Definition, cache: &mut FxHashMap<usize, Vec<ModInt>>| match def {
                        // 有向角は複比 (I,J;D1,D2) で評価するので、直角は -1、0度は 1。
                        Definition::GivenPoint if id == eg.ang90.0 => Some(vec![ModInt::new(-1), ModInt::new(1), ModInt::new(1)]),
                        Definition::GivenPoint if id == eg.ang0.0 => Some(vec![ModInt::new(1), ModInt::new(1), ModInt::new(1)]),
                        Definition::FreePoint | Definition::GivenPoint | Definition::ConstantHomogeneous(..) => None,
                        _ => geometry.construct(eg, def, &mut |q| coords::evaluate(eg, &geometry, q, cache, &mut HashSet::new())),
                    };
                    let (Some(v1), Some(v2)) = (own(i, &e.original_definition, &mut cache), own(rep.0, &eg.entities[rep.0].original_definition, &mut cache))
                        else { continue };
                    if !Self::numeric_values_proportional(&v1, &v2) { return false; }
                }
            }
            true
        })
    }

    /// 🌟 動点法(Method of Moving Points)の次数を数値的に測る。祖先の自由点の1つ(mover)を直線に沿って動かし、
    /// 複数の t で評価して、有限体上のランク判定で座標が満たす有理関数の次数を求める。親の次数の和という構造的な
    /// 上界と違い、中点のように次数が上がらない操作を正しく低く測れる。
    /// mover が見つからないか、どれかのサンプルで評価できなければ None(次数不明)。呼び出し側は次数で足切りしない。
    pub fn measure_numerical_degree(&self, entity: ClassId, max_d: usize) -> Option<usize> {
        let ancestors = self.free_point_ancestors_of(&[entity]);
        if ancestors.is_empty() { return Some(0); } // 自由点に一切依存しない(定数)ので次数0

        let (mover, base_vars) = self.setup_mover_and_base_vars(&ancestors)?;
        let mover_name = self.entities[mover.0].name.clone();

        let k = 2 * max_d + 2;
        let (x0, y0, dx, dy) = self.random_mover_line();
        let mut t_vals = Vec::with_capacity(k);
        let mut x_vals = Vec::with_capacity(k);
        let mut y_vals = Vec::with_capacity(k);
        for i in 1..=k {
            let t = ModInt::new(i as i64);
            let mut vars = base_vars.clone();
            vars.insert(format!("{}_x", mover_name), x0 + t * dx);
            vars.insert(format!("{}_y", mover_name), y0 + t * dy);
            let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
            let v = self.evaluate_node(entity, &vars, &mut cache)?;
            if v.len() < 3 || v[2].0 == 0 { return None; }
            t_vals.push(t);
            x_vals.push(v[0] / v[2]);
            y_vals.push(v[1] / v[2]);
        }
        let dxd = crate::mmp_math::get_numerical_degree(&t_vals, &x_vals, max_d);
        let dyd = crate::mmp_math::get_numerical_degree(&t_vals, &y_vals, max_d);
        Some(dxd.max(dyd))
    }

    /// 🌟 measure_numerical_degree のメモ化版。候補の多い DefinedBy パターンのマッチ候補を次数の低いものから試す
    /// (logic_core::matcher)など同じ実体に何度も呼ばれるので、代表元の GeoEntity::degree_cache に結果を持つ。
    pub fn cached_degree(&self, id: ClassId, max_d: usize) -> Option<usize> {
        let rep = self.get_rep(id);
        if let Some(cached) = self.entities[rep.0].degree_cache.get() {
            return cached;
        }
        let deg = self.measure_numerical_degree(rep, max_d);
        self.entities[rep.0].degree_cache.set(Some(deg));
        deg
    }

    /// 🌟 measure_numerical_degreeの「まだエンティティとして存在しない候補」版。
    /// resolve_point_demandsのような「実際に作る前に有望さを判定したい」
    /// 場面向けに、2直線l1, l2の交点をentityとして作らずに次数だけ測定する。
    pub fn measure_intersection_degree_candidate(&self, l1: ClassId, l2: ClassId, max_d: usize) -> Option<usize> {
        let ancestors = self.free_point_ancestors_of(&[l1, l2]);
        if ancestors.is_empty() { return Some(0); }

        let (mover, base_vars) = self.setup_mover_and_base_vars(&ancestors)?;
        let mover_name = self.entities[mover.0].name.clone();

        let k = 2 * max_d + 2;
        let (x0, y0, dx, dy) = self.random_mover_line();
        let mut t_vals = Vec::with_capacity(k);
        let mut x_vals = Vec::with_capacity(k);
        let mut y_vals = Vec::with_capacity(k);
        for i in 1..=k {
            let t = ModInt::new(i as i64);
            let mut vars = base_vars.clone();
            vars.insert(format!("{}_x", mover_name), x0 + t * dx);
            vars.insert(format!("{}_y", mover_name), y0 + t * dy);
            let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
            let v1 = self.evaluate_node(l1, &vars, &mut cache)?;
            let v2 = self.evaluate_node(l2, &vars, &mut cache)?;
            let p = mmp_calculators::calc_intersection(&v1, &v2);
            // 🐛 2直線がこの標本で平行だと交点は無限遠(z=0)にあり、下の x/z が 0 除算になる。
            // 有限の交点が無ければ次数は測れない。
            if p.len() < 3 || p[2].0 == 0 { return None; }
            t_vals.push(t);
            x_vals.push(p[0] / p[2]);
            y_vals.push(p[1] / p[2]);
        }
        let dxd = crate::mmp_math::get_numerical_degree(&t_vals, &x_vals, max_d);
        let dyd = crate::mmp_math::get_numerical_degree(&t_vals, &y_vals, max_d);
        Some(dxd.max(dyd))
    }

    /// 🌟 同次座標の時系列サンプルから次数を測る共通処理。比だけに意味があるので、最後の成分で他の全成分を
    /// 割った値それぞれの次数の最大値を返す。成分数は問わない(点・直線の3、円の係数の4など)。基準の成分が
    /// どれかのサンプルで0なら None。
    fn degree_of_homogeneous_samples(t_vals: &[ModInt], samples: &[Vec<ModInt>], max_d: usize) -> Option<usize> {
        let n = samples.first()?.len();
        if n < 2 { return None; }
        let norm_idx = n - 1;
        if samples.iter().any(|s| s.len() != n || s[norm_idx].0 == 0) { return None; }
        let mut max_deg = 0;
        for i in 0..norm_idx {
            let ratios: Vec<ModInt> = samples.iter().map(|s| s[i] / s[norm_idx]).collect();
            max_deg = max_deg.max(crate::mmp_math::get_numerical_degree(t_vals, &ratios, max_d));
        }
        Some(max_deg)
    }

    /// 🌟 parents(2〜4点)それぞれの次数と、combine で組み合わせた結果の次数を、同じ mover・同じ他の自由点座標の
    /// 1回のサンプリングで測る。deg(A)+deg(B) のような素朴な和より結果の次数が小さい組は、隠れた定理や偶然の
    /// 一致が効いている兆候(「相性が良い」)とみなせる。parent ごとに measure_numerical_degree を別々に呼ぶと
    /// mover や座標が揃わず、次数を比べる意味がなくなる。
    pub fn measure_group_degrees(
        &self,
        parents: &[ClassId],
        combine: impl Fn(&[Vec<ModInt>]) -> Vec<ModInt>,
        max_d: usize,
    ) -> Option<(Vec<usize>, usize)> {
        let ancestors = self.free_point_ancestors_of(parents);
        if ancestors.is_empty() { return Some((vec![0; parents.len()], 0)); }

        let (mover, base_vars) = self.setup_mover_and_base_vars(&ancestors)?;
        let mover_name = self.entities[mover.0].name.clone();

        let k = 2 * max_d + 2;
        let (x0, y0, dx, dy) = self.random_mover_line();
        let mut t_vals = Vec::with_capacity(k);
        let mut parent_samples: Vec<Vec<Vec<ModInt>>> = vec![Vec::with_capacity(k); parents.len()];
        let mut combined_samples: Vec<Vec<ModInt>> = Vec::with_capacity(k);
        for i in 1..=k {
            let t = ModInt::new(i as i64);
            let mut vars = base_vars.clone();
            vars.insert(format!("{}_x", mover_name), x0 + t * dx);
            vars.insert(format!("{}_y", mover_name), y0 + t * dy);
            let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
            let mut vals = Vec::with_capacity(parents.len());
            for &p in parents {
                vals.push(self.evaluate_node(p, &vars, &mut cache)?);
            }
            combined_samples.push(combine(&vals));
            for (idx, v) in vals.into_iter().enumerate() {
                parent_samples[idx].push(v);
            }
            t_vals.push(t);
        }

        let mut parent_degs = Vec::with_capacity(parents.len());
        for samples in &parent_samples {
            parent_degs.push(Self::degree_of_homogeneous_samples(&t_vals, samples, max_d)?);
        }
        let combined_deg = Self::degree_of_homogeneous_samples(&t_vals, &combined_samples, max_d)?;
        Some((parent_degs, combined_deg))
    }

    /// 🌟 measure_group_degreesの2点(直線)特化版。resolve_demandsから使う。
    pub fn measure_line_affinity(&self, a: ClassId, b: ClassId, max_d: usize) -> Option<(usize, usize, usize)> {
        let (degs, combined) = self.measure_group_degrees(
            &[a, b],
            |vals| mmp_calculators::calc_line_through_points(&vals[0], &vals[1]),
            max_d,
        )?;
        Some((degs[0], degs[1], combined))
    }

    /// 🌟 measure_group_degrees の3点(外接円)版。deg(A)+deg(B)+deg(C) に比べて Circumcircle(A,B,C) の次数が
    /// 小さい組は、同じ円に乗りやすい構造の兆候。
    #[allow(dead_code)]   // まだ探索のヒューリスティックに繋いでいない
    pub fn measure_circle_affinity(&self, a: ClassId, b: ClassId, c: ClassId, max_d: usize) -> Option<(usize, usize, usize, usize)> {
        let (degs, combined) = self.measure_group_degrees(
            &[a, b, c],
            |vals| mmp_calculators::calc_circumcircle(&vals[0], &vals[1], &vals[2]),
            max_d,
        )?;
        Some((degs[0], degs[1], degs[2], combined))
    }

    /// 🌟 measure_group_degrees の4点(複比)版。複比は (k,1,1) なので実質 k の次数が結果を決める。4点の次数の和に
    /// 比べて複比の次数が異常に高い(無関係な4点)なら、生成自体を諦めるゲートに使う。
    pub fn measure_cross_ratio_affinity(&self, a: ClassId, b: ClassId, c: ClassId, d: ClassId, max_d: usize) -> Option<(usize, usize, usize, usize, usize)> {
        let (degs, combined) = self.measure_group_degrees(
            &[a, b, c, d],
            |vals| mmp_calculators::calc_cross_ratio(&vals[0], &vals[1], &vals[2], &vals[3])
                .map(|k| vec![k, ModInt::new(1), ModInt::new(1)])
                .unwrap_or_default(),
            max_d,
        )?;
        Some((degs[0], degs[1], degs[2], degs[3], combined))
    }

    /// 🌟 新しく作った複比 new_id の値を、既存の全ての複比(点の複比・線束の複比)と1回の乱数サンプルで比べ、
    /// 一致すれば log_conjecture_candidate で予想として記録する。証明状態は変えない。
    /// 複比の値は (k,1,1) なので、比例ではなく等値で比べる。
    pub fn detect_cross_ratio_coincidences(&self, new_id: ClassId) {
        let new_rep = self.get_rep(new_id);
        // 🌟 点の複比と線束の複比の一致は透視射影不変性(theorems.rs)が成り立つ組み合わせそのものなので、両方を対象にする。
        let others: Vec<ClassId> = (0..self.entities.len())
            .filter(|&i| matches!(self.entities[i].original_definition, Definition::CrossRatio(..) | Definition::CrossRatioOfLines(..)))
            .map(ClassId)
            .map(|id| self.get_rep(id))
            .filter(|&rep| rep != new_rep)
            .collect();
        if others.is_empty() { return; }

        let roots: Vec<ClassId> = std::iter::once(new_rep).chain(others.iter().copied()).collect();
        let ancestors = self.free_point_ancestors_of(&roots);
        if ancestors.is_empty() { return; }

        let mut vars: FxHashMap<String, ModInt> = FxHashMap::default();
        if !self.assign_free_point_coords(&ancestors, &mut vars) { return; }
        let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
        let Some(v_new) = self.evaluate_node(new_rep, &vars, &mut cache) else { return; };
        if v_new.is_empty() { return; }

        for &other in &others {
            if let Some(v_other) = self.evaluate_node(other, &vars, &mut cache)
                && !v_other.is_empty() && v_new[0].0 == v_other[0].0 {
                    self.log_conjecture_candidate(new_rep, other, "複比の値が一致(透視射影関係などの可能性)");
                }
        }
    }

    /// 🌟 measure_numerical_degree系の共通処理: 祖先の自由点の中から
    /// 「他の構造的前提(直線/円の上にあること)を持たない」ものを1つ選んで
    /// mover(動点)とし、残りは(前提を満たす形で)1回だけ座標を固定する。
    /// 適切なmoverが見つからない場合はNone。
    fn setup_mover_and_base_vars(&self, ancestors: &[ClassId]) -> Option<(ClassId, FxHashMap<String, ModInt>)> {
        let mover = *ancestors.iter().find(|&&fp| !self.has_extraneous_incidence(fp))?;
        let others: Vec<ClassId> = ancestors.iter().copied().filter(|&fp| fp != mover).collect();
        let mut base_vars: FxHashMap<String, ModInt> = FxHashMap::default();
        // 次数測定は自分の乱数の列を使う(数値チェックの回数に結果を左右されないため)。
        if !self.assign_free_point_coords_with(&others, &mut base_vars, RngSource::Degree) { return None; }
        Some((mover, base_vars))
    }

    /// 数値検証・次数測定の乱数(SplitMix64)。rand::random だと実行ごとに座標が変わり、
    /// ごく低い確率とはいえ同じ問題で判定が変わりうる。
    pub(crate) fn random_modint(&self) -> ModInt {
        let mut z = self.rng_state.get().wrapping_add(0x9E37_79B9_7F4A_7C15);
        self.rng_state.set(z);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        ModInt::new((z ^ (z >> 31)) as i64)
    }

    /// 🌟 moverが動く先の「一般の位置にある直線」: 基点(x0,y0)と方向(dx,dy)を
    /// 無作為に選ぶ(moverの座標はx0+t*dx, y0+t*dyとしてtでパラメータ化される)。
    fn random_mover_line(&self) -> (ModInt, ModInt, ModInt, ModInt) {
        (
            self.random_degree_modint(),
            self.random_degree_modint(),
            self.random_degree_modint(),
            self.random_degree_modint(),
        )
    }

    /// 次数測定用の乱数(数値チェックとは別の列。degree_rng_state 参照)。
    fn random_degree_modint(&self) -> ModInt {
        let mut z = self.degree_rng_state.get().wrapping_add(0x9E37_79B9_7F4A_7C15);
        self.degree_rng_state.set(z);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        ModInt::new((z ^ (z >> 31)) as i64)
    }
}

/// 有限体での各定義の値。点・直線は同次座標、二次曲線は6係数、スカラーは [値, 1, 1]。
fn modint_construct(eg: &EGraph, def: &Definition, get: &mut dyn FnMut(ClassId) -> Option<Vec<ModInt>>) -> Option<Vec<ModInt>> {
    match def {
        Definition::FreePoint | Definition::GivenPoint => None,
        Definition::Midpoint(p1, p2) => {
            let v1 = get(*p1)?;
            let v2 = get(*p2)?;
            EGraph::to_option(mmp_calculators::calc_midpoint(&v1, &v2))
        }
        Definition::LineThroughPoints(p1, p2) => {
            let v1 = get(*p1)?;
            let v2 = get(*p2)?;
            // 🐛 calc_line_through_points は2点が数値的に一致すると空 Vec を返すので、to_option で None にする。
            let result = mmp_calculators::calc_line_through_points(&v1, &v2);
            if result.is_empty() {
                // 🔮 CONJECTURE: 無作為な座標(独立一様分布, 法998244353)で
                // p1とp2が偶然一致する確率は約10億分の1で、単発でも観測されたなら
                // ほぼ確実に偶然ではない(Schwartz-Zippel補題の逆読み)。まだ記号的
                // には別物として扱われている2点が、実は常に同一なのではないか、
                // という「証明はできていないが数値的根拠のある予想」として
                // 目立つ形でログに残す(数値サニティチェックの土台として黙って
                // Noneに変換するだけでは、この情報がそのまま捨てられてしまう)。
                eg.log_conjecture_candidate(*p1, *p2, "2点が同一点である");
            }
            EGraph::to_option(result)
        }
        Definition::Intersection(l1, l2) => {
            let v1 = get(*l1)?;
            let v2 = get(*l2)?;
            let result = mmp_calculators::calc_intersection(&v1, &v2);
            if result.is_empty() || result.iter().all(|x| x.0 == 0) {
                // 🔮 CONJECTURE: 2直線の交点が定義不能([0,0,0])になるのは、
                // 2直線が数値的に同一直線である場合だけ(平行なだけの別直線は
                // 無限遠点で交わる、通常の交点として well-defined)。上と同じ理由で
                // 「実はl1とl2は同一直線なのでは」という予想として記録する。
                eg.log_conjecture_candidate(*l1, *l2, "2直線が同一直線である");
            }
            EGraph::to_option(result)
        }
        Definition::DirectionOf(l) => {
            let v = get(*l)?;
            if v.len() >= 3 {
                // 直線 ax + by + c = 0 の方向は同次座標 (b, -a, 0)。Intersection(L∞, l) と同じ3要素にそろえる
                // (要素数が違うと、同じ方向を数値チェックが別の値と判定する)。l が無限遠直線だと (0,0,0) になるので
                // to_option で弾く。
                EGraph::to_option(mmp_calculators::normalize(&[v[1], -v[0], ModInt::new(0)]))
            } else {
                None
            }
        }
        // 🌟 有向角 = 無限遠直線上の4点の複比 (I,J;D1,D2)。D1,D2 は DirectionOf/PerpDirectionOf で (x,y,0) に
        // 評価されるので、円周点 I,J と合わせた4点は共線で、calc_cross_ratio がそのまま使える。I,J を基準側に
        // 置くと値は τ_D2/τ_D1 になり、有向角の加法性・交替律が求める代数法則を満たす。
        Definition::AnglePair(d1, d2) => {
            let v1 = get(*d1)?;
            let v2 = get(*d2)?;
            let vi = get(eg.circ_i)?;
            let vj = get(eg.circ_j)?;
            mmp_calculators::calc_cross_ratio(&vi, &vj, &v1, &v2)
                .map(|k| vec![k, ModInt::new(1), ModInt::new(1)])
        }
        Definition::LengthSq(p1, p2) => {
            let v1 = get(*p1)?;
            let v2 = get(*p2)?;
            // calc_squared_distance は無限遠点(z=0)に対して None を返す。
            mmp_calculators::calc_squared_distance(&v1, &v2)
                .map(|d| vec![d, ModInt::new(1), ModInt::new(1)])
        }
        Definition::PerpendicularLine(l, p) => {
            let vl = get(*l)?;
            let vp = get(*p)?;
            EGraph::to_option(mmp_calculators::calc_perpendicular(&vl, &vp))
        }
        // 🌟 以前は未実装で、ParallelLine型のエンティティ(まだ他の定義と
        // マージされていないもの)を数値サニティチェック(numeric_plausibility_check)
        // で評価できず、健全性チェックが素通りしてしまう抜け穴になっていた。
        Definition::ParallelLine(l, p) => {
            let vl = get(*l)?;
            let vp = get(*p)?;
            EGraph::to_option(mmp_calculators::calc_parallel(&vl, &vp))
        }
        // 🌟 同上の理由でPerpDirectionOfも実装する。方向ベクトル(dx,dy)を
        // 90度回転させるだけ((dx,dy) -> (-dy,dx))。
        Definition::PerpDirectionOf(d) => {
            let v = get(*d)?;
            if v.len() >= 2 {
                // DirectionOfと同じ理由でz成分0を付けた3要素の同次座標に統一する。
                // (同じくv=[0,0,...]由来の全ゼロ退化値をto_optionで弾く)
                EGraph::to_option(mmp_calculators::normalize(&[-v[1], v[0], ModInt::new(0)]))
            } else {
                None
            }
        }
        // 🌟 外接円は「3点 + 円周点 I,J を通る二次曲線」として calc_conic_through_5_points で作る(円も Conic)。
        // I,J への接続は apply_trivial_relations が張る。
        Definition::Circumcircle(p1, p2, p3) => {
            let v1 = get(*p1)?;
            let v2 = get(*p2)?;
            let v3 = get(*p3)?;
            let vi = get(eg.circ_i)?;
            let vj = get(eg.circ_j)?;
            EGraph::to_option(mmp_calculators::calc_conic_through_5_points(&[v1, v2, v3, vi, vj]))
        }
        Definition::TangentLine(c, p) => {
            let vc = get(*c)?;
            let vp = get(*p)?;
            // 円も6係数の二次曲線として評価されるので、接線は極線の式1つで足りる。
            EGraph::to_option(mmp_calculators::calc_tangent_to_conic(&vc, &vp))
        }
        // 🌟 mmp_core/mod.rs::Definition::SecondIntersectionOfLineAndConic
        // のドキュメント参照。既知の交点p、直線l、二次曲線cから、
        // もう一方の交点を斉次座標のまま(割り算無しで)直接求める。
        Definition::SecondIntersectionOfLineAndConic(p, l, c) => {
            let vp = get(*p)?;
            let vl = get(*l)?;
            let vc = get(*c)?;
            EGraph::to_option(mmp_calculators::calc_second_intersection_of_line_and_conic(&vp, &vl, &vc))
        }
        // 🌟 2円の根軸。mmp_core/mod.rs::Definition::RadicalAxis のドキュメント参照。
        Definition::RadicalAxis(c1, c2) => {
            let v1 = get(*c1)?;
            let v2 = get(*c2)?;
            EGraph::to_option(mmp_calculators::calc_radical_axis(&v1, &v2))
        }
        // 🌟 一方の交点が既知のときの2円のもう一方の交点(根軸経由)。
        Definition::SecondIntersectionOfCircles(p, c1, c2) => {
            let vp = get(*p)?;
            let v1 = get(*c1)?;
            let v2 = get(*c2)?;
            EGraph::to_option(mmp_calculators::calc_second_intersection_of_circles(&vp, &v1, &v2))
        }
        Definition::HarmonicConjugateOf(a, b, c) => {
            let va = get(*a)?;
            let vb = get(*b)?;
            let vc = get(*c)?;
            EGraph::to_option(mmp_calculators::calc_harmonic_conjugate(&va, &vb, &vc))
        }
        // 🌟 複比(A,B;C,D)はPoint型ではなくScalar型の値(A,B,C,Dが直線上に
        // ある前提でのτ_D/τ_C)なので、点のような同次座標[x,y,z]ではなく
        // LengthSqと同じ「値, 1, 1」の3要素形式で返す(numeric_values_proportional
        // が単純な値比較として扱えるようにするための既存の慣習)。
        Definition::CrossRatio(a, b, c, d) => {
            let va = get(*a)?;
            let vb = get(*b)?;
            let vc = get(*c)?;
            let vd = get(*d)?;
            mmp_calculators::calc_cross_ratio(&va, &vb, &vc, &vd)
                .map(|k| vec![k, ModInt::new(1), ModInt::new(1)])
        }
        // 🌟 線束の複比。直線の同次係数を双対平面の点とみなせば、共点な4直線の複比は点の複比と同じ
        // calc_cross_ratio で計算できる。
        Definition::CrossRatioOfLines(a, b, c, d) => {
            let va = get(*a)?;
            let vb = get(*b)?;
            let vc = get(*c)?;
            let vd = get(*d)?;
            mmp_calculators::calc_cross_ratio(&va, &vb, &vc, &vd)
                .map(|k| vec![k, ModInt::new(1), ModInt::new(1)])
        }
        // 🌟 円周点I,Jのような「常にこの値」の定数。varsの内容に関わらず
        // 埋め込まれたModIntをそのまま返す。
        Definition::ConstantHomogeneous(a, b, c) => Some(vec![*a, *b, *c]),
        // 🌟 5点を通る一般二次曲線の係数[A,B,C,D,E,F]。calc_circumcircleの
        // 一般化(calc_conic_through_5_pointsのコメント参照)。
        Definition::ConicThrough5Points(p1, p2, p3, p4, p5) => {
            let v1 = get(*p1)?;
            let v2 = get(*p2)?;
            let v3 = get(*p3)?;
            let v4 = get(*p4)?;
            let v5 = get(*p5)?;
            EGraph::to_option(mmp_calculators::calc_conic_through_5_points(&[v1, v2, v3, v4, v5]))
        }
        // 🌟 2つのScalarの積。LengthSq等と同じ「値,1,1」の3要素形式で
        // 評価する(numeric_values_proportionalが単純な値比較として扱える)。
        Definition::Product(a, b) => {
            let va = get(*a)?;
            let vb = get(*b)?;
            if va.is_empty() || vb.is_empty() { return None; }
            Some(vec![va[0] * vb[0], ModInt::new(1), ModInt::new(1)])
        }
    }
}

fn modint_free(eg: &EGraph, rep: ClassId, def: &Definition, vars: &FxHashMap<String, ModInt>) -> Option<Vec<ModInt>> {
    match def {
        // 🐛 座標がまだ割り当てられていない自由点は、(0,0) で黙って計算を
        // 続けず評価不能にする。マージで1つの同値類に複数の定義が同居すると
        // (外接円 Circumcircle(A,B,C) と Circumcircle(B,C,D) など)、座標の揃って
        // いない定義を (0,0) で評価してしまい、揃っている別の定義に切り替わら
        // なかった。None を返せば coords::evaluate が次の定義を試す。
        // 呼び出し側は全ての祖先の自由点に座標を入れてから呼ぶので、座標が
        // 欠けるのは自由点を置いている途中だけ。
        Definition::FreePoint => {
            let x = vars.get(&format!("{}_x", eg.entities[rep.0].name)).copied()?;
            let y = vars.get(&format!("{}_y", eg.entities[rep.0].name)).copied()?;
            Some(vec![x, y, ModInt::new(1)])
        }
        Definition::GivenPoint => {
            let x = vars.get(&format!("{}_x", eg.entities[rep.0].name)).copied().unwrap_or(ModInt::new(0));
            let y = vars.get(&format!("{}_y", eg.entities[rep.0].name)).copied().unwrap_or(ModInt::new(0));
            Some(vec![x, y, ModInt::new(1)])
        }
        _ => None,
    }
}

/// 自由点の座標を名前で引く(`{名前}_x`, `{名前}_y`)評価。
pub(crate) struct ModIntVars<'v> {
    pub vars: &'v FxHashMap<String, ModInt>,
}

impl Geometry for ModIntVars<'_> {
    type Shape = Vec<ModInt>;
    fn free(&self, eg: &EGraph, rep: ClassId, def: &Definition) -> Option<Vec<ModInt>> { modint_free(eg, rep, def, self.vars) }
    fn construct(&self, eg: &EGraph, def: &Definition, get: &mut dyn FnMut(ClassId) -> Option<Vec<ModInt>>) -> Option<Vec<ModInt>> {
        modint_construct(eg, def, get)
    }
}

/// 有限体での自由点の置き方。どちらの乱数の列を使うかを持つ(数値チェックと次数測定は別の列)。
pub(crate) struct ModIntPlacer<'v> {
    pub vars: &'v mut FxHashMap<String, ModInt>,
    pub rng: RngSource,
}

/// 乱数の列。数値チェックの回数が変わっても次数測定の結果が動かないよう、2本に分けてある。
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum RngSource { Numeric, Degree }

impl ModIntPlacer<'_> {
    fn random(&self, eg: &EGraph) -> ModInt {
        match self.rng { RngSource::Numeric => eg.random_modint(), RngSource::Degree => eg.random_degree_modint() }
    }

    fn set(&mut self, eg: &EGraph, point: ClassId, x: ModInt, y: ModInt) {
        let name = &eg.entities[point.0].name;
        self.vars.insert(format!("{}_x", name), x);
        self.vars.insert(format!("{}_y", name), y);
    }
}

impl Geometry for ModIntPlacer<'_> {
    type Shape = Vec<ModInt>;
    fn free(&self, eg: &EGraph, rep: ClassId, def: &Definition) -> Option<Vec<ModInt>> { modint_free(eg, rep, def, self.vars) }
    fn construct(&self, eg: &EGraph, def: &Definition, get: &mut dyn FnMut(ClassId) -> Option<Vec<ModInt>>) -> Option<Vec<ModInt>> {
        modint_construct(eg, def, get)
    }
}

impl Placement for ModIntPlacer<'_> {
    fn is_placed(&self, eg: &EGraph, point: ClassId) -> bool {
        self.vars.contains_key(&format!("{}_x", eg.entities[point.0].name))
    }
    fn place_randomly(&mut self, eg: &EGraph, point: ClassId) {
        let x = self.random(eg);
        let y = self.random(eg);
        self.set(eg, point, x, y);
    }
    fn unplace(&mut self, eg: &EGraph, point: ClassId) {
        let name = &eg.entities[point.0].name;
        self.vars.remove(&format!("{}_x", name));
        self.vars.remove(&format!("{}_y", name));
    }
    fn place_on_two_lines(&mut self, eg: &EGraph, point: ClassId, l1: &Vec<ModInt>, l2: &Vec<ModInt>) -> bool {
        let inter = mmp_calculators::calc_intersection(l1, l2);
        if inter.len() < 3 || inter[2].0 == 0 { return false; } // 平行(無限遠)や退化は諦める
        self.set(eg, point, inter[0] / inter[2], inter[1] / inter[2]);
        true
    }
    /// 直線 a*x+b*y+c=0 の上のランダムな点。
    fn place_on_line(&mut self, eg: &EGraph, point: ClassId, line: &Vec<ModInt>) -> bool {
        if line.len() < 3 { return false; }
        let (a, b, c) = (line[0], line[1], line[2]);
        let (x, y) = if b.0 != 0 {
            let x = self.random(eg);
            (x, -(a * x + c) / b)
        } else if a.0 != 0 {
            let y = self.random(eg);
            (-c / a, y)
        } else {
            return false; // 縮退した直線(0=0)
        };
        self.set(eg, point, x, y);
        true
    }
    fn conic_usable(&self, conic: &Vec<ModInt>) -> bool { conic.len() >= 6 }
    /// 二次曲線上のランダムな点。既知の点 (x1,y1) を通るランダムな直線 (x1+t dx, y1+t dy) を代入すると t の2次式の
    /// 定数項が0になるので、非自明な解 t=-β/α が平方根なしに求まる(Vieta)。
    fn place_on_conic(&mut self, eg: &EGraph, point: ClassId, conic: &Vec<ModInt>, known: &Vec<ModInt>) -> bool {
        let (a, b, c, d, e) = (conic[0], conic[1], conic[2], conic[3], conic[4]);
        if known.len() < 3 || known[2].0 == 0 { return false; }
        let (x1, y1) = (known[0] / known[2], known[1] / known[2]);
        let two = ModInt::new(2);
        for _ in 0..8 {
            let dx = self.random(eg);
            let dy = self.random(eg);
            let alpha = a * dx * dx + b * dx * dy + c * dy * dy;
            if alpha.0 == 0 { continue; } // 漸近方向(ごく低確率)。引き直す
            let beta = two * a * x1 * dx + b * (x1 * dy + y1 * dx) + two * c * y1 * dy + d * dx + e * dy;
            let t = -(beta / alpha);
            self.set(eg, point, x1 + t * dx, y1 + t * dy);
            return true;
        }
        false
    }
    fn lies_on(&self, point: &Vec<ModInt>, v: &Vec<ModInt>, curve_type: EntityType) -> bool {
        if point.len() < 3 { return false; }
        let (x, y, z) = (point[0], point[1], point[2]);
        match curve_type {
            EntityType::Line if v.len() >= 3 => (v[0] * x + v[1] * y + v[2] * z).0 == 0,
            EntityType::Conic if v.len() >= 6 =>
                (v[0] * x * x + v[1] * x * y + v[2] * y * y + v[3] * x * z + v[4] * y * z + v[5] * z * z).0 == 0,
            _ => false,
        }
    }
}

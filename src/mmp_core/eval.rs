//! 🌟 数値評価環境(MMPテスト用)と、それを土台にした健全性チェック。
//! ここでの数値計算はあくまでテスト・事後検証のためのものであり、
//! メインの証明導出(合同閉包・定理適用)は一切これに依存しない。

use std::collections::HashSet;
use rustc_hash::FxHashMap;
use crate::mmp_math::ModInt;
use crate::mmp_calculators;
use super::{ClassId, ConjectureEntry, ConjectureValue, Definition, EntityType, EGraph, Justification};

impl EGraph {
    /// 🌟 数値評価環境 (MMPテスト用)
    pub fn evaluate_node(
        &self,
        node_id: ClassId,
        vars: &FxHashMap<String, ModInt>,
        cache: &mut FxHashMap<usize, Vec<ModInt>>,
    ) -> Option<Vec<ModInt>> {
        let mut in_progress = HashSet::new();
        self.evaluate_node_inner(node_id, vars, cache, &mut in_progress)
    }

    /// 🌟 evaluate_node の実体。PerpDirectionOf/HarmonicConjugateOfのように、
    /// マージによって「互いを参照し合う定義」が同じコンポーネントに同居する
    /// ことがある(例: D=Harm(A,B,C) と C=Harm(A,B,D) が対合として互いに
    /// マージされる)。素朴に再帰するとどちらの定義から計算しても計算不能な
    /// 組み合わせで無限再帰(スタックオーバーフロー)に陥るため、
    /// 計算中のIDへの再突入を in_progress で検出し、その場合はその定義を
    /// 諦めて(Noneを返して)コンポーネント内の他の定義を試す。
    fn evaluate_node_inner(
        &self,
        node_id: ClassId,
        vars: &FxHashMap<String, ModInt>,
        cache: &mut FxHashMap<usize, Vec<ModInt>>,
        in_progress: &mut HashSet<usize>,
    ) -> Option<Vec<ModInt>> {
        let rep_id = self.get_rep(node_id);
        if let Some(val) = cache.get(&rep_id.0) {
            return Some(val.clone());
        }
        if !in_progress.insert(rep_id.0) {
            return None;
        }

        let name = self.entities[rep_id.0].name.clone();
        let definitions = match self.entities[rep_id.0].components.first() {
            Some(c) => c.definitions.clone(),
            None => { in_progress.remove(&rep_id.0); return None; }
        };

        // 🌟 マージ後は1つのコンポーネントに複数の定義が同居し得るので、
        // 計算可能なものが見つかるまで順に試す(以前は.first()決め打ちで、
        // たまたま循環参照側が先頭に来ると即失敗していた)。
        let mut result = None;
        for def in &definitions {
            if let Some(v) = self.evaluate_definition(def, &name, vars, cache, in_progress) {
                result = Some(v);
                break;
            }
        }

        in_progress.remove(&rep_id.0);
        if let Some(ref v) = result {
            cache.insert(rep_id.0, v.clone());
        }
        result
    }

    fn evaluate_definition(
        &self,
        def: &Definition,
        name: &str,
        vars: &FxHashMap<String, ModInt>,
        cache: &mut FxHashMap<usize, Vec<ModInt>>,
        in_progress: &mut HashSet<usize>,
    ) -> Option<Vec<ModInt>> {
        match def {
            // 🐛 座標がまだ割り当てられていない自由点は、(0,0) で黙って計算を
            // 続けず評価不能にする。マージで1つの同値類に複数の定義が同居すると
            // (外接円 Circumcircle(A,B,C) と Circumcircle(B,C,D) など)、座標の揃って
            // いない定義を (0,0) で評価してしまい、揃っている別の定義に切り替わら
            // なかった。None を返せば evaluate_node_inner が次の定義を試す。
            // 呼び出し側は全ての祖先の自由点に座標を入れてから呼ぶので、座標が
            // 欠けるのは制約付きサンプリングの途中だけ。
            Definition::FreePoint => {
                let x = vars.get(&format!("{}_x", name)).copied()?;
                let y = vars.get(&format!("{}_y", name)).copied()?;
                Some(vec![x, y, ModInt::new(1)])
            }
            Definition::GivenPoint => {
                let x = vars.get(&format!("{}_x", name)).copied().unwrap_or(ModInt::new(0));
                let y = vars.get(&format!("{}_y", name)).copied().unwrap_or(ModInt::new(0));
                Some(vec![x, y, ModInt::new(1)])
            }
            Definition::Midpoint(p1, p2) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_midpoint(&v1, &v2))
            }
            Definition::LineThroughPoints(p1, p2) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
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
                    self.log_conjecture_candidate(*p1, *p2, "2点が同一点である");
                }
                Self::to_option(result)
            }
            Definition::Intersection(l1, l2) => {
                let v1 = self.evaluate_node_inner(*l1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*l2, vars, cache, in_progress)?;
                let result = mmp_calculators::calc_intersection(&v1, &v2);
                if result.is_empty() || result.iter().all(|x| x.0 == 0) {
                    // 🔮 CONJECTURE: 2直線の交点が定義不能([0,0,0])になるのは、
                    // 2直線が数値的に同一直線である場合だけ(平行なだけの別直線は
                    // 無限遠点で交わる、通常の交点として well-defined)。上と同じ理由で
                    // 「実はl1とl2は同一直線なのでは」という予想として記録する。
                    self.log_conjecture_candidate(*l1, *l2, "2直線が同一直線である");
                }
                Self::to_option(result)
            }
            Definition::DirectionOf(l) => {
                let v = self.evaluate_node_inner(*l, vars, cache, in_progress)?;
                if v.len() >= 3 {
                    // 直線 ax + by + c = 0 の方向は同次座標 (b, -a, 0)。Intersection(L∞, l) と同じ3要素にそろえる
                    // (要素数が違うと、同じ方向を数値チェックが別の値と判定する)。l が無限遠直線だと (0,0,0) になるので
                    // to_option で弾く。
                    Self::to_option(mmp_calculators::normalize(&[v[1], -v[0], ModInt::new(0)]))
                } else {
                    None
                }
            }
            // 🌟 有向角 = 無限遠直線上の4点の複比 (I,J;D1,D2)。D1,D2 は DirectionOf/PerpDirectionOf で (x,y,0) に
            // 評価されるので、円周点 I,J と合わせた4点は共線で、calc_cross_ratio がそのまま使える。I,J を基準側に
            // 置くと値は τ_D2/τ_D1 になり、有向角の加法性・交替律が求める代数法則を満たす。
            Definition::AnglePair(d1, d2) => {
                let v1 = self.evaluate_node_inner(*d1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*d2, vars, cache, in_progress)?;
                let vi = self.evaluate_node_inner(self.circ_i, vars, cache, in_progress)?;
                let vj = self.evaluate_node_inner(self.circ_j, vars, cache, in_progress)?;
                mmp_calculators::calc_cross_ratio(&vi, &vj, &v1, &v2)
                    .map(|k| vec![k, ModInt::new(1), ModInt::new(1)])
            }
            Definition::LengthSq(p1, p2) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                // calc_squared_distance は無限遠点(z=0)に対して None を返す。
                mmp_calculators::calc_squared_distance(&v1, &v2)
                    .map(|d| vec![d, ModInt::new(1), ModInt::new(1)])
            }
            Definition::PerpendicularLine(l, p) => {
                let vl = self.evaluate_node_inner(*l, vars, cache, in_progress)?;
                let vp = self.evaluate_node_inner(*p, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_perpendicular(&vl, &vp))
            }
            // 🌟 以前は未実装で、ParallelLine型のエンティティ(まだ他の定義と
            // マージされていないもの)を数値サニティチェック(numeric_plausibility_check)
            // で評価できず、健全性チェックが素通りしてしまう抜け穴になっていた。
            Definition::ParallelLine(l, p) => {
                let vl = self.evaluate_node_inner(*l, vars, cache, in_progress)?;
                let vp = self.evaluate_node_inner(*p, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_parallel(&vl, &vp))
            }
            // 🌟 同上の理由でPerpDirectionOfも実装する。方向ベクトル(dx,dy)を
            // 90度回転させるだけ((dx,dy) -> (-dy,dx))。
            Definition::PerpDirectionOf(d) => {
                let v = self.evaluate_node_inner(*d, vars, cache, in_progress)?;
                if v.len() >= 2 {
                    // DirectionOfと同じ理由でz成分0を付けた3要素の同次座標に統一する。
                    // (同じくv=[0,0,...]由来の全ゼロ退化値をto_optionで弾く)
                    Self::to_option(mmp_calculators::normalize(&[-v[1], v[0], ModInt::new(0)]))
                } else {
                    None
                }
            }
            // 🌟 外接円は「3点 + 円周点 I,J を通る二次曲線」として calc_conic_through_5_points で作る(円も Conic)。
            // I,J への接続は apply_trivial_relations が張る。
            Definition::Circumcircle(p1, p2, p3) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                let v3 = self.evaluate_node_inner(*p3, vars, cache, in_progress)?;
                let vi = self.evaluate_node_inner(self.circ_i, vars, cache, in_progress)?;
                let vj = self.evaluate_node_inner(self.circ_j, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_conic_through_5_points(&[v1, v2, v3, vi, vj]))
            }
            Definition::TangentLine(c, p) => {
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                let vp = self.evaluate_node_inner(*p, vars, cache, in_progress)?;
                // 🌟 第1引数の係数の長さで振り分ける(6係数の二次曲線と、4係数の円)。
                let result = if vc.len() >= 6 {
                    mmp_calculators::calc_tangent_to_conic(&vc, &vp)
                } else {
                    mmp_calculators::calc_tangent_line(&vc, &vp)
                };
                Self::to_option(result)
            }
            // 🌟 mmp_core/mod.rs::Definition::SecondIntersectionOfLineAndConic
            // のドキュメント参照。既知の交点p、直線l、二次曲線cから、
            // もう一方の交点を斉次座標のまま(割り算無しで)直接求める。
            Definition::SecondIntersectionOfLineAndConic(p, l, c) => {
                let vp = self.evaluate_node_inner(*p, vars, cache, in_progress)?;
                let vl = self.evaluate_node_inner(*l, vars, cache, in_progress)?;
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_second_intersection_of_line_and_conic(&vp, &vl, &vc))
            }
            // 🌟 2円の根軸。mmp_core/mod.rs::Definition::RadicalAxis のドキュメント参照。
            Definition::RadicalAxis(c1, c2) => {
                let v1 = self.evaluate_node_inner(*c1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*c2, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_radical_axis(&v1, &v2))
            }
            // 🌟 一方の交点が既知のときの2円のもう一方の交点(根軸経由)。
            Definition::SecondIntersectionOfCircles(p, c1, c2) => {
                let vp = self.evaluate_node_inner(*p, vars, cache, in_progress)?;
                let v1 = self.evaluate_node_inner(*c1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*c2, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_second_intersection_of_circles(&vp, &v1, &v2))
            }
            Definition::HarmonicConjugateOf(a, b, c) => {
                let va = self.evaluate_node_inner(*a, vars, cache, in_progress)?;
                let vb = self.evaluate_node_inner(*b, vars, cache, in_progress)?;
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_harmonic_conjugate(&va, &vb, &vc))
            }
            // 🌟 複比(A,B;C,D)はPoint型ではなくScalar型の値(A,B,C,Dが直線上に
            // ある前提でのτ_D/τ_C)なので、点のような同次座標[x,y,z]ではなく
            // LengthSqと同じ「値, 1, 1」の3要素形式で返す(numeric_values_proportional
            // が単純な値比較として扱えるようにするための既存の慣習)。
            Definition::CrossRatio(a, b, c, d) => {
                let va = self.evaluate_node_inner(*a, vars, cache, in_progress)?;
                let vb = self.evaluate_node_inner(*b, vars, cache, in_progress)?;
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                let vd = self.evaluate_node_inner(*d, vars, cache, in_progress)?;
                mmp_calculators::calc_cross_ratio(&va, &vb, &vc, &vd)
                    .map(|k| vec![k, ModInt::new(1), ModInt::new(1)])
            }
            // 🌟 線束の複比。直線の同次係数を双対平面の点とみなせば、共点な4直線の複比は点の複比と同じ
            // calc_cross_ratio で計算できる。
            Definition::CrossRatioOfLines(a, b, c, d) => {
                let va = self.evaluate_node_inner(*a, vars, cache, in_progress)?;
                let vb = self.evaluate_node_inner(*b, vars, cache, in_progress)?;
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                let vd = self.evaluate_node_inner(*d, vars, cache, in_progress)?;
                mmp_calculators::calc_cross_ratio(&va, &vb, &vc, &vd)
                    .map(|k| vec![k, ModInt::new(1), ModInt::new(1)])
            }
            // 🌟 円周点I,Jのような「常にこの値」の定数。varsの内容に関わらず
            // 埋め込まれたModIntをそのまま返す。
            Definition::ConstantHomogeneous(a, b, c) => Some(vec![*a, *b, *c]),
            // 🌟 5点を通る一般二次曲線の係数[A,B,C,D,E,F]。calc_circumcircleの
            // 一般化(calc_conic_through_5_pointsのコメント参照)。
            Definition::ConicThrough5Points(p1, p2, p3, p4, p5) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                let v3 = self.evaluate_node_inner(*p3, vars, cache, in_progress)?;
                let v4 = self.evaluate_node_inner(*p4, vars, cache, in_progress)?;
                let v5 = self.evaluate_node_inner(*p5, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_conic_through_5_points(&[v1, v2, v3, v4, v5]))
            }
            // 🌟 2つのScalarの積。LengthSq等と同じ「値,1,1」の3要素形式で
            // 評価する(numeric_values_proportionalが単純な値比較として扱える)。
            Definition::Product(a, b) => {
                let va = self.evaluate_node_inner(*a, vars, cache, in_progress)?;
                let vb = self.evaluate_node_inner(*b, vars, cache, in_progress)?;
                if va.is_empty() || vb.is_empty() { return None; }
                Some(vec![va[0] * vb[0], ModInt::new(1), ModInt::new(1)])
            }
        }
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
    /// 外積(クロス積)がゼロかどうかで比較する(mmp_tester.rsのverify_identicalと
    /// 同じロジック。EGraphからmmp_tester.rsに依存させたくないのでここに複製する)。
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
    /// 定義グラフは DAG なのでメモ化が必須。ただし循環で「不可欠」と倒した結果は経路に依存するのでメモ化しない。
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

    /// 🌟 このFreePointが、自身の座標では裏付けられない接続(incidence)を
    /// 1つでも持っているか(=numeric_plausibility_checkがこの点に依存する
    /// 数値評価を信用してよいか)を判定する。
    fn has_extraneous_incidence(&self, free_point: ClassId) -> bool {
        let rep = self.get_rep(free_point);
        let comp = match self.entities[rep.0].components.first() {
            Some(c) => c,
            None => return false,
        };
        comp.subobjects.iter()
            .map(|&s| self.get_rep(s))
            .filter(|&s| matches!(self.entities[s.0].entity_type, EntityType::Line | EntityType::Conic))
            .any(|curve| !self.is_natural_incidence(rep, curve))
    }

    /// 🌟 has_extraneous_incidenceが真だったFreePointについて、その前提の
    /// 相手となる直線/円を1つ選ぶ(自身の定義からは自然に従わない、
    /// link_logical_incidenceだけに由来する接続のうち最初に見つかったもの)。
    /// 1点が複数の構造的前提を同時に持つ場合、ここでは最初の1つしか満たさない
    /// (全部を同時に満たす座標は一般には存在しないので、これは近似的な
    /// 対処にとどまる)。
    fn find_incidence_constraint(&self, free_point: ClassId) -> Option<ClassId> {
        let rep = self.get_rep(free_point);
        let comp = self.entities[rep.0].components.first()?;
        comp.subobjects.iter()
            .map(|&s| self.get_rep(s))
            .find(|&s| matches!(self.entities[s.0].entity_type, EntityType::Line | EntityType::Conic)
                && !self.is_natural_incidence(rep, s))
    }

    /// 🌟 id を、座標が割り当て済みの自由点だけで評価できる定義が少なくとも1つあるか。サンプリングの途中で、
    /// まだ座標の決まっていない自由点に依存する評価を先に弾く。
    fn free_point_ancestors_ready(&self, id: ClassId, vars: &FxHashMap<String, ModInt>) -> bool {
        // マージで定義が同居した同値類では、どれか1つの定義で評価できれば十分(全ての定義の祖先は要求しない)。
        let mut stack = HashSet::new();
        let mut ready_memo = FxHashMap::default();
        self.node_ready(id, vars, &mut stack, &mut ready_memo)
    }

    /// nodeを、座標が既に割り当てられた自由点だけで評価できる定義が(再帰的に)
    /// 少なくとも1つあるか。循環に当たった経路は「評価できない」とみなす。
    /// 循環の影響を受けた偽は経路に依存するので、真だけをメモ化する。
    fn node_ready(&self, id: ClassId, vars: &FxHashMap<String, ModInt>,
                  stack: &mut HashSet<usize>, memo: &mut FxHashMap<usize, bool>) -> bool {
        let rep = self.get_rep(id);
        if memo.contains_key(&rep.0) { return true; }
        if !stack.insert(rep.0) { return false; }
        let defs = self.entities[rep.0].components.first()
            .map(|c| c.definitions.clone()).unwrap_or_default();
        let name = &self.entities[rep.0].name;
        let ready = defs.iter().any(|d| match d {
            Definition::FreePoint => vars.contains_key(&format!("{}_x", name)),
            Definition::GivenPoint => true,
            _ => d.get_parents().iter().all(|&p| self.node_ready(p, vars, stack, memo)),
        });
        stack.remove(&rep.0);
        if ready { memo.insert(rep.0, true); }
        ready
    }

    /// 自由点 fp が、自身の定義からは従わない全ての接続(直線・二次曲線に乗っている)を、
    /// いま割り当てた座標で実際に満たしているか。
    fn incidences_hold(&self, fp: ClassId, vars: &FxHashMap<String, ModInt>,
                       cache: &mut FxHashMap<usize, Vec<ModInt>>) -> bool {
        let Some(p) = self.evaluate_node(fp, vars, cache) else { return false };
        if p.len() < 3 { return false; }
        let (x, y, z) = (p[0], p[1], p[2]);
        self.find_extraneous_incidences(fp).into_iter().all(|curve| {
            let Some(v) = self.evaluate_node(curve, vars, cache) else { return false };
            match self.entities[curve.0].entity_type {
                EntityType::Line if v.len() >= 3 => (v[0] * x + v[1] * y + v[2] * z).0 == 0,
                EntityType::Conic if v.len() >= 6 =>
                    (v[0] * x * x + v[1] * x * y + v[2] * y * y + v[3] * x * z + v[4] * y * z + v[5] * z * z).0 == 0,
                _ => false,
            }
        })
    }

    /// curve の定義のうち少なくとも1つが point を必要とするか(= その定義で評価
    /// する限り、point が curve に乗っていることは自動的に満たされる)。
    fn some_definition_requires(&self, point: ClassId, curve: ClassId) -> bool {
        let (point, curve) = (self.get_rep(point), self.get_rep(curve));
        let defs = match self.entities[curve.0].components.first() {
            Some(c) => c.definitions.clone(),
            None => return false,
        };
        let mut memo = rustc_hash::FxHashMap::default();
        defs.iter().any(|d| d.get_parents().iter().any(|&p| {
            let mut stack = HashSet::new();
            self.evaluation_requires_point(point, p, &mut stack, &mut memo)
        }))
    }

    /// 🌟 直線の係数(a,b,c: a*x+b*y+c=0)を満たすランダムな点(x,y)を1つ選ぶ。
    fn sample_point_on_line_coeffs(&self, a: ModInt, b: ModInt, c: ModInt) -> Option<(ModInt, ModInt)> {
        if b.0 != 0 {
            let x = self.random_modint();
            let y = -(a * x + c) / b;
            Some((x, y))
        } else if a.0 != 0 {
            let y = self.random_modint();
            let x = -c / a;
            Some((x, y))
        } else {
            None // 縮退した直線(0=0)。理論上起こらないはずだが安全側に倒す
        }
    }

    /// 🌟 直線lineの上にあるランダムな点を1つサンプリングする。
    /// lineが依存する自由点の座標がまだ決まっていなければNone(呼び出し側で
    /// 後の反復に回してもらう)。
    fn sample_point_on_line(&self, line: ClassId, vars: &FxHashMap<String, ModInt>, cache: &mut FxHashMap<usize, Vec<ModInt>>) -> Option<(ModInt, ModInt)> {
        if !self.free_point_ancestors_ready(line, vars) { return None; }
        let coeffs = self.evaluate_node(line, vars, cache)?;
        if coeffs.len() < 3 { return None; }
        self.sample_point_on_line_coeffs(coeffs[0], coeffs[1], coeffs[2])
    }

    /// 🌟 Circumcircle/ConicThrough5Points の定義から、その二次曲線に乗っていることが保証された点を1つ返す
    /// (円もこの経路)。無限遠点(z=0)は Vieta のサンプリングに使えないので避ける。
    fn conic_definition_known_point(&self, conic: ClassId) -> Option<ClassId> {
        let rep = self.get_rep(conic);
        let comp = self.entities[rep.0].components.first()?;
        comp.definitions.iter().find_map(|def| {
            match def {
                Definition::Circumcircle(p1, _, _) => Some(*p1),
                Definition::ConicThrough5Points(p1, p2, p3, p4, p5) => {
                    [*p1, *p2, *p3, *p4, *p5].into_iter()
                        .find(|&p| !self.is_connected(p, self.line_infinity))
                }
                _ => None,
            }
        })
    }

    /// 🌟 二次曲線 conic 上のランダムな点を1つ取る。方程式に既知の点 (x1,y1) を通るランダムな直線
    /// (x1+t dx, y1+t dy) を代入すると t の2次式の定数項が0になるので、非自明な解 t=-β/α が平方根なしに
    /// 求まる(Vieta)。
    fn sample_point_on_conic(&self, conic: ClassId, vars: &FxHashMap<String, ModInt>, cache: &mut FxHashMap<usize, Vec<ModInt>>) -> Option<(ModInt, ModInt)> {
        if !self.free_point_ancestors_ready(conic, vars) { return None; }
        let coeffs = self.evaluate_node(conic, vars, cache)?;
        if coeffs.len() < 6 { return None; }
        let (a, b, c, d, e) = (coeffs[0], coeffs[1], coeffs[2], coeffs[3], coeffs[4]);

        let known_point = self.conic_definition_known_point(conic)?;
        // known_pointはconicの生成元自身なので、free_point_ancestors_ready(conic, ..)が
        // 真であれば必ずその祖先もvarsに揃っている(部分集合関係)。
        let kp = self.evaluate_node(known_point, vars, cache)?;
        if kp.len() < 3 || kp[2].0 == 0 { return None; }
        let (x1, y1) = (kp[0] / kp[2], kp[1] / kp[2]);

        let two = ModInt::new(2);
        for _ in 0..8 {
            let dx = self.random_modint();
            let dy = self.random_modint();
            let alpha = a * dx * dx + b * dx * dy + c * dy * dy;
            if alpha.0 == 0 { continue; } // 縮退方向(漸近方向、理論上ごく低確率)。引き直す
            let beta = two * a * x1 * dx + b * (x1 * dy + y1 * dx) + two * c * y1 * dy + d * dx + e * dy;
            let t = -(beta / alpha);
            return Some((x1 + t * dx, y1 + t * dy));
        }
        None
    }

    /// 🌟 has_extraneous_incidence(fp) が真の自由点に、乗っていると分かっている直線・二次曲線の上の座標を
    /// 割り当てる。評価できる直線が2本以上あれば、1本だけ選ばずにその交点を取る(1本しか満たさない座標では、
    /// もう1本との正しい合流を数値チェックが却下してしまう)。
    fn sample_point_on_constraint(&self, fp: ClassId, vars: &FxHashMap<String, ModInt>, cache: &mut FxHashMap<usize, Vec<ModInt>>) -> Option<(ModInt, ModInt)> {
        let rep = self.get_rep(fp);
        let ready_lines: Vec<ClassId> = self.find_extraneous_incidences(rep).into_iter()
            .filter(|&c| self.entities[c.0].entity_type == EntityType::Line && self.free_point_ancestors_ready(c, vars))
            .collect();
        if ready_lines.len() >= 2 {
            let v1 = self.evaluate_node(ready_lines[0], vars, cache)?;
            let v2 = self.evaluate_node(ready_lines[1], vars, cache)?;
            let inter = mmp_calculators::calc_intersection(&v1, &v2);
            if inter.len() < 3 || inter[2].0 == 0 { return None; } // 平行(無限遠)や退化は諦める
            return Some((inter[0] / inter[2], inter[1] / inter[2]));
        }

        let curve = self.find_incidence_constraint(rep)?;
        match self.entities[curve.0].entity_type {
            EntityType::Line => self.sample_point_on_line(curve, vars, cache),
            // 🌟 EntityType::Circle撤廃(円もConic)により、sample_point_on_circle
            // (4係数専用)への分岐は不要になった。全てsample_point_on_conic
            // (6係数、円は3実点+I+Jの5点として自動的に含まれる)に一本化する。
            EntityType::Conic => self.sample_point_on_conic(curve, vars, cache),
            _ => None,
        }
    }

    /// 🌟 find_incidence_constraintの「複数版」: has_extraneous_incidenceが
    /// 真となる原因になっている(=自身の定義からは自然に従わない)接続を
    /// 全て列挙する。sample_point_on_constraintが「2本以上の直線に同時に
    /// 乗っている」ケースを検出するために使う。
    fn find_extraneous_incidences(&self, free_point: ClassId) -> Vec<ClassId> {
        let rep = self.get_rep(free_point);
        let comp = match self.entities[rep.0].components.first() {
            Some(c) => c,
            None => return Vec::new(),
        };
        // 🐛 subobjects はマージ前の生のIDを持ち続けるので、代表元に直すと同じ曲線が
        // 何度も現れる(miquel では CircAEF が数十回)。重複を落とさないと、下の
        // 「2本の直線に乗っているなら交点」の分岐が同じ直線どうしの交点を計算して
        // 退化し、その点の座標が決まらなくなる(発見モードの compute_incidence_constraints
        // で直したのと同じ穴)。
        let mut out: Vec<ClassId> = comp.subobjects.iter()
            .map(|&s| self.get_rep(s))
            .filter(|&s| matches!(self.entities[s.0].entity_type, EntityType::Line | EntityType::Conic))
            .collect();
        out.sort_unstable_by_key(|c| c.0);
        out.dedup();
        out.retain(|&s| !self.is_natural_incidence(rep, s));
        out
    }

    /// 🌟 numeric_plausibility_check用に、祖先の自由点それぞれへ座標を割り当てる。
    /// 構造的前提を持たない自由点には単純な乱数座標を、持つ自由点にはその前提
    /// (直線/円の上にあること)を実際に満たす座標を割り当てる。前提を満たす
    /// 座標は、前提の相手(直線/円)が依存する自由点の座標が先に決まっている
    /// 必要があるため、複数パスで「計算できるものから確定させる」不動点反復を
    /// 行う。全ての制約点を解決できればtrue、対応できない構造的前提や
    /// 循環依存が残ればfalseを返す(呼び出し側は判定不能(None)に倒すこと)。
    fn assign_free_point_coords(&self, ancestors: &[ClassId], vars: &mut FxHashMap<String, ModInt>) -> bool {
        let mut pending: Vec<ClassId> = Vec::new();
        for &fp in ancestors {
            if self.has_extraneous_incidence(fp) {
                pending.push(fp);
            } else {
                let name = self.entities[fp.0].name.clone();
                vars.insert(format!("{}_x", name), self.random_modint());
                vars.insert(format!("{}_y", name), self.random_modint());
            }
        }

        let constrained: Vec<ClassId> = pending.clone();
        let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
        loop {
            if pending.is_empty() {
                // 🐛 最後に、制約付きの自由点が全ての構造的前提を本当に満たしているかを
                // 確かめる。サンプリングは前提を1つしか満たさない(直線と円の両方に乗る点は
                // 片方にしか乗らない)ことがあり、行き詰まりの解消で自由に置いた点も前提を
                // 外れうる。そういう座標で比べると、正しい結合を「数値的に別物」と誤って
                // 却下してしまう(bench_2010g1 で75件)。前提を満たさない座標しか作れない
                // ときは、これまで通り判定不能にする。
                return constrained.iter().all(|&fp| self.incidences_hold(fp, vars, &mut cache));
            }
            let mut progressed = false;
            let mut still_pending = Vec::new();
            for fp in pending.drain(..) {
                match self.sample_point_on_constraint(fp, vars, &mut cache) {
                    Some((x, y)) => {
                        let name = self.entities[fp.0].name.clone();
                        vars.insert(format!("{}_x", name), x);
                        vars.insert(format!("{}_y", name), y);
                        progressed = true;
                    }
                    None => still_pending.push(fp),
                }
            }
            pending = still_pending;
            if !progressed {
                // 🐛 循環の解消(実測で判明): 円 Omega = Circumcircle(A,B,C) の上に自由点D
                // がある図で、証明が進んで Omega に Circumcircle(B,C,D) などの定義が
                // 同居すると、A・B・C それぞれにも「Aを使わずに Omega を評価する経路が
                // ある」ので Omega への接続が制約扱いになる。すると A,B,C,D の全員が
                // 互いの座標を待って1つも決まらず、数値チェックが全部「判定不能」を
                // 返していた。判定不能は結合を許す側に倒れるので、無関係な直線どうしが
                // 結合され、図が崩壊した(bench_2016armog10p2)。
                //
                // 実際に必要なのは「どの点を自由に置き、どの点を曲線上に取るか」の
                // 順序だけで、A,B,C を自由に置けば D は Circumcircle(A,B,C) の上に
                // 取れ、全ての定義が一致する。そこで行き詰まったら、制約の相手の曲線の
                // どれかの定義がその点を必要とする(=その定義で評価すれば自動的に
                // 乗っている)点のうち、最も古い1つを自由に置いてから続ける。
                let pick = pending.iter().copied()
                    .filter(|&fp| self.find_extraneous_incidences(fp).iter()
                        .all(|&c| self.some_definition_requires(fp, c)))
                    .min_by_key(|fp| fp.0);
                match pick {
                    Some(fp) => {
                        let name = self.entities[fp.0].name.clone();
                        vars.insert(format!("{}_x", name), self.random_modint());
                        vars.insert(format!("{}_y", name), self.random_modint());
                        pending.retain(|&q| q != fp);
                    }
                    None => return false,
                }
            }
        }
    }

    /// 🌟 idの祖先(Definitionの親を再帰的に辿った先)にあるFreePointを全て集める。
    /// 定数(GivenPoint)はそこで打ち切る(座標を持たないので祖先探索の対象外)。
    /// マージ後は1つのエンティティが複数のDefinitionを持ち得るので、
    /// 「安全側」に倒して全てのDefinitionの親を辿る(いずれか1つでも構造的にしか
    /// 保証されていないFreePointに触れたら、そちら経由の値かもしれないとみなし
    /// 用心する)。
    fn collect_free_point_ancestors(&self, id: ClassId, visited: &mut HashSet<usize>, out: &mut Vec<ClassId>) {
        let rep = self.get_rep(id);
        if !visited.insert(rep.0) { return; }
        let defs = match self.entities[rep.0].components.first() {
            Some(c) => c.definitions.clone(),
            None => return,
        };
        for def in &defs {
            match def {
                Definition::FreePoint => out.push(rep),
                Definition::GivenPoint => {} // Ang90/Ang0/Line_infinity等の定数。座標を持たないので対象外
                _ => {
                    for p in def.get_parents() {
                        self.collect_free_point_ancestors(p, visited, out);
                    }
                }
            }
        }
    }

    /// 🌟 マージを確定する前の数値的な裏付け。祖先の自由点にランダムな座標を割り当て(前提のある点は前提を
    /// 満たすように)、a と b が本当に同じ値になるかを trials 回検算する。明確に矛盾すれば Some(false)、
    /// 座標を組み立てられないか評価できなければ None(判定不能)。
    /// congruence.rs の構造的な伝播(propagate_*_uniqueness)が偶然の一致で誤った同一視をしないためのゲートで、
    /// これ自体は何も証明しない。
    pub(crate) fn numeric_plausibility_check(&self, a: ClassId, b: ClassId, trials: usize) -> Option<bool> {
        // 🐛 問題文は「P はこの円の上」のような前提を座標ではなく link_logical_incidence で与えることが多い。
        // そういう自由点に完全な乱数座標を置くと前提を満たさず、正しいマージまで却下してしまうので、
        // assign_free_point_coords は前提を満たす座標を取る。取れないときだけ None に倒す。
        let mut visited = HashSet::new();
        let mut ancestors = Vec::new();
        self.collect_free_point_ancestors(a, &mut visited, &mut ancestors);
        self.collect_free_point_ancestors(b, &mut visited, &mut ancestors);
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

    /// 🌟 動点法(Method of Moving Points)の次数を数値的に測る。祖先の自由点の1つ(mover)を直線に沿って動かし、
    /// 複数の t で評価して、有限体上のランク判定で座標が満たす有理関数の次数を求める。親の次数の和という構造的な
    /// 上界と違い、中点のように次数が上がらない操作を正しく低く測れる。
    /// mover が見つからないか、どれかのサンプルで評価できなければ None(次数不明)。呼び出し側は次数で足切りしない。
    pub fn measure_numerical_degree(&self, entity: ClassId, max_d: usize) -> Option<usize> {
        let mut visited = HashSet::new();
        let mut ancestors = Vec::new();
        self.collect_free_point_ancestors(entity, &mut visited, &mut ancestors);
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
        let mut visited = HashSet::new();
        let mut ancestors = Vec::new();
        self.collect_free_point_ancestors(l1, &mut visited, &mut ancestors);
        self.collect_free_point_ancestors(l2, &mut visited, &mut ancestors);
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
        let mut visited = HashSet::new();
        let mut ancestors = Vec::new();
        for &p in parents {
            self.collect_free_point_ancestors(p, &mut visited, &mut ancestors);
        }
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

        let mut visited = HashSet::new();
        let mut ancestors = Vec::new();
        self.collect_free_point_ancestors(new_rep, &mut visited, &mut ancestors);
        for &other in &others {
            self.collect_free_point_ancestors(other, &mut visited, &mut ancestors);
        }
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
        if !self.assign_free_point_coords(&others, &mut base_vars) { return None; }
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
            self.random_modint(),
            self.random_modint(),
            self.random_modint(),
            self.random_modint(),
        )
    }
}

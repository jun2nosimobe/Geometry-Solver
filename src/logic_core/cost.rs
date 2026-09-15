//! 🌟 定理マッチングの「見積もりと枝刈り」。
//!
//! どのパターンを次に評価すると安いか(estimate_cost)、そして候補が多すぎる
//! ときに熱(heat)でどこまで絞るか(*_candidates / heat_capped_*)を、ここに
//! 集めてある。探索そのもの(matcher.rs)からこの方針だけを切り離しておくと、
//! 「遅い・届かない」の原因が探索の構造の側なのか、絞り方の側なのかを
//! 分けて考えられる。

use std::rc::Rc;

use crate::mmp_core::ClassId;
use super::*;

impl ProverEngine {
    /// 🌟 順序/相異の制約が、いま束縛されている変数の範囲だけで既に破れているか。
    ///
    /// Pattern::Order / Distinct は estimate_cost が「全変数が束縛されるまで
    /// INFINITY」を返すので、DFSはそれらを最後まで選ばない。つまり A=B の
    /// ような明らかに無駄な割り当てでも、残りの変数を全部束縛しきってから
    /// 初めて弾かれる。各定理が distinct(&["LOA","LOB"]) →
    /// distinct(&["LOA","LOB","LOC"]) → …と段階的な制約を手で書き並べている
    /// のは、この穴の手作業の回避策(「複比の透視射影不変性」や
    /// 「共点二弦の相似」のコメント参照)。
    ///
    /// これを使うと、束縛済みの範囲で既に破れている枝を最も早い時点で切れる。
    /// まだ束縛されていない変数が絡む部分は「まだ分からない」として通すので、
    /// 通る解は一切減らない(純粋に枝刈りが増えるだけ)――束縛済み変数の
    /// 代表元はこのdfs_match木の中では動かない(マッチング中はe-graphを
    /// 書き換えない)ので、いま破れている制約が深いところで満たされることは無い。
    ///
    /// 🐛 Distinct はここで見ない(実測の結果)。Distinct も同じ理屈で前倒し
    /// できて、しかも効果は遥かに大きい――消費仕事量が simson −23%、
    /// orthocenter −21%、bench_2012egmop1 −28% と、この前倒しで減る分の
    /// ほぼ全部が Distinct 由来だった。にもかかわらず入れていないのは、
    /// 37問中 30→29 と bench_2018chnwesternmop5 を落とすため。
    ///
    /// 枝刈り自体は健全なので、これは「無駄なはずの枝を探索していたことが、
    /// たまたまその問題の証明に必要な状態を作っていた」という探索の巡り合わせ。
    /// dfs_cap を1.5倍・2倍にしても、heat_cap や fanout_heat_cap を広げても
    /// 戻らなかった。オンデマンド作図の回数も31対32でほぼ同じなので、
    /// 「刈った枝が需要を登録していた」という筋でもない。
    /// Distinct も見るようにするのは下の match に腕を1つ足すだけなので、
    /// この巡り合わせへの弱さが別途解消できたときに入れ直せる。
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
        match pat {
            Pattern::Fact(def) => {
                let unbound_count = def.args.iter().filter(|v| !bind.contains_key(*v)).count();
                if unbound_count == 0 { return 0.0; }

                let base_cost = if def.fact_type == "Identical" {
                    if unbound_count == 1 { 1.0 } else { 15.0 }
                } else if def.fact_type == "Connected" {
                    if unbound_count == 1 { 5.0 } else {
                        // 🐛 FIX: 以前は両方未束縛のConnectedを「(None,None)は何もしない」
                        // 前提でコスト10000(=事実上最後回し)にしていたが、(None,None)を
                        // きちんと実装した今は「親の型で絞り込んだ局所探索」でしかない。
                        // 固定値のままだと、円のように個体数が少ない型を親に持つ場合
                        // (安く見積もるべき)と、点のように個体数が多い型を親に持つ場合
                        // (高く見積もるべき)を区別できない。親変数の宣言型を引いて、
                        // 実際にその型が今グラフに何個あるかで見積もる。
                        let parent_var = &def.args[1];
                        match theorem.entities.get(parent_var) {
                            Some(&expected_type) => {
                                // 🌟 最適化: 以前はここで entities を毎回全走査していた。
                                // estimate_cost はDFSの各ノードで残りパターンの数だけ
                                // 呼ばれるホットパスなので、実体数が数百になる自由作図後は
                                // 見積もりだけで効いてくる。EGraph側のキャッシュを使う
                                // (type_generationが動いたときだけ数え直す)。
                                let count = self.egraph.count_of_type(expected_type);
                                (count as f64) * 5.0 + 10.0
                            }
                            None => 10000.0, // 型情報すら無ければ従来通り最後回し
                        }
                    }
                } else if def.fact_type == "DefinedBy" {
                    if unbound_count == def.args.len() { 
                        let penalty = match def.target_type.as_deref().unwrap_or("") {
                            "Midpoint" | "LengthSq" | "Intersection" => 0.0,
                            "LineThroughPoints" | "PerpendicularLine" | "TangentLine" => 10.0,
                            "DirectionOf" | "AnglePair" | "Circumcircle" => 20.0,
                            _ => 5.0,
                        };
                        100.0 + (unbound_count as f64) + penalty 
                    } else {
                        10.0 + (unbound_count as f64) * 20.0
                    }
                } else {
                    100.0
                };

                // バインド済み変数の熱と次数が高いほどコストを下げる(優先探索)
                let mut heat = 0.0;
                for v in &def.args {
                    if let Some(&id) = bind.get(v) {
                        let rep = self.egraph.get_rep(id);
                        heat += self.egraph.entities[rep.0].heat_with_degree();
                    }
                }
                
                (base_cost - heat).max(0.1) // 完全に0にはせず僅かなコストを残す[cite: 5]
            }
            Pattern::Order(vars) | Pattern::Distinct(vars) | Pattern::OrderNonStrict(vars) => {
                if vars.iter().any(|v| !bind.contains_key(v)) { std::f64::INFINITY } else { 0.0 }
            }
            Pattern::Not(inner_pat) => self.estimate_cost(inner_pat, bind, theorem),
        }
    }
    

    /// 🌟 match_connected_fact の局所スキャン分岐((Some,None)/(None,Some))
    /// 向けの熱量駆動cap。これらの分岐は「ある実体自身に繋がっている
    /// (少数のはずの)候補」を集めるので、通常は無条件で全件試して問題
    /// なかった。しかし診断計測(円周角の定理)で、多くの点が乗っている円
    /// のような「ハブ」実体では数十件になり得ると判明した――(None,None)
    /// 分岐(identical_self_bind_candidates/connected_pairs_for_types)に
    /// 既に入れているのと同じ熱降順cap(=40)を、候補が実際に多い場合に
    /// 限って適用する(少ない場合はソートのコストも省き従来通り全件試す)。
    pub(crate) fn heat_capped_connected_candidates(&self, candidates: rustc_hash::FxHashSet<ClassId>) -> Vec<ClassId> {
        let mut v: Vec<ClassId> = candidates.into_iter().collect();
        if v.len() > self.heat_cap {
            v.sort_by(|&a, &b| {
                let ha = self.egraph.entities[a.0].heat();
                let hb = self.egraph.entities[b.0].heat();
                hb.partial_cmp(&ha).unwrap_or(std::cmp::Ordering::Equal)
            });
            v.truncate(self.heat_cap);
        }
        v
    }

    /// 🌟 identical_self_bind_cacheのドキュメント参照。Identical(v1, v2)の
    /// 両方未束縛(自己束縛)分岐が問い合わせる、型だけで決まる候補代表元の
    /// 共有列挙結果を返す(heatによる並べ替え・上位40件への絞り込みは
    /// 呼び出し側が毎回この結果に対して行う)。
    pub(crate) fn identical_self_bind_candidates(&mut self, et: crate::mmp_core::EntityType) -> Rc<Vec<ClassId>> {
        let cur_gen = self.egraph.type_generation.get(&et).copied().unwrap_or(0);
        if let Some((cached, cached_gen)) = self.identical_self_bind_cache.get(&et) {
            if *cached_gen == cur_gen { return cached.clone(); }
        }
        let mut reps = Vec::new();
        for id in self.egraph.iter_reps_of_type(et) {
            if self.egraph.entities[id.0].is_active() { reps.push(id); }
        }
        let result = Rc::new(reps);
        self.identical_self_bind_cache.insert(et, (result.clone(), cur_gen));
        result
    }

    /// 🌟 identical_self_bind_angle_cache/identical_self_bind_plain_scalar_cache
    /// のドキュメント参照。EntityType::Scalarの自己束縛候補を「角度
    /// (AnglePair)由来のものだけ」に絞った専用キャッシュ。angle_generation
    /// (mmp_core/mod.rs)が変わっていなければ(=角度が絡む生成・併合が
    /// 一度も起きていなければ)、無関係な長さ・積・複比の生成では
    /// 再計算しない。
    pub(crate) fn identical_self_bind_angle_candidates(&mut self) -> Rc<Vec<ClassId>> {
        let cur_gen = self.egraph.angle_generation;
        if let Some((cached, cached_gen)) = &self.identical_self_bind_angle_cache {
            if *cached_gen == cur_gen { return cached.clone(); }
        }
        let mut reps = Vec::new();
        for id in self.egraph.iter_reps_of_type(crate::mmp_core::EntityType::Scalar) {
            if self.egraph.entities[id.0].is_active() && self.egraph.is_angle_value(id) {
                reps.push(id);
            }
        }
        let result = Rc::new(reps);
        self.identical_self_bind_angle_cache = Some((result.clone(), cur_gen));
        result
    }

    /// 🌟 上のidentical_self_bind_angle_candidatesの裏返し: EntityType::Scalarの
    /// うち角度(AnglePair)由来ではないもの(長さ・積・複比等)だけに絞った
    /// 専用キャッシュ。plain_scalar_generation(mmp_core/mod.rs)が変わって
    /// いなければ再計算しない――角度側の生成・併合だけが起きた場合に、
    /// こちらまで無駄に無効化されるのを防ぐ。EntityType::Angle撤廃より前は
    /// EntityType::Scalarに角度が混ざること自体が無かったので、この絞り込みは
    /// 撤廃前の挙動をそのまま再現するためのものでもある(絞り込まずに
    /// 返すと、角度に無関係なIdentical自己束縛のheatソート済みcapが
    /// 角度候補に食われてしまう)。
    pub(crate) fn identical_self_bind_plain_scalar_candidates(&mut self) -> Rc<Vec<ClassId>> {
        let cur_gen = self.egraph.plain_scalar_generation;
        if let Some((cached, cached_gen)) = &self.identical_self_bind_plain_scalar_cache {
            if *cached_gen == cur_gen { return cached.clone(); }
        }
        let mut reps = Vec::new();
        for id in self.egraph.iter_reps_of_type(crate::mmp_core::EntityType::Scalar) {
            if self.egraph.entities[id.0].is_active() && !self.egraph.is_angle_value(id) {
                reps.push(id);
            }
        }
        let result = Rc::new(reps);
        self.identical_self_bind_plain_scalar_cache = Some((result.clone(), cur_gen));
        result
    }

    /// 🌟 defined_by_full_scan_cacheのドキュメント参照。DefinedByパターンの
    /// 親変数・result_varがどちらも未束縛の場合に問い合わせる、期待される
    /// 結果の型だけで決まる全代表元の共有列挙結果を返す。
    pub(crate) fn defined_by_type_scan_candidates(&mut self, et: crate::mmp_core::EntityType) -> Rc<Vec<ClassId>> {
        let cur_gen = self.egraph.type_generation.get(&et).copied().unwrap_or(0);
        if let Some((cached, cached_gen)) = self.defined_by_full_scan_cache.get(&et) {
            if *cached_gen == cur_gen { return cached.clone(); }
        }
        let result = Rc::new(self.egraph.iter_reps_of_type(et).collect::<Vec<_>>());
        self.defined_by_full_scan_cache.insert(et, (result.clone(), cur_gen));
        result
    }

    /// 🌟 connected_join_cacheのドキュメント参照。Connected(child, parent)の
    /// 両方未束縛分岐が問い合わせる、型だけで決まる(child_rep, parent_rep)
    /// ペアの共有ジョイン結果を返す。type_generationが前回計算時と
    /// 変わっていなければキャッシュをそのまま返し(定理をまたいだ再利用)、
    /// 変わっていれば再計算してキャッシュを更新する。
    pub(crate) fn connected_pairs_for_types(&mut self, c_type: crate::mmp_core::EntityType, p_type: crate::mmp_core::EntityType) -> Rc<Vec<(ClassId, ClassId)>> {
        let cur_c_gen = self.egraph.type_generation.get(&c_type).copied().unwrap_or(0);
        let cur_p_gen = self.egraph.type_generation.get(&p_type).copied().unwrap_or(0);
        if let Some((cached, gen_c, gen_p)) = self.connected_join_cache.get(&(c_type, p_type)) {
            if *gen_c == cur_c_gen && *gen_p == cur_p_gen {
                return cached.clone();
            }
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

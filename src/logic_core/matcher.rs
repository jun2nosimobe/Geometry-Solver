//! 🌟 定理マッチングの探索本体(DFS)。
//!
//! パターン列を1本ずつ消費しながら変数を束縛していく深さ優先探索と、
//! fact_type ごとの候補の展開。どれを次に選ぶか・どこまで候補を見るかの
//! 方針は cost.rs に分けてある。

use std::cmp::Ordering;
use std::rc::Rc;
use std::hash::{Hash, Hasher};

use crate::mmp_core::{ClassId, Definition, EntityType, Fact};
use super::*;

impl ProverEngine {
    /// 🌟 dep_mask引数のドキュメント参照(entity_type_bit/ALL_TYPES_MASK、
    /// mod冒頭)。「呼び出し元が本来欲しいのは戻り値」だが全ての中間関数
    /// (match_fact_pattern以下)のシグネチャを戻り値ありに変えるのは
    /// 侵襲が大きいため、代わりに末尾の&mut u8引数として同じ情報を運ぶ。
    /// 各呼び出しは以下の規約を守る:
    ///   1. 受け取ったdep_maskは「呼び出し元(親)が集計したい先」を指す。
    ///   2. 自分自身の探索(このstate_sig1つ分)にはローカルなmy_maskを
    ///      新たに作り、子への再帰呼び出しにはdep_maskではなく&mut my_mask
    ///      を渡す(自分の探索に閉じた集計にするため)。
    ///   3. 末尾で、matched_anyがfalseならfailed_pathsにmy_maskを添えて
    ///      記録し、成功/失敗を問わずmy_maskを親のdep_maskへORして返す。
    pub fn dfs_match(
        &mut self,
        theorem: &TheoremDef,
        patterns: &[Pattern],
        active: u64,
        bind: Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashMap<u64, (u8, [u64; 4])>,
        dep_mask: &mut u8,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
        self.dfs_calls += 1;
        if self.dfs_calls > self.dfs_cap { return; }

        // 🌟 失敗パスのキャッシュチェック
        let state_sig = {
            let mut hasher = rustc_hash::FxHasher::default();
            // 🌟 最適化: 以前は bind と flip_states をそれぞれ Vec に collect して
            // ソートしてから順に流し込んでいた。この署名はDFSの全ノードで作られる
            // ので、1ノードあたり2回のヒープ確保と2回のソートを払っていた。
            //
            // 要るのは「同じ状態なら同じ値」だけで、順序そのものに意味は無い。
            // 各要素を個別に潰してから wrapping_add で畳み込めば、順序に依らない
            // 値が確保もソートも無しで得られる(可換な畳み込み)。
            // 個別のハッシュは十分に撹拌されているので、加算の可換性が衝突を
            // 増やす度合いは無視できる――実測でも simson / nine_point_full /
            // orthocenter / bench_2012egmop1 の消費仕事量が1ステップも変わらない
            // (= 枝刈りの当たり外れが以前と完全に一致している)ことを確認済み。
            // 🌟 最適化: 以前は bind と flip_states をそれぞれ Vec に collect して
            // ソートしていた。この署名はDFSの全ノードで作られるので、1ノード
            // あたり2回のヒープ確保を払っていた。定理の変数は実測で最大でも
            // 20個程度なので、スタック上の固定長バッファに集めて同じように
            // ソートすれば、確保だけを消せる。
            //
            // 🌟 ハッシュに流し込む順序も内容も以前と完全に同じにしてある。
            // 一度「順序に依らない可換な畳み込み(個別ハッシュのwrapping_add)」
            // にして確保もソートも消す版を試したが、FxHashの出力は撹拌が弱く、
            // 足し合わせると衝突が無視できない量になる――実測で探索の経路が
            // 大きく変わってしまった(simson 136k→197k、bench_2012egmop1
            // 3.66M→1.49M など)。失敗パスのキャッシュは衝突すると正しい枝を
            // 誤って刈るので、値が変わらないことを優先する。
            const SIG_CAP: usize = 48;
            (active.count_ones() as usize).hash(&mut hasher);
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
        };

        // 🌟 global_failed_pathsのドキュメント参照(ProverEngine)。エントリは
        // (依存マスク, 挿入時点でのALL_ENTITY_TYPES順type_generation
        // スナップショット)。タスクをまたいで永続化されるようになった今、
        // 「取り出した時点でまだ有効か」をエントリごとに都度検証する必要が
        // ある――マスクが立っている型についてだけ、挿入時のスナップショット
        // と現在値を比較する(マスク0のエントリは何と比較するまでもなく
        // 常に有効)。無効なら通常のキャッシュミスとして扱い、探索し直す
        // (再度失敗すれば新しいスナップショット付きで上書きされる)。
        if let Some(&(cached_mask, cached_gens)) = failed_paths.get(&state_sig) {
            let still_valid = (0..4).all(|i| {
                (cached_mask & (1 << i)) == 0
                    || self.egraph.type_generation.get(&ALL_ENTITY_TYPES[i]).copied().unwrap_or(0) == cached_gens[i]
            });
            if still_valid {
                *dep_mask |= cached_mask;
                return;
            }
        }

        if active == 0 {
            for (v_name, id) in &bind {
                if let Some(expected_type) = theorem.entities.get(v_name) {
                    let actual_type = self.egraph.entities[self.egraph.get_rep(*id).0].entity_type;
                    if *expected_type != actual_type { return; }
                }
            }
            on_match(&bind, &flip_states);
            return;
        }

        // 🌟 最適化: 「まだ消費していないパターン」をビットマスクで持つ。
        //
        // 以前は分岐のたびに「評価対象を除いた残り」を新しい Vec として組み直し、
        // Rc に包んでいた。ポインタ共有で済むのは子への受け渡しだけで、組み直し
        // そのもの(残りパターン数だけの Pattern::clone)はDFSの全ノードで走る。
        // Pattern は fact_type: String と args: Vec<String> を持つので、この
        // clone は文字列のヒープ確保を伴っていた。
        //
        // パターン列は定理ごとに不変なので、実体は定理の持ち物をそのまま借り、
        // 「どれがまだ生きているか」だけを u64 のビットで持てばよい。確保も
        // clone も消え、子への受け渡しは整数1個のコピーになる
        // (定理1つあたりのパターン数は実測で最大31本。上限64本は
        // theorems::tests::every_theorem_fits_the_pattern_bitmask で保証する)。
        let mut best_idx = 0;
        let mut best_cost = std::f64::INFINITY;
        for i in 0..patterns.len() {
            if active & (1u64 << i) == 0 { continue; }
            let cost = self.estimate_cost(&patterns[i], &bind, theorem);
            if cost < best_cost { best_cost = cost; best_idx = i; }
        }
        let next_active = active & !(1u64 << best_idx);
        let mut matched_any = false;
        // 🌟 このstate_sig(このdfs_match呼び出し1回分)の探索が実際に
        // 依存した型の集計。子への再帰にはdep_maskではなくこちらを渡す。
        let mut my_mask: u8 = 0;

        // クロージャをラップして、1度でもマッチしたかを記録する
        let mut wrapped_on_match = |b: &Bind, f: &FlipStates| {
            matched_any = true;
            on_match(b, f);
        };

        match &patterns[best_idx] {
            Pattern::Order(vars) => {
                let mut is_ordered = true;
                for i in 0..vars.len().saturating_sub(1) {
                    if let (Some(id1), Some(id2)) = (bind.get(&vars[i]), bind.get(&vars[i+1])) {
                        if self.egraph.get_rep(*id1).0 >= self.egraph.get_rep(*id2).0 { is_ordered = false; break; }
                    }
                }
                if is_ordered { self.dfs_match(theorem, patterns, next_active, bind, flip_states, failed_paths, &mut my_mask, &mut wrapped_on_match); }
            }
            // 🌟 Pattern::OrderNonStrictのドキュメント参照。Orderとの違いは
            // "<"ではなく"<="(等しい場合は許可)で判定する点のみ。
            Pattern::OrderNonStrict(vars) => {
                let mut is_ordered = true;
                for i in 0..vars.len().saturating_sub(1) {
                    if let (Some(id1), Some(id2)) = (bind.get(&vars[i]), bind.get(&vars[i+1])) {
                        if self.egraph.get_rep(*id1).0 > self.egraph.get_rep(*id2).0 { is_ordered = false; break; }
                    }
                }
                if is_ordered { self.dfs_match(theorem, patterns, next_active, bind, flip_states, failed_paths, &mut my_mask, &mut wrapped_on_match); }
            }
            Pattern::Distinct(vars) => {
                let mut unique_ids = rustc_hash::FxHashSet::default();
                let mut is_distinct = true;
                for v in vars {
                    if let Some(&id) = bind.get(v) {
                        let rep_id = self.egraph.get_rep(id);
                        if !unique_ids.insert(rep_id.0) { is_distinct = false; break; }
                    }
                }
                if is_distinct { self.dfs_match(theorem, patterns, next_active, bind, flip_states, failed_paths, &mut my_mask, &mut wrapped_on_match); }
            }
            Pattern::Fact(def) => {
                self.match_fact_pattern(theorem, def, patterns, next_active, &bind, flip_states, failed_paths, &mut my_mask, &mut wrapped_on_match);
            }
            Pattern::Not(inner_pat) => {
                let mut inner_matched = false;
                // 内側は「そのパターン1本だけ」を別のスライスとして評価する。
                let inner = [(**inner_pat).clone()];
                self.dfs_match(theorem, &inner, 1, bind.clone(), flip_states.clone(), failed_paths, &mut my_mask, &mut |_, _| {
                    inner_matched = true;
                });
                if !inner_matched {
                    self.dfs_match(theorem, patterns, next_active, bind, flip_states, failed_paths, &mut my_mask, &mut wrapped_on_match);
                }
            }
        }

        // 🌟 どこにも進めなかった場合、この状態を失敗として記録する
        // (実際に依存した型マスクmy_maskと、その時点でのtype_generation
        // スナップショットを添えて――Distinct/Order/両方束縛済みのチェック
        // だけで確定した失敗はmy_mask=0のままなので、型がいくつ変化しても
        // 永続的に有効なエントリとして残る。global_failed_pathsに昇格した
        // 今、このスナップショットが「取り出し側での有効性の再検証」の
        // 基準になる)。
        if !matched_any {
            failed_paths.insert(state_sig, (my_mask, snapshot_type_generations(&self.egraph)));
        }
        // 🌟 成功・失敗を問わず、この部分木が触れた型を呼び出し元(親)へ
        // 伝播する。親が(この呼び出しとは別の枝の失敗を含めて)最終的に
        // 失敗してfailed_pathsに記録する際、この情報も正しく合算される。
        *dep_mask |= my_mask;
    }

    /// 🌟 match_fact_pattern はfact_typeごとの処理を振り分けるだけの薄いディスパッチャ。
    /// 以前はこの関数自体が360行あり(Identical/Connected/DefinedBy/汎用の4種の
    /// マッチングロジックが全て1つのmatchの中に同居していた)、可読性の観点から
    /// fact_typeごとの専用メソッドに分割した。挙動は一切変えていない。
    pub fn match_fact_pattern(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef,
        patterns: &[Pattern],
        active: u64,
        bind: &Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashMap<u64, (u8, [u64; 4])>,
        dep_mask: &mut u8,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
        match def.fact_type.as_str() {
            "Identical" => self.match_identical_fact(theorem, def, patterns, active, bind, flip_states, failed_paths, dep_mask, on_match),
            "Connected" => self.match_connected_fact(theorem, def, patterns, active, bind, flip_states, failed_paths, dep_mask, on_match),
            "DefinedBy" => self.match_defined_by_fact(theorem, def, patterns, active, bind, flip_states, failed_paths, dep_mask, on_match),
            _ => self.match_generic_fact(theorem, def, patterns, active, bind, flip_states, failed_paths, dep_mask, on_match),
        }
    }

    /// 🌟 "Identical" パターン: v1, v2 の束縛状況(両方束縛済み/片方だけ/どちらも未束縛)
    /// に応じて分岐する。
    pub(crate) fn match_identical_fact(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef,
        patterns: &[Pattern],
        active: u64,
        bind: &Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashMap<u64, (u8, [u64; 4])>,
        dep_mask: &mut u8,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
        let v1 = &def.args[0];
        let v2 = &def.args[1];
        let expected_type = theorem.entities.get(v1).copied(); // 🌟 型情報取得

        match (bind.get(v1).copied(), bind.get(v2).copied()) {
            // 🌟 dep_maskのドキュメント参照(dfs_match)。両方束縛済み/片方だけ
            // 束縛済みの分岐は、既に束縛済みの代表元を直接見るだけで
            // どの型のプールも列挙しないため、依存マスクを一切追加しない
            // (=dep_maskをそのまま子に渡す、new my_maskを作らない)。
            (Some(id1), Some(id2)) => {
                if self.egraph.get_rep(id1) == self.egraph.get_rep(id2) {
                    self.dfs_match(theorem, patterns, active, bind.clone(), flip_states.clone(), failed_paths, dep_mask, on_match);
                }
            }
            (Some(id), None) | (None, Some(id)) => {
                let unbound_var = if bind.get(v1).is_none() { v1 } else { v2 };
                let mut next_bind = bind.clone();
                next_bind.insert(unbound_var.clone(), self.egraph.get_rep(id));
                self.dfs_match(theorem, patterns, active, next_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
            }
            (None, None) => {
                // 🌟 dep_maskのドキュメント参照。ここから先は「型のプールを
                // 列挙する」分岐なので、実際に問い合わせた型をdep_maskへ
                // 記録する(全ての候補に対する再帰呼び出しで共有する)。
                // 🐛 移植バグ修正: 以前はここで「同じ代表元(=既にマージ済み)を持つ
                // 異なる ClassId のペア」を全列挙しており、1つの等価クラスに
                // N個のエンティティが吸収されていると N*(N-1) 通りに爆発していた
                // (「有向角の加法性」のように、この分岐から探索を始める定理で
                // simsonのタイムアウトの主因になっていた)。
                //
                // Python版の対応する _match_identical (両方未束縛) は、対象の型を
                // 持つ「異なる代表元」それぞれについて v1=v2=その代表元、という
                // 自己束縛を O(代表元の数) で列挙するだけだった。この定理は本来
                // schedule_matcher_task によるシード付き起動(実際に発見された
                // Identical事実からD1..D6を具体的に束縛する経路)で使われる前提であり、
                // シード無しの全探索(schedule_full_sweep)から来た場合はこの程度の
                // 軽い足がかりで十分。Python版と同じ挙動に合わせて計算量を落とす。
                // 🌟 RETE的な共有列挙キャッシュ(ユーザー提案「案4」、
                // identical_self_bind_cacheのドキュメント参照): 期待される型が
                // 分かっている場合、この生の候補集合はbindの中身に依存せず
                // 型だけで決まるので、定理をまたいで共有する(型が不明な稀な
                // フォールバックでは従来通りのフルスキャン)。heatによる
                // 並べ替えは共有前の生の集合に対してではなく、キャッシュから
                // 取り出した後に(常に最新のheat_bonusで)行う。
                // 🌟 EntityType::Angle撤廃(mmp_core/mod.rs::EntityTypeの
                // ドキュメント参照)への対応: 角度追跡系定理のIdentical(Ang1,Ang2)
                // シード(theorems.rsで既にtarget_type=Some("Angle")が付いている、
                // 元々は記録目的だけの慣習だったマーカー)は、統合後の
                // EntityType::Scalarの自己束縛候補プールが長さ・積・複比まで
                // 無差別に含むようになった影響を受けやすい――「有向角の加法性」
                // のようにこの分岐から始まる定理で、無関係なScalarまで候補に
                // 混ざるとheatソート済みcapを無駄に消費し、証明が届かなくなる
                // (miquel_quadrilateralで実際に観測)。
                // 🌟 当初はidentical_self_bind_candidates(Scalar)の共有結果を
                // 取り出した後にis_angle_valueで絞り込むだけの実装だったが、
                // それだと絞り込む「前」の共有キャッシュ自体が
                // type_generation[Scalar]で無効化判定されたままなので、
                // 無関係な長さ・積・複比の新規生成のたびに(角度候補を
                // 一切含まない場合でも)このキャッシュが丸ごと無効化・
                // 再列挙され続け、期待したキャッシュ効果が得られなかった
                // (3回集計でベンチマーク合格率69/96→57/96に悪化する回帰と
                // して実測された)。identical_self_bind_angle_candidates/
                // identical_self_bind_plain_scalar_candidatesという、
                // angle_generation/plain_scalar_generationという互いに
                // 独立した専用カウンタで無効化判定する2つの専用キャッシュに
                // 分離し、角度側・非角度側どちらの生成イベントも「無関係な
                // もう一方」のキャッシュを無効化しないようにする。
                let wants_angle = def.target_type.as_deref() == Some("Angle");
                // 🌟 is_cross_ratio_of_lines_valueのドキュメント(mmp_core/query.rs)
                // 参照。同じ理由(自己束縛プールの無関係な値による汚染)で、
                // sub_type="CrossRatioOfLines"マーカーが付いているパターンは
                // さらにCrossRatioOfLines由来のものだけに絞る。
                let wants_cr_of_lines = def.sub_type.as_deref() == Some("CrossRatioOfLines");
                let mut reps: Vec<ClassId> = match expected_type {
                    Some(EntityType::Scalar) if wants_angle => (*self.identical_self_bind_angle_candidates()).clone(),
                    Some(EntityType::Scalar) if wants_cr_of_lines => {
                        (*self.identical_self_bind_plain_scalar_candidates()).iter()
                            .copied()
                            .filter(|&id| self.egraph.is_cross_ratio_of_lines_value(id))
                            .collect()
                    }
                    Some(EntityType::Scalar) => (*self.identical_self_bind_plain_scalar_candidates()).clone(),
                    Some(et) => {
                        (*self.identical_self_bind_candidates(et)).clone()
                    }
                    None => {
                        let mut reps = Vec::new();
                        for i in 0..self.egraph.entities.len() {
                            let id = ClassId(i);
                            if self.egraph.get_rep(id) != id { continue; } // 代表元のみ
                            if self.egraph.entities[i].is_active() {
                                reps.push(id);
                            }
                        }
                        reps
                    }
                };
                // 🐛 実測に基づくFIX: このシード無し(両変数未束縛)経路は、
                // apply_conclusionsが直後にheat_bonusを加算した「たった今マージ
                // されたばかりの代表元」(=この定理が本来欲しがっている候補で
                // ある可能性が高い)を、生成順(ClassId順)のまま辿っていたため
                // 後回しにしてしまい、無関係な候補を大量に試してからようやく
                // 正解に辿り着く(あるいはdfs_cap/持ち時間の方が先に尽きる)、
                // という実際の性能問題を「共点二弦の相似」定理のテストで観測した。
                // heat(base_importance+heat_bonus)の降順に並べ替えるだけで、
                // 直近にマージされた=熱い代表元から先に試せるようになる
                // (match_defined_by_factの全件スキャンで既に使われているのと
                // 同じ「熱で優先順位を付ける」考え方をこちらにも適用しただけ)。
                reps.sort_by(|&a, &b| {
                    let ha = self.egraph.entities[a.0].heat();
                    let hb = self.egraph.entities[b.0].heat();
                    hb.partial_cmp(&ha).unwrap_or(std::cmp::Ordering::Equal)
                });
                // 🌟 この経路は本来「シードが来なかった時の保険」に過ぎず
                // (本命はschedule_matcher_task/DefinedByシード)、候補が
                // 大量にある問題(例: 複比が大量生成されるtest_cross_ratio)では
                // 無関係なエンティティまで大量に自己束縛して試すコストが
                // 無視できなくなり得る。上のheatソートで関係のある候補は
                // ほぼ確実に先頭付近に来るため、候補数を適当な上限で打ち切っても
                // 正解を逃すリスクは小さい――ワーストケースの青天井を防ぐ
                // 安全弁として導入する(全問題で悪影響が無いことを確認済み)。
                //
                // 🌟 ユーザー提案(人間の解き方=角度追跡→長さ比→構図の反復。
                // その中で「今まさにhotな」対象から芋づる式に辿る)への対応:
                // 「有向角の加法性」のように、同じ型に対する(None,None)自己束縛
                // パターンをこの定理が2つ以上持つ場合(Ang12≡Ang45とAng23≡Ang56)、
                // それぞれ独立に候補集合を列挙して掛け合わせる(cap×cap通り)ため、
                // 固定cap=40のままだと最悪1,600通りの組み合わせを生み、simsonの
                // dfs_call消費量トップの直接原因になっていた(実測で確認済み)。
                // 熱で降順ソート済みの列に対し「本当にhotな候補は少数のはず」という
                // 前提で、こういう「二重自己束縛」定理に限ってcapを大きく絞り、
                // 全角度を無差別スキャンする代わりに直近heat_bonusが乗った少数の
                // 候補だけから辿らせる。単独の自己束縛(cap×1)しか持たない定理は
                // 従来通り40のままなので、他の定理への影響は無い。
                let self_bind_pattern_count = theorem.patterns.iter().filter(|p| {
                    matches!(p, Pattern::Fact(d) if d.fact_type == "Identical"
                        && d.args.len() == 2
                        && theorem.entities.get(&d.args[0]).copied() == expected_type)
                }).count();
                // 🌟 診断(円周角の定理の逆)で判明した追加ケース: 自己束縛
                // パターン自体は1つでも、そのIdentical(v1,v2)のv1・v2それぞれに
                // 同じtarget_typeのDefinedByパターンが独立にぶら下がっている
                // 場合(has_paired_defined_by_fanoutのドキュメント参照)、
                // 自己束縛のcapがそのまま下流(DefinedByペアリング→Connected
                // チェーン全体)の分岐係数になる。こちらも同じcap=10で絞る。
                let squared_fanout = self_bind_pattern_count >= 2
                    || has_paired_defined_by_fanout(theorem, v1, v2);
                let max_candidates = if squared_fanout { self.fanout_heat_cap } else { self.heat_cap };
                reps.truncate(max_candidates);
                // 🌟 dep_maskのドキュメント参照。expected_typeが分かっていれば
                // その型のプールを列挙したことになる。Noneの(稀な)フォール
                // バックは全エンティティを舐めるので安全側に倒して全型を
                // 依存対象にする。
                *dep_mask |= match expected_type {
                    Some(et) => entity_type_bit(et),
                    None => ALL_TYPES_MASK,
                };
                for rep in reps {
                    let mut next_bind = bind.clone();
                    next_bind.insert(v1.clone(), rep);
                    next_bind.insert(v2.clone(), rep);
                    self.dfs_match(theorem, patterns, active, next_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
                }
            }
        }
    }

    /// 🌟 "Connected" パターン: child/parent の束縛状況の4通り(両方/片方×2/どちらも未束縛)
    /// で分岐する。
    ///
    /// 🐛 FIX(EntityType::Direction撤廃で新たに生まれたバグ): 「方向」が独立した
    /// 型で無くなり、L∞に繋がっただけのPointになったため、「この直線に乗っている
    /// 点を探す」という(Line,Point)型の"Connected"パターンが、以前は型で
    /// 自動的に除外されていたその直線自身の方向(=L∞上の点)まで有効な候補として
    /// 拾ってしまうようになった。逆に「この直線の方向を求める」という
    /// (Line,Direction)パターンは、その直線上の"普通の"点(A,Bなど)まで候補に
    /// 混ざってしまう。どちらも実際にcyclic_quad等で観測された(候補が2〜3倍に
    /// 水増しされ、DFS予算を無駄食いして証明が届かなくなる/大幅に遅くなる)。
    /// これまで一度も読まれていなかったFactPatternDef::target_type/sub_type
    /// (「円周角の定理」のtarget_type=Some("Line")/sub_type=Some("Point")のような
    /// 記述が既にコメント的に付いていた慣習)を、ここで初めて実際の判定に使う:
    /// target_type=="Direction"ならparent側、sub_type=="Direction"ならchild側の
    /// Point候補を「L∞上にある点だけ」に絞り、それ以外(既定)は逆に「L∞上に
    /// ない点だけ」に絞る(型撤廃前と同じ、有限点だけを候補にする挙動)。
    pub(crate) fn match_connected_fact(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef,
        patterns: &[Pattern],
        active: u64,
        bind: &Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashMap<u64, (u8, [u64; 4])>,
        dep_mask: &mut u8,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
        use crate::mmp_core::EntityType;
        let child_var = &def.args[0];
        let parent_var = &def.args[1];
        let expected_c_type = theorem.entities.get(child_var).copied();
        let expected_p_type = theorem.entities.get(parent_var).copied();
        let wants_child_direction = def.sub_type.as_deref() == Some("Direction");
        let wants_parent_direction = def.target_type.as_deref() == Some("Direction");
        // 🌟 EntityType::Circle撤廃(mmp_core/mod.rs::EntityTypeのドキュメント
        // 参照)により、"Circle"マーカーもここに追加する: target_type/sub_type
        // =="Circle"ならこのPoint型変数(Conicの間違いではなく、こちらは
        // Connectedのchild/parentそれぞれの"宣言型"のことなので、ここでの
        // Circleは実際にはConic型変数に対して使う)が実際にI,Jを両方通る
        // (=本物の円である)ものだけを受理し、無い場合は逆にI,Jを通らない
        // (=一般の非円二次曲線)ものだけを受理する――Direction/Pointの
        // 場合と全く同じ「マーカー無し=旧来の狭い方の型」という既定にする。
        let wants_child_circle = def.sub_type.as_deref() == Some("Circle");
        let wants_parent_circle = def.target_type.as_deref() == Some("Circle");
        // 🌟 候補id(宣言型et)がこのパターン変数として受理できるかを判定する。
        // et が Point/Conic 以外なら型一致だけで従来通り。
        // et が Point なら、「L∞上にあるか」がwants_direction(このパターン
        // 変数が方向を欲しがっているか)と一致する場合だけ受理する。
        // et が Conic なら、「I,Jを両方通るか(=円か)」がwants_circleと
        // 一致する場合だけ受理する(旧EntityType::Circle/Conicの分離を
        // incidenceで再現する)。
        let accept_point = |egraph: &crate::mmp_core::EGraph, id: ClassId, et: EntityType, wants_direction: bool, wants_circle: bool| -> bool {
            if egraph.entities[id.0].entity_type != et { return false; }
            match et {
                EntityType::Point => egraph.is_connected(id, egraph.line_infinity) == wants_direction,
                EntityType::Conic => {
                    let is_circle = egraph.is_connected(id, egraph.circ_i) && egraph.is_connected(id, egraph.circ_j);
                    is_circle == wants_circle
                }
                _ => true,
            }
        };

        match (bind.get(child_var).copied(), bind.get(parent_var).copied()) {
            // 🐛 実装時に見落としかけたバグ: match_identical_factの(Some,Some)と
            // 違い、こちらはis_connected(=incidenceという、state_sigのハッシュ
            // (bindの値=代表元IDだけ)には含まれない"追加の状態")を見ている。
            // 同じ2つの代表元のまま、後からlink_logical_incidenceで新たに
            // 接続されると(それ自体はマージではないのでstate_sigは変わらない)、
            // この判定結果は変わり得る。link_logical_incidenceは接続する
            // 両実体の型を必ずnote_type_changedするので、その型を依存対象に
            // しておけば正しく無効化できる。
            (Some(c_id), Some(p_id)) => {
                let c_type = self.egraph.entities[self.egraph.get_rep(c_id).0].entity_type;
                let p_type = self.egraph.entities[self.egraph.get_rep(p_id).0].entity_type;
                *dep_mask |= entity_type_bit(c_type) | entity_type_bit(p_type);
                // 🌟 FIX
                if self.egraph.is_connected(c_id, p_id) {
                    self.dfs_match(theorem, patterns, active, bind.clone(), flip_states.clone(), failed_paths, dep_mask, on_match);
                }
            }
            (Some(c_id), None) => {
                // 🌟 dep_maskのドキュメント参照。このローカルスキャンはc_repに
                // 実際に繋がっている候補をexpected_p_typeで絞り込むので、
                // 新たにその型の実体がc_repへ接続されると結果が変わりうる
                // (link_logical_incidenceは接続する両実体の型を必ずnote_type_
                // changedするので、これで正しく捕捉できる)。型が不明なら
                // 安全側に倒して全型に依存するとみなす。
                // 🌟 最適化: 以前はここが「全エンティティを舐めてis_connectedで
                // 判定する」O(全エンティティ数)の総当たりになっていた
                // ((None, Some(p_id))側の分岐は既にp_rep自身のsubobjectsだけを
                // 見る局所探索に最適化済みで、この分岐だけ非対称に取り残されて
                // いた)。link_logical_incidenceは常に双方向にリンクを張るので
                // (is_connectedの実装もこれを前提に両側を見ている)、c_rep自身の
                // subobjects(局所的で少数)だけを見れば取りこぼしなく同じ結果が
                // 得られる。大きい問題(entities数が多い)ほど効果が大きい。
                let c_rep = self.egraph.get_rep(c_id);
                // 🌟 (None, Some(p_id))側の分岐と同じく、まず候補を(重複除去しつつ)
                // 集め切ってから、egraphへの不変借用を終わらせた後でdfs_matchを呼ぶ
                // (dfs_matchは&mut selfを要求するため)。
                let mut candidates = rustc_hash::FxHashSet::default();
                for comp in &self.egraph.entities[c_rep.0].components {
                    for &sub in &comp.subobjects {
                        let p_rep = self.egraph.get_rep(sub);
                        if p_rep == c_rep || !self.egraph.entities[p_rep.0].is_active() { continue; }
                        if let Some(et) = expected_p_type {
                            if !accept_point(&self.egraph, p_rep, et, wants_parent_direction, wants_parent_circle) { continue; }
                        }
                        candidates.insert(p_rep);
                    }
                }
                // 🌟 診断計測(円周角の定理)で判明: この「局所」スキャンは通常は
                // 少数(その実体自身に繋がっているものだけ)だが、多くの点が
                // 乗っている円のような「ハブ」実体では数十件になり得る。
                // (None,None)分岐に加えたのと同じ熱降順cap(=40)を、候補が
                // 実際に多い場合に限って適用する(heat_capped_connected_
                // candidatesのドキュメント参照)。
                *dep_mask |= match expected_p_type {
                    Some(et) => entity_type_bit(et),
                    None => ALL_TYPES_MASK,
                };
                for p_rep in self.heat_capped_connected_candidates(candidates) {
                    let mut next_bind = bind.clone();
                    next_bind.insert(parent_var.clone(), p_rep);
                    self.dfs_match(theorem, patterns, active, next_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
                }
            }
            // 🌟 dep_maskのドキュメント参照。(Some,None)と対称。
            (None, Some(p_id)) => {
                let p_rep = self.egraph.get_rep(p_id);
                let mut child_candidates = rustc_hash::FxHashSet::default();
                for comp in &self.egraph.entities[p_rep.0].components {
                    for &sub in &comp.subobjects {
                        // 🌟 FIX: 必ず rep を通す
                        let s_rep = self.egraph.get_rep(sub);
                        if self.egraph.entities[s_rep.0].is_active() { child_candidates.insert(s_rep); }
                    }
                }
                child_candidates.retain(|&c_rep| {
                    expected_c_type.map_or(true, |et| accept_point(&self.egraph, c_rep, et, wants_child_direction, wants_child_circle))
                });
                *dep_mask |= match expected_c_type {
                    Some(et) => entity_type_bit(et),
                    None => ALL_TYPES_MASK,
                };
                for c_rep in self.heat_capped_connected_candidates(child_candidates) {
                    let mut next_bind = bind.clone();
                    next_bind.insert(child_var.clone(), c_rep);
                    self.dfs_match(theorem, patterns, active, next_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
                }
            }
            // 🐛 FIX: 以前は子・親どちらも未束縛の場合に何もせず候補ゼロで
            // 諦めていた(Concyclicを専用Factから「N点が同じ円にConnected」
            // という形に置き換えたことで、この分岐が実際に必要になり発覚した)。
            // 親の型(例:Circle)で絞り込み、各親候補についてはその親自身が
            // 繋がっている子(局所的で少数)だけを見る形で列挙する。
            (None, None) => {
                // 🌟 RETE的な共有ジョインキャッシュ(ユーザー提案「案4」、
                // connected_join_cacheのドキュメント参照): この分岐は
                // bindの中身に依存せず(child_type, parent_type)という
                // 型の組み合わせだけで結果が決まるので、複数の定理・タスクが
                // 同じ型の組み合わせを問い合わせる場合に定理をまたいで
                // 共有できる。両方の型が分かっている(ほぼ全ての定理で
                // そうである)場合のみキャッシュを使い、型が不明な稀な
                // フォールバックでは従来通りのフルスキャンを行う。
                // 🌟 dep_maskのドキュメント参照。以下の全ての分岐(型が既知の
                // キャッシュ済みジョイン/型不明のフルスキャン)がここで
                // プールを列挙するので、まとめて記録する。
                *dep_mask |= match (expected_c_type, expected_p_type) {
                    (Some(ct), Some(pt)) => entity_type_bit(ct) | entity_type_bit(pt),
                    _ => ALL_TYPES_MASK,
                };
                if let (Some(ct), Some(pt)) = (expected_c_type, expected_p_type) {
                    let raw_pairs = self.connected_pairs_for_types(ct, pt);
                    // 🌟 connected_pairs_for_typesは(child_type, parent_type)の
                    // 組み合わせだけで結果を共有キャッシュするため、L∞上の点/
                    // I,Jを通る円かどうかを含めるか除外するかはここで結果を
                    // 受け取った後にふるいにかける(キャッシュ自体は複数の
                    // 定理・向きで安全に共有され続ける)。
                    let needs_filter = ct == EntityType::Point || pt == EntityType::Point
                        || ct == EntityType::Conic || pt == EntityType::Conic;
                    let pairs: Rc<Vec<(ClassId, ClassId)>> = if needs_filter {
                        Rc::new(raw_pairs.iter().copied().filter(|&(c, p)| {
                            (ct != EntityType::Point || self.egraph.is_connected(c, self.egraph.line_infinity) == wants_child_direction)
                                && (pt != EntityType::Point || self.egraph.is_connected(p, self.egraph.line_infinity) == wants_parent_direction)
                                && (ct != EntityType::Conic || (self.egraph.is_connected(c, self.egraph.circ_i) && self.egraph.is_connected(c, self.egraph.circ_j)) == wants_child_circle)
                                && (pt != EntityType::Conic || (self.egraph.is_connected(p, self.egraph.circ_i) && self.egraph.is_connected(p, self.egraph.circ_j)) == wants_parent_circle)
                        }).collect())
                    } else {
                        raw_pairs
                    };
                    // 🌟 ユーザー提案(「複比の透視射影不変性」を熱量駆動の考え方で
                    // 高速化したい)への対応: この分岐(Connected両方未束縛)は
                    // match_identical_fact/match_defined_by_factの類似分岐と違い、
                    // これまで熱による並べ替えもcapも一切無く、connected_pairs_
                    // for_typesが返す全ペアを無差別に試していた。「複比の透視射影
                    // 不変性(点→線束)」はO,A,B,C,D等9自由変数を持つが天然のシードが
                    // 無く、先頭のConnected(A,L)(点,直線どちらも未束縛)がまさに
                    // この分岐から始まるため、点や直線が多い問題ではこの1パターン
                    // だけで全(点,直線)接続ペアを総当たりすることになっていた。
                    // identical_self_bind_candidates(cap=40、熱降順)と同じ発想を
                    // ここにも適用する: 候補が多い場合のみ熱(base_importance+
                    // heat_bonus、両端の合計)で降順ソートしてから絞り、少数の
                    // 場合はこれまで通り全件試す(ソートのコストも省く)。
                    if pairs.len() <= self.heat_cap {
                        for &(c_rep, p_rep) in pairs.iter() {
                            let mut next_bind = bind.clone();
                            next_bind.insert(child_var.clone(), c_rep);
                            next_bind.insert(parent_var.clone(), p_rep);
                            self.dfs_match(theorem, patterns, active, next_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
                        }
                    } else {
                        let mut ordered: Vec<(ClassId, ClassId)> = (*pairs).clone();
                        let heat_of = |id: ClassId| -> f64 { self.egraph.entities[id.0].heat() };
                        ordered.sort_by(|&(c1, p1), &(c2, p2)| {
                            let h1 = heat_of(c1) + heat_of(p1);
                            let h2 = heat_of(c2) + heat_of(p2);
                            h2.partial_cmp(&h1).unwrap_or(std::cmp::Ordering::Equal)
                        });
                        ordered.truncate(self.heat_cap);
                        for (c_rep, p_rep) in ordered {
                            let mut next_bind = bind.clone();
                            next_bind.insert(child_var.clone(), c_rep);
                            next_bind.insert(parent_var.clone(), p_rep);
                            self.dfs_match(theorem, patterns, active, next_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
                        }
                    }
                } else {
                    let mut parent_candidates: Vec<ClassId> = Vec::new();
                    if let Some(et) = expected_p_type {
                        for p_rep in self.egraph.iter_reps_of_type(et) {
                            if self.egraph.entities[p_rep.0].is_active()
                                && accept_point(&self.egraph, p_rep, et, wants_parent_direction, wants_parent_circle) {
                                parent_candidates.push(p_rep);
                            }
                        }
                    } else {
                        for i in 0..self.egraph.entities.len() {
                            let p_id = ClassId(i);
                            let p_rep = self.egraph.get_rep(p_id);
                            if p_rep != p_id || !self.egraph.entities[i].is_active() { continue; }
                            parent_candidates.push(p_rep);
                        }
                    }

                    for p_rep in parent_candidates {
                        let child_candidates: Vec<ClassId> = match self.egraph.entities[p_rep.0].components.first() {
                            Some(comp) => comp.subobjects.iter()
                                .map(|&id| self.egraph.get_rep(id))
                                .filter(|&id| {
                                    if !self.egraph.entities[id.0].is_active() { return false; }
                                    match expected_c_type {
                                        Some(et) => accept_point(&self.egraph, id, et, wants_child_direction, wants_child_circle),
                                        None => true,
                                    }
                                })
                                .collect(),
                            None => vec![],
                        };
                        for c_rep in child_candidates {
                            let mut next_bind = bind.clone();
                            next_bind.insert(child_var.clone(), c_rep);
                            next_bind.insert(parent_var.clone(), p_rep);
                            self.dfs_match(theorem, patterns, active, next_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
                        }
                    }
                }
            }
        }
    }

    /// 🌟 "DefinedBy" パターン: result_var(定義された図形そのもの)の束縛状況から
    /// 候補ノードを絞り込み(defined_by_valid_nodes)、それぞれの候補が実際に
    /// target_type型の定義を持っているかを親変数との整合性込みで展開する
    /// (defined_by_collect_matches)。どちらも元は1つの巨大なmatchアームだった。
    pub(crate) fn match_defined_by_fact(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef,
        patterns: &[Pattern],
        active: u64,
        bind: &Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashMap<u64, (u8, [u64; 4])>,
        dep_mask: &mut u8,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
        let target_type = def.target_type.as_deref().unwrap_or("");
        let result_var = &def.args[def.args.len() - 1];
        let parent_vars = &def.args[0..def.args.len() - 1];
        let expected_r_type = theorem.entities.get(result_var).copied();

        let valid_nodes = self.defined_by_valid_nodes(target_type, result_var, parent_vars, expected_r_type, bind, dep_mask);
        let mut matches = self.defined_by_collect_matches(def, target_type, parent_vars, result_var, &valid_nodes, bind, &flip_states);

        if matches.is_empty() && target_type == "LineThroughPoints" && parent_vars.len() == 2 {
            if let (Some(&p1), Some(&p2)) = (bind.get(&parent_vars[0]), bind.get(&parent_vars[1])) {
                let r1 = self.egraph.get_rep(p1);
                let r2 = self.egraph.get_rep(p2);
                if r1 != r2 {
                    *self.construction_demands.entry((r1, r2)).or_insert(0.0) += 1.0;
                }
            }
        }
        // 🌟 NEW: 「2直線が既に存在するのに、その交点(Intersection)がまだ
        // 図形として存在しない」場合の需要記録。LineThroughPointsの需要
        // (「2点はあるのに、それを結ぶ直線がない」)と対称な仕組みで、
        // 「垂線の足」「補助円との交点」のような、問題文に最初から
        // 登録されていない補助点をDFS/需要駆動だけで発見できるようにする
        // (ユーザー要望: orthocenter/orthocenter_altでE,Fのような補助点を
        // 手で問題文に書かなくても発見できるようにしたい)。
        // resolve_point_demands(main.rsのリカバリーフェーズ)が実際に
        // Definition::Intersectionとして作図する。ここではLineThroughPoints
        // と同様、「需要はあるが今は作らない」――大量の無関係な直線ペアの
        // 交点まで無差別に作ってしまう爆発を避けるため、実際に定理が
        // 欲しがった(=パターンマッチで必要とされた)組み合わせだけを
        // 需要として記録し、実際の作図は頻度上位の少数に限定する。
        if matches.is_empty() && target_type == "Intersection" && parent_vars.len() == 2 {
            if let (Some(&l1), Some(&l2)) = (bind.get(&parent_vars[0]), bind.get(&parent_vars[1])) {
                let r1 = self.egraph.get_rep(l1);
                let r2 = self.egraph.get_rep(l2);
                if r1 != r2
                    && self.egraph.entities[r1.0].entity_type == EntityType::Line
                    && self.egraph.entities[r2.0].entity_type == EntityType::Line
                {
                    let key = if r1.0 < r2.0 { (r1, r2) } else { (r2, r1) };
                    *self.point_construction_demands.entry(key).or_insert(0.0) += 1.0;
                }
            }
        }

        // 🌟 ユーザー要望: 「複比の透視射影不変性のように関連するオブジェクトが
        // 非常に多い定理を、次数(MMP/動点法)をヒューリスティックに使って
        // 最適な順序でマッチングしたい」。
        //
        // 背景: DefinedByパターンの親変数が全て未束縛のフルスキャン
        // (defined_by_valid_nodes)では、既存の全エンティティ(例: 全ての直線)を
        // 候補として試すため、9自由変数の透視射影不変性のような定理では
        // 候補数がそのままdfs_matchの分岐数になる。dfs_capは全体で共有される
        // 有限予算なので、「正しい(=証明に必要な)候補」がこの分岐の中で早く
        // 試されるかどうかが、他の定理へ回る予算を食い潰すかどうかを左右する。
        // 次数は「その候補がどれだけ単純な構成か」の目安になり(実測: 中点や
        // 素直な2点直線は低次数、無関係な直線同士を繰り返し交差させた構成は
        // 高次数)、多くの名前付き定理は問題の基本的な図形(低次数)に対して
        // 使われることが多いため、次数の低い候補から先に試すことで「早く
        // 見つかるか、安く諦めるか」のどちらかになりやすい。
        //
        // 候補が少ない(=そもそも分岐が爆発しない)通常のケースでは次数測定
        // 自体のコストが無駄になるため、候補数がある程度多い場合のみ計算する
        // (DEGREE_HEURISTIC_THRESHOLD件以下ならこれまで通り熱だけで並べる)。
        // 次数はGeoEntity::degree_cacheでエンティティ単位にメモ化されるため、
        // 同じ問題内で繰り返しこの分岐に来ても実測コストは初回だけで済む。
        //
        // 🐛 実測に基づくFIX: 当初はTHRESHOLD=4, MAX_D=2で試したところ、
        // (a) simsonのような「候補が5〜10件程度」の中規模スキャンにまで
        // 次数測定が発動してしまい、既存12問題+orthocenter/orthocenter_altの
        // 合計実行時間が全体的に悪化した(simson: 3.9s→7.9〜8.1s、複数回
        // 再現)。(b) MAX_D=2(サンプル数k=2*2+2=6)は次数0/1/2を区別する
        // ぎりぎりの点数しかなく、random_mover_line(真の乱数)が引く方向に
        // よってランク判定が数値的にぶれやすく、同じ問題を実行するたびに
        // (プロセスごとに乱数シードが変わるため)測定される次数が変わり得て、
        // マッチ順序ひいては探索時間そのものが再現しない(orthocenterで
        // 実行毎に6秒/14秒/19秒とばらつくのを確認)という、まさにこのセッション
        // 冒頭でim::HashMapのRandomStateを潰して排除したのと同種の
        // 非決定性を、次数測定の乱数サンプリング経由で再び持ち込んでしまって
        // いた。THRESHOLD=10(=既存12問題+orthocenter/orthocenter_altでは
        // ほぼ発動しない)・MAX_D=4(=resolve_point_demandsで既に実績のある値、
        // k=10点でランク判定に十分な余裕がある)に調整することで、既存の
        // 全問題(cargo test 23/23 + 12問題+orthocenter/orthocenter_alt+
        // test_cross_ratioの計16問題)の実行時間・成否を完全に元通りに保ちつつ、
        // 複比の透視射影不変性(9自由変数、cross_ratio系のみで有効)を
        // 全問題のデフォルト定理集合へ強制的に加える実験では、この次数
        // ヒューリスティック無しだと壊れていたnine_point/orthic_incenter/
        // miquel_quadrilateralが(遅いながらも)全て正しく証明に到達できる
        // ことを確認した――「壊れる」を「遅いが正しい」まで改善できたが、
        // デフォルト採用に足るほどの速さにはまだ届いていない(今後の課題)。
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
        matches.sort_by(|(b1, _), (b2, _)| {
            let heat1 = self.calc_bind_heat(b1) - DEGREE_WEIGHT * degree_score(b1);
            let heat2 = self.calc_bind_heat(b2) - DEGREE_WEIGHT * degree_score(b2);
            // 熱(次数で調整済み)が高い(降順)ものを優先し、同値の場合はIDで決定論的にソート[cite: 5]
            heat2.partial_cmp(&heat1).unwrap_or(Ordering::Equal)
                .then_with(|| {
                    let mut k1: Vec<_> = b1.iter().collect(); k1.sort_by_key(|k| k.0);
                    let mut k2: Vec<_> = b2.iter().collect(); k2.sort_by_key(|k| k.0);
                    format!("{:?}", k1).cmp(&format!("{:?}", k2))
                })
        });
        matches.dedup_by_key(|(b, _)| {
            let mut keys: Vec<_> = b.iter().collect();
            keys.sort_by_key(|k| k.0);
            format!("{:?}", keys)
        });
        for (new_bind, new_flip) in matches {
            self.dfs_match(theorem, patterns, active, new_bind, new_flip, failed_paths, dep_mask, on_match);
        }
    }

    /// 🌟 "DefinedBy" の候補ノード列挙: result_var が既に束縛されていればそれ1つ、
    /// 親変数が全て束縛されていれば対応する定義をmemoから探す(無ければ
    /// AnglePair/DirectionOf/LengthSqに限り新規生成する)、どちらでもなければ
    /// 型が合う全エンティティをフルスキャンする。
    pub(crate) fn defined_by_valid_nodes(
        &mut self,
        target_type: &str,
        result_var: &String,
        parent_vars: &[String],
        expected_r_type: Option<EntityType>,
        bind: &Bind,
        dep_mask: &mut u8,
    ) -> Vec<ClassId> {
        let mut valid_nodes = Vec::new();

        // 🐛 実装時に見落としかけたバグ(match_connected_factの(Some,Some)と
        // 同種): この候補は「res_idという特定の1実体」を直接見るだけに
        // 見えるが、defined_by_collect_matches側がres_idのcomponents[0].
        // definitions(target_typeの定義を実際に持つか)を検証する。
        // GeoEntity::componentsは生成時にしか新規の定義を追加されず、
        // 唯一の例外はmerge_entitiesが吸収した側の定義を合流させる場合
        // ――つまりres_idが後から(同じEntityType同士としか併合されない)
        // 別の実体とマージされると、新しく目的の定義を獲得しうる。
        // res_idの型を依存対象にしておけば正しく無効化できる。
        if let Some(&res_id) = bind.get(result_var) {
            let res_rep = self.egraph.get_rep(res_id);
            *dep_mask |= entity_type_bit(self.egraph.entities[res_rep.0].entity_type);
            valid_nodes.push(res_rep);
        }
        // 🌟 FIX: *v ではなく v をそのまま渡す
        else if parent_vars.iter().all(|v| bind.contains_key(v)) {
            // 🌟 dep_maskのドキュメント参照。この枝は「(全親から決まる)この
            // 正確なDefinitionを持つ実体が既に存在するか」を見る。無ければ
            // 生成する(ホワイトリスト対象)か諦めるかのどちらだが、いずれの
            // 結果も「結果の型に新しい実体が現れたかどうか」に依存するため、
            // 結果の型を依存対象とする(型が不明な場合だけ安全側に倒す)。
            *dep_mask |= expected_r_type.map(entity_type_bit).unwrap_or(ALL_TYPES_MASK);
            let parent_ids: Vec<ClassId> = parent_vars.iter().map(|v| self.egraph.get_rep(bind[v])).collect();

            // 🌟 FIX: 全ての DefinedBy 対象型を網羅する
            let temp_def = match target_type {
                "AnglePair" => Definition::AnglePair(parent_ids[0], parent_ids[1]),
                "DirectionOf" => Definition::DirectionOf(parent_ids[0]),
                "LineThroughPoints" => Definition::new_line(parent_ids[0], parent_ids[1]),
                "Midpoint" => {
                    let (a,b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::Midpoint(a, b)
                },
                "Intersection" => {
                    let (a,b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::Intersection(a, b)
                },
                "LengthSq" => {
                    let (a,b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::LengthSq(a, b)
                },
                // 🌟 スパイラル相似の中点対応のために追加: LengthSqと全く同じく
                // 可換(normalize_definitionがClassId順にソートする)なので同じ
                // パターンで正規化する。以前はProductがDefinedByパターンの
                // 前提として参照されたことが無かった(共点二弦の相似は
                // constructionsでのみProductを作り、前提としては使わない)ため
                // この分岐が無くても困らなかったが、「比の等式を前提として
                // 要求する」定理(スパイラル相似)を書くにはProduct自体を
                // DefinedByで前提チェックできる必要がある。
                "Product" => {
                    let (a,b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::Product(a, b)
                },
                "PerpendicularLine" => Definition::PerpendicularLine(parent_ids[0], parent_ids[1]),
                "ParallelLine" => Definition::ParallelLine(parent_ids[0], parent_ids[1]),
                "TangentLine" => Definition::TangentLine(parent_ids[0], parent_ids[1]),
                "Circumcircle" => {
                    let mut arr = [parent_ids[0].0, parent_ids[1].0, parent_ids[2].0];
                    arr.sort_unstable();
                    Definition::Circumcircle(ClassId(arr[0]), ClassId(arr[1]), ClassId(arr[2]))
                }
                // 🌟 mmp_core/mod.rs::Definition::SecondIntersectionOfLineAndConic
                // のドキュメント参照。TangentLine/Circumcircleと同じく自動生成
                // ホワイトリスト(下のmatches!)には含めない――既知の点・直線・
                // 曲線の組み合わせから無差別に生成すると全件スキャン時に無駄な
                // 補助点が量産されかねないため、既存のエンティティ(MCTSが
                // 既に作ったもの、または定理のconstructionsが明示的に作った
                // もの)を探すだけに留める。
                "SecondIntersectionOfLineAndConic" if parent_ids.len() == 3 =>
                    Definition::SecondIntersectionOfLineAndConic(parent_ids[0], parent_ids[1], parent_ids[2]),
                "RadicalAxis" if parent_ids.len() == 2 => Definition::RadicalAxis(parent_ids[0], parent_ids[1]),
                "SecondIntersectionOfCircles" if parent_ids.len() == 3 =>
                    Definition::SecondIntersectionOfCircles(parent_ids[0], parent_ids[1], parent_ids[2]),
                // 🌟 CrossRatioのV4正規化はここで手書きで複製せず、mod.rs側の
                // normalize_definitionをそのまま呼ぶ(4元クライン群の畳み込みは
                // 単純なソートより複雑なので、ロジックを1箇所に保つ)。
                "CrossRatio" if parent_ids.len() == 4 => self.egraph.normalize_definition(
                    &Definition::CrossRatio(parent_ids[0], parent_ids[1], parent_ids[2], parent_ids[3])
                ),
                // 🌟 CrossRatioOfLines(線束の複比)もCrossRatioと同じV4正規化。
                "CrossRatioOfLines" if parent_ids.len() == 4 => self.egraph.normalize_definition(
                    &Definition::CrossRatioOfLines(parent_ids[0], parent_ids[1], parent_ids[2], parent_ids[3])
                ),
                _ => Definition::GivenPoint,
            };

            if let Some(&existing) = self.egraph.memo.get(&temp_def) {
                valid_nodes.push(self.egraph.get_rep(existing));
            } else if matches!(target_type, "AnglePair" | "DirectionOf" | "LengthSq" | "CrossRatio" | "CrossRatioOfLines" | "Product") {
                // 🌟 ユーザー提案:「複比の定理を使うときは複比自体を次数を用いて
                // 生成に制限をかけて」への対応。複比は4点(または4直線)から
                // 作られるため、無関係な組み合わせ(透視射影不変性のような
                // 多自由変数の定理が、DFSの中で偶然束縛してしまった無関係な
                // 4点/4直線)では次数が際限なく積み上がり得る。生成前に次数を
                // 測定し、異常に高い候補は(この特定の束縛での生成だけを諦める
                // ――failed_pathsによりこのDFS枝は自然に打ち切られる)ことで、
                // 無駄な複比エンティティの増殖と、それに続く
                // detect_cross_ratio_coincidencesの比較コストの増大を防ぐ。
                // 次数が測定不能(None)な場合は安全側に倒し、制限しない。
                // 🌟 CrossRatioOfLinesもmeasure_cross_ratio_affinityでそのまま
                // 測定できる(4引数をpointかlineかを区別せずevaluate_nodeに
                // 渡すだけなので、entity_typeによらず動く)。
                if matches!(target_type, "CrossRatio" | "CrossRatioOfLines") {
                    let cr_parents = match temp_def {
                        Definition::CrossRatio(a, b, c, d) | Definition::CrossRatioOfLines(a, b, c, d) => Some((a, b, c, d)),
                        _ => None,
                    };
                    if let Some((a, b, c, d)) = cr_parents {
                        const CR_DEGREE_CAP: usize = 8;
                        const CR_MAX_D: usize = 6;
                        if let Some((da, db, dc, dd, d_cr)) = self.egraph.measure_cross_ratio_affinity(a, b, c, d, CR_MAX_D) {
                            if d_cr > CR_DEGREE_CAP {
                                println!("  🚫 [複比の生成を制限] 次数{}(次数{}+{}+{}+{})が高すぎるため、{}の生成を見送りました", d_cr, da, db, dc, dd, target_type);
                                return valid_nodes;
                            }
                        }
                    }
                }

                let e_type = match target_type {
                    "AnglePair" => EntityType::Scalar,
                    "DirectionOf" => EntityType::Point,
                    _ => EntityType::Scalar
                };

                // 🌟 FIX: 親図形の名前を取得して結合し、誰と誰の角(方向)なのかを明示する
                let p_names: Vec<String> = parent_ids.iter()
                    .map(|&id| self.egraph.entities[id.0].name.clone())
                    .collect();

                let prefix = if target_type == "DirectionOf" { "Dir" } else { target_type };
                let name = format!("{}_{}_(Auto)", prefix, p_names.join("_"));

                let new_id = self.egraph.create_entity(name, temp_def.clone(), e_type);
                self.egraph.apply_trivial_relations(new_id, &temp_def);
                // 🌟 ユーザー提案:「複比同士の関係式からconjectureを発行して、
                // そこから定理適用の形を見つける」への対応。新しく作られた
                // 複比(点の複比・線束の複比のどちらでも)の値を既存の他の
                // 複比と数値的に比較し、一致するものがあれば予想(conjecture)
                // として記録する(detect_cross_ratio_coincidences側がCrossRatio/
                // CrossRatioOfLines両方を対象にスキャンするので、点の複比と
                // 線束の複比が一致する、というまさに定理A/Bが探している
                // 組み合わせも検出できる)。
                if matches!(target_type, "CrossRatio" | "CrossRatioOfLines") {
                    self.egraph.detect_cross_ratio_coincidences(new_id);
                }
                valid_nodes.push(new_id);
            }
        }
        // 🌟 高速化(ユーザー要望「TheoremDefの改善、Simson級を1秒未満に」への
        // 対応): 親変数の一部だけが束縛されている場合(例: AnglePair(D2,D3,Ang23)
        // でD2だけ既知)。以前はこのケースを見落として下のフルスキャン
        // (期待される結果の型の全代表元、または全エンティティ)にそのまま
        // フォールバックしていた。実測(--profileの診断カウンタで「有向角の
        // 加法性」の探索木を追跡)で、この見落としがsimson全体のdfs_call
        // 消費量トップ(平均19,000回超/試行、全体の約1/4)の直接の原因だと
        // 判明した。
        //
        // 束縛済みの親(anchor)のGeoEntity::usesは「anchorをDefinitionの
        // 親として参照する実体」の集合で、create_entity時に登録され
        // (mod.rs参照)、mergeのたびにcongruence.rs::merge_entitiesが
        // 生き残った側へ正しく引き継ぐ(=マージを経ても取りこぼさない)。
        // 安全性: ここで返すvalid_nodesはdefined_by_collect_matchesが
        // 実際のDefinition(target_type・全親の一致)で改めて検証する
        // 「候補プール」に過ぎないため、真に有効な候補を含む上位集合
        // (superset)でありさえすれば正しい――そしてtarget_typeの定義上、
        // 真に有効な結果ノードは必ずanchorを親の1つとして持つ(=create_entity
        // 時にanchorのusesへ登録済み)ため、この絞り込みは取りこぼしが起きない。
        else if let Some(&anchor_raw) = parent_vars.iter().find_map(|v| bind.get(v)) {
            // 🌟 dep_maskのドキュメント参照。anchorのusesは新しい結果型の
            // 実体がanchorを親として作られるたびに増える。
            *dep_mask |= expected_r_type.map(entity_type_bit).unwrap_or(ALL_TYPES_MASK);
            let anchor = self.egraph.get_rep(anchor_raw);
            let mut seen = rustc_hash::FxHashSet::default();
            for &used_id in &self.egraph.entities[anchor.0].uses {
                let u_rep = self.egraph.get_rep(used_id);
                if let Some(et) = expected_r_type {
                    if self.egraph.entities[u_rep.0].entity_type != et { continue; }
                }
                if seen.insert(u_rep) {
                    valid_nodes.push(u_rep);
                }
            }
        }
        // 🌟 FIX 3: どちらも未バインドの場合のみフルスキャン
        // 🌟 型インデックス化: 期待される結果の型が分かっていれば
        // type_index経由でその型の代表元だけを引く(理由は
        // match_identical_fact/match_connected_factの(None,None)分岐と同じ)。
        else if let Some(et) = expected_r_type {
            *dep_mask |= entity_type_bit(et);
            let cached = self.defined_by_type_scan_candidates(et);
            valid_nodes.extend(cached.iter().copied());
        } else {
            *dep_mask |= ALL_TYPES_MASK;
            for i in 0..self.egraph.entities.len() {
                let id = ClassId(i);
                if self.egraph.get_rep(id) == id {
                    valid_nodes.push(id);
                }
            }
        }

        valid_nodes
    }

    /// 🌟 "DefinedBy" の候補ノードそれぞれについて、実際にtarget_type型の定義を
    /// 持っているかを確認し、親変数との束縛の整合性(順不同図形は順列展開、
    /// 有向角のフリップ許可時は両方向)を取りながら (Bind, FlipStates) の
    /// 候補列を作る。読み取り専用(egraphを変更しない)。
    pub(crate) fn defined_by_collect_matches(
        &self,
        def: &FactPatternDef,
        target_type: &str,
        parent_vars: &[String],
        result_var: &String,
        valid_nodes: &[ClassId],
        bind: &Bind,
        flip_states: &FlipStates,
    ) -> Vec<(Bind, FlipStates)> {
        let mut matches = Vec::new();
        for &node_id in valid_nodes {
            for comp in &self.egraph.entities[node_id.0].components {
                for d in &comp.definitions {
                    if d.get_type_name() == target_type {
                        let d_parents = d.get_parents();
                        if d_parents.len() == parent_vars.len() {
                            let is_unordered = matches!(target_type, "Midpoint" | "LineThroughPoints" | "Intersection" | "LengthSq" | "Circumcircle");

                            let perms = if is_unordered {
                                if d_parents.len() == 2 {
                                    vec![(vec![d_parents[0], d_parents[1]], None), (vec![d_parents[1], d_parents[0]], None)]
                                } else if d_parents.len() == 3 {
                                    // 🌟 FIX: Python版にあった3変数の全順列展開を復活
                                    vec![
                                        (vec![d_parents[0], d_parents[1], d_parents[2]], None),
                                        (vec![d_parents[0], d_parents[2], d_parents[1]], None),
                                        (vec![d_parents[1], d_parents[0], d_parents[2]], None),
                                        (vec![d_parents[1], d_parents[2], d_parents[0]], None),
                                        (vec![d_parents[2], d_parents[0], d_parents[1]], None),
                                        (vec![d_parents[2], d_parents[1], d_parents[0]], None),
                                    ]
                                } else { vec![(d_parents.clone(), None)] }
                            } else if matches!(target_type, "CrossRatio" | "CrossRatioOfLines") && d_parents.len() == 4 {
                                // 🌟 複比の値を厳密に保つ4元クライン群V4の4通りだけを試す
                                // (mod.rs::normalize_definitionのCrossRatio/CrossRatioOfLines
                                // 正規化と対になる唯一の正しい順列集合――全24順列や、
                                // Circumcircle等と同じ「完全な順不同」ではないことに注意。
                                // 他の20順列は値そのものが変わるので、ここで一緒に試して
                                // しまうと異なる複比を誤って同一視することになる)。
                                let p = &d_parents;
                                vec![
                                    (vec![p[0], p[1], p[2], p[3]], None),
                                    (vec![p[1], p[0], p[3], p[2]], None),
                                    (vec![p[2], p[3], p[0], p[1]], None),
                                    (vec![p[3], p[2], p[1], p[0]], None),
                                ]
                            } else if target_type == "AnglePair" && def.allow_flip && d_parents.len() == 2 {
                                let mut valid_perms = Vec::new();
                                let state = def.flip_group.as_ref().and_then(|g| flip_states.get(g).copied());
                                if state != Some(true) { valid_perms.push((vec![d_parents[0], d_parents[1]], Some(false))); }
                                if state != Some(false) { valid_perms.push((vec![d_parents[1], d_parents[0]], Some(true))); }
                                valid_perms
                            } else {
                                vec![(d_parents.clone(), None)]
                            };

                            for (p_ids, flip_val) in perms {
                                let mut next_bind = bind.clone();
                                let mut conflict = false;
                                for (v_name, &p_id) in parent_vars.iter().zip(p_ids.iter()) {
                                    if let Some(&existing) = next_bind.get(v_name) {
                                        if self.egraph.get_rep(existing) != self.egraph.get_rep(p_id) { conflict = true; break; }
                                    }
                                    next_bind.insert(v_name.clone(), p_id);
                                }
                                if let Some(&existing) = next_bind.get(result_var) {
                                    if self.egraph.get_rep(existing) != node_id { conflict = true; }
                                }
                                next_bind.insert(result_var.clone(), node_id);

                                if !conflict {
                                    let mut next_flip = flip_states.clone();
                                    if let (Some(group), Some(val)) = (&def.flip_group, flip_val) {
                                        next_flip.insert(group.clone(), val);
                                    }
                                    // 🌟 個別の角度のフリップ状態も記憶させる
                                    if let Some(val) = flip_val {
                                        next_flip.insert(result_var.clone(), val);
                                    }
                                    matches.push((next_bind, next_flip));
                                }
                            }
                        }
                    }
                }
            }
        }
        matches
    }

    /// 🌟 "Identical"/"Connected"/"DefinedBy" 以外の汎用フォールバック:
    /// 既知の事実(self.facts)一覧から get_fact_bindings で束縛候補を集める。
    pub(crate) fn match_generic_fact(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef,
        patterns: &[Pattern],
        active: u64,
        bind: &Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashMap<u64, (u8, [u64; 4])>,
        dep_mask: &mut u8,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
        // 🌟 dep_maskのドキュメント参照(dfs_match)。ここはself.facts(任意の
        // fact_typeを持ち得る、動的に増減する事実ストア)を舐める稀な
        // フォールバック経路で、依存先を型単位で正確に特定できないため
        // 安全側に倒して全型に依存するとみなす。
        *dep_mask |= ALL_TYPES_MASK;
        let mut matches = Vec::new();
        for fact in &self.facts {
            matches.extend(self.get_fact_bindings(theorem, fact, &def.fact_type, &def.args, bind));
        }

        matches.sort_by(|b1, b2| {
            let heat1 = self.calc_bind_heat(b1);
            let heat2 = self.calc_bind_heat(b2);
            heat2.partial_cmp(&heat1).unwrap_or(Ordering::Equal)
                .then_with(|| {
                    let mut k1: Vec<_> = b1.iter().collect(); k1.sort_by_key(|k| k.0);
                    let mut k2: Vec<_> = b2.iter().collect(); k2.sort_by_key(|k| k.0);
                    format!("{:?}", k1).cmp(&format!("{:?}", k2))
                })
        });
        matches.dedup_by_key(|b| {
            let mut keys: Vec<_> = b.iter().collect();
            keys.sort_by_key(|k| k.0);
            format!("{:?}", keys)
        });

        for new_bind in matches {
            self.dfs_match(theorem, patterns, active, new_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
        }
    }

    pub(crate) fn get_fact_bindings(&self, theorem: &TheoremDef, fact: &Fact, fact_type: &str, args: &[String], current_bind: &Bind) -> Vec<Bind> {
        let (f_type, f_objs) = match fact {
            Fact::Identical(a, b) => ("Identical", vec![*a, *b]),
            Fact::Connected(c, p) => ("Connected", vec![*c, *p]),
            Fact::Parallel(a, b) => ("Parallel", vec![*a, *b]),
        };

        if f_type != fact_type || f_objs.len() != args.len() { return vec![]; }

        // 🌟 爆速化: 事実探索の段階でターゲット型と異なるエンティティを即座に破棄
        for (i, arg_name) in args.iter().enumerate() {
            if f_type == "Connected" {
                if let Some(expected_type) = theorem.entities.get(arg_name).copied() {
                    if self.egraph.entities[self.egraph.get_rep(f_objs[i]).0].entity_type != expected_type {
                        return vec![]; 
                    }
                }
            }
        }

        let is_unordered = f_type == "Identical";
        let perms = if is_unordered { get_permutations(&f_objs) } else { vec![f_objs.clone()] };

        let mut matches = Vec::new();
        for perm in perms {
            let mut next_bind = current_bind.clone();
            let mut conflict = false;
            for (i, arg_name) in args.iter().enumerate() {
                // 🌟 型チェック
                if let Some(expected_type) = theorem.entities.get(arg_name).copied() {
                    if self.egraph.entities[self.egraph.get_rep(perm[i]).0].entity_type != expected_type {
                        conflict = true; break;
                    }
                }
                if let Some(&existing) = next_bind.get(arg_name) {
                    if self.egraph.get_rep(existing) != self.egraph.get_rep(perm[i]) {
                        conflict = true; break;
                    }
                }
                next_bind.insert(arg_name.clone(), perm[i]);
            }
            if !conflict { matches.push(next_bind); }
        }
        matches
    }

    pub fn is_already_proven(&self, conclusions: &[FactTemplate], bind: &Bind, flips: &FlipStates) -> bool {
        for conc in conclusions {
            match conc.fact_type.as_str() {
                "Identical" => {
                    if let (Some(&id1), Some(&id2)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1])) {
                        let rep1 = self.egraph.get_rep(id1);
                        let rep2 = self.egraph.get_rep(id2);
                        // 🌟 FIX: 型に関わらず、代表元が同じなら証明済みとみなす
                        if rep1 != rep2 { return false; }

                        // 🌟 EntityType::Angle撤廃(mmp_core/mod.rs::EntityTypeの
                        // ドキュメント参照)により、以前ここにあった
                        // 「entity_type==Angleの場合だけフリップの向きを確認する」
                        // という型による絞り込みは撤廃した。FlipStates自体が
                        // match_defined_by(target_type=="AnglePair"の場合だけ)で
                        // しか populate されない、既に型非依存な文字列ベースの
                        // 仕組みだったため、非角度のIdentical比較では
                        // flips.get(...)が常にNone(→false)になり、
                        // f1==f2(false==false)は自動的に成り立つ――つまり
                        // 型チェックは元々冗長で、外しても角度以外の判定は
                        // 一切変わらない。
                        let f1 = flips.get(&conc.args[0]).copied().unwrap_or(false);
                        let f2 = flips.get(&conc.args[1]).copied().unwrap_or(false);
                        if f1 != f2 { return false; }
                    } else { return false; }
                },
                "Connected" => {
                    if let (Some(&child), Some(&parent)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1])) {
                        if !self.egraph.is_connected(child, parent) { return false; }
                    } else { return false; }
                },
                _ => return false,
            }
        }
        true
    }
}

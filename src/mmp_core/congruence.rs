//! 🌟 合同閉包エンジン: マージ本体(union-find側の実際の統合処理)と、
//! 「直線の一致条件」「2直線の交点の一意性」の局所伝播による自動マージ。
//! MCTSのような無方向な探索がこの局所伝播を誤って踏み抜かないよう、
//! マージを確定する前に eval.rs の numeric_plausibility_check で
//! 数値的な裏付けを取ってから merge_entities_justified を呼ぶ。

use super::{dedup_sorted_ids, BumpCause, ClassId, Definition, EntityType, EGraph, Justification, LogicalComponent, ProofEdge};
use rustc_hash::FxHashMap;

impl EGraph {
    // 🌟 マージロジック (merge_numerical)
    pub fn merge_entities(&mut self, id1: ClassId, id2: ClassId) -> bool {
        let root1 = self.get_rep(id1);
        let root2 = self.get_rep(id2);
        if root1 == root2 { return false; }

        self.parents[root2.0].set(root1.0);

        let root2_comps = std::mem::take(&mut self.entities[root2.0].components);
        let root2_heat = self.entities[root2.0].heat_bonus;
        let root2_imp = self.entities[root2.0].base_importance;
        let root2_mcts_depth = self.entities[root2.0].mcts_depth;
        let root2_name = std::mem::take(&mut self.entities[root2.0].name);
        let root2_uses = std::mem::take(&mut self.entities[root2.0].uses);

        // 🌟 FIX: root1のコンポーネントも一度takeし、mutable borrowの競合を回避する
        let mut root1_comps = std::mem::take(&mut self.entities[root1.0].components);

        // 🌟 definitions は挿入順を保つ Vec に溜め、重複は明示的に除く(subobjects と同じ)。評価器は
        // 「計算できる定義が見つかるまで順に試す」ので、並び順が変わると探索そのものが変わる。
        let mut merged_defs: Vec<Definition> = Vec::new();
        let push_def = |defs: &mut Vec<Definition>, d: Definition| {
            if !defs.contains(&d) { defs.push(d); }
        };
        // 🌟 subobjectsは重複除去だけでなく順序も決定的にしたいので、
        // Vecに集めてから dedup_sorted_ids で仕上げる(生のHashSetを
        // そのまま最終的な順序として使わない)。
        let mut merged_subs_raw: Vec<ClassId> = Vec::new();
        for comp in root1_comps.drain(..) {
            for def in comp.definitions {
                push_def(&mut merged_defs, self.normalize_definition(&def));
            }
            for sub in comp.subobjects {
                merged_subs_raw.push(self.get_rep(sub));
            }
        }
        for comp in root2_comps {
            for def in comp.definitions {
                push_def(&mut merged_defs, self.normalize_definition(&def));
            }
            for sub in comp.subobjects {
                merged_subs_raw.push(self.get_rep(sub));
            }
        }
        let merged_subs = dedup_sorted_ids(merged_subs_raw);
        // 🌟 mmp_core/mod.rs::angle_generation/plain_scalar_generationの
        // ドキュメント参照。merged_defsがこの直後にinto_iter().collect()で
        // 消費される前に、AnglePair定義を1つでも含むか(=統合後の実体が
        // 角度由来のScalarになるか)を控えておく。
        let merge_touches_angle = merged_defs.iter().any(|d| matches!(d, Definition::AnglePair(_, _)));

        // ここで再度 root1_entity の可変参照を取得
        let root1_entity = &mut self.entities[root1.0];
        root1_entity.heat_bonus = root1_entity.heat_bonus.max(root2_heat);
        root1_entity.base_importance = root1_entity.base_importance.max(root2_imp);
        // 🌟 MCTS連鎖の深さは、統合後の実体が「より浅い(=より根拠が確かな)方」の
        // 経緯を引き継ぐべきなので、maxではなくminを取る(片方が実は既知の浅い
        // 実体と同一だったなら、もう「無根拠に積み上げられた深い産物」とは
        // 見なさない)。
        root1_entity.mcts_depth = root1_entity.mcts_depth.min(root2_mcts_depth);

        root1_entity.components = vec![LogicalComponent {
            definitions: merged_defs,
            subobjects: merged_subs,
        }];

        if root2_name.len() < root1_entity.name.len() {
            root1_entity.name = root2_name;
        } else if root2_name.len() == root1_entity.name.len()
            && !root2_name.contains("(Ghost)")
            && root1_entity.name.contains("(Ghost)") {
            root1_entity.name = root2_name;
        }
        self.entities[root1.0].uses.extend(root2_uses);

        self.worklist.push(root1);
        // 🌟 実際に併合が起きた印。logic_core.rs::MatchTaskのfailed_paths
        // 持ち越し判定(merge_generationのドキュメント参照)が使う。
        self.merge_generation += 1;
        // 🌟 type_generationのドキュメント参照。merge_entities/
        // merge_entities_justifiedは常に同じEntityType同士しか統合しない
        // (点は点、円は円としか併合されない)不変条件があるため、root1
        // (生き残った側、今はroot2の内容も統合済み)のentity_typeを見るだけで
        // 「どちらの型で併合が起きたか」を一意に特定できる。
        self.note_type_changed(self.entities[root1.0].entity_type, BumpCause::Merge);
        // 🌟 mmp_core/mod.rs::angle_generation/plain_scalar_generationの
        // ドキュメント参照。上と同じ理由(常に同じEntityType同士しか
        // 併合されない)で、root1のentity_typeを見るだけで判定できる。
        if self.entities[root1.0].entity_type == EntityType::Scalar {
            self.note_scalar_kind_changed(merge_touches_angle);
        }
        true
    }

    /// 🌟 merge_entitiesに加えて、「なぜこの2つが同一なのか」をproof_edgesに
    /// 記録する版。証明復元(explain_identical/generate_proof)で使う。
    /// マージが実際に起きた場合のみ記録する(既に同じ代表元なら何もしない)。
    pub fn merge_entities_justified(&mut self, id1: ClassId, id2: ClassId, justification: Justification) -> bool {
        let root1 = self.get_rep(id1);
        let root2 = self.get_rep(id2);
        if root1 == root2 { return false; }
        let did_merge = self.merge_entities(id1, id2);
        if did_merge {
            // root2は吸収された側(union-find上、二度とrootに戻らない)なので、
            // このキーへの書き込みは実質的に一度きり。表示名はoriginal_name
            // (create_entity時に一度だけ設定され、以後マージで書き換わらない)
            // 経由で常に安定して引けるので、ここではraw ClassIdだけ持てば十分。
            self.proof_edges.entry(root2.0).or_insert(ProofEdge { from: root2, to: root1, justification });
        }
        did_merge
    }

    pub fn apply_congruence_closure(&mut self) -> bool {
        let mut changed_any = false;

        while let Some(changed_id) = self.worklist.pop() {
            let rep_id = self.get_rep(changed_id);
            let uses: Vec<ClassId> = self.entities[rep_id.0].uses.iter().copied().collect();

            let mut def_map: FxHashMap<Definition, ClassId> = FxHashMap::default();

            for used_id in uses {
                let u_rep = self.get_rep(used_id);
                if u_rep != used_id { continue; }

                // 🌟 FIX: 不変参照を維持し続けないように、definitions をクローンして借用を即座にドロップする
                let definitions = if let Some(comp) = self.entities[u_rep.0].components.first() {
                    comp.definitions.clone()
                } else {
                    continue;
                };

                for def in &definitions {
                    if matches!(def, Definition::FreePoint | Definition::GivenPoint) { continue; }
                    let norm_def = self.normalize_definition(def);

                    // 🌟 1. グローバルな memo (既存図形) との照合
                    if let Some(&global_existing) = self.memo.get(&norm_def) {
                        let g_rep = self.get_rep(global_existing);
                        if g_rep != u_rep {
                            let justification = Justification::Congruence { definition: self.format_definition(&norm_def) };
                            if self.merge_entities_justified(g_rep, u_rep, justification) {
                                changed_any = true;
                                break;
                            }
                        }
                    }
                    // 🌟 2. 現在のループ内で新しく生成された同一定義との照合
                    else if let Some(&existing_rep) = def_map.get(&norm_def) {
                        if existing_rep != u_rep {
                            let justification = Justification::Congruence { definition: self.format_definition(&norm_def) };
                            if self.merge_entities_justified(existing_rep, u_rep, justification) {
                                changed_any = true;
                                break;
                            }
                        }
                    } else {
                        def_map.insert(norm_def.clone(), u_rep);
                        // 🌟 既存の実体が正規化後の定義で初めて memo に載る場合も、insert_memo を通して型の世代を上げる。
                        self.insert_memo(norm_def, u_rep); // 🌟 グローバルにも登録
                    }
                }
            }

            // 🌟 [構造的マージ] 接続関係から従う合同閉包を、全図形の総当たりではなく、今回変化した図形の
            // 隣接関係(subobjects)だけを辿って局所的に伝播する:
            // - 直線が変化した: 「2点を共有する直線は同一」を、この直線上の点が他に乗っている直線だけで判定する。
            // - 点が変化した: 「2直線の交点は一意」を memo の O(1) 参照で判定する。
            // ここでのマージも worklist に積まれるので、連鎖的な合流はこの while ループがそのまま続けて処理する。
            let rep_id = self.get_rep(changed_id); // 上のuses処理でrepが動いた可能性があるので取り直す
            match self.entities[rep_id.0].entity_type {
                EntityType::Line => {
                    if self.propagate_line_uniqueness(rep_id) { changed_any = true; }
                }
                // 🌟 二次曲線(円を含む)も直線と全く同じ理由(点/方向が変化しても、
                // それを含む二次曲線側の「一致条件」は自動的には再トリガーされない)
                // でここに追加。
                EntityType::Conic => {
                    if self.propagate_conic_uniqueness(rep_id) { changed_any = true; }
                }
                // 🌟 スカラー(複比)の一致から、点の一致を導く。propagate_cross_ratio_uniqueness 参照。
                EntityType::Scalar => {
                    if self.propagate_cross_ratio_uniqueness(rep_id) { changed_any = true; }
                }
                EntityType::Point => {
                    if self.propagate_point_uniqueness(rep_id) { changed_any = true; }

                    // 🐛 点が他の点とマージされても、それを含む直線の一致判定は自動では走らない
                    // (propagate_line_uniqueness は直線自身の rep が変わったときしか呼ばれない)。1点を共有する2直線の
                    // 方向が後から一致した、というような合流を見逃さないよう、この点を含む直線についても再実行する。
                    let lines: Vec<ClassId> = self.entities[rep_id.0].components.first()
                        .map(|c| dedup_sorted_ids(c.subobjects.iter()
                            .map(|&s| self.get_rep(s))
                            .filter(|&s| self.entities[s.0].entity_type == EntityType::Line)))
                        .unwrap_or_default();
                    for l in lines {
                        if self.propagate_line_uniqueness(l) { changed_any = true; }
                    }

                    // 🌟 同じ理由で、この点が乗っている二次曲線の一致判定も再実行する。円周点 I,J はあらゆる円に
                    // 乗っているので、I,J 自身が変化すると全ての円が対象になるが、I,J は定数で他の実体と統合されない。
                    let conics: Vec<ClassId> = self.entities[rep_id.0].components.first()
                        .map(|c| dedup_sorted_ids(c.subobjects.iter()
                            .map(|&s| self.get_rep(s))
                            .filter(|&s| self.entities[s.0].entity_type == EntityType::Conic)))
                        .unwrap_or_default();
                    for c in conics {
                        if self.propagate_conic_uniqueness(c) { changed_any = true; }
                    }
                }
            }
        }

        changed_any
    }

    /// 🌟 「直線の一致条件」の局所伝播版。line 上の点(少数)だけを見て、それらの点が他に乗っている直線との
    /// 共有点数を調べる。全直線を舐めない。
    /// 方向は無限遠直線上のただの Point なので、「1点を共有し方向も同じ」は「無限遠点を含めて2点を共有」
    /// という同じ規則に含まれる(平行なだけの直線は無限遠点1つしか共有しない)。
    fn propagate_line_uniqueness(&mut self, line: ClassId) -> bool {
        let mut line = self.get_rep(line);

        // 🐛 共有点を数える前に、この直線上の点どうしの「交点の一意性」を局所的な不動点まで確定させる。
        // まだ別IDのままの同一点を「別々の2つの共有点」と数え、無関係な直線をマージしてしまうため。
        loop {
            let points: Vec<ClassId> = match self.entities[line.0].components.first() {
                Some(c) => c.subobjects.iter()
                    .map(|&id| self.get_rep(id))
                    .filter(|&id| self.entities[id.0].entity_type == EntityType::Point)
                    .collect(),
                None => return false,
            };
            let mut any = false;
            for p in points {
                if self.propagate_point_uniqueness(p) { any = true; }
            }
            line = self.get_rep(line);
            if !any { break; }
        }

        // 🐛 FIX: subobjects は merge 前の生のIDをそのまま持ち続けるため、
        // 同じ代表元を指す複数のエントリが残ることがある(例えばLineとその
        // Demand版が別々に同じ点へリンクされ、後で合流した場合)。
        // rep化した後に必ず重複を除いてから使う(dedup_sorted_idsで順序も決定的にする)。
        let points: Vec<ClassId> = match self.entities[line.0].components.first() {
            Some(c) => dedup_sorted_ids(c.subobjects.iter()
                .map(|&id| self.get_rep(id))
                .filter(|&id| self.entities[id.0].entity_type == EntityType::Point)),
            None => return false,
        };

        // line上の各点(方向を含む)について、他に乗っている直線ごとに共有数を数える。
        // 🐛 FIX: 1点につき同じ他直線への加算は高々1にする(重複subobjectsで
        // 1点しか共有していないのに2点共有と誤カウントするのを防ぐ)。
        let mut shared_points: FxHashMap<ClassId, Vec<ClassId>> = FxHashMap::default();
        for &p in &points {
            if let Some(comp) = self.entities[p.0].components.first() {
                let other_lines_of_p: Vec<ClassId> = dedup_sorted_ids(comp.subobjects.iter()
                    .map(|&id| self.get_rep(id))
                    .filter(|&id| id != line && self.entities[id.0].entity_type == EntityType::Line));
                for other in other_lines_of_p {
                    shared_points.entry(other).or_default().push(p);
                }
            }
        }

        for (other_line, shared) in shared_points {
            let line = self.get_rep(line); // 途中のマージでrepが変わっている可能性
            let other_line = self.get_rep(other_line);
            if line == other_line { continue; }

            if shared.len() >= 2 {
                // 🐛 shared は重複除去済みでも、まだマージされていない2つの代表元が同じ点を指していることがある。
                // 1点の共有を2点と数えないよう、数値的に等しい代表元を1つにまとめてから閾値を判定する
                // (propagate_conic_uniqueness と同じ)。
                let mut distinct_shared: Vec<ClassId> = Vec::new();
                for &p in &shared {
                    let is_dup = distinct_shared.iter()
                        .any(|&q| self.numeric_plausibility_check(p, q, 2) == Some(true));
                    if !is_dup { distinct_shared.push(p); }
                }
                if distinct_shared.len() < 2 { continue; }

                // 🌟 マージを確定する前に、ランダムな座標で本当に2直線が等しいかを検算する。明確に矛盾する
                // (Some(false))ならマージしない。判定不能(None)なら進める。
                if self.numeric_plausibility_check(line, other_line, 2) == Some(false) {
                    let name1 = self.entities[line.0].name.clone();
                    let name2 = self.entities[other_line.0].name.clone();
                    println!("  🚫 [健全性チェック] {} と {} は共有点={}(重複除去後)だが数値的に別の直線のため結合を却下",
                        name1, name2, distinct_shared.len());
                    continue;
                }
                let name1 = self.entities[line.0].name.clone();
                let name2 = self.entities[other_line.0].name.clone();
                let justification = Justification::LineUniqueness { shared_points: distinct_shared.clone() };
                if self.merge_entities_justified(line, other_line, justification) {
                    println!("  ⚙️ [E-Graph自動マージ] 幾何条件(共有点={}、重複除去後)により直線を結合: {} ≡ {}",
                        distinct_shared.len(), name1, name2);
                    return true;
                }
            }
        }
        false
    }

    /// 🌟 「二次曲線の一致条件」の局所伝播版。propagate_line_uniqueness と同じ発想で、二次曲線は一般の位置の
    /// 5点で決まるのでしきい値は5。円は構造的に I,J にも接続されているので、実点3つを共有すれば共有点は
    /// 3+I+J=5 になり、「円は3点で決まる」が特別扱いなしに従う(3点しか共有しない一般の二次曲線は
    /// マージされない)。同一の円が別実体のまま残ると、実体数が膨らむうえ、片方にだけ乗った情報が
    /// もう片方に伝わらず証明が途切れる。
    fn propagate_conic_uniqueness(&mut self, conic: ClassId) -> bool {
        let mut conic = self.get_rep(conic);

        // 🐛 propagate_line_uniqueness と同じ理由で、共有点を数える前に点どうしの交点の一意性を確定させる
        // (しないと共有点数を過小評価し、マージすべき二次曲線を見逃す)。
        loop {
            let points: Vec<ClassId> = match self.entities[conic.0].components.first() {
                Some(c) => c.subobjects.iter()
                    .map(|&id| self.get_rep(id))
                    .filter(|&id| self.entities[id.0].entity_type == EntityType::Point)
                    .collect(),
                None => return false,
            };
            let mut any = false;
            for p in points {
                if self.propagate_point_uniqueness(p) { any = true; }
            }
            conic = self.get_rep(conic);
            if !any { break; }
        }

        let points: Vec<ClassId> = match self.entities[conic.0].components.first() {
            Some(c) => dedup_sorted_ids(c.subobjects.iter()
                .map(|&id| self.get_rep(id))
                .filter(|&id| self.entities[id.0].entity_type == EntityType::Point)),
            None => return false,
        };

        // conic上の各点について、他に乗っている二次曲線ごとに共有数を数える。
        let mut shared_points: FxHashMap<ClassId, Vec<ClassId>> = FxHashMap::default();
        for &p in &points {
            if let Some(comp) = self.entities[p.0].components.first() {
                let other_conics_of_p: Vec<ClassId> = dedup_sorted_ids(comp.subobjects.iter()
                    .map(|&id| self.get_rep(id))
                    .filter(|&id| id != conic && self.entities[id.0].entity_type == EntityType::Conic));
                for other in other_conics_of_p {
                    shared_points.entry(other).or_default().push(p);
                }
            }
        }

        for (other_conic, shared) in shared_points {
            let conic = self.get_rep(conic); // 途中のマージでrepが変わっている可能性
            let other_conic = self.get_rep(other_conic);
            if conic == other_conic { continue; }

            // 🌟 直線は2点、二次曲線は(一般の位置にある)5点で一意に決まる。
            if shared.len() >= 5 {
                // 🐛 まだマージされていない2つの代表元が同じ点(例: 別々に作った同じ垂心)を指していると、真の共有点が
                // 5点未満でも5点以上と数えてしまう。数値的に等しい代表元を1つにまとめてから、改めて5点以上かを判定する
                // (shared は5前後と少ないので O(n²) の数値チェックは無視できる)。
                let mut distinct_shared: Vec<ClassId> = Vec::new();
                for &p in &shared {
                    let is_dup = distinct_shared.iter()
                        .any(|&q| self.numeric_plausibility_check(p, q, 2) == Some(true));
                    if !is_dup { distinct_shared.push(p); }
                }
                if distinct_shared.len() < 5 { continue; }

                // 🌟 却下済みペアキャッシュ(EGraph::rejected_conic_pairsの
                // ドキュメント参照): 前回このペアを却下した時点からマージが
                // 1件も起きていなければ、結果は変わりようがないので数値
                // チェックを省略する。
                let cache_key = if conic.0 < other_conic.0 { (conic.0, other_conic.0) } else { (other_conic.0, conic.0) };
                if self.rejected_conic_pairs.get(&cache_key) == Some(&self.merge_generation) {
                    continue;
                }
                // 🌟 健全性の穴の修正: propagate_line_uniquenessと同様、マージを
                // 確定する前に数値的な裏付けを取る。
                if self.numeric_plausibility_check(conic, other_conic, 2) == Some(false) {
                    self.rejected_conic_pairs.insert(cache_key, self.merge_generation);
                    let name1 = self.entities[conic.0].name.clone();
                    let name2 = self.entities[other_conic.0].name.clone();
                    println!("  🚫 [健全性チェック] {} と {} は共有点={}(重複除去後)だが数値的に別の二次曲線のため結合を却下",
                        name1, name2, distinct_shared.len());
                    continue;
                }
                let name1 = self.entities[conic.0].name.clone();
                let name2 = self.entities[other_conic.0].name.clone();
                let justification = Justification::ConicUniqueness { shared_points: distinct_shared.clone() };
                if self.merge_entities_justified(conic, other_conic, justification) {
                    println!("  ⚙️ [E-Graph自動マージ] 幾何条件(共有点={}、重複除去後)により二次曲線を結合: {} ≡ {}",
                        distinct_shared.len(), name1, name2);
                    return true;
                }
            }
        }
        false
    }

    /// 🌟 「複比の透視射影不変性の逆」。共線な4点の複比 (A,B;C,D) は A,B,C を固定すると D について単射なので、
    ///   (A,B;C,D) = (A,B;C,E) かつ A,B,C が相異なり、5点が同じ直線上 ⟹ D = E
    /// 探索が見つけたいのは共点・共線という接続の主張なので、証明に効くのはこの「スカラーの等式から接続を
    /// 導く」向き(メネラウス・チェバの逆の射影版)。
    /// 定理(TheoremDef)ではなく局所伝播として書くのは、CrossRatio が V4 で正準化されるため「3つ同じで1つ違う」
    /// スロットが ClassId の大小で変わり、パターンでは4通りに分裂するから。ここなら軌道を自分で回して照合できる。
    fn propagate_cross_ratio_uniqueness(&mut self, scalar: ClassId) -> bool {
        let scalar = self.get_rep(scalar);
        // 同じ同値類に入っている = 値が等しい複比たち。
        let defs: Vec<[ClassId; 4]> = match self.entities[scalar.0].components.first() {
            Some(c) => c.definitions.iter().filter_map(|d| match d {
                Definition::CrossRatio(a, b, c2, d2) =>
                    Some([self.get_rep(*a), self.get_rep(*b), self.get_rep(*c2), self.get_rep(*d2)]),
                _ => None,
            }).collect(),
            None => return false,
        };
        if defs.len() < 2 { return false; }

        for i in 0..defs.len() {
            for j in (i + 1)..defs.len() {
                let t1 = defs[i];
                let t2 = defs[j];
                // t2 のV4軌道を回して、t1 と3箇所一致するものを探す。
                let orbit = [
                    [t2[0], t2[1], t2[2], t2[3]],
                    [t2[1], t2[0], t2[3], t2[2]],
                    [t2[2], t2[3], t2[0], t2[1]],
                    [t2[3], t2[2], t2[1], t2[0]],
                ];
                for u in orbit {
                    let diff: Vec<usize> = (0..4).filter(|&k| t1[k] != u[k]).collect();
                    if diff.len() != 1 { continue; }
                    let k = diff[0];
                    let (p, q) = (t1[k], u[k]);
                    if p == q { continue; }
                    // 一意性が効くのは、固定された3点が相異なるときだけ。
                    let fixed: Vec<ClassId> = (0..4).filter(|&x| x != k).map(|x| t1[x]).collect();
                    if fixed[0] == fixed[1] || fixed[1] == fixed[2] || fixed[0] == fixed[2] { continue; }
                    // 複比が意味を持つのは4点が共線のときだけ。t1側の共通直線を
                    // 取り、qもその上にあることを確かめる(そうでなければ
                    // 「同じ直線上の射影座標」という議論が成り立たない)。
                    let line = match self.find_common_line(&t1) { Some(l) => l, None => continue };
                    if !self.is_connected(q, line) { continue; }
                    if self.numeric_plausibility_check(p, q, 2) == Some(false) {
                        let (n1, n2) = (self.entities[p.0].name.clone(), self.entities[q.0].name.clone());
                        println!("  🚫 [健全性チェック] {} と {} は複比の一意性から一致するはずだが数値的に別の点のため結合を却下", n1, n2);
                        continue;
                    }
                    let (n1, n2) = (self.entities[p.0].name.clone(), self.entities[q.0].name.clone());
                    let justification = Justification::Theorem {
                        name: "複比の透視射影不変性の逆(共線4点の4点目の一意性)".to_string(),
                        premises: fixed.iter().map(|&f| ("Connected".to_string(), vec![f, line]))
                            .chain(std::iter::once(("Connected".to_string(), vec![q, line])))
                            .collect(),
                    };
                    if self.merge_entities_justified(p, q, justification) {
                        println!("  ⚙️ [E-Graph自動マージ] 複比の一意性(透視射影不変性の逆)により点を結合: {} ≡ {}", n1, n2);
                        return true;
                    }
                }
            }
        }
        false
    }

    /// 🌟 「2直線の交点の一意性」の局所伝播版。point(方向を含む)が乗っている直線のペアについて、
    /// その交点が memo に登録済みかを O(1) で引くだけ。全点を舐めない。
    /// 方向は Intersection(line, 無限遠直線) ではなく DirectionOf(line) で登録されているので、
    /// ペアの片方が無限遠直線のときは DirectionOf での読み替えも試す。
    fn propagate_point_uniqueness(&mut self, point: ClassId) -> bool {
        let point = self.get_rep(point);
        // 🐛 FIX: subobjects の重複エントリを rep 化した後に除いてから使う(理由は
        // propagate_line_uniqueness と同様。dedup_sorted_idsで順序も決定的にする)。
        let lines: Vec<ClassId> = match self.entities[point.0].components.first() {
            Some(c) => dedup_sorted_ids(c.subobjects.iter()
                .map(|&id| self.get_rep(id))
                .filter(|&id| self.entities[id.0].entity_type == EntityType::Line)),
            None => return false,
        };

        let mut candidates: Vec<(ClassId, ClassId, ClassId)> = Vec::new();
        for i in 0..lines.len() {
            for j in (i + 1)..lines.len() {
                let (l1, l2) = (lines[i], lines[j]);
                let inter_def = self.normalize_definition(&Definition::Intersection(l1, l2));
                if let Some(&existing) = self.memo.get(&inter_def) { candidates.push((existing, l1, l2)); }

                if l1 == self.line_infinity
                    && let Some(&existing) = self.memo.get(&Definition::DirectionOf(l2)) { candidates.push((existing, l1, l2)); }
                if l2 == self.line_infinity
                    && let Some(&existing) = self.memo.get(&Definition::DirectionOf(l1)) { candidates.push((existing, l1, l2)); }
            }
        }

        for (existing, via_l1, via_l2) in candidates {
            let existing_rep = self.get_rep(existing);
            let point_rep = self.get_rep(point);
            if existing_rep != point_rep {
                // 🌟 マージを確定する前に数値的な裏付けを取る(propagate_line_uniqueness と同じ)。平行な2直線の交点は
                // 無限遠点になり、それが方向と同一視されるのは正しい(方向も Point なので型の不一致は起きない)。
                if self.numeric_plausibility_check(existing_rep, point_rep, 2) == Some(false) {
                    let name1 = self.entities[existing_rep.0].name.clone();
                    let name2 = self.entities[point_rep.0].name.clone();
                    println!("  🚫 [健全性チェック] {} と {} は2直線の交点として一致するはずだが数値的に別の点のため結合を却下",
                        name1, name2);
                    continue;
                }
                let name1 = self.entities[existing_rep.0].name.clone();
                let name2 = self.entities[point_rep.0].name.clone();
                let justification = Justification::PointUniqueness { via_lines: (via_l1, via_l2) };
                if self.merge_entities_justified(existing_rep, point_rep, justification) {
                    println!("  ⚙️ [E-Graph自動マージ] 2直線の交点の一意性により点を結合: {} ≡ {}", name1, name2);
                    return true;
                }
            }
        }
        false
    }
}

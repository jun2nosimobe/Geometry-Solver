//! 🌟 合同閉包エンジン: マージ本体(union-find側の実際の統合処理)と、
//! 「直線の一致条件」「2直線の交点の一意性」の局所伝播による自動マージ。
//! MCTSのような無方向な探索がこの局所伝播を誤って踏み抜かないよう、
//! マージを確定する前に eval.rs の numeric_plausibility_check で
//! 数値的な裏付けを取ってから merge_entities_justified を呼ぶ。

use super::{dedup_sorted_ids, ClassId, Definition, EntityType, EGraph, Justification, LogicalComponent, ProofEdge};
use rustc_hash::FxHashMap;

impl EGraph {
    // 🌟 マージロジック (merge_numerical)
    pub fn merge_entities(&mut self, id1: ClassId, id2: ClassId) -> bool {
        let root1 = self.get_rep(id1);
        let root2 = self.get_rep(id2);
        if root1 == root2 { return false; }

        self.parents[root2.0].set(root1.0);

        let mut root2_comps = std::mem::take(&mut self.entities[root2.0].components);
        let root2_heat = self.entities[root2.0].heat_bonus;
        let root2_imp = self.entities[root2.0].base_importance;
        let root2_mcts_depth = self.entities[root2.0].mcts_depth;
        let root2_name = std::mem::take(&mut self.entities[root2.0].name);
        let mut root2_uses = std::mem::take(&mut self.entities[root2.0].uses);

        // 🌟 FIX: root1のコンポーネントも一度takeし、mutable borrowの競合を回避する
        let mut root1_comps = std::mem::take(&mut self.entities[root1.0].components);

        let mut merged_defs = std::collections::HashSet::new();
        // 🌟 subobjectsは重複除去だけでなく順序も決定的にしたいので、
        // Vecに集めてから dedup_sorted_ids で仕上げる(生のHashSetを
        // そのまま最終的な順序として使わない)。
        let mut merged_subs_raw: Vec<ClassId> = Vec::new();

        for comp in root1_comps.drain(..) {
            for def in comp.definitions {
                merged_defs.insert(self.normalize_definition(&def));
            }
            for sub in comp.subobjects {
                merged_subs_raw.push(self.get_rep(sub));
            }
        }
        for comp in root2_comps {
            for def in comp.definitions {
                merged_defs.insert(self.normalize_definition(&def));
            }
            for sub in comp.subobjects {
                merged_subs_raw.push(self.get_rep(sub));
            }
        }
        let merged_subs = dedup_sorted_ids(merged_subs_raw);

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
            definitions: merged_defs.into_iter().collect(),
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
                        self.memo.insert(norm_def, u_rep); // 🌟 グローバルにも登録
                    }
                }
            }

            // 🌟 [構造的マージ] 点・直線の接続関係(incidence)から従う合同閉包を、
            // 全図形×全図形の総当たりではなく、"今回変化した図形(rep_id)の
            // 局所的な隣接関係(subobjects)だけを辿る" DFS的な伝播で行う。
            //
            // - 直線が変化した場合:「直線の一致条件」(2直線が2点を共有、
            //   または1点を共有しつつ方向も等しいなら同一直線)を、
            //   この直線上の点それぞれが他にどの直線に乗っているかだけを見て判定する。
            // - 点が変化した場合:「2直線の交点の一意性」(この点が乗っている
            //   2直線の交点として既に登録済みの点があれば同一点)を、
            //   memoへのO(1)参照だけで判定する(全点を舐めない)。
            //
            // 以前はここを「全直線ペア×全点」のO(直線数^2 × 点数)の総当たりで
            // 実行しており(apply_congruence_closureが呼ばれるたびに無条件で
            // 走っていた)、かつ「点の一致」版は専用のBlackboard定理として
            // dfs_match経由でしか判定できず、どちらも無駄が大きかった。
            // ここでのマージも merge_entities 経由で worklist に積まれるので、
            // 連鎖的な合流はこの while ループが自然に続けて処理する。
            let rep_id = self.get_rep(changed_id); // 上のuses処理でrepが動いた可能性があるので取り直す
            match self.entities[rep_id.0].entity_type {
                EntityType::Line => {
                    if self.propagate_line_uniqueness(rep_id) { changed_any = true; }
                }
                // 🌟 円も直線と全く同じ理由(点/方向が変化しても、それを含む円側の
                // 「円の一致条件」は自動的には再トリガーされない)でここに追加。
                EntityType::Circle => {
                    if self.propagate_circle_uniqueness(rep_id) { changed_any = true; }
                }
                // 🌟 Directionは「無限遠直線上の点」として扱うので、通常の点と同じく
                // propagate_point_uniquenessの対象にする。
                EntityType::Point | EntityType::Direction => {
                    if self.propagate_point_uniqueness(rep_id) { changed_any = true; }

                    // 🐛 FIX: 点/方向が変化(他の点/方向とマージ)しても、それを
                    // 含む直線側の「直線の一致条件」判定は自動的には再トリガー
                    // されない(propagate_line_uniquenessは直線自身のrepが
                    // 変化したときしか呼ばれないため)。このため「2直線が
                    // 既に1点を共有していて、後から同位角判定などで方向まで
                    // 一致した」というケースで、方向の一致が確立された直後に
                    // 直線同士の合流だけが見逃されてStallする実例が
                    // orthocenter_altで見つかった(同位角による平行判定で
                    // Dir_Alt_A≡Dir_Line_AHが確立された直後、Alt_A≡Line_AHへの
                    // 合流だけが起きなかった)。この点/方向を含む直線それぞれ
                    // についてもpropagate_line_uniquenessを再実行することで
                    // これを修正する。
                    let lines: Vec<ClassId> = self.entities[rep_id.0].components.first()
                        .map(|c| dedup_sorted_ids(c.subobjects.iter()
                            .map(|&s| self.get_rep(s))
                            .filter(|&s| self.entities[s.0].entity_type == EntityType::Line)))
                        .unwrap_or_default();
                    for l in lines {
                        if self.propagate_line_uniqueness(l) { changed_any = true; }
                    }

                    // 🌟 同じ理由で、この点が乗っている円側の「円の一致条件」も
                    // 再トリガーする(HAGeo-409ベンチマークで、同じ4点が乗って
                    // いるはずのCircumcircleが別実体のまま統合されない問題が
                    // 見つかったことへの対応。EGraph::merge_generationのドキュメント
                    // 参照のような大掛かりな仕組みは不要で、直線と全く同じ
                    // パターンで解決できる)。Directionは円に乗ることが無いので
                    // 実質Pointの場合だけ意味を持つが、フィルタが空になるだけで
                    // 無害なのでDirection側でも同じコードパスを共有する。
                    let circles: Vec<ClassId> = self.entities[rep_id.0].components.first()
                        .map(|c| dedup_sorted_ids(c.subobjects.iter()
                            .map(|&s| self.get_rep(s))
                            .filter(|&s| self.entities[s.0].entity_type == EntityType::Circle)))
                        .unwrap_or_default();
                    for c in circles {
                        if self.propagate_circle_uniqueness(c) { changed_any = true; }
                    }
                }
                _ => {}
            }
        }

        changed_any
    }

    /// 🌟 「直線の一致条件」の局所伝播版。
    /// line 自身が乗っている点(局所・少数)だけを見て、それらの点が他に
    /// 乗っている直線との共有点数を調べる。全直線を舐めない。
    ///
    /// Direction(方向)は「無限遠直線上の点」として扱うので、この関数では
    /// 通常の点と全く区別しない。これにより「2直線が1点を共有しかつ方向が
    /// 同じなら同一直線」という以前の特別扱い(same_dir)は、単に
    /// 「無限遠直線上の共有点も含めて2点共有」という同じルールに統合される
    /// (平行なだけの別々の直線は無限遠点1つしか共有しないので誤ってマージ
    /// されない。同一直線は通常の点+無限遠点の2つを共有するので正しく
    /// マージされる)。
    fn propagate_line_uniqueness(&mut self, line: ClassId) -> bool {
        let mut line = self.get_rep(line);
        let is_point_like = |et: EntityType| et == EntityType::Point || et == EntityType::Direction;

        // 🐛 FIX: 共有点を数える前に、この直線上の点(方向を含む)どうしの
        // 「2直線の交点の一意性」を先に局所的な不動点まで確定させておく。
        // これをやらないと、本来は同一になるはずだがまだ別IDのままの2つ
        // (例: 外心の候補O1とO2、あるいはまだ別々に導出された同じ方向)を
        // 「別々の2つの共有点」と誤認し、無関係な直線を誤ってマージして
        // しまうことがある(外心の証明で実際に発生した)。
        loop {
            let points: Vec<ClassId> = match self.entities[line.0].components.first() {
                Some(c) => c.subobjects.iter()
                    .map(|&id| self.get_rep(id))
                    .filter(|&id| is_point_like(self.entities[id.0].entity_type))
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
                .filter(|&id| is_point_like(self.entities[id.0].entity_type))),
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
                // 🌟 健全性の穴の修正: マージを確定する前に、ランダムな座標での
                // 具体例で本当にこの2直線が等しいかを検算する。数値的に明確に
                // 矛盾する場合(Some(false))はこの偶然の一致を却下し、このペアは
                // マージしない(判定不能なSome(true)/Noneの場合は従来通り進める)。
                if self.numeric_plausibility_check(line, other_line, 2) == Some(false) {
                    let name1 = self.entities[line.0].name.clone();
                    let name2 = self.entities[other_line.0].name.clone();
                    println!("  🚫 [健全性チェック] {} と {} は共有点={}だが数値的に別の直線のため結合を却下",
                        name1, name2, shared.len());
                    continue;
                }
                let name1 = self.entities[line.0].name.clone();
                let name2 = self.entities[other_line.0].name.clone();
                let justification = Justification::LineUniqueness { shared_points: shared.clone() };
                if self.merge_entities_justified(line, other_line, justification) {
                    println!("  ⚙️ [E-Graph自動マージ] 幾何条件(共有点={})により直線を結合: {} ≡ {}",
                        shared.len(), name1, name2);
                    return true;
                }
            }
        }
        false
    }

    /// 🌟 「円の一致条件」の局所伝播版。propagate_line_uniquenessと全く同じ
    /// 発想だが、直線が2点で一意に決まるのに対し円は(非共線な)3点で
    /// 一意に決まるため、しきい値だけが2→3に変わる。
    ///
    /// HAGeo-409ベンチマークの調査で判明した問題への対応: 例えば
    /// Circumcircle(A,B,C)とCircumcircle(A,B,D)がどちらも「A,B,C,Dの4点が
    /// 乗っている」ことまで構造的に分かっていても、この伝播が無いと
    /// 永遠に別々の円エンティティのまま残り、(a)エンティティ数が無駄に
    /// 膨れ上がりマッチングを遅くする、(b)片方の円だけに乗っている
    /// 情報(接線・他の点の接続等)がもう片方には伝わらず証明が断絶する、
    /// という2つの問題を引き起こしていた。
    fn propagate_circle_uniqueness(&mut self, circle: ClassId) -> bool {
        let mut circle = self.get_rep(circle);

        // 🐛 propagate_line_uniquenessと同じ理由: 共有点を数える前に、この円上の
        // 点どうしの「2直線の交点の一意性」を先に局所的な不動点まで確定させて
        // おく。これをやらないと、本来は同一になるはずだがまだ別IDのままの2点を
        // 「別々の2点」と誤認し、共有点数を過小評価して本来マージすべき円を
        // 見逃すことがある。
        loop {
            let points: Vec<ClassId> = match self.entities[circle.0].components.first() {
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
            circle = self.get_rep(circle);
            if !any { break; }
        }

        let points: Vec<ClassId> = match self.entities[circle.0].components.first() {
            Some(c) => dedup_sorted_ids(c.subobjects.iter()
                .map(|&id| self.get_rep(id))
                .filter(|&id| self.entities[id.0].entity_type == EntityType::Point)),
            None => return false,
        };

        // circle上の各点について、他に乗っている円ごとに共有数を数える。
        let mut shared_points: FxHashMap<ClassId, Vec<ClassId>> = FxHashMap::default();
        for &p in &points {
            if let Some(comp) = self.entities[p.0].components.first() {
                let other_circles_of_p: Vec<ClassId> = dedup_sorted_ids(comp.subobjects.iter()
                    .map(|&id| self.get_rep(id))
                    .filter(|&id| id != circle && self.entities[id.0].entity_type == EntityType::Circle));
                for other in other_circles_of_p {
                    shared_points.entry(other).or_default().push(p);
                }
            }
        }

        for (other_circle, shared) in shared_points {
            let circle = self.get_rep(circle); // 途中のマージでrepが変わっている可能性
            let other_circle = self.get_rep(other_circle);
            if circle == other_circle { continue; }

            // 🌟 直線は2点、円は(非共線な)3点で一意に決まる。
            if shared.len() >= 3 {
                // 🌟 却下済みペアキャッシュ(EGraph::rejected_circle_pairsの
                // ドキュメント参照): 前回このペアを却下した時点からマージが
                // 1件も起きていなければ、結果は変わりようがないので数値
                // チェックを省略する。
                let cache_key = if circle.0 < other_circle.0 { (circle.0, other_circle.0) } else { (other_circle.0, circle.0) };
                if self.rejected_circle_pairs.get(&cache_key) == Some(&self.merge_generation) {
                    continue;
                }
                // 🌟 健全性の穴の修正: propagate_line_uniquenessと同様、マージを
                // 確定する前に数値的な裏付けを取る。
                if self.numeric_plausibility_check(circle, other_circle, 2) == Some(false) {
                    self.rejected_circle_pairs.insert(cache_key, self.merge_generation);
                    let name1 = self.entities[circle.0].name.clone();
                    let name2 = self.entities[other_circle.0].name.clone();
                    println!("  🚫 [健全性チェック] {} と {} は共有点={}だが数値的に別の円のため結合を却下",
                        name1, name2, shared.len());
                    continue;
                }
                let name1 = self.entities[circle.0].name.clone();
                let name2 = self.entities[other_circle.0].name.clone();
                let justification = Justification::CircleUniqueness { shared_points: shared.clone() };
                if self.merge_entities_justified(circle, other_circle, justification) {
                    println!("  ⚙️ [E-Graph自動マージ] 幾何条件(共有点={})により円を結合: {} ≡ {}",
                        shared.len(), name1, name2);
                    return true;
                }
            }
        }
        false
    }

    /// 🌟 「2直線の交点の一意性」の局所伝播版。
    /// point(方向を含む)自身が乗っている直線(局所・少数)のペアについて、
    /// その交点が memo に既に登録されていないかをO(1)参照するだけ。全点を舐めない。
    ///
    /// 方向(Direction)は Definition::Intersection(line, 無限遠直線) ではなく
    /// Definition::DirectionOf(line) という別のDefinitionで登録されている
    /// (定理側のパターンを変えずに済ませるため、あえて既存の表現のままにしてある)。
    /// そのため、ペアのどちらかが無限遠直線のときは DirectionOf での読み替えも試す。
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

                if l1 == self.line_infinity {
                    if let Some(&existing) = self.memo.get(&Definition::DirectionOf(l2)) { candidates.push((existing, l1, l2)); }
                }
                if l2 == self.line_infinity {
                    if let Some(&existing) = self.memo.get(&Definition::DirectionOf(l1)) { candidates.push((existing, l1, l2)); }
                }
            }
        }

        for (existing, via_l1, via_l2) in candidates {
            let existing_rep = self.get_rep(existing);
            let point_rep = self.get_rep(point);
            if existing_rep != point_rep {
                // 🌟 健全性の穴の修正: propagate_line_uniquenessと同様、マージを
                // 確定する前に数値的な裏付けを取る。
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

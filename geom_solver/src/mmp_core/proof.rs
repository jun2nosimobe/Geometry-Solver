//! 🌟 証明復元: e-graphのマージ履歴(「証明の森」)を目標から遡って辿り、
//! 実際に使われたステップだけを人間可読な証明文として再構成する。
//! Python版のextract_proof.pyは全ログを無差別にダンプするだけで無関係な
//! 定理まで大量に混入していたが、こちらはexplain_identical/
//! find_incidence_justificationで「実際に目標へ辿り着くのに使われた
//! ステップだけ」を復元するので、不要な定理は原理的に混入しない。

use super::{ClassId, EGraph, Justification, ProofEdge};

impl EGraph {
    /// 🌟 証明復元の中核: id からproof_edgesを根に向かって辿り、経路上の
    /// (辺の出発点, 辺の到達点, 理由) を根に近い側が末尾になる順で返す。
    fn proof_path_to_root(&self, mut id: ClassId) -> Vec<ProofEdge> {
        let mut path = Vec::new();
        let mut guard = 0usize;
        while let Some(edge) = self.proof_edges.get(&id.0) {
            path.push(edge.clone());
            id = edge.to;
            guard += 1;
            if guard > self.entities.len() + 10 { break; } // 循環防止の安全弁
        }
        path
    }

    /// 🌟 idの「一番最初に確認できる名前」。idが後にマージで吸収された
    /// (union-find上でrootでなくなった)場合、その.nameフィールドは
    /// merge_entities内でstd::mem::takeされて空文字になってしまうため、
    /// 現在のself.entities[id.0].nameを見ても意味がない。
    /// 代わりに、idが最初に吸収された瞬間に記録されたfrom_nameスナップショット
    /// (proof_path_to_rootの最初の要素)を使う。一度も吸収されていない
    /// (=今なお現在の代表元そのもの)場合は、素直に現在の名前を使う。
    /// 🌟 このClassIdが最初に(create_entity時に)何と名付けられたかを返す。
    /// .nameは「短い方が勝つ」ヒューリスティックにより、たとえこのIDが
    /// union-find上のrootのまま(一度も吸収されていない)でも、後から吸収した
    /// 側の方が短ければ書き換わってしまうことがある。original_nameは
    /// create_entity時に一度だけ設定されそれ以降は絶対に変わらないので、
    /// 証明復元では常にこちらを使う。
    fn earliest_known_name(&self, id: ClassId) -> String {
        self.entities[id.0].original_name.clone()
    }

    /// 🌟 a ≡ b であることの証明を、実際にそう判明した合流点(union-findの
    /// 「証明の森」)まで遡って復元する。a, b が同じ同値類でなければ空を返す。
    /// 返り値は a → (中間の合流点) → b という順の証明ステップ列。
    pub fn explain_identical(&self, a: ClassId, b: ClassId) -> Vec<ProofEdge> {
        if self.get_rep(a) != self.get_rep(b) { return Vec::new(); }
        let path_a = self.proof_path_to_root(a);
        let mut path_b = self.proof_path_to_root(b);
        path_b.reverse();
        // 🌟 b側の経路は元々「bの根に向かう向き」で記録されているので、
        // 逆順にした後は表示上の from/to も入れ替えて、
        // a → ... → 合流点 → ... → b と読める自然な順序にする。
        // (等式自体は対称なので、元の向きのままでも数学的には正しいが、
        // 読みやすさのための整形。名前はoriginal_name経由でraw ClassIdから
        // 常に安定して引けるので、入れ替えが必要なのはfrom/toそのものだけ)。
        for edge in &mut path_b {
            std::mem::swap(&mut edge.from, &mut edge.to);
        }
        let mut result = path_a;
        result.extend(path_b);
        result
    }

    /// 🌟 pointがcircle(またはline)に乗っている理由を、直接記録された
    /// incidence_provenanceの中から探す(repベースで照合するので、記録時と
    /// 違うエンティティ経由で同じ代表元に辿り着いた場合も見つかる)。
    /// 見つかった場合、その記録に使われた「元のid」も一緒に返す
    /// (pointやcircle自体がその後マージで代表元が変わっていることがあるため、
    /// 呼び出し側がexplain_identicalで橋渡しの説明を追加できるように)。
    pub fn find_incidence_justification(&self, point: ClassId, circle_or_line: ClassId) -> Option<(ClassId, ClassId, Justification)> {
        let p_rep = self.get_rep(point);
        let c_rep = self.get_rep(circle_or_line);
        for (&(x, y), just) in &self.incidence_provenance {
            let (rx, ry) = (self.get_rep(x), self.get_rep(y));
            if (rx == p_rep && ry == c_rep) || (rx == c_rep && ry == p_rep) {
                let (orig_point, orig_circle) = if rx == p_rep { (x, y) } else { (y, x) };
                return Some((orig_point, orig_circle, just.clone()));
            }
        }
        None
    }

    /// 🌟 pointsの全てが乗っている共通の円を(あれば)1つ返す。
    pub fn find_shared_circle(&self, points: &[ClassId]) -> Option<ClassId> {
        if points.is_empty() { return None; }
        for i in 0..self.entities.len() {
            let cand = ClassId(i);
            if self.get_rep(cand) != cand { continue; }
            if self.entities[i].entity_type != super::EntityType::Circle { continue; }
            if points.iter().all(|&p| self.is_connected(p, cand)) {
                return Some(cand);
            }
        }
        None
    }

    /// 🌟 証明経路の中に、名前付き定理の連鎖(Given/Theorem/Congruence/Trivial)
    /// ではなく、局所伝播のショートカット(LineUniqueness/PointUniqueness)だけを
    /// 根拠にしたステップが含まれているかを判定する。
    ///
    /// 🐛 背景: propagate_line_uniqueness/propagate_point_uniqueness(「2直線が
    /// 十分な点/方向を共有していれば同一視する」「2直線の交点は一意」)は、
    /// マージを確定する前にnumeric_plausibility_checkで有限体上のランダムな
    /// 1点(または少数)による数値的裏付けを取ってはいるものの、これは
    /// あくまで「ランダムに選んだ具体例で矛盾が見つからなかった」という
    /// 確率的な根拠(Schwartz-Zippel的な議論)であり、名前付き定理を
    /// 前提から結論へ連鎖させる形式的な演繹ではない。この2つのJustification
    /// だけがそれに該当する(Congruenceは定義の構造的な一致、Trivialは
    /// apply_trivial_relations由来の定義から機械的に従う結合なので、
    /// どちらも数値サンプリングには依存しない)。
    ///
    /// MCTSのような無方向な探索は、この局所伝播だけを頼りに大量の補助構成を
    /// 経由して目標へ到達することがあり(実測: orthocenter_altで観測)、
    /// 個々のステップは(numeric_plausibility_checkにより)偽陽性ではなさそうで
    /// あっても、その経路全体を「形式的な証明」と呼ぶのは正確ではない。
    /// generate_proof/main.rsの🎉表示で、この違いを利用者に明示するために使う。
    pub fn proof_uses_numeric_shortcut(edges: &[ProofEdge]) -> bool {
        edges.iter().any(|e| matches!(
            e.justification,
            Justification::LineUniqueness { .. } | Justification::PointUniqueness { .. }
        ))
    }

    fn format_justification(&self, j: &Justification) -> String {
        let name = |id: ClassId| self.earliest_known_name(id);
        match j {
            Justification::Given => "問題の初期条件(前提)として与えられている".to_string(),
            Justification::Theorem { name: theorem_name, premises } => {
                if premises.is_empty() {
                    format!("定理「{}」", theorem_name)
                } else {
                    let ps: Vec<String> = premises.iter()
                        .map(|(ft, args)| format!("{}({})", ft, args.iter().map(|&a| name(a)).collect::<Vec<_>>().join(", ")))
                        .collect();
                    format!("定理「{}」 (前提: {})", theorem_name, ps.join(" ∧ "))
                }
            }
            Justification::Congruence { definition } => format!("合同閉包: どちらも {} として定義される", definition),
            Justification::LineUniqueness { shared_points } => format!(
                "2直線が{}点を共有({})しているため同一直線",
                shared_points.len(),
                shared_points.iter().map(|&p| name(p)).collect::<Vec<_>>().join(", ")
            ),
            Justification::PointUniqueness { via_lines } => format!(
                "直線 {} と直線 {} の交点として一意に定まる",
                name(via_lines.0), name(via_lines.1)
            ),
            Justification::Trivial { reason } => reason.clone(),
        }
    }

    /// 🌟 ユーザー要望: 「e-graphのマージ履歴から証明を作ってresultに出力する
    /// 仕組み」。Python版のextract_proof.pyは全ログを無差別にダンプするだけ
    /// だったため無関係な定理まで大量に混入していたが、こちらはexplain_identical/
    /// find_incidence_justificationで「実際に目標へ辿り着くのに使われた
    /// ステップだけ」を証明の森から遡って再構成するので、不要な定理は
    /// 原理的に混入しない。
    pub fn generate_proof(&self, fact_type: &str, target_args: &[ClassId]) -> String {
        let mut out = String::new();
        out.push_str("========================================\n");
        out.push_str("✨ 証明 (E-Graphのマージ履歴から復元) ✨\n");
        out.push_str("========================================\n\n");

        match fact_type {
            "Identical" if target_args.len() == 2 => {
                let edges = self.explain_identical(target_args[0], target_args[1]);
                if edges.is_empty() {
                    out.push_str("(まだ証明されていません、またはこの2つは元から同一の図形です)\n");
                } else {
                    if Self::proof_uses_numeric_shortcut(&edges) {
                        out.push_str(
                            "⚠️ 注意: 以下の経路には「2直線が十分な点/方向を共有」「2直線の交点は\n\
                             一意」といった局所伝播ショートカット(理由の行に明記)が含まれています。\n\
                             これらは確定前に有限体上のランダムな数値サンプリングで矛盾がないことを\n\
                             確認していますが、名前付き定理を前提から結論へ連鎖させる形式的な演繹\n\
                             ではなく、あくまで「ランダムな具体例で反例が見つからなかった」という\n\
                             確率的な根拠に基づいています。以下は形式的な証明としてではなく、\n\
                             その根拠付きの参考記録として読んでください。\n\n"
                        );
                    }
                    for (i, edge) in edges.iter().enumerate() {
                        out.push_str(&format!("Step {:2}: {} ≡ {}\n", i + 1,
                            self.earliest_known_name(edge.from), self.earliest_known_name(edge.to)));
                        out.push_str(&format!("         └─ 理由: {}\n\n", self.format_justification(&edge.justification)));
                    }
                    let g1 = self.earliest_known_name(target_args[0]);
                    let g2 = self.earliest_known_name(target_args[1]);
                    out.push_str(&format!("∴ {} ≡ {} ∎\n", g1, g2));
                }
            }
            "Concyclic" => {
                if let Some(circle) = self.find_shared_circle(target_args) {
                    out.push_str(&format!("共通の円: {}\n\n", self.entities[circle.0].name));
                    for &p in target_args {
                        let p_name = self.earliest_known_name(p);
                        match self.find_incidence_justification(p, circle) {
                            Some((_, _, just)) => {
                                out.push_str(&format!("- {} ∈ {}\n", p_name, self.entities[circle.0].name));
                                out.push_str(&format!("    └─ 理由: {}\n\n", self.format_justification(&just)));
                            }
                            None => {
                                out.push_str(&format!("- {} ∈ {} (直接の根拠が記録されていません)\n\n", p_name, self.entities[circle.0].name));
                            }
                        }
                    }
                    out.push_str("∴ 上記の点はすべて同じ円に乗っている ∎\n");
                } else {
                    out.push_str("(共通の円がまだ見つかっていません)\n");
                }
            }
            _ => {
                out.push_str(&format!("(目標タイプ「{}」の証明復元には未対応です)\n", fact_type));
            }
        }
        out
    }
}

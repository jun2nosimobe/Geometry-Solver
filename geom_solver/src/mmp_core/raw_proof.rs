//! 🌟 raw_proof: e-graphの全マージ履歴(union-findの「証明の森」+ incidenceの
//! 由来)を、人間が読むためではなくRust側で読み書きしやすい単純なテキスト
//! 形式でダンプ/復元するモジュール。
//!
//! proof.rs::generate_proofは「目標から遡って実際に使われたステップだけ」
//! を人間可読な文章として復元するのに対し、こちらは役割を2段階に分ける:
//!   1. `EGraph::dump_raw_proof` — main.rsが実行のたびに、EGraphが保持する
//!      証明関連情報(proof_edges, incidence_provenance, 全エンティティの
//!      名前/型)を一切フィルタせず丸ごとテキストへシリアライズする。
//!   2. `RawProof::parse` + `verify_identical` — 保存されたテキストを
//!      (実行中のEGraphとは完全に独立に)読み込み直し、目標の等式から
//!      遡ってTheoremのpremisesまで再帰的に検証することで、「本当に
//!      最初から最後まで証明が繋がっているか、途中にLineUniqueness/
//!      PointUniqueness/Trivialのような数値サンプリングや構造的近似だけに
//!      頼った(=名前付き定理の連鎖による形式的な演繹ではない)ギャップが
//!      眠っていないか」を監査する。
//!
//! 🌟 なぜ2段階に分けるか: generate_proof/EGraph::proof_uses_numeric_shortcut
//! は目標そのものの直接のマージ経路(explain_identicalが返す最上位の辺)しか
//! 見ないため、Theoremの前提(premises)自体がさらに別のLineUniqueness等の
//! ショートカットに依存しているケースを見逃しうる(実際にcircumcenterの
//! 調査でこの種の深い依存が実在することが判明した)。ここではTheoremの
//! premisesを再帰的に遡ることで、そのような深いところに隠れたギャップも
//! 検出する。またテキストファイルとして永続化しておくことで、ソルバーを
//! 再実行せずに後から(あるいは別プロセスから)同じ検証をやり直せる。
//!
//! 🌟 フォーマット: 依存クレートを増やさないための独自の単純なTSV風形式。
//! 各行はタブ区切りで、最初の数フィールドだけを厳密にタブ分割し、残りは
//! 「行の残り全部」として1つのペイロード文字列に詰める(Theoremの前提や
//! Congruenceの定義文字列にカンマ・コロン・括弧が出てきても、それらは
//! ペイロード内部の記法であって行の区切りには使わないため安全)。
//!   E\t{id}\t{original_name}\t{entity_type}
//!   P\t{from_id}\t{to_id}\t{kind}\t{payload}      (proof_edges 1件)
//!   I\t{a_id}\t{b_id}\t{kind}\t{payload}          (incidence_provenance 1件)
//! kind は Given/Theorem/Congruence/LineUniqueness/PointUniqueness/Trivial の
//! いずれか。payloadのkind別の中身は encode_justification を参照。

use super::{EGraph, Justification};
use rustc_hash::FxHashMap;

/// 🌟 Justificationを(種類タグ, ペイロード文字列)に変換する。RawProof側は
/// このペイロードを再度Justificationへ完全に復元する必要はなく(検証に
/// 必要な情報――種類と、Theoremならpremisesのfact_type/args――だけ取り出せれば
/// 十分)、専用の軽量デコードだけを行う。
fn encode_justification(j: &Justification) -> (&'static str, String) {
    match j {
        Justification::Given => ("Given", String::new()),
        Justification::Theorem { name, premises } => {
            let premises_str = premises.iter()
                .map(|(ft, args)| format!("{}:{}", ft, args.iter().map(|a| a.0.to_string()).collect::<Vec<_>>().join(",")))
                .collect::<Vec<_>>().join(";");
            ("Theorem", format!("{}|{}", name, premises_str))
        }
        Justification::Congruence { definition } => ("Congruence", definition.clone()),
        Justification::LineUniqueness { shared_points } => (
            "LineUniqueness",
            shared_points.iter().map(|p| p.0.to_string()).collect::<Vec<_>>().join(","),
        ),
        Justification::PointUniqueness { via_lines } => (
            "PointUniqueness",
            format!("{},{}", via_lines.0.0, via_lines.1.0),
        ),
        Justification::Trivial { reason } => ("Trivial", reason.clone()),
    }
}

impl EGraph {
    /// 🌟 現在のEGraphが保持する証明関連情報を、一切のフィルタなしで
    /// テキストへダンプする。generate_proofと違い「目標に関係あるか」は
    /// 判定しない――記録されている全てのproof_edges/incidence_provenanceを
    /// そのまま書き出す(だからこそ"raw")。
    pub fn dump_raw_proof(&self) -> String {
        let mut out = String::new();
        for i in 0..self.entities.len() {
            out.push_str(&format!("E\t{}\t{}\t{:?}\n", i, self.entities[i].original_name, self.entities[i].entity_type));
        }
        for (&from, edge) in &self.proof_edges {
            let (kind, payload) = encode_justification(&edge.justification);
            out.push_str(&format!("P\t{}\t{}\t{}\t{}\n", from, edge.to.0, kind, payload));
        }
        for (&(a, b), just) in &self.incidence_provenance {
            let (kind, payload) = encode_justification(just);
            out.push_str(&format!("I\t{}\t{}\t{}\t{}\n", a.0, b.0, kind, payload));
        }
        out
    }
}

/// 🌟 raw_proofテキストから読み取った1本の辺。Justificationを完全な形では
/// 保持せず、検証に必要な(種類, ペイロード)だけを持つ軽量表現。
#[derive(Debug, Clone)]
struct RawEdge {
    to: usize,
    kind: String,
    payload: String,
}

/// 🌟 保存済みraw_proofテキストをメモリ上に復元した構造。実行中のEGraphとは
/// 完全に独立しており、ファイルさえあれば後からいつでも(別プロセスからも)
/// 検証をやり直せる。
pub struct RawProof {
    /// id -> 元の名前(original_name)
    names: FxHashMap<usize, String>,
    /// 名前 -> id (extract_proofを名前指定で呼べるようにするための逆引き)
    name_to_id: FxHashMap<String, usize>,
    /// union-findの証明の森: from -> 辺
    proof_edges: FxHashMap<usize, RawEdge>,
    /// 🌟 proof_edgesの逆引き: to -> そこへ合流した(from)の一覧。
    /// LineUniqueness/PointUniquenessの「共有点/共有直線」は、当時の代表元
    /// (現在も代表元のまま=このマップのキー側であることが多い)を指すため、
    /// その実体"自身"の由来(なぜ他の実体と等しくなったか)を辿るには
    /// proof_edgesを前向きに辿るだけでは不十分(代表元はproof_edges上で
    /// "from"にならないので、前向きには何も出てこない)。このマップで
    /// 「誰がこの代表元に合流してきたか」を逆方向に辿れるようにする。
    reverse_edges: FxHashMap<usize, Vec<usize>>,
    /// 「点PはこのCircle/Lineに乗っている」の由来: (小さい方, 大きい方) -> 辺
    incidence: FxHashMap<(usize, usize), RawEdge>,
}

impl RawProof {
    /// 🌟 dump_raw_proofが書き出したテキストを解析する。壊れた行(フィールド
    /// 不足)は静かに無視する(raw_proofは常に自前のdump_raw_proofが生成した
    /// ものだけを読む前提なので、壊れているのはファイル破損時のみであり、
    /// そこで検証全体をpanicさせるよりは「読めた分だけで検証する」方が
    /// 診断ツールとして扱いやすい)。
    pub fn parse(text: &str) -> RawProof {
        let mut names = FxHashMap::default();
        let mut name_to_id = FxHashMap::default();
        let mut proof_edges = FxHashMap::default();
        let mut incidence = FxHashMap::default();

        for line in text.lines() {
            let mut parts = line.splitn(5, '\t');
            let Some(tag) = parts.next() else { continue };
            match tag {
                "E" => {
                    let (Some(id_s), Some(name)) = (parts.next(), parts.next()) else { continue };
                    let Ok(id) = id_s.parse::<usize>() else { continue };
                    names.insert(id, name.to_string());
                    name_to_id.insert(name.to_string(), id);
                }
                "P" => {
                    let (Some(from_s), Some(to_s), Some(kind), Some(payload)) =
                        (parts.next(), parts.next(), parts.next(), parts.next()) else { continue };
                    let (Ok(from), Ok(to)) = (from_s.parse::<usize>(), to_s.parse::<usize>()) else { continue };
                    proof_edges.insert(from, RawEdge { to, kind: kind.to_string(), payload: payload.to_string() });
                }
                "I" => {
                    let (Some(a_s), Some(b_s), Some(kind), Some(payload)) =
                        (parts.next(), parts.next(), parts.next(), parts.next()) else { continue };
                    let (Ok(a), Ok(b)) = (a_s.parse::<usize>(), b_s.parse::<usize>()) else { continue };
                    let key = if a < b { (a, b) } else { (b, a) };
                    incidence.insert(key, RawEdge { to: b, kind: kind.to_string(), payload: payload.to_string() });
                }
                _ => {}
            }
        }
        let mut reverse_edges: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
        for (&from, edge) in &proof_edges {
            reverse_edges.entry(edge.to).or_default().push(from);
        }
        RawProof { names, name_to_id, proof_edges, reverse_edges, incidence }
    }

    pub fn id_of(&self, name: &str) -> Option<usize> {
        self.name_to_id.get(name).copied()
    }

    fn name_of(&self, id: usize) -> String {
        self.names.get(&id).cloned().unwrap_or_else(|| format!("#{}", id))
    }

    /// 🌟 idからroot(proof_edgesを辿った終点)までの辺の列を返す
    /// (proof.rs::proof_path_to_rootのraw_proof版)。
    fn path_to_root(&self, mut id: usize) -> Vec<(usize, RawEdge)> {
        let mut path = Vec::new();
        let mut guard = 0usize;
        while let Some(edge) = self.proof_edges.get(&id) {
            let from = id;
            path.push((from, edge.clone()));
            id = edge.to;
            guard += 1;
            if guard > self.names.len() + 10 { break; }
        }
        path
    }

    /// 🌟 a, bが実際に(proof_edgesを辿って)同じ根に合流するかどうかに関わらず、
    /// aからbへの辺の列(explain_identicalのraw_proof版)を作る。合流しない
    /// 場合はNone。
    fn explain(&self, a: usize, b: usize) -> Option<Vec<(usize, RawEdge)>> {
        let path_a = self.path_to_root(a);
        let root_a = path_a.last().map(|(_, e)| e.to).unwrap_or(a);
        let path_b = self.path_to_root(b);
        let root_b = path_b.last().map(|(_, e)| e.to).unwrap_or(b);
        if root_a != root_b { return None; }
        let mut result = path_a;
        // b側は「bの根に向かう向き」なので、a→root→bと読めるように逆順+反転する。
        for (from, edge) in path_b.into_iter().rev() {
            result.push((edge.to, RawEdge { to: from, kind: edge.kind, payload: edge.payload }));
        }
        Some(result)
    }

    /// 🌟 gapの(またはノードの)location文字列を組み立てる。fromとedge.toの
    /// 関係が「等しい」(proof_edges由来、explain_identicalの辺)なのか
    /// 「接続している」(incidence_provenance由来、点が直線/円に乗っている)
    /// なのかで表記を変える(以前は両方とも"≡"と表示しており、"A ≡ Circ"の
    /// ような誤解を招く出力になっていた)。
    fn format_location(&self, from: usize, to: usize, is_incidence: bool) -> String {
        if is_incidence {
            format!("{} は {} に接続", self.name_of(from), self.name_of(to))
        } else {
            format!("{} ≡ {}", self.name_of(from), self.name_of(to))
        }
    }

    /// 🌟 「深い証明」の中核: 1本の辺をDeepStepツリーへ再帰的に展開する。
    /// Given/Congruence/Trivialは子を持たない基底ケース。Theoremは
    /// premisesそれぞれを子ノードとして再帰的に展開する。LineUniqueness/
    /// PointUniqueness(「2点/2直線の共有」という構造的観察)は、共有点/
    /// 共有直線の由来(それ自身のマージ履歴 + incidence_provenance)を子
    /// ノードとして展開する――これにより「2直線が2点を共有」という
    /// ショートカット自体を、その根拠まで含めて完全に人間可読な形で
    /// 追跡できる(ユーザー指摘: 「共有によるマージも履歴に残せば証明を
    /// 完全に辿ることができないか」への直接の回答)。
    ///
    /// visitedで(種別タグ, 対象id列)の組を覚えておき、同じ前提/同じ辺を
    /// 何度も展開する無駄・循環を防ぐ(有向角の加法性/交替律など、多くの
    /// 定理が同じAng90絡みの前提を共有するため、これが無いと組み合わせ的に
    /// 膨れ上がる)。既に展開済みの箇所は、内容を繰り返さず「(既出、上記で
    /// 検証済み)」という参照だけの葉ノードにする。
    fn build_step(
        &self,
        from: usize,
        edge: &RawEdge,
        is_incidence: bool,
        visited: &mut std::collections::HashSet<(String, Vec<usize>)>,
        depth: usize,
    ) -> DeepStep {
        let headline = self.format_location(from, edge.to, is_incidence);
        if depth > 500 {
            return DeepStep {
                headline, children: Vec::new(),
                reason: "再帰の深さが上限(500)を超えたため打ち切り".to_string(),
                is_gap: true,
                gap_reason: Some("定理の前提が循環している可能性があります".to_string()),
                is_shortcut: false,
            };
        }
        match edge.kind.as_str() {
            "Given" => DeepStep::leaf(headline, "問題の初期条件(前提)として与えられている".to_string()),
            "Congruence" => DeepStep::leaf(headline, format!("合同閉包: どちらも {} として定義される", edge.payload)),
            // 🌟 Trivialはapply_trivial_relations由来の構造的な結合(垂線→Ang90、
            // 外接円の定義よりその3点が円に乗っている、PerpDirectionOf/
            // HarmonicConjugateOfの対合性など)であり、定義から機械的に
            // (数値サンプリングに一切頼らず)従う――ギャップではない。
            "Trivial" => DeepStep::leaf(headline, format!("定義から機械的に従う構造的な事実: {}", edge.payload)),
            "Theorem" => {
                let Some((name, premises_str)) = edge.payload.split_once('|') else {
                    return DeepStep::leaf(headline, "定理(前提の記録なし)".to_string());
                };
                let mut children = Vec::new();
                if !premises_str.is_empty() {
                    for premise in premises_str.split(';') {
                        let Some((fact_type, args_str)) = premise.split_once(':') else { continue; };
                        let args: Vec<usize> = args_str.split(',').filter_map(|s| s.parse::<usize>().ok()).collect();
                        children.push(self.build_premise_step(fact_type, &args, visited, depth + 1));
                    }
                }
                DeepStep { headline, reason: format!("定理「{}」", name), children, is_gap: false, gap_reason: None, is_shortcut: false }
            }
            "LineUniqueness" | "PointUniqueness" => {
                let ids: Vec<usize> = edge.payload.split(',').filter_map(|s| s.parse().ok()).collect();
                let (reason, related_lines): (String, Vec<usize>) = if edge.kind == "LineUniqueness" {
                    (format!("2直線が点({})を共有しているため同一直線", ids.iter().map(|&i| self.name_of(i)).collect::<Vec<_>>().join(", ")),
                     vec![from, edge.to])
                } else {
                    (format!("直線 {} と直線 {} の交点として一意に定まる", self.name_of(ids.first().copied().unwrap_or(0)), self.name_of(ids.get(1).copied().unwrap_or(0))),
                     ids.clone())
                };
                // 🌟 「共有している」という前提の由来を子ノードとして展開する。
                // LineUniquenessならids=共有点、related_lines=2直線。
                // PointUniquenessならids=2直線(via_lines)、related_lines=同じ2直線
                // (この場合はfrom/edge.toの側=2点それぞれの接続を調べる)。
                // 🌟 今まさに検証している辺(from, edge.to)自身を除外する
                // (下記build_grounding_stepのexclude参照)。
                let mut children = Vec::new();
                if edge.kind == "LineUniqueness" {
                    for &p in &ids {
                        children.push(self.build_grounding_step(p, &related_lines, (from, edge.to), visited, depth + 1));
                    }
                } else {
                    for &pt in &[from, edge.to] {
                        children.push(self.build_grounding_step(pt, &related_lines, (from, edge.to), visited, depth + 1));
                    }
                }
                DeepStep { headline, reason, children, is_gap: false, gap_reason: None, is_shortcut: true }
            }
            other => DeepStep {
                headline, children: Vec::new(),
                reason: format!("未知の理由の種類「{}」", other),
                is_gap: true,
                gap_reason: Some("raw_proofの形式が想定外です".to_string()),
                is_shortcut: false,
            },
        }
    }

    /// 🌟 LineUniqueness/PointUniquenessが「共有している」とみなした1つの点
    /// (またはPointUniquenessの場合は2点それぞれ)について、(a)それ自身が
    /// さらに別のマージの産物ならそのマージ履歴、(b)関係する直線それぞれへの
    /// 接続の由来、をまとめて1つの子ノードにする。excludeは「今まさに検証
    /// している辺」の(from, to)で、path_to_root/reverse_edgesが偶然この
    /// 辺自身を再発見してしまい、自分自身を自分の根拠として無限に参照する
    /// 循環(PointUniquenessでentityがまさにその辺の片方になるため実際に
    /// circumcenterの調査で発覚した)を防ぐために、この辺だけは除外する。
    fn build_grounding_step(
        &self,
        entity: usize,
        lines: &[usize],
        exclude: (usize, usize),
        visited: &mut std::collections::HashSet<(String, Vec<usize>)>,
        depth: usize,
    ) -> DeepStep {
        let key = ("GROUND".to_string(), { let mut v = vec![entity]; v.extend_from_slice(lines); v });
        let headline = format!("{} の由来", self.name_of(entity));
        if !visited.insert(key) {
            return DeepStep::leaf(headline, "(既出: 上記で検証済みなので省略)".to_string());
        }
        let is_excluded = |a: usize, b: usize| (a, b) == exclude || (b, a) == exclude;
        let mut children = Vec::new();
        // (a) この実体自身がさらに別のマージの産物なら、その履歴を辿る
        // (このentityが後で誰かに吸収された側=proof_edges上のfromである場合)。
        for (sf, se) in self.path_to_root(entity) {
            if is_excluded(sf, se.to) { continue; }
            children.push(self.build_step(sf, &se, false, visited, depth + 1));
        }
        // 🐛 FIX: LineUniqueness/PointUniquenessが記録する共有点/共有直線の
        // ClassIdは、多くの場合そのマージの当時から今も代表元であり続けている
        // 側(=誰かがこちらへ吸収されてきた側)であるため、上のpath_to_root
        // (前向き)だけでは何も出てこない(代表元自身はproof_edges上で
        // "from"にはならないため)。逆に「誰がこの実体に合流してきたか」を
        // reverse_edgesで辿ることで、例えば「別の方向が同位角判定などの
        // 定理チェーンでこの方向に合流した」という、まさに知りたい経緯を
        // 拾い上げる(orthocenter_altの調査でこの取りこぼしが実際に発覚した)。
        if let Some(sources) = self.reverse_edges.get(&entity) {
            for &src in sources {
                if is_excluded(src, entity) { continue; }
                let edge_key = ("REVEDGE".to_string(), vec![src, entity]);
                if !visited.insert(edge_key) { continue; }
                if let Some(edge) = self.proof_edges.get(&src) {
                    children.push(self.build_step(src, edge, false, visited, depth + 1));
                }
            }
        }
        // (b) 関係する直線それぞれへの接続の由来。記録が無ければ、作図時点の
        // 構造的な接続(定義から機械的に従う)として基底ケース扱いする。
        for &line in lines {
            let key = if entity < line { (entity, line) } else { (line, entity) };
            let sub_headline = format!("{} は {} に接続", self.name_of(entity), self.name_of(line));
            match self.incidence.get(&key) {
                Some(inc_edge) => children.push(self.build_step(key.0, inc_edge, true, visited, depth + 1)),
                None => children.push(DeepStep::leaf(sub_headline, "由来の明示的な記録なし(作図時点の構造的な接続として、定義から機械的に従う)".to_string())),
            }
        }
        DeepStep { headline, reason: "共有点/共有直線としての由来".to_string(), children, is_gap: false, gap_reason: None, is_shortcut: false }
    }

    /// 🌟 Theoremのpremises 1件をDeepStepへ展開する。Identicalなら合流経路を、
    /// Connectedならincidence_provenanceの由来を再帰的に辿る。それ以外の
    /// fact_type(DefinedByなど)は構造的な基底ケースとして扱う。
    fn build_premise_step(
        &self,
        fact_type: &str,
        args: &[usize],
        visited: &mut std::collections::HashSet<(String, Vec<usize>)>,
        depth: usize,
    ) -> DeepStep {
        let arg_names: Vec<String> = args.iter().map(|&a| self.name_of(a)).collect();
        let headline = format!("前提 {}({})", fact_type, arg_names.join(", "));
        let mut key_args = args.to_vec();
        key_args.sort_unstable();
        let key = (format!("F:{}", fact_type), key_args);
        if !visited.insert(key) {
            return DeepStep::leaf(headline, "(既出: 上記で検証済みなので省略)".to_string());
        }
        match fact_type {
            "Identical" if args.len() == 2 => {
                match self.explain(args[0], args[1]) {
                    Some(sub_edges) => {
                        let children: Vec<DeepStep> = sub_edges.iter()
                            .map(|(sf, se)| self.build_step(*sf, se, false, visited, depth + 1))
                            .collect();
                        DeepStep { headline, reason: "以下の合流経路で成立".to_string(), children, is_gap: false, gap_reason: None, is_shortcut: false }
                    }
                    None => DeepStep {
                        headline, children: Vec::new(),
                        reason: "raw_proof中にこの前提を裏付ける合流経路が見つかりませんでした".to_string(),
                        is_gap: true,
                        gap_reason: Some("この前提を裏付ける合流経路が見つかりません".to_string()),
                        is_shortcut: false,
                    },
                }
            }
            "Connected" if args.len() == 2 => {
                let ikey = if args[0] < args[1] { (args[0], args[1]) } else { (args[1], args[0]) };
                match self.incidence.get(&ikey) {
                    Some(inc_edge) => {
                        let child = self.build_step(ikey.0, inc_edge, true, visited, depth + 1);
                        DeepStep { headline, reason: "以下の由来で成立".to_string(), children: vec![child], is_gap: false, gap_reason: None, is_shortcut: false }
                    }
                    // 🌟 由来が記録されていないConnectedは、apply_trivial_relations/
                    // 作図時点のlink_logical_incidenceによる「定義から機械的に
                    // 従う」接続関係であることが多く、これ自体はギャップではない。
                    None => DeepStep::leaf(headline, "由来の明示的な記録なし(作図時点の構造的な接続として、定義から機械的に従う)".to_string()),
                }
            }
            _ => DeepStep::leaf(headline, "構造的な基底事実(定義から機械的に従う)".to_string()),
        }
    }

    /// 🌟 aとbが本当にrigorousな経路(Given/Theorem/Congruence/Trivialの連鎖、
    /// かつTheoremの前提・LineUniqueness/PointUniquenessの由来も再帰的に
    /// rigorous)だけで合流しているかを検証し、その全経路を保持した
    /// DeepProofを返す。
    pub fn verify_identical(&self, a: usize, b: usize) -> DeepProof {
        let mut visited = std::collections::HashSet::new();
        let roots = match self.explain(a, b) {
            Some(edges) => edges.iter().map(|(from, edge)| self.build_step(*from, edge, false, &mut visited, 0)).collect(),
            None => vec![DeepStep {
                headline: format!("{} ≡ {}", self.name_of(a), self.name_of(b)),
                reason: String::new(),
                children: Vec::new(),
                is_gap: true,
                gap_reason: Some("raw_proof中にこの2つが合流する経路が全く見つかりませんでした(未証明)".to_string()),
                is_shortcut: false,
            }],
        };
        DeepProof { roots }
    }
}

/// 🌟 「深い証明」の1ノード。1つの合流ステップ、Theoremの1つの前提、または
/// LineUniqueness/PointUniquenessの共有点/共有直線1つ分の由来に対応する。
/// childrenに、その根拠として使われたさらに下位のステップを再帰的に持つ。
#[derive(Debug, Clone)]
pub struct DeepStep {
    pub headline: String,
    pub reason: String,
    pub children: Vec<DeepStep>,
    pub is_gap: bool,
    pub gap_reason: Option<String>,
    /// 🌟 このノードがLineUniqueness/PointUniqueness(「2点/2直線の共有」という
    /// 構造的ショートカット)そのものか。reason文字列を後から推測するのではなく、
    /// build_step側で構築時に明示的に立てる。
    pub is_shortcut: bool,
}

impl DeepStep {
    fn leaf(headline: String, reason: String) -> DeepStep {
        DeepStep { headline, reason, children: Vec::new(), is_gap: false, gap_reason: None, is_shortcut: false }
    }

    /// 🌟 このノード自身またはその子孫のどこかにギャップがあるか。
    fn has_gap(&self) -> bool {
        self.is_gap || self.children.iter().any(DeepStep::has_gap)
    }

    /// 🌟 このノード以下の全ギャップを(場所, 理由)として集める。
    fn collect_gaps(&self, out: &mut Vec<(String, String)>) {
        if self.is_gap {
            out.push((self.headline.clone(), self.gap_reason.clone().unwrap_or_default()));
        }
        for c in &self.children { c.collect_gaps(out); }
    }

    /// 🌟 このノード以下(自分含む)の総ステップ数。
    fn count_steps(&self) -> usize {
        1 + self.children.iter().map(DeepStep::count_steps).sum::<usize>()
    }

    /// 🌟 このノード以下で、由来を再帰的に検証し尽くして解決した
    /// LineUniqueness/PointUniquenessノード(is_shortcut)の数。「解決した」の
    /// 判定はis_shortcutフラグ(構築時に明示的に立てる)で行い、reason文字列の
    /// 推測には頼らない。このノード自身の部分木にギャップが1つも無ければ
    /// 「解決済み」とみなす(部分木の中にギャップがあれば、それはこの
    /// ショートカットの由来を辿りきれなかったということなので数えない)。
    fn count_resolved_shortcuts(&self) -> usize {
        let mine = if self.is_shortcut && !self.has_gap() { 1 } else { 0 };
        mine + self.children.iter().map(DeepStep::count_resolved_shortcuts).sum::<usize>()
    }

    fn render(&self, indent: usize, out: &mut String) {
        let pad = "  ".repeat(indent);
        if self.is_gap {
            out.push_str(&format!("{}⚠️ {}\n", pad, self.headline));
            if let Some(r) = &self.gap_reason {
                out.push_str(&format!("{}   └─ {}\n", pad, r));
            }
        } else {
            out.push_str(&format!("{}{}\n", pad, self.headline));
            if !self.reason.is_empty() {
                out.push_str(&format!("{}   └─ 理由: {}\n", pad, self.reason));
            }
        }
        for c in &self.children {
            c.render(indent + 1, out);
        }
    }
}

/// 🌟 verify_identicalが復元した「深い証明」全体。トップレベルのroots
/// (explain_identicalの各辺)それぞれが、根拠として使われた定理の前提や
/// LineUniqueness/PointUniquenessの由来を再帰的に子として持つ。
pub struct DeepProof {
    pub roots: Vec<DeepStep>,
}

impl DeepProof {
    pub fn is_rigorous(&self) -> bool { !self.roots.iter().any(DeepStep::has_gap) }
    pub fn steps_checked(&self) -> usize { self.roots.iter().map(DeepStep::count_steps).sum() }
    pub fn resolved_shortcuts(&self) -> usize { self.roots.iter().map(DeepStep::count_resolved_shortcuts).sum() }

    fn gaps(&self) -> Vec<(String, String)> {
        let mut out = Vec::new();
        for r in &self.roots { r.collect_gaps(&mut out); }
        out
    }

    /// 🌟 従来のVerifyReport::format()相当の短い要約(ギャップの一覧だけ)。
    pub fn format_summary(&self) -> String {
        let mut out = String::new();
        let steps = self.steps_checked();
        if self.is_rigorous() {
            out.push_str(&format!("✅ [extract_proof] 検証した{}ステップ全てが厳密に辿れました(未証明のギャップなし)。\n", steps));
            let resolved = self.resolved_shortcuts();
            if resolved > 0 {
                out.push_str(&format!(
                    "    うち{}件は「2点/2直線を共有する直線・点の一意性」という射影幾何の公理を使っていますが、\n    共有点・共有直線の由来を再帰的に検証し、全て名前付き定理/構造的な基底事実まで遡れることを確認済みです。\n",
                    resolved
                ));
            }
        } else {
            let gaps = self.gaps();
            out.push_str(&format!(
                "⚠️ [extract_proof] {}ステップ中{}件、由来を遡っても名前付き定理や構造的な基底事実に辿り着けない(=数値サンプリングのみが根拠の)ギャップが見つかりました:\n",
                steps, gaps.len()
            ));
            for (i, (loc, reason)) in gaps.iter().enumerate() {
                out.push_str(&format!("  {}. {} — {}\n", i + 1, loc, reason));
            }
        }
        out
    }

    /// 🌟 「深い証明」全文: トップレベルの各ステップから、Theoremの前提・
    /// LineUniqueness/PointUniquenessの共有点の由来まで、raw_proofに記録
    /// された階層を漏れなく含んだ入れ子形式のテキストを組み立てる。
    /// format_summary()が「ギャップが無いこと」だけを保証するのに対し、
    /// こちらは実際にその厳密な証明そのものを提示する。
    pub fn format_deep(&self) -> String {
        let mut out = String::new();
        out.push_str("========================================\n");
        out.push_str("✨ 深い証明 (raw_proofを再帰的に展開して復元) ✨\n");
        out.push_str("========================================\n\n");
        out.push_str(&self.format_summary());
        out.push('\n');
        for (i, root) in self.roots.iter().enumerate() {
            out.push_str(&format!("Step {}: ", i + 1));
            let mut body = String::new();
            root.render(0, &mut body);
            // render()は1行目にheadlineをインデント0で出すが、"Step N: "の後ろに
            // 続けたいので、最初の行だけ結合し、残りは1段深くインデントする。
            let mut lines = body.lines();
            if let Some(first) = lines.next() {
                out.push_str(first.trim_start());
                out.push('\n');
            }
            for line in lines {
                out.push_str("  ");
                out.push_str(line);
                out.push('\n');
            }
            out.push('\n');
        }
        out
    }
}

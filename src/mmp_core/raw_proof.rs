//! 🌟 raw_proof: e-graph の全マージ履歴(union-find の「証明の森」+ incidence の由来)を、Rust 側で読み書き
//! しやすい単純なテキスト形式でダンプ/復元するモジュール。
//! proof.rs::generate_proof が「目標から遡って実際に使われたステップだけ」を文章にするのに対し、こちらは2段階:
//!   1. `EGraph::dump_raw_proof` — 証明関連の情報(proof_edges, incidence_provenance, 全エンティティの名前/型)を
//!      フィルタせずにテキストへ書き出す(solve.rs が実行のたびに呼ぶ)。
//!   2. `RawProof::parse` + `verify_identical` — 保存したテキストを実行中の EGraph と独立に読み直し、目標の等式から
//!      Theorem の premises まで再帰的に遡って、数値サンプリングや構造的な近似(LineUniqueness/PointUniqueness/Trivial)
//!      だけに頼ったギャップが無いかを監査する。
//! 目標の直接のマージ経路だけを見ると、前提がさらにショートカットに依存しているケースを見逃すので、premises を
//! 再帰的に遡る。テキストに残すので、ソルバーを再実行せずに同じ検証をやり直せる。
//! フォーマット: 依存クレートを増やさない独自の TSV 風形式。先頭の数フィールドだけをタブで分割し、残りは1つの
//! ペイロード文字列にする(前提や定義の文字列にカンマ・コロン・括弧が出てきても区切りに使わないので安全)。
//!   E\t{id}\t{original_name}\t{entity_type}
//!   P\t{from_id}\t{to_id}\t{kind}\t{payload}      (proof_edges 1件)
//!   I\t{a_id}\t{b_id}\t{kind}\t{payload}          (incidence_provenance 1件)
//! kind は Given/Theorem/Congruence/LineUniqueness/PointUniqueness/Trivial のいずれか。payload の中身は
//! encode_justification を参照。

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
        Justification::ConicUniqueness { shared_points } => (
            "ConicUniqueness",
            shared_points.iter().map(|p| p.0.to_string()).collect::<Vec<_>>().join(","),
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
        // 🌟 D行: このIDがcreate_entity時に(一度だけ、以後不変に)持っていた
        // 「元の定義」。type_nameと、その定義自身の引数(=定義された図形自体は
        // 含まない)をダンプする。FreePoint/GivenPointのように引数を持たない
        // 定義は、DefinedBy前提の検索対象になり得ないのでダンプしない。
        // これにより、RawProof側は「あるDefinition(type, args)を最初に持って
        // いた実体はどれか」を(生きているEGraphが無くても)特定できるように
        // なる――extract_proofが「DefinedBy前提は本当は名前付き定理の合流の
        // 産物なのに定義から自明と表示してしまう」問題を、全合流履歴の総当たり
        // ではなくピンポイントな最短経路で解消するための土台。
        for i in 0..self.entities.len() {
            let def = &self.entities[i].original_definition;
            let parents = def.get_parents();
            if parents.is_empty() { continue; }
            let args_str = parents.iter().map(|p| p.0.to_string()).collect::<Vec<_>>().join(",");
            out.push_str(&format!("D\t{}\t{}\t{}\n", i, def.get_type_name(), args_str));
        }
        for (&from, edge) in &self.proof_edges {
            let (kind, payload) = encode_justification(&edge.justification);
            out.push_str(&format!("P\t{}\t{}\t{}\t{}\n", from, edge.to.0, kind, payload));
        }
        for (&(a, b), just) in &self.incidence_provenance {
            let (kind, payload) = encode_justification(just);
            out.push_str(&format!("I\t{}\t{}\t{}\t{}\n", a.0, b.0, kind, payload));
        }
        // 時刻(監査が根拠の順序を確かめる): TE 実体を作った時刻、TP マージした時刻、TL 接続を最初に張った時刻と文脈。
        for (i, t) in self.entity_time.iter().enumerate() {
            out.push_str(&format!("TE\t{}\t{}\n", i, t));
        }
        for (&from, edge) in &self.proof_edges {
            out.push_str(&format!("TP\t{}\t{}\n", from, edge.seq));
        }
        for (&(a, b), &(t, kind)) in &self.incidence_time {
            let k = match kind { super::LinkKind::Definition => "def", super::LinkKind::Premise => "premise", super::LinkKind::Bare => "bare" };
            out.push_str(&format!("TL\t{}\t{}\t{}\t{}\n", a.0, b.0, t, k));
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
    /// 🌟 Definition単位の由来トラッキング: id -> (type_name, 創出時点での引数)。
    /// D行から読み取る。
    original_defs: FxHashMap<usize, (String, Vec<usize>)>,
    /// 🌟 「(type_name, 引数を最終的な代表元まで辿った正準形)」から、それを
    /// 最初に持っていた実体id(複数あり得る)への逆引きインデックス。parse時に
    /// original_defsから一度だけ構築する(canonical_def_key参照)。
    by_definition: FxHashMap<(String, Vec<usize>), Vec<usize>>,
    /// 時刻(TE/TP/TL 行)。無い(古いダンプ)なら時刻つきの監査は使わない。
    ent_time: FxHashMap<usize, u64>,
    edge_time: FxHashMap<usize, u64>,
    /// 接続 (a, b, 時刻, 文脈)。
    links: Vec<(usize, usize, u64, String)>,
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
        let mut original_defs: FxHashMap<usize, (String, Vec<usize>)> = FxHashMap::default();
        let mut ent_time: FxHashMap<usize, u64> = FxHashMap::default();
        let mut edge_time: FxHashMap<usize, u64> = FxHashMap::default();
        let mut links: Vec<(usize, usize, u64, String)> = Vec::new();

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
                "D" => {
                    let (Some(id_s), Some(type_name), Some(args_s)) =
                        (parts.next(), parts.next(), parts.next()) else { continue };
                    let Ok(id) = id_s.parse::<usize>() else { continue };
                    let args: Vec<usize> = args_s.split(',').filter_map(|s| s.parse::<usize>().ok()).collect();
                    original_defs.insert(id, (type_name.to_string(), args));
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
                "TE" | "TP" => {
                    let (Some(a_s), Some(t_s)) = (parts.next(), parts.next()) else { continue };
                    let (Ok(a), Ok(t)) = (a_s.parse::<usize>(), t_s.parse::<u64>()) else { continue };
                    if tag == "TE" { ent_time.insert(a, t); } else { edge_time.insert(a, t); }
                }
                "TL" => {
                    let (Some(a_s), Some(b_s), Some(t_s), Some(k)) = (parts.next(), parts.next(), parts.next(), parts.next()) else { continue };
                    let (Ok(a), Ok(b), Ok(t)) = (a_s.parse::<usize>(), b_s.parse::<usize>(), t_s.parse::<u64>()) else { continue };
                    links.push((a, b, t, k.to_string()));
                }
                _ => {}
            }
        }
        let mut reverse_edges: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
        for (&from, edge) in &proof_edges {
            reverse_edges.entry(edge.to).or_default().push(from);
        }
        let mut proof = RawProof {
            names, name_to_id, proof_edges, reverse_edges, incidence,
            original_defs, by_definition: FxHashMap::default(),
            ent_time, edge_time, links,
        };
        // 🌟 by_definitionインデックスの構築はproof_edges/reverse_edgesが
        // 揃った後でなければfinal_repが正しく計算できないため、ここで最後に行う。
        let mut by_definition: FxHashMap<(String, Vec<usize>), Vec<usize>> = FxHashMap::default();
        for (&id, (type_name, args)) in &proof.original_defs {
            let key = proof.canonical_def_key(type_name, args);
            by_definition.entry(key).or_default().push(id);
        }
        proof.by_definition = by_definition;
        proof
    }

    /// 🌟 idからproof_edgesを辿った最終的な代表元(根)を返す(get_repのraw_proof版、
    /// 経路圧縮なし)。
    fn final_rep(&self, mut id: usize) -> usize {
        let mut guard = 0usize;
        while let Some(edge) = self.proof_edges.get(&id) {
            id = edge.to;
            guard += 1;
            if guard > self.names.len() + 10 { break; }
        }
        id
    }

    /// 🌟 (type_name, 定義自身の引数)を、各引数を最終的な代表元へ正規化した
    /// 「正準形」に変換する。順不同な定義種別(normalize_definition参照:
    /// LineThroughPoints/Midpoint/Intersection/LengthSq/Circumcircleは全引数、
    /// HarmonicConjugateOfは最初の2引数のみ)は、比較可能になるようソートする。
    fn canonical_def_key(&self, type_name: &str, raw_args: &[usize]) -> (String, Vec<usize>) {
        let mut chased: Vec<usize> = raw_args.iter().map(|&a| self.final_rep(a)).collect();
        match type_name {
            "LineThroughPoints" | "Midpoint" | "Intersection" | "LengthSq" if chased.len() == 2 => {
                chased.sort_unstable();
            }
            // 🌟 AnglePairはnormalize_definition上は順序付き(sort対象外)だが、
            // 多くの定理パターンがallow_flip=trueで「D1,D2どちら向きでも良い」
            // としてマッチしているため、この2つのIDが逆順で保存された"元の
            // 定義"を持つ実体を見逃さないよう、探索キーとしては順不同として
            // 扱う(見つかった候補は必ずfinal_rep一致で検証されるため、これに
            // よって誤った――実在しない――合流経路を提示することはない)。
            "AnglePair" if chased.len() == 2 => {
                chased.sort_unstable();
            }
            "Circumcircle" if chased.len() == 3 => {
                chased.sort_unstable();
            }
            // 複比は値を保つ4通りの並べ替え(クラインの4元群)を同じ定義として扱う(normalize_definition と同じ)ので、
            // 並べ替えた形で照合された前提からも元の実体を引けるよう、4通りのうち最小の並びにそろえる。
            "CrossRatio" | "CrossRatioOfLines" if chased.len() == 4 => {
                let (a, b, c, d) = (chased[0], chased[1], chased[2], chased[3]);
                chased = [[a, b, c, d], [b, a, d, c], [c, d, a, b], [d, c, b, a]].into_iter().min().unwrap().to_vec();
            }
            "HarmonicConjugateOf" if chased.len() == 3 => {
                let mut ab = [chased[0], chased[1]];
                ab.sort_unstable();
                chased = vec![ab[0], ab[1], chased[2]];
            }
            _ => {}
        }
        (type_name.to_string(), chased)
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

    /// 🌟 gap(またはノード)の location 文字列を組み立てる。from と edge.to の関係が「等しい」(proof_edges)なら ≡、
    /// 「接続している」(incidence_provenance、点が直線/円に乗っている)なら別の記号で書く。
    fn format_location(&self, from: usize, to: usize, is_incidence: bool) -> String {
        if is_incidence {
            format!("{} は {} に接続", self.name_of(from), self.name_of(to))
        } else {
            format!("{} ≡ {}", self.name_of(from), self.name_of(to))
        }
    }

    /// 🌟 「深い証明」の中核: 1本の辺を DeepStep ツリーへ再帰的に展開する。Given/Congruence/Trivial は子を持たない
    /// 基底ケース。Theorem は premises を子として展開する。LineUniqueness/PointUniqueness(「2点/2直線の共有」)は、
    /// 共有点・共有直線の由来(それ自身のマージ履歴 + incidence_provenance)を子として展開するので、共有による
    /// マージもその根拠まで辿れる。
    /// visited で(種別タグ, 対象id列)を覚えて、同じ前提を何度も展開する無駄と循環を防ぐ(多くの定理が Ang90 絡みの
    /// 前提を共有する)。展開済みの箇所は「(既出、上記で検証済み)」という参照だけの葉にする。
    fn build_step(
        &self,
        from: usize,
        edge: &RawEdge,
        is_incidence: bool,
        visited: &mut Seen,
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
                        // 🌟 fact_type は "DefinedBy:AnglePair" のようにコロンを含むので、最後のコロンで区切る(引数部分はカンマ
                        // 区切りの数字だけなので一意に定まる)。
                        let Some((fact_type, args_str)) = premise.rsplit_once(':') else { continue; };
                        let args: Vec<usize> = args_str.split(',').filter_map(|s| s.parse::<usize>().ok()).collect();
                        children.push(self.build_premise_step(fact_type, &args, visited, depth + 1));
                    }
                }
                DeepStep { headline, reason: format!("定理「{}」", name), children, is_gap: false, gap_reason: None, is_shortcut: false }
            }
            "LineUniqueness" | "ConicUniqueness" | "PointUniqueness" => {
                let ids: Vec<usize> = edge.payload.split(',').filter_map(|s| s.parse().ok()).collect();
                // 🌟 ConicUniquenessはLineUniquenessと全く同じ構造(N点の共有→
                // 同一の図形)なので、対象を表す語("直線"/"円")だけ差し替えて
                // 同じロジックを共有する。
                let (reason, related_lines): (String, Vec<usize>) = if edge.kind == "PointUniqueness" {
                    (format!("直線 {} と直線 {} の交点として一意に定まる", self.name_of(ids.first().copied().unwrap_or(0)), self.name_of(ids.get(1).copied().unwrap_or(0))),
                     ids.clone())
                } else {
                    let obj_word = if edge.kind == "LineUniqueness" { "直線" } else { "円" };
                    (format!("2{}が点({})を共有しているため同一{}", obj_word, ids.iter().map(|&i| self.name_of(i)).collect::<Vec<_>>().join(", "), obj_word),
                     vec![from, edge.to])
                };
                // 🌟 「共有している」という前提の由来を子ノードとして展開する。
                // LineUniqueness/ConicUniquenessならids=共有点、related_lines=2つの図形。
                // PointUniquenessならids=2直線(via_lines)、related_lines=同じ2直線
                // (この場合はfrom/edge.toの側=2点それぞれの接続を調べる)。
                // 🌟 今まさに検証している辺(from, edge.to)自身を除外する
                // (下記build_grounding_stepのexclude参照)。
                let mut children = Vec::new();
                if edge.kind != "PointUniqueness" {
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

    /// 🌟 ある実体(entity)が、これまでにどんな他の実体を吸収して現在の姿に
    /// なったか(=どんな名前付き定理がその過程で使われたか)を子ノードの列
    /// として返す共通処理。(a)この実体自身がさらに別のマージの産物なら
    /// そのマージ履歴(前向きpath_to_root)、(b)逆に「誰がこの実体に合流して
    /// きたか」(reverse_edges)、の両方を辿る。excludeは「今まさに検証して
    /// いる辺」の(from, to)で、これ自身を自分の根拠として再発見してしまう
    /// 循環を防ぐために除外する(呼び出し元が該当する辺を持たない場合は
    /// 存在しないid同士のペアを渡せばよい)。
    fn merge_ancestry_steps(
        &self,
        entity: usize,
        exclude: (usize, usize),
        visited: &mut Seen,
        depth: usize,
    ) -> Vec<DeepStep> {
        let is_excluded = |a: usize, b: usize| (a, b) == exclude || (b, a) == exclude;
        let mut children = Vec::new();
        for (sf, se) in self.path_to_root(entity) {
            if is_excluded(sf, se.to) { continue; }
            children.push(self.build_step(sf, &se, false, visited, depth + 1));
        }
        // 🐛 共有点や DefinedBy の結果として参照される ClassId は、今も代表元であり続けている側であることが多く、
        // path_to_root(前向き)では何も出ない。誰がこの実体に合流してきたかを reverse_edges で辿って、その経緯
        // (別の方向が定理のチェーンでこの方向に合流した、など)を拾う。
        if let Some(sources) = self.reverse_edges.get(&entity) {
            for &src in sources {
                if is_excluded(src, entity) { continue; }
                let edge_key = ("REVEDGE".to_string(), vec![src, entity]);
                if !matches!(visited.enter(edge_key.clone()), Enter::New) { continue; }
                if let Some(edge) = self.proof_edges.get(&src) {
                    children.push(self.build_step(src, edge, false, visited, depth + 1));
                }
                visited.finish(edge_key);
            }
        }
        children
    }

    /// 🌟 LineUniqueness/PointUniquenessが「共有している」とみなした1つの点
    /// (またはPointUniquenessの場合は2点それぞれ)について、(a)それ自身の
    /// 合流履歴(merge_ancestry_steps)、(b)関係する直線それぞれへの接続の
    /// 由来、をまとめて1つの子ノードにする。
    fn build_grounding_step(
        &self,
        entity: usize,
        lines: &[usize],
        exclude: (usize, usize),
        visited: &mut Seen,
        depth: usize,
    ) -> DeepStep {
        let key = ("GROUND".to_string(), { let mut v = vec![entity]; v.extend_from_slice(lines); v });
        // 見出しに対象の直線も入れる(別の直線の組での「同じ点の由来」を、圧縮した証明が同じステップとみなさないように)。
        let headline = format!("{} の由来({} の共有点)", self.name_of(entity),
            lines.iter().map(|&l| self.name_of(l)).collect::<Vec<_>>().join("・"));
        match visited.enter(key.clone()) {
            Enter::Done => return DeepStep::seen_before(headline),
            Enter::Open => return DeepStep::cycle(headline),
            Enter::New => {}
        }
        let mut children = self.merge_ancestry_steps(entity, exclude, visited, depth);
        // (b) 関係する直線それぞれへの接続の由来。記録が無ければ、作図時点の
        // 構造的な接続(定義から機械的に従う)として基底ケース扱いする。
        for &line in lines {
            let key = if entity < line { (entity, line) } else { (line, entity) };
            let sub_headline = format!("{} は {} に接続", self.name_of(entity), self.name_of(line));
            match self.incidence.get(&key) {
                Some(inc_edge) => children.push(self.build_step(key.0, inc_edge, true, visited, depth + 1)),
                None => children.push(self.build_structural_incidence_step(entity, line, sub_headline, exclude, visited, depth + 1)),
            }
        }
        visited.finish(key);
        DeepStep { headline, reason: "共有点/共有直線としての由来".to_string(), children, is_gap: false, gap_reason: None, is_shortcut: false }
    }

    /// 🌟 接続の由来が incidence に記録されていない場合の基底ケース。「作図時点の構造的な接続」として葉にしてよいのは、
    /// 問われている直線・円そのものが定義上その点を通る場合だけ。定義上その点を通る別の実体が後から合流したのなら、
    /// その合流(名前付き定理の仕事)を展開する ― 基底扱いにすると証明の本体が消える(orthocenter では垂心定理の本体が
    /// 消えたまま「全て厳密」と報告していた)。
    fn build_structural_incidence_step(
        &self,
        entity: usize,
        line: usize,
        headline: String,
        exclude: (usize, usize),
        visited: &mut Seen,
        depth: usize,
    ) -> DeepStep {
        let (re, rl) = (self.final_rep(entity), self.final_rep(line));
        let is_excluded = |a: usize, b: usize| (a, b) == exclude || (b, a) == exclude;
        // 定義が「この接続」を直に持つ実体 o と、その定義中の該当引数 a を探す。
        // o が器の側なら (a ≡ 点) と (o ≡ 器)、o が点の側なら (o ≡ 点) と (a ≡ 器)
        // が橋渡しになる。id が一致する橋渡しは不要(本当に構造的)。
        let mut best: Option<(usize, usize, Vec<(usize, usize)>)> = None;
        for (&o, (_, args)) in self.original_defs.iter() {
            let ro = self.final_rep(o);
            let owner_is_container = ro == rl;
            if !owner_is_container && ro != re { continue; }
            for &a in args {
                let ra = self.final_rep(a);
                let bridges: Vec<(usize, usize)> = if owner_is_container {
                    if ra != re { continue; }
                    [(a, entity), (o, line)].into_iter().filter(|&(x, y)| x != y).collect()
                } else {
                    if ra != rl { continue; }
                    [(o, entity), (a, line)].into_iter().filter(|&(x, y)| x != y).collect()
                };
                // 🌟 いま検証中の辺そのものを根拠にすると循環する
                // (実際、これを見落として「証明したい等式」で接続を
                // 正当化する出力が出た)。
                if bridges.iter().any(|&(x, y)| is_excluded(x, y)) { continue; }
                // 橋渡しが少ないものを優先し、同数なら id で決定的に選ぶ。
                let better = match &best {
                    None => true,
                    Some((bo, ba, bb)) => (bridges.len(), o, a) < (bb.len(), *bo, *ba),
                };
                if better { best = Some((o, a, bridges)); }
            }
        }
        let Some((o, _a, bridges)) = best else {
            return DeepStep::leaf(headline, "由来の明示的な記録なし(作図時点の構造的な接続として、定義から機械的に従う)".to_string());
        };
        if bridges.is_empty() {
            return DeepStep::leaf(headline, "作図時点の構造的な接続(定義から機械的に従う)".to_string());
        }
        let key = ("STRUCT_INC".to_string(), vec![entity, line, o]);
        match visited.enter(key.clone()) {
            Enter::Done => return DeepStep::seen_before(headline),
            Enter::Open => return DeepStep::cycle(headline),
            Enter::New => {}
        }
        let mut children = Vec::new();
        for (x, y) in &bridges {
            match self.explain(*x, *y) {
                Some(edges) => {
                    for (f, e) in edges {
                        children.push(self.build_step(f, &e, false, visited, depth + 1));
                    }
                }
                None => children.push(DeepStep {
                    headline: format!("{} ≡ {}", self.name_of(*x), self.name_of(*y)),
                    reason: String::new(),
                    children: Vec::new(),
                    is_gap: true,
                    gap_reason: Some("この2つが合流する経路がraw_proof中に見つかりませんでした".to_string()),
                    is_shortcut: false,
                }),
            }
        }
        visited.finish(key);
        DeepStep {
            headline,
            reason: format!("{} の定義がこの接続を直に持ち、あとは{}",
                self.name_of(o),
                bridges.iter()
                    .map(|&(x, y)| format!("{} ≡ {}", self.name_of(x), self.name_of(y)))
                    .collect::<Vec<_>>().join(" かつ ")),
            children,
            is_gap: false,
            gap_reason: None,
            is_shortcut: false,
        }
    }

    /// 🌟 DefinedBy 前提の結果や Identical(X,X) のように「既に同じ実体を指している」前提は、自明な基底事実に見えて、
    /// 実際にはその実体が名前付き定理で他の実体を吸収してきた結果として成り立っていることが多い。この実体の
    /// merge_ancestry_steps(合流してきた履歴)を子として展開し、合流履歴が無いときだけ自明な基底事実として扱う。
    /// ⚠️ 精度の限界: どの定義がどの合流で加わったかまでは記録していないので、合流履歴が複数あれば全て列挙する
    /// (この引数の組と無関係な合流が混ざりうる)。それでも一律に「定義から従う」とするよりは正直な提示になる。
    fn build_result_ancestry_step(
        &self,
        entity: usize,
        headline: String,
        visited: &mut Seen,
        depth: usize,
    ) -> DeepStep {
        let key = ("RESULT_ANCESTRY".to_string(), vec![entity]);
        match visited.enter(key.clone()) {
            Enter::Done => return DeepStep::seen_before(headline),
            Enter::Open => return DeepStep::cycle(headline),
            Enter::New => {}
        }
        let ancestry = self.merge_ancestry_steps(entity, (usize::MAX, usize::MAX), visited, depth);
        visited.finish(key);
        if ancestry.is_empty() {
            DeepStep::leaf(headline, "構造的な基底事実(定義から機械的に従う。この実体が他の実体を吸収した履歴はありません)".to_string())
        } else {
            DeepStep {
                headline,
                reason: format!(
                    "{} にこれまで合流してきた実体の履歴により成立(⚠️ この特定の組み合わせと無関係な合流が混在する可能性があります)",
                    self.name_of(entity)
                ),
                children: ancestry,
                is_gap: false,
                gap_reason: None,
                is_shortcut: false,
            }
        }
    }

    /// 🌟 Definition 単位の由来(by_definition 索引)を使い、DefinedBy 前提を「result の合流履歴の総当たり」ではなく
    /// 「この引数の組を最初に持っていた実体1つ + そこから result への最短合流経路」に絞る。各実体の元の定義は
    /// create_entity 時に確定する不変情報なので、そこから逆引きできる。
    /// fact_type が "DefinedBy:{type_name}" の形でない場合は build_result_ancestry_step にフォールバックする。
    fn build_defined_by_step(
        &self,
        fact_type: &str,
        args: &[usize],
        headline: String,
        visited: &mut Seen,
        depth: usize,
    ) -> DeepStep {
        let result_id = *args.last().unwrap();
        let Some((_, type_name)) = fact_type.split_once(':') else {
            return self.build_result_ancestry_step(result_id, headline, visited, depth);
        };
        let def_args = &args[..args.len() - 1];
        let key = self.canonical_def_key(type_name, def_args);
        let result_final = self.final_rep(result_id);
        // このDefinitionを最初に持っていた実体のうち、resultと同じ最終代表元に
        // 合流しているものを探す(複数あり得るが、診断ツールとしては最初の
        // 1件で十分――どれを選んでも「本当にこの定義からresultへ辿り着ける」
        // という結論自体は変わらない)。
        let origin = self.by_definition.get(&key).and_then(|ids| {
            ids.iter().copied().find(|&oid| self.final_rep(oid) == result_final)
        });
        match origin {
            None => {
                // 見つからない場合(正規化の想定漏れ等)は、安全側に倒して
                // 従来のresult全体の合流履歴を提示する。
                self.build_result_ancestry_step(result_id, headline, visited, depth)
            }
            Some(origin_id) if origin_id == result_id => {
                // resultはこの定義そのもので作られた実体自身(他実体からの
                // 合流を一切経ていない)。正真正銘の基底事実。
                DeepStep::leaf(headline, format!(
                    "{} はこの定義そのもので作られた実体自身であり、他の実体からの合流を経ていません(基底事実)",
                    self.name_of(result_id)
                ))
            }
            Some(origin_id) => {
                let ground_key = ("DEFORIGIN".to_string(), vec![origin_id, result_id]);
                match visited.enter(ground_key.clone()) {
                    Enter::Done => return DeepStep::seen_before(headline),
                    Enter::Open => return DeepStep::cycle(headline),
                    Enter::New => {}
                }
                match self.explain(origin_id, result_id) {
                    Some(sub_edges) if !sub_edges.is_empty() => {
                        let children: Vec<DeepStep> = sub_edges.iter()
                            .map(|(sf, se)| self.build_step(*sf, se, false, visited, depth + 1))
                            .collect();
                        visited.finish(ground_key);
                        DeepStep {
                            headline,
                            reason: format!(
                                "{} が元々この定義で作られており、以下の経路で {} に合流した",
                                self.name_of(origin_id), self.name_of(result_id)
                            ),
                            children, is_gap: false, gap_reason: None, is_shortcut: false,
                        }
                    }
                    // final_repが一致していればexplainも非空の経路を返すはずだが
                    // (理論上到達しないはずの)保険としてancestryへ委譲する。
                    _ => self.build_result_ancestry_step(result_id, headline, visited, depth),
                }
            }
        }
    }

    /// 🌟 Theoremのpremises 1件をDeepStepへ展開する。Identicalは合流経路を
    /// (両辺が既に同じ実体を指す場合は自明な基底事実として)、Connectedは
    /// incidence_provenanceの由来を再帰的に辿る。DefinedByはbuild_defined_by_step
    /// でDefinition単位の由来をピンポイントに辿る。
    fn build_premise_step(
        &self,
        fact_type: &str,
        args: &[usize],
        visited: &mut Seen,
        depth: usize,
    ) -> DeepStep {
        let arg_names: Vec<String> = args.iter().map(|&a| self.name_of(a)).collect();
        let headline = format!("前提 {}({})", fact_type, arg_names.join(", "));
        let mut key_args = args.to_vec();
        key_args.sort_unstable();
        let key = (format!("F:{}", fact_type), key_args);
        match visited.enter(key.clone()) {
            Enter::Done => return DeepStep::seen_before(headline),
            Enter::Open => return DeepStep::cycle(headline),
            Enter::New => {}
        }
        let step = match fact_type {
            // 🌟 Identical(X,X): 既に同じ実体(id)を指している場合、その実体が
            // なぜ「この役割」を持つに至ったか(=どのDefinedBy前提の合流の
            // 産物か)は、隣接するDefinedBy前提側(build_defined_by_step)が
            // Definition単位でピンポイントに説明する。ここで同じ話を(resultの
            // 合流履歴を丸ごと辿って)重複表示すると証明が不必要に長くなる
            // だけなので、単なる自明な基底事実として扱う。
            "Identical" if args.len() == 2 && args[0] == args[1] => {
                DeepStep::leaf(headline, "同一の実体を指しているため自明(この実体がどう定義されたかは隣接するDefinedBy前提を参照)".to_string())
            }
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
                    // 🌟 由来が記録されていない Connected は、定義がこの接続を直に持つ実体まで戻り、そこからの合流を展開する
                    // (共有点の由来と同じ扱い)。一律に「作図時点の接続」とすると、マージを経て初めて成り立つ接続の根拠が消える。
                    None => self.build_structural_incidence_step(args[0], args[1], headline, (usize::MAX, usize::MAX), visited, depth + 1),
                }
            }
            // 🌟 DefinedBy(引数..., 結果): 最後の引数が「定義された図形そのもの」
            // (AnglePair/Midpoint/DirectionOfなど、いずれもpatternの最後の要素)。
            // build_defined_by_stepがDefinition単位の由来索引(by_definition)を
            // 使い、「この定義を最初に持っていた実体からresultへの最短経路」
            // だけをピンポイントに辿る――これにより「見た目は定義から自明だが
            // 実際には円周角の定理・有向角の交替律などの合流の産物」という
            // ケースを、resultの全合流履歴を総当たりで列挙することなく可視化する。
            _ if (fact_type == "DefinedBy" || fact_type.starts_with("DefinedBy:")) && !args.is_empty() => {
                self.build_defined_by_step(fact_type, args, headline, visited, depth + 1)
            }
            _ => DeepStep::leaf(headline, "構造的な基底事実(定義から機械的に従う)".to_string()),
        };
        visited.finish(key);
        step
    }

    /// 🌟 aとbが本当にrigorousな経路(Given/Theorem/Congruence/Trivialの連鎖、
    /// かつTheoremの前提・LineUniqueness/PointUniquenessの由来も再帰的に
    /// rigorous)だけで合流しているかを検証し、その全経路を保持した
    /// DeepProofを返す。
    pub fn verify_identical(&self, a: usize, b: usize) -> DeepProof {
        let mut visited = Seen::default();
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

/// 深い証明を組み立てるときに、展開した主張(種別タグ, 対象id列)を覚える。検証を終えたもの(再び出たら「既出」)と、
/// いま検証している祖先(再び出たら説明の循環)を区別する ― 区別しないと、自分の主張を根拠にした説明を「既出・検証済み」
/// として素通りさせる(pappus の監査で見つかった)。
#[derive(Default)]
pub(crate) struct Seen {
    state: std::collections::HashMap<(String, Vec<usize>), bool>,
}

enum Enter { New, Done, Open }

impl Seen {
    fn enter(&mut self, key: (String, Vec<usize>)) -> Enter {
        match self.state.get(&key) {
            Some(true) => Enter::Done,
            Some(false) => Enter::Open,
            None => { self.state.insert(key, false); Enter::New }
        }
    }
    fn finish(&mut self, key: (String, Vec<usize>)) { self.state.insert(key, true); }
}

impl DeepStep {
    fn seen_before(headline: String) -> DeepStep {
        DeepStep::leaf(headline, "(既出: 上記で検証済みなので省略)".to_string())
    }
    fn cycle(headline: String) -> DeepStep {
        DeepStep {
            headline, children: Vec::new(),
            reason: "(循環: いま検証している祖先の主張を根拠にしている)".to_string(),
            is_gap: true,
            gap_reason: Some("説明が循環している(この前提は、まだ検証を終えていない祖先の主張に依存する)".to_string()),
            is_shortcut: false,
        }
    }
}

/// 時刻つきの監査の途中状態。主張ごとに「成り立った最も早い時刻」を覚え、検証中の祖先の参照は循環として報告する。
struct Timed<'a> {
    raw: &'a RawProof,
    memo: std::collections::HashMap<(String, Vec<usize>), Option<u64>>,
    rep: FxHashMap<usize, usize>,
    /// 接続を、両端の最終的な代表元の組(小さい方, 大きい方)で引く: (a, b, 時刻, 文脈)。
    link_index: FxHashMap<(usize, usize), Vec<(usize, usize, u64, String)>>,
}

impl<'a> Timed<'a> {
    fn new(raw: &'a RawProof) -> Self {
        let mut rep = FxHashMap::default();
        for &id in raw.names.keys() { rep.insert(id, raw.final_rep(id)); }
        let mut link_index: FxHashMap<(usize, usize), Vec<(usize, usize, u64, String)>> = FxHashMap::default();
        for (a, b, t, k) in &raw.links {
            let (ra, rb) = (raw.final_rep(*a), raw.final_rep(*b));
            link_index.entry((ra.min(rb), ra.max(rb))).or_default().push((*a, *b, *t, k.clone()));
        }
        Timed { raw, memo: Default::default(), rep, link_index }
    }

    fn frep(&self, id: usize) -> usize { self.rep.get(&id).copied().unwrap_or_else(|| self.raw.final_rep(id)) }

    /// a から b への合流経路(最小共通祖先まで)。辺は (from, 辺, 時刻)。つながっていなければ None。
    fn lca_path(&self, a: usize, b: usize) -> Option<Vec<(usize, RawEdge, u64)>> {
        if a == b { return Some(Vec::new()); }
        let up = |mut x: usize| -> Vec<(usize, RawEdge)> {
            let mut v = Vec::new();
            let mut guard = 0usize;
            while let Some(e) = self.raw.proof_edges.get(&x) { v.push((x, e.clone())); x = e.to; guard += 1; if guard > self.raw.names.len() + 10 { break; } }
            v
        };
        let (pa, pb) = (up(a), up(b));
        let root = |p: &Vec<(usize, RawEdge)>, x: usize| p.last().map(|(_, e)| e.to).unwrap_or(x);
        if root(&pa, a) != root(&pb, b) { return None; }
        // a 側の祖先の位置。
        let mut pos: FxHashMap<usize, usize> = FxHashMap::default();
        pos.insert(a, 0);
        for (i, (_, e)) in pa.iter().enumerate() { pos.insert(e.to, i + 1); }
        let mut from_b = Vec::new();
        let mut x = b;
        let mut k = 0usize;
        while !pos.contains_key(&x) { let (f, e) = pb[k].clone(); x = e.to; from_b.push((f, e)); k += 1; }
        let lca_pos = pos[&x];
        let t = |f: usize| self.raw.edge_time.get(&f).copied().unwrap_or(0);
        let mut out: Vec<(usize, RawEdge, u64)> = pa[..lca_pos].iter().map(|(f, e)| (*f, e.clone(), t(*f))).collect();
        for (f, e) in from_b.into_iter().rev() {
            let tf = t(f);
            out.push((e.to, RawEdge { to: f, kind: e.kind, payload: e.payload }, tf));
        }
        Some(out)
    }

    fn path_time(&self, a: usize, b: usize) -> Option<u64> {
        self.lca_path(a, b).map(|p| p.iter().map(|(_, _, t)| *t).max().unwrap_or(0))
    }

    /// 主張の記憶: Some(t) なら済み(時刻 t)、None なら検証中。
    fn enter(&mut self, key: &(String, Vec<usize>), headline: &str) -> Result<(), (u64, DeepStep)> {
        match self.memo.get(key) {
            Some(Some(t)) => Err((*t, DeepStep::seen_before(headline.to_string()))),
            Some(None) => Err((0, DeepStep::cycle(headline.to_string()))),
            None => { self.memo.insert(key.clone(), None); Ok(()) }
        }
    }

    /// 前提(時刻 t)を、時刻 seq のステップの根拠として使えるか確かめる。
    fn before(step: DeepStep, t: u64, seq: u64) -> DeepStep {
        if t < seq || step.is_gap { return step; }
        DeepStep {
            headline: step.headline.clone(), reason: String::new(), children: vec![step], is_gap: true,
            gap_reason: Some(format!("時刻の逆転: この前提が成り立ったのは時刻 {} で、これを使ったステップ(時刻 {})より後", t, seq)),
            is_shortcut: false,
        }
    }

    fn identical(&mut self, a: usize, b: usize) -> (u64, Vec<DeepStep>) {
        match self.lca_path(a, b) {
            None => (0, vec![DeepStep {
                headline: format!("{} ≡ {}", self.raw.name_of(a), self.raw.name_of(b)), reason: String::new(), children: Vec::new(),
                is_gap: true, gap_reason: Some("raw_proof中にこの2つが合流する経路が見つかりません".to_string()), is_shortcut: false,
            }]),
            Some(path) => {
                let t = path.iter().map(|(_, _, t)| *t).max().unwrap_or(0);
                (t, path.into_iter().map(|(f, e, seq)| self.edge_step(f, &e, seq, false)).collect())
            }
        }
    }

    /// マージ(または理由つきの接続)1本。前提はこの時刻 seq より前に成り立っていなければならない。
    fn edge_step(&mut self, from: usize, edge: &RawEdge, seq: u64, is_incidence: bool) -> DeepStep {
        let headline = self.raw.format_location(from, edge.to, is_incidence);
        let key = (if is_incidence { "EI" } else { "E" }.to_string(), vec![from, edge.to]);
        if let Err((_, step)) = self.enter(&key, &headline) { return step; }
        let step = match edge.kind.as_str() {
            "Given" => DeepStep::leaf(headline, "問題の初期条件(前提)として与えられている".to_string()),
            "Congruence" => DeepStep::leaf(headline, format!("合同閉包: どちらも {} として定義される", edge.payload)),
            "Trivial" => DeepStep::leaf(headline, format!("定義から機械的に従う構造的な事実: {}", edge.payload)),
            "Theorem" => {
                let (name, premises_str) = edge.payload.split_once('|').unwrap_or((edge.payload.as_str(), ""));
                let mut children = Vec::new();
                for premise in premises_str.split(';').filter(|x| !x.is_empty()) {
                    let Some((fact_type, args_str)) = premise.rsplit_once(':') else { continue };
                    let args: Vec<usize> = args_str.split(',').filter_map(|x| x.parse::<usize>().ok()).collect();
                    let (t, st) = self.premise(fact_type, &args);
                    children.push(Self::before(st, t, seq));
                }
                DeepStep { headline, reason: format!("定理「{}」", name), children, is_gap: false, gap_reason: None, is_shortcut: false }
            }
            "LineUniqueness" | "ConicUniqueness" | "PointUniqueness" => {
                let ids: Vec<usize> = edge.payload.split(',').filter_map(|x| x.parse().ok()).collect();
                let mut children = Vec::new();
                let reason = if edge.kind == "PointUniqueness" {
                    let (l1, l2) = (ids.first().copied().unwrap_or(0), ids.get(1).copied().unwrap_or(0));
                    for pt in [from, edge.to] {
                        for l in [l1, l2] { let (t, st) = self.incidence(pt, l); children.push(Self::before(st, t, seq)); }
                    }
                    format!("直線 {} と直線 {} の交点として一意に定まる", self.raw.name_of(l1), self.raw.name_of(l2))
                } else {
                    for &pt in &ids {
                        for obj in [from, edge.to] { let (t, st) = self.incidence(pt, obj); children.push(Self::before(st, t, seq)); }
                    }
                    let w = if edge.kind == "LineUniqueness" { "直線" } else { "円" };
                    format!("2{}が点({})を共有しているため同一{}", w, ids.iter().map(|&i| self.raw.name_of(i)).collect::<Vec<_>>().join(", "), w)
                };
                DeepStep { headline, reason, children, is_gap: false, gap_reason: None, is_shortcut: true }
            }
            other => DeepStep { headline, reason: format!("未知の理由の種類「{}」", other), children: Vec::new(), is_gap: true,
                gap_reason: Some("raw_proofの形式が想定外です".to_string()), is_shortcut: false },
        };
        self.memo.insert(key, Some(seq));
        step
    }

    fn premise(&mut self, fact_type: &str, args: &[usize]) -> (u64, DeepStep) {
        let headline = format!("前提 {}({})", fact_type, args.iter().map(|&a| self.raw.name_of(a)).collect::<Vec<_>>().join(", "));
        match fact_type {
            "Identical" if args.len() == 2 && args[0] == args[1] =>
                (0, DeepStep::leaf(headline, "同一の実体を指しているため自明".to_string())),
            "Identical" if args.len() == 2 => {
                let mut k = args.to_vec(); k.sort_unstable();
                let key = ("I".to_string(), k);
                if let Err(r) = self.enter(&key, &headline) { return r; }
                let (t, children) = self.identical(args[0], args[1]);
                self.memo.insert(key, Some(t));
                (t, DeepStep { headline, reason: "以下の合流経路で成立".to_string(), children, is_gap: false, gap_reason: None, is_shortcut: false })
            }
            "Connected" if args.len() == 2 => self.incidence(args[0], args[1]),
            _ if fact_type.starts_with("DefinedBy:") && !args.is_empty() => self.defined_by(&fact_type["DefinedBy:".len()..], args, headline),
            _ => (0, DeepStep::leaf(headline, "構造的な基底事実(定義から機械的に従う)".to_string())),
        }
    }

    /// 点(または曲線)p が曲線 c に乗る: 記録された接続 (x, y) のうち、p ≡ x・c ≡ y の合流も含めて最も早く成り立つものを使う。
    fn incidence(&mut self, p: usize, c: usize) -> (u64, DeepStep) {
        let headline = format!("{} は {} に接続", self.raw.name_of(p), self.raw.name_of(c));
        let key = ("C".to_string(), vec![p.min(c), p.max(c)]);
        if let Err(r) = self.enter(&key, &headline) { return r; }
        let (rp, rc) = (self.frep(p), self.frep(c));
        let cands = self.link_index.get(&(rp.min(rc), rp.max(rc))).cloned().unwrap_or_default();
        let mut best: Option<(u64, usize, usize, u64, String)> = None;
        for (a, b, t, k) in cands {
            let (x, y) = if self.frep(a) == rp && self.frep(b) == rc { (a, b) } else { (b, a) };
            let (Some(tx), Some(ty)) = (self.path_time(p, x), self.path_time(c, y)) else { continue };
            let time = t.max(tx).max(ty);
            if best.as_ref().is_none_or(|bst| time < bst.0) { best = Some((time, x, y, t, k)); }
        }
        let Some((time, x, y, t, kind)) = best else {
            let step = DeepStep { headline, reason: String::new(), children: Vec::new(), is_gap: true,
                gap_reason: Some("この接続を張った記録が見つかりません".to_string()), is_shortcut: false };
            self.memo.insert(key, Some(0));
            return (0, step);
        };
        let mut children = Vec::new();
        if x != p { let (_, st) = self.identical(p, x); children.extend(st); }
        if y != c { let (_, st) = self.identical(c, y); children.extend(st); }
        let lkey = if x < y { (x, y) } else { (y, x) };
        let link_step = match self.raw.incidence.get(&lkey).cloned() {
            Some(e) => self.edge_step(lkey.0, &e, t, true),
            None => {
                let h = format!("{} は {} に接続", self.raw.name_of(x), self.raw.name_of(y));
                match kind.as_str() {
                    "def" => DeepStep::leaf(h, "作図時点の構造的な接続(定義から機械的に従う)".to_string()),
                    "premise" => DeepStep::leaf(h, "問題の前提(探索の前に張った接続)".to_string()),
                    _ => DeepStep { headline: h, reason: String::new(), children: Vec::new(), is_gap: true,
                        gap_reason: Some("理由の記録が無い接続(定義でも問題の前提でもない)".to_string()), is_shortcut: false },
                }
            }
        };
        children.push(link_step);
        self.memo.insert(key, Some(time));
        (time, DeepStep { headline, reason: "以下の由来で成立".to_string(), children, is_gap: false, gap_reason: None, is_shortcut: false })
    }

    /// DefinedBy:型(引数..., 結果): その定義を元々持っていた実体 o と、引数・結果への合流。最も早いものを使う。
    fn defined_by(&mut self, type_name: &str, args: &[usize], headline: String) -> (u64, DeepStep) {
        let key = (format!("D:{}", type_name), args.to_vec());
        if let Err(r) = self.enter(&key, &headline) { return r; }
        let (def_args, result) = (&args[..args.len() - 1], args[args.len() - 1]);
        let ck = self.raw.canonical_def_key(type_name, def_args);
        let origins = self.raw.by_definition.get(&ck).cloned().unwrap_or_default();
        let mut best: Option<(u64, usize, Vec<(usize, usize)>)> = None;
        for o in origins {
            if self.frep(o) != self.frep(result) { continue; }
            let Some((_, oargs)) = self.raw.original_defs.get(&o).cloned() else { continue };
            // 引数の対応(最終的な代表元が同じもの同士。順不同の定義もあるので貪欲に組む)。
            let mut used = vec![false; oargs.len()];
            let mut bridges = vec![(o, result)];
            let mut ok = true;
            for &a in def_args {
                match (0..oargs.len()).find(|&j| !used[j] && self.frep(oargs[j]) == self.frep(a)) {
                    Some(j) => { used[j] = true; bridges.push((oargs[j], a)); }
                    None => { ok = false; break; }
                }
            }
            if !ok { continue; }
            let mut time = self.raw.ent_time.get(&o).copied().unwrap_or(0);
            for &(x, y) in &bridges { match self.path_time(x, y) { Some(t) => time = time.max(t), None => { ok = false; break; } } }
            if !ok { continue; }
            if best.as_ref().is_none_or(|bst| time < bst.0) { best = Some((time, o, bridges)); }
        }
        let Some((time, o, bridges)) = best else {
            // 定義を元々持つ実体が無い(memo に後から登録された定義など)。時刻は確かめられない。
            self.memo.insert(key, Some(0));
            return (0, DeepStep { headline, reason: String::new(), children: Vec::new(), is_gap: true,
                gap_reason: Some("この定義を元々持っていた実体が見つからない(定義の由来を確かめられない)".to_string()), is_shortcut: false });
        };
        let mut children = Vec::new();
        for (x, y) in bridges { if x != y { let (_, st) = self.identical(x, y); children.extend(st); } }
        self.memo.insert(key, Some(time));
        let reason = if children.is_empty() {
            format!("{} はこの定義そのもので作られた実体(基底事実)", self.raw.name_of(o))
        } else {
            format!("{} が元々この定義で作られており、以下の合流で引数・結果につながる", self.raw.name_of(o))
        };
        (time, DeepStep { headline, reason, children, is_gap: false, gap_reason: None, is_shortcut: false })
    }
}

impl RawProof {
    /// 時刻(TE/TP/TL 行)を持つダンプか。
    pub fn has_times(&self) -> bool { !self.edge_time.is_empty() || !self.links.is_empty() }

    /// 時刻つきの監査: 目標の等式の合流経路から前提を再帰的にたどり、各ステップの前提がそのステップより前に成り立っていたか、
    /// 説明が循環していないかも確かめる(verify_identical は探索の終わりの図から根拠を選ぶので、後からできた事実で
    /// 前のマージを説明して循環することがあった)。
    pub fn verify_identical_timed(&self, a: usize, b: usize) -> DeepProof {
        let mut tm = Timed::new(self);
        let (_, roots) = tm.identical(a, b);
        DeepProof { roots }
    }

    /// 接続・共円の目標の時刻つき監査。
    pub fn verify_incidences_timed(&self, pairs: &[(usize, usize)]) -> DeepProof {
        let mut tm = Timed::new(self);
        DeepProof { roots: pairs.iter().map(|&(p, c)| tm.incidence(p, c).1).collect() }
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

/// 🌟 エンティティ名に付いた "_(Auto)"/"_(Demand)" ラベルを取り除く(入れ子になっていても replace 1回で全て消える)。
/// 証明を読みやすくするための整形だけで、ClassId は変わらないので曖昧さは生じない(重複排除のキーには使わない)。
fn clean_label(s: &str) -> String {
    s.replace("_(Auto)", "").replace("_(Demand)", "")
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

    /// 🌟 compressed_proof: (Auto)/(Demand) ラベルを除き、前提から結論へ上から順に書き、既に示した事実の重複を省く。
    /// format_deep は目標始点の入れ子構造なので、その木を post-order(前提を先に、結論を後に)で辿って1本のステップ列に
    /// 平坦化する。同じ headline のノードが複数箇所に現れたら(既出プレースホルダも含む)、新しいステップを作らずに
    /// 既存のステップ番号への参照(「Step N より」)にする。
    pub fn format_compressed(&self) -> String {
        let mut out = String::new();
        out.push_str("========================================\n");
        out.push_str("✨ 圧縮された証明 (前提→結論の順、重複ステップは参照に置換) ✨\n");
        out.push_str("========================================\n\n");

        let mut seen: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
        let mut steps: Vec<String> = Vec::new();
        for root in &self.roots {
            Self::flatten_step(root, &mut seen, &mut steps);
        }

        for (i, s) in steps.iter().enumerate() {
            out.push_str(&format!("Step {:2}: {}\n\n", i + 1, s));
        }
        if steps.is_empty() {
            out.push_str("(ステップがありません)\n");
        }
        out
    }

    /// 🌟 format_compressedの中核。DeepStep木を1つ、post-order(子が先、
    /// 自分が後)で辿り、まだ登場していなければstepsに1行追加してその
    /// ステップ番号(1始まり)を返す。既に同じheadlineのステップがあれば
    /// (「(既出...)」プレースホルダ経由も含め)新規に追加せずそのステップ
    /// 番号だけを返す――呼び出し元(親ノード)はこれを「Step N より」という
    /// 参照として使う。
    ///
    /// 重複判定のキーには(表示用にAuto/Demandラベルを除去する前の)生の
    /// headlineを使う。「既出」プレースホルダは元のノードとbuild_*側で全く
    /// 同じ組み立て方でheadlineを作ってから生成されるため、ラベル除去前の
    /// 文字列同士は必ず一致する。
    fn flatten_step(
        node: &DeepStep,
        seen: &mut std::collections::HashMap<String, usize>,
        steps: &mut Vec<String>,
    ) -> Option<usize> {
        if node.reason.starts_with("(既出") {
            // このノード自体は実体を持たない参照プレースホルダ。対応する
            // 本物のステップは(木の構築順の性質上)既にseenへ登録済みのはず。
            return seen.get(&node.headline).copied();
        }
        if let Some(&idx) = seen.get(&node.headline) {
            return Some(idx);
        }
        let mut child_refs: Vec<usize> = Vec::new();
        for c in &node.children {
            if let Some(idx) = Self::flatten_step(c, seen, steps)
                && !child_refs.contains(&idx) { child_refs.push(idx); }
        }
        let headline = clean_label(&node.headline);
        let line = if node.is_gap {
            format!("⚠️ {} — {}", headline, clean_label(&node.gap_reason.clone().unwrap_or_default()))
        } else {
            let reason = clean_label(&node.reason);
            let refs = if child_refs.is_empty() {
                String::new()
            } else {
                format!(" (Step {} より)", child_refs.iter().map(|n| n.to_string()).collect::<Vec<_>>().join(", "))
            };
            if reason.is_empty() {
                format!("{}{}", headline, refs)
            } else {
                format!("{} — {}{}", headline, reason, refs)
            }
        };
        steps.push(line);
        let idx = steps.len();
        seen.insert(node.headline.clone(), idx);
        Some(idx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 🌟 orthocenter の検証で判明した取りこぼしの回帰テスト。
    ///
    /// 目標の点 H2 が直線 L_a に乗っている根拠は、どこにも直接記録されていない。
    /// 記録から言えるのは「H2 は定義上 L_c 上にある」ことだけで、L_c が
    /// 名前付き定理で L_a と合流したからこそ H2 は L_a 上に来る。以前の
    /// extract_proof はこれを「作図時点の構造的な接続」として基底扱いし、
    /// 証明の本体である定理を落としたまま「全て厳密」と報告していた。
    fn fixture() -> String {
        let mut t = String::new();
        for (id, name) in [(0, "H1"), (1, "H2"), (2, "L_a"), (3, "L_b"), (4, "L_c")] {
            t.push_str(&format!("E\t{}\t{}\tPoint\n", id, name));
        }
        // H1 = L_a ∩ L_b、H2 = L_b ∩ L_c
        t.push_str("D\t0\tIntersection\t2,3\n");
        t.push_str("D\t1\tIntersection\t3,4\n");
        // L_c が「鍵となる定理」で L_a に合流した。
        t.push_str("P\t4\t2\tTheorem\t鍵となる定理|\n");
        // 目標: H1 ≡ H2 は L_a と L_b の交点の一意性から。
        t.push_str("P\t0\t1\tPointUniqueness\t2,3\n");
        t
    }

    #[test]
    fn the_container_side_merge_is_not_swallowed_as_a_construction() {
        let raw = RawProof::parse(&fixture());
        let report = raw.verify_identical(0, 1);
        let text = report.format_deep();
        assert!(text.contains("鍵となる定理"),
            "器(直線)の側の合流を生んだ定理が証明に現れていない:\n{}", text);
    }

    /// 🌟 同じ修正で一度踏んだ落とし穴の回帰テスト。接続の根拠として
    /// 「いま証明しようとしている等式そのもの」を選ぶと循環する。
    #[test]
    fn the_edge_under_verification_is_never_used_to_justify_itself() {
        let raw = RawProof::parse(&fixture());
        let report = raw.verify_identical(0, 1);
        let text = report.format_deep();
        let occurrences = text.matches("H1 ≡ H2").count() + text.matches("H2 ≡ H1").count();
        assert!(occurrences <= 1,
            "目標の等式が自分自身の根拠として再登場している(循環):\n{}", text);
    }
}

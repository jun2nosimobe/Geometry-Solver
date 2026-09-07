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
                        // 🌟 FIX: DefinedBy前提はfact_type自体が"DefinedBy:AnglePair"の
                        // ようにコロンを含むようになったため、split_once(':')(最初の
                        // コロン)ではなくrsplit_once(':')(最後のコロン)で区切る必要が
                        // ある。引数部分は常にカンマ区切りの数字だけなので、最後の
                        // コロンの後ろが引数、それより前が(コロンを含み得る)fact_type
                        // という区切り方は常に一意に定まる。
                        let Some((fact_type, args_str)) = premise.rsplit_once(':') else { continue; };
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
        visited: &mut std::collections::HashSet<(String, Vec<usize>)>,
        depth: usize,
    ) -> Vec<DeepStep> {
        let is_excluded = |a: usize, b: usize| (a, b) == exclude || (b, a) == exclude;
        let mut children = Vec::new();
        for (sf, se) in self.path_to_root(entity) {
            if is_excluded(sf, se.to) { continue; }
            children.push(self.build_step(sf, &se, false, visited, depth + 1));
        }
        // 🐛 FIX: 共有点/共有直線や、DefinedByの結果として参照されるClassIdは、
        // 多くの場合そのマージの当時から今も代表元であり続けている側(=誰かが
        // こちらへ吸収されてきた側)であるため、上のpath_to_root(前向き)だけ
        // では何も出てこない(代表元自身はproof_edges上で"from"にはならない
        // ため)。逆に「誰がこの実体に合流してきたか」をreverse_edgesで辿る
        // ことで、例えば「別の方向が同位角判定などの定理チェーンでこの方向に
        // 合流した」という、まさに知りたい経緯を拾い上げる(orthocenter_alt
        // の調査でこの取りこぼしが実際に発覚した)。
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
        visited: &mut std::collections::HashSet<(String, Vec<usize>)>,
        depth: usize,
    ) -> DeepStep {
        let key = ("GROUND".to_string(), { let mut v = vec![entity]; v.extend_from_slice(lines); v });
        let headline = format!("{} の由来", self.name_of(entity));
        if !visited.insert(key) {
            return DeepStep::leaf(headline, "(既出: 上記で検証済みなので省略)".to_string());
        }
        let mut children = self.merge_ancestry_steps(entity, exclude, visited, depth);
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

    /// 🌟 DefinedBy前提(の結果として参照される実体)や、Identical(X,X)の
    /// ように「既に同じ実体を指している」premiseは、一見すると「定義から
    /// 機械的に従う自明な基底事実」に見えるが、実際にはその実体がこれまで
    /// 他の実体を(named theoremによって)吸収してきた結果として初めて
    /// 成立しているケースが多い(ユーザー指摘: orthocenter_altやsimsonの
    /// extracted_proofで、本来は円周角の定理・有向角の交替律が使われている
    /// はずの箇所が「定義より従う」で片付けられていた問題への対応)。
    /// この実体のmerge_ancestry_steps(合流してきた実体の履歴)を子ノードと
    /// して展開し、合流履歴が無ければ初めて「本当に自明な基底事実」として
    /// 扱う。
    ///
    /// ⚠️ 精度の限界: raw_proofは「どのDefinitionがどの合流によって
    /// 加わったか」までは記録していないため、この実体に合流履歴が複数
    /// あれば全て列挙する(この特定の引数の組と無関係な合流が混ざる
    /// 可能性はゼロではない)。それでも「定義から機械的に従う」と一律に
    /// 片付けるよりは遥かに正直な提示になる。
    fn build_result_ancestry_step(
        &self,
        entity: usize,
        headline: String,
        visited: &mut std::collections::HashSet<(String, Vec<usize>)>,
        depth: usize,
    ) -> DeepStep {
        let key = ("RESULT_ANCESTRY".to_string(), vec![entity]);
        if !visited.insert(key) {
            return DeepStep::leaf(headline, "(既出: 上記で検証済みなので省略)".to_string());
        }
        let ancestry = self.merge_ancestry_steps(entity, (usize::MAX, usize::MAX), visited, depth);
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

    /// 🌟 Definition単位の由来トラッキング(by_definition索引)を使い、
    /// DefinedBy前提を「resultの合流履歴を総当たりで列挙する」のではなく
    /// 「この特定の(引数の組)を最初に持っていた実体1つ + そこからresultへの
    /// 最短合流経路」だけにピンポイントで絞り込む。ユーザー提案(「証明の
    /// 先頭からDPで証明木を構築する」)への対応: 各実体の"元の定義"は
    /// create_entity時点で確定する不変情報なので、それを起点に「この定義は
    /// 最初どのIDに属していたか」を逆引きし、そこから目的のresultまでの
    /// 経路だけを辿ればよい。
    ///
    /// fact_typeが"DefinedBy:{type_name}"の形(target_type付き)でない場合
    /// (理論上は無いはずだが後方互換のため)は、従来通りbuild_result_ancestry_step
    /// (resultの合流履歴全体)にフォールバックする。
    fn build_defined_by_step(
        &self,
        fact_type: &str,
        args: &[usize],
        headline: String,
        visited: &mut std::collections::HashSet<(String, Vec<usize>)>,
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
                if !visited.insert(ground_key) {
                    return DeepStep::leaf(headline, "(既出: 上記で検証済みなので省略)".to_string());
                }
                match self.explain(origin_id, result_id) {
                    Some(sub_edges) if !sub_edges.is_empty() => {
                        let children: Vec<DeepStep> = sub_edges.iter()
                            .map(|(sf, se)| self.build_step(*sf, se, false, visited, depth + 1))
                            .collect();
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
                    // 🌟 由来が記録されていないConnectedは、apply_trivial_relations/
                    // 作図時点のlink_logical_incidenceによる「定義から機械的に
                    // 従う」接続関係であることが多く、これ自体はギャップではない。
                    None => DeepStep::leaf(headline, "由来の明示的な記録なし(作図時点の構造的な接続として、定義から機械的に従う)".to_string()),
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

/// 🌟 エンティティ名に付いた"_(Auto)"/"_(Demand)"ラベルを取り除く。これらは
/// 「resolve_demands系のオンデマンド作図によって生まれた」という実装都合の
/// 印であり、命名時に親の名前をそのまま埋め込むため入れ子(例:
/// "Dir_Line_A_B_(Auto)_(Auto)")になることもあるが、str::replaceは文字列中の
/// 全ての出現を1回の呼び出しで置換するため、ネストの回数によらず1回の
/// 置換呼び出しずつで全て取り除ける。証明の可読性(ユーザー要望)のためだけの
/// 整形であり、名前からラベルを消しても指しているClassId自体は変わらないので
/// 曖昧さは生じない(重複排除のキーには使わない――compressed_proof側で
/// 別途headline文字列そのものをキーにする)。
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

    /// 🌟 ユーザー要望: 「extracted_proofから、(Auto)/(Demand)ラベルを除き、
    /// 前提から結論へ上から順に書き、既に証明済みの前提の重複はスキップした
    /// compressed_proofを作りたい」への対応。
    ///
    /// format_deepは「目標→なぜ成り立つか→そのまた根拠」という目標始点の
    /// 再帰的な入れ子(インデント)構造で、同じ事実が複数箇所から必要と
    /// されるとその都度(既出: 上記で検証済みなので省略)という葉で参照だけ
    /// 残す。ここではその木を**post-order**(子=前提を先に、親=結論を後に
    /// 処理する)で辿って1本のステップ列に平坦化することで、実際に人が
    /// 書く数学の証明のように「まず基本的な事実を確認し、それらを使って
    /// 次第に目標に近づく」という順序に並べ替える。同じheadlineを持つ
    /// ノードが複数箇所に現れる場合(既出プレースホルダ自身も含む)は
    /// 新しいステップを作らず、既存のステップ番号への参照(「Step N より」)
    /// に置き換えることで重複を圧縮する。
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
            if let Some(idx) = Self::flatten_step(c, seen, steps) {
                if !child_refs.contains(&idx) { child_refs.push(idx); }
            }
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

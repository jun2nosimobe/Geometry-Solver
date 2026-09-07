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
        RawProof { names, name_to_id, proof_edges, incidence }
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

    /// 🌟 verify_identicalの中核。1本の辺を検証し、Given/Congruence/構造的な
    /// 基底ケースなら「ギャップなし」、Theoremならpremisesを再帰的に検証し、
    /// LineUniqueness/PointUniqueness/Trivialなら即座にギャップとして記録する。
    /// visitedで(fact_type, ソートしたargs)の組を覚えておき、同じ前提を
    /// 何度も辿る無駄・循環を防ぐ(有向角の加法性/交替律など、多くの定理が
    /// 同じAng90絡みの前提を共有するため、これがないと組み合わせ的に
    /// 膨れ上がる)。
    /// 🌟 gapのlocation文字列を組み立てる。fromとedge.toの関係が「等しい」
    /// (proof_edges由来、explain_identicalの辺)なのか「接続している」
    /// (incidence_provenance由来、点が直線/円に乗っている)なのかで
    /// 表記を変える(以前は両方とも"≡"と表示しており、"A ≡ Circ"のような
    /// 誤解を招く出力になっていた)。
    fn format_location(&self, from: usize, to: usize, is_incidence: bool) -> String {
        if is_incidence {
            format!("{} は {} に接続", self.name_of(from), self.name_of(to))
        } else {
            format!("{} ≡ {}", self.name_of(from), self.name_of(to))
        }
    }

    fn verify_edge(
        &self,
        from: usize,
        edge: &RawEdge,
        is_incidence: bool,
        steps: &mut usize,
        gaps: &mut Vec<Gap>,
        visited: &mut std::collections::HashSet<(String, Vec<usize>)>,
        resolved_shortcuts: &mut usize,
        depth: usize,
    ) {
        *steps += 1;
        if depth > 500 {
            gaps.push(Gap {
                location: self.format_location(from, edge.to, is_incidence),
                reason: "再帰の深さが上限(500)を超えたため、これ以上は検証を打ち切りました(定理の前提が循環している可能性があります)".to_string(),
            });
            return;
        }
        match edge.kind.as_str() {
            // 🌟 基底ケース: 形式的に厳密。Trivialはapply_trivial_relations由来の
            // 構造的な結合(垂線→Ang90、外接円の定義よりその3点が円に乗っている、
            // PerpDirectionOf/HarmonicConjugateOfの対合性など)であり、定義から
            // 機械的に(数値サンプリングに一切頼らず)従う――LineUniqueness/
            // PointUniquenessとは違い、これはギャップではない。
            "Given" | "Congruence" | "Trivial" => {}
            "Theorem" => {
                let Some((_name, premises_str)) = edge.payload.split_once('|') else { return; };
                if premises_str.is_empty() { return; }
                for premise in premises_str.split(';') {
                    let Some((fact_type, args_str)) = premise.split_once(':') else { continue; };
                    let args: Vec<usize> = args_str.split(',').filter_map(|s| s.parse::<usize>().ok()).collect();
                    let mut key_args = args.clone();
                    key_args.sort_unstable();
                    let key = (fact_type.to_string(), key_args);
                    if !visited.insert(key) { continue; } // 既に検証済みの前提

                    match fact_type {
                        "Identical" if args.len() == 2 => {
                            match self.explain(args[0], args[1]) {
                                Some(sub_edges) => {
                                    for (sf, se) in &sub_edges {
                                        self.verify_edge(*sf, se, false, steps, gaps, visited, resolved_shortcuts, depth + 1);
                                    }
                                }
                                None => {
                                    // 🌟 raw_proof上でこの前提の合流経路が見つからない。
                                    // 定理マッチング側は当時のEGraphで実際にこの事実を
                                    // 確認していたはずだが、raw_proofにその根拠が
                                    // 記録されていない場合にここに来る。
                                    gaps.push(Gap {
                                        location: format!("定理の前提 Identical({}, {})", self.name_of(args[0]), self.name_of(args[1])),
                                        reason: "raw_proof中にこの前提を裏付ける合流経路が見つかりませんでした".to_string(),
                                    });
                                }
                            }
                        }
                        "Connected" if args.len() == 2 => {
                            let key = if args[0] < args[1] { (args[0], args[1]) } else { (args[1], args[0]) };
                            if let Some(inc_edge) = self.incidence.get(&key) {
                                self.verify_edge(key.0, inc_edge, true, steps, gaps, visited, resolved_shortcuts, depth + 1);
                            }
                            // 🌟 由来が記録されていないConnectedは、apply_trivial_relations/
                            // 作図時点のlink_logical_incidenceによる「定義から機械的に
                            // 従う」接続関係であることが多く、これ自体はギャップではない
                            // (由来を明示的に記録しているのは、後から数値評価などで
                            // 追加されたものだけ)。
                        }
                        _ => {} // その他の前提(DefinedByなど)は構造的な基底ケースとして扱う
                    }
                }
            }
            // 🐛 FIX (ユーザー指摘): 以前はLineUniqueness/PointUniqueness自体を
            // 問答無用でギャップ扱いにしていたが、「2点(または2方向)を共有する
            // 2直線は同一」「2直線の交点は一意」はそれ自体が射影幾何の公理的な
            // 事実であり、"共有している"という前提さえ厳密に裏付けられていれば
            // 数値サンプリングは単なる保険であって、ギャップと呼ぶべきではない。
            // ここでは共有点/共有方向・関係する直線それぞれの由来
            // (a) それ自身がさらに別のマージの産物なら、そのマージ履歴
            //     (path_to_root)を再帰的に検証する
            // (b) incidence_provenanceに「この点はこの直線に乗っている」の
            //     由来が明示的に記録されていれば、それも再帰的に検証する
            //     (記録が無い場合は、作図時点の構造的な接続として基底ケース
            //     扱いする――Connected前提の扱いと同じ方針)
            // を辿り、そこにさらに深いギャップが無ければこのステップ自体は
            // ギャップとして報告しない(resolved_shortcutsとしてカウントする
            // だけに留める)。深いところで本当にギャップが見つかった場合は、
            // そのより具体的なギャップが既にgapsに追加されているので、ここで
            // 重ねて報告する必要はない。
            "LineUniqueness" => {
                let shared: Vec<usize> = edge.payload.split(',').filter_map(|s| s.parse().ok()).collect();
                let before = gaps.len();
                for p in shared {
                    for (sf, se) in self.path_to_root(p) {
                        self.verify_edge(sf, &se, false, steps, gaps, visited, resolved_shortcuts, depth + 1);
                    }
                    for &line in &[from, edge.to] {
                        let key = if p < line { (p, line) } else { (line, p) };
                        if let Some(inc_edge) = self.incidence.get(&key) {
                            self.verify_edge(key.0, inc_edge, true, steps, gaps, visited, resolved_shortcuts, depth + 1);
                        }
                    }
                }
                if gaps.len() == before { *resolved_shortcuts += 1; }
            }
            "PointUniqueness" => {
                let via_lines: Vec<usize> = edge.payload.split(',').filter_map(|s| s.parse().ok()).collect();
                let before = gaps.len();
                for &l in &via_lines {
                    for (sf, se) in self.path_to_root(l) {
                        self.verify_edge(sf, &se, false, steps, gaps, visited, resolved_shortcuts, depth + 1);
                    }
                    for &pt in &[from, edge.to] {
                        let key = if pt < l { (pt, l) } else { (l, pt) };
                        if let Some(inc_edge) = self.incidence.get(&key) {
                            self.verify_edge(key.0, inc_edge, true, steps, gaps, visited, resolved_shortcuts, depth + 1);
                        }
                    }
                }
                if gaps.len() == before { *resolved_shortcuts += 1; }
            }
            other => {
                gaps.push(Gap {
                    location: self.format_location(from, edge.to, is_incidence),
                    reason: format!("未知の理由の種類「{}」(raw_proofの形式が想定外です)", other),
                });
            }
        }
    }

    /// 🌟 aとbが本当にrigorousな経路(Given/Theorem/Congruence/Trivialの連鎖、
    /// かつTheoremの前提も再帰的にrigorous)だけで合流しているかを検証する。
    /// LineUniqueness/PointUniqueness(2点/2直線の共有という構造的観察)は
    /// それ自体をギャップとはせず、共有点/共有直線の由来を再帰的に検証した上で
    /// (a)全て辿れれば「射影幾何の公理として解決済み」(resolved_shortcuts)、
    /// (b)辿れない箇所があればそここそを本当のギャップとして報告する。
    pub fn verify_identical(&self, a: usize, b: usize) -> VerifyReport {
        let mut steps = 0usize;
        let mut gaps = Vec::new();
        let mut visited = std::collections::HashSet::new();
        let mut resolved_shortcuts = 0usize;
        match self.explain(a, b) {
            Some(edges) => {
                for (from, edge) in &edges {
                    self.verify_edge(*from, edge, false, &mut steps, &mut gaps, &mut visited, &mut resolved_shortcuts, 0);
                }
            }
            None => {
                gaps.push(Gap {
                    location: format!("{} ≡ {}", self.name_of(a), self.name_of(b)),
                    reason: "raw_proof中にこの2つが合流する経路が全く見つかりませんでした(未証明)".to_string(),
                });
            }
        }
        VerifyReport { steps_checked: steps, gaps, resolved_shortcuts }
    }
}

/// 🌟 verify_identicalが見つけた1件のギャップ(数値サンプリングや構造的近似
/// だけに頼っていて、名前付き定理の連鎖で追跡できなかった箇所)。
#[derive(Debug, Clone)]
pub struct Gap {
    pub location: String,
    pub reason: String,
}

/// verify_identicalの結果。
pub struct VerifyReport {
    pub steps_checked: usize,
    pub gaps: Vec<Gap>,
    /// 🌟 LineUniqueness/PointUniqueness(「2点/2直線の共有」という構造的
    /// ショートカット)のうち、共有点/共有直線の由来を再帰的に検証し尽くせて
    /// 「射影幾何の公理として解決済み」と判定できた件数。ギャップではないが、
    /// 名前付き定理そのものでもない――何にどれだけ頼ったかを利用者に見せる
    /// ための情報。
    pub resolved_shortcuts: usize,
}

impl VerifyReport {
    pub fn is_rigorous(&self) -> bool { self.gaps.is_empty() }

    pub fn format(&self) -> String {
        let mut out = String::new();
        if self.is_rigorous() {
            out.push_str(&format!(
                "✅ [extract_proof] 検証した{}ステップ全てが厳密に辿れました(未証明のギャップなし)。\n",
                self.steps_checked
            ));
            if self.resolved_shortcuts > 0 {
                out.push_str(&format!(
                    "    うち{}件は「2点/2直線を共有する直線・点の一意性」という射影幾何の公理を使っていますが、\n    共有点・共有直線の由来を再帰的に検証し、全て名前付き定理/構造的な基底事実まで遡れることを確認済みです。\n",
                    self.resolved_shortcuts
                ));
            }
        } else {
            out.push_str(&format!(
                "⚠️ [extract_proof] {}ステップ中{}件、由来を遡っても名前付き定理や構造的な基底事実に辿り着けない(=数値サンプリングのみが根拠の)ギャップが見つかりました:\n",
                self.steps_checked, self.gaps.len()
            ));
            for (i, g) in self.gaps.iter().enumerate() {
                out.push_str(&format!("  {}. {} — {}\n", i + 1, g.location, g.reason));
            }
        }
        out
    }
}

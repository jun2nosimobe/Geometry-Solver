//! 🌟 ユーザー要望「GeoGebraのようなインターフェースを作りたい。自分で点や
//! 直線、円などを自由に作図し、freepointを自由に動かしたりできて、更に
//! 定理発見モードで定理を見つけられるようにしたい」への対応。
//!
//! 役割分担:
//!   - 作図と描画・ドラッグはブラウザ側(web/app.js)が持つ。自由点を掴んで
//!     動かすたびに図全体を作り直すので、1回あたり数ミリ秒で終わる必要が
//!     あり、サーバ往復は挟めない。JS側は表示のためだけの浮動小数点評価器を
//!     持つ。
//!   - 「この図で成り立つ定理は何か」はエンジン側が持つ。JS側の浮動小数点は
//!     あくまで絵であって、主張の真偽はすべて有限体上の乱数評価
//!     (padic_eval)で判定する。
//!
//! つまりブラウザは「作図手順(DAG)」の編集器で、その手順を丸ごとこちらへ
//! 送ると、同じ手順をEGraph上に組み直して検出器を回し、見つかった関係を
//! ユーザーが付けた名前のまま返す。描いた位置そのものは検出には使わない
//! (特定の位置でたまたま成り立つ関係ではなく、その作図手順である限り常に
//! 成り立つ関係を探したいため)。
//!
//! 依存を増やさないため、HTTPもJSONも使わず、std::net の TcpListener と
//! 行指向のテキストプロトコルだけで組んである。

use std::collections::HashMap;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};

use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};

const INDEX_HTML: &str = include_str!("../web/index.html");
const APP_JS: &str = include_str!("../web/app.js");
const APP_CSS: &str = include_str!("../web/app.css");

pub fn run(args: &[String]) {
    let port: u16 = args.iter()
        .find_map(|a| a.strip_prefix("--port="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(8080);
    let addr = format!("127.0.0.1:{}", port);
    let listener = match TcpListener::bind(&addr) {
        Ok(l) => l,
        Err(e) => {
            println!("⚠️ {} を開けませんでした: {}", addr, e);
            println!("   別のポートを使うには --port=8081 のように指定してください。");
            return;
        }
    };
    println!("🖥️  作図インターフェースを開きました:  http://{}/", addr);
    println!("   ブラウザでこのURLを開いてください。終了は Ctrl+C。");
    for stream in listener.incoming() {
        match stream {
            Ok(s) => { std::thread::spawn(move || handle(s)); }
            Err(e) => println!("⚠️ 接続に失敗しました: {}", e),
        }
    }
}

fn handle(mut stream: TcpStream) {
    let (method, path, body) = match read_request(&mut stream) {
        Some(r) => r,
        None => return,
    };
    let (status, content_type, body) = match (method.as_str(), path.as_str()) {
        ("GET", "/") => ("200 OK", "text/html; charset=utf-8", INDEX_HTML.to_string()),
        ("GET", "/app.js") => ("200 OK", "text/javascript; charset=utf-8", APP_JS.to_string()),
        ("GET", "/app.css") => ("200 OK", "text/css; charset=utf-8", APP_CSS.to_string()),
        ("POST", "/discover") => ("200 OK", "text/plain; charset=utf-8", discover_response(&body)),
        _ => ("404 Not Found", "text/plain; charset=utf-8", "not found".to_string()),
    };
    let head = format!(
        "HTTP/1.1 {}\r\nContent-Type: {}\r\nContent-Length: {}\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n",
        status, content_type, body.as_bytes().len());
    let _ = stream.write_all(head.as_bytes());
    let _ = stream.write_all(body.as_bytes());
    let _ = stream.flush();
}

/// ブラウザからのリクエストを (メソッド, パス, 本文) に分解する。
/// ローカルの1ユーザー向けなので、必要最小限の解釈しかしない。
fn read_request(stream: &mut TcpStream) -> Option<(String, String, String)> {
    let mut reader = BufReader::new(stream.try_clone().ok()?);
    let mut start = String::new();
    if reader.read_line(&mut start).ok()? == 0 { return None; }
    let mut parts = start.split_whitespace();
    let method = parts.next()?.to_string();
    let path = parts.next()?.to_string();
    let mut content_length = 0usize;
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line).ok()? == 0 { break; }
        let trimmed = line.trim_end();
        if trimmed.is_empty() { break; }
        if let Some(v) = trimmed.to_ascii_lowercase().strip_prefix("content-length:") {
            content_length = v.trim().parse().unwrap_or(0);
        }
    }
    let mut body = vec![0u8; content_length];
    if content_length > 0 { reader.read_exact(&mut body).ok()?; }
    Some((method, path, String::from_utf8_lossy(&body).to_string()))
}

// ============================================================
// 作図手順のテキスト表現
// ============================================================

/// 作図1手。ブラウザ側とこちらで同じ文法を共有する
/// (web/app.js の `serialize` が作り、ここが読む)。
///
/// ```text
/// point  A  free                      # 自由点
/// point  D  on L1                     # 「L1上にある」という仮定を持つ自由点
/// point  P  inter L1 L2               # 2直線の交点
/// point  M  mid A B                   # 中点
/// point  Q  second_lc A L1 C1         # 既知の交点Aを持つ、直線と円のもう一方の交点
/// point  R  second_cc A C1 C2         # 既知の交点Aを持つ、2円のもう一方の交点
/// line   L1 through A B
/// line   L2 perp L1 A                 # L1に垂直でAを通る
/// line   L3 para L1 A                 # L1に平行でAを通る
/// line   L4 tangent C1 A              # 円C1のA(円上の点)における接線
/// line   L5 radical C1 C2             # 2円の根軸
/// circle C1 through A B C
/// ```
/// 座標は送らない ―― 検出は「この作図手順である限り常に成り立つ関係」を
/// 探すものなので、画面上のどこに置いたかは本質的に関係がない。
fn build_egraph(script: &str) -> Result<(EGraph, Vec<(String, ClassId)>), String> {
    let mut egraph = EGraph::new();
    let mut env: HashMap<String, ClassId> = HashMap::new();
    let mut order: Vec<(String, ClassId)> = Vec::new();

    for (lineno, raw) in script.lines().enumerate() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.is_empty() { continue; }
        let t: Vec<&str> = line.split_whitespace().collect();
        let err = |m: String| format!("{}行目: {}", lineno + 1, m);
        if t.len() < 3 { return Err(err(format!("項目が足りません: 「{}」", line))); }
        let (kind, name, op) = (t[0], t[1].to_string(), t[2]);
        if env.contains_key(&name) { return Err(err(format!("名前「{}」が重複しています", name))); }

        let lookup = |n: &str, want: EntityType| -> Result<ClassId, String> {
            let id = *env.get(n).ok_or_else(|| err(format!("「{}」がまだ作図されていません", n)))?;
            let got = egraph.entities[egraph.get_rep(id).0].entity_type;
            if got != want {
                return Err(err(format!("「{}」の種類が違います(必要: {:?}、実際: {:?})", n, want, got)));
            }
            Ok(id)
        };
        let need = |i: usize| -> Result<&str, String> {
            t.get(i).copied().ok_or_else(|| err(format!("引数が足りません: 「{}」", line)))
        };

        let (def, ty, extra_incidence): (Definition, EntityType, Option<ClassId>) = match (kind, op) {
            ("point", "free") => (Definition::FreePoint, EntityType::Point, None),
            ("point", "on") => {
                let curve_name = need(3)?;
                let curve = *env.get(curve_name)
                    .ok_or_else(|| err(format!("「{}」がまだ作図されていません", curve_name)))?;
                let ty = egraph.entities[egraph.get_rep(curve).0].entity_type;
                if !matches!(ty, EntityType::Line | EntityType::Conic) {
                    return Err(err(format!("「{}」は直線でも円でもないので、その上に点は置けません", curve_name)));
                }
                (Definition::FreePoint, EntityType::Point, Some(curve))
            }
            ("point", "inter") => (Definition::Intersection(
                lookup(need(3)?, EntityType::Line)?, lookup(need(4)?, EntityType::Line)?),
                EntityType::Point, None),
            ("point", "mid") => (Definition::Midpoint(
                lookup(need(3)?, EntityType::Point)?, lookup(need(4)?, EntityType::Point)?),
                EntityType::Point, None),
            ("point", "second_lc") => (Definition::SecondIntersectionOfLineAndConic(
                lookup(need(3)?, EntityType::Point)?, lookup(need(4)?, EntityType::Line)?,
                lookup(need(5)?, EntityType::Conic)?), EntityType::Point, None),
            ("point", "second_cc") => (Definition::SecondIntersectionOfCircles(
                lookup(need(3)?, EntityType::Point)?, lookup(need(4)?, EntityType::Conic)?,
                lookup(need(5)?, EntityType::Conic)?), EntityType::Point, None),
            ("line", "through") => (Definition::new_line(
                lookup(need(3)?, EntityType::Point)?, lookup(need(4)?, EntityType::Point)?),
                EntityType::Line, None),
            ("line", "perp") => (Definition::PerpendicularLine(
                lookup(need(3)?, EntityType::Line)?, lookup(need(4)?, EntityType::Point)?),
                EntityType::Line, None),
            ("line", "para") => (Definition::ParallelLine(
                lookup(need(3)?, EntityType::Line)?, lookup(need(4)?, EntityType::Point)?),
                EntityType::Line, None),
            ("line", "tangent") => (Definition::TangentLine(
                lookup(need(3)?, EntityType::Conic)?, lookup(need(4)?, EntityType::Point)?),
                EntityType::Line, None),
            ("line", "radical") => (Definition::RadicalAxis(
                lookup(need(3)?, EntityType::Conic)?, lookup(need(4)?, EntityType::Conic)?),
                EntityType::Line, None),
            ("circle", "through") => (Definition::Circumcircle(
                lookup(need(3)?, EntityType::Point)?, lookup(need(4)?, EntityType::Point)?,
                lookup(need(5)?, EntityType::Point)?), EntityType::Conic, None),
            _ => return Err(err(format!("知らない作図です: 「{} … {}」", kind, op))),
        };

        let id = egraph.create_entity(name.clone(), def, ty);
        if let Some(curve) = extra_incidence {
            egraph.link_logical_incidence_justified(id, curve,
                crate::mmp_core::Justification::Given);
        }
        env.insert(name.clone(), id);
        order.push((name, id));
    }
    if order.is_empty() { return Err("作図が空です".to_string()); }
    egraph.apply_congruence_closure();
    Ok((egraph, order))
}

// ============================================================
// 検出
// ============================================================

/// 1件の発見。UI側はこれを行として受け取り、idsに挙がった図形を強調表示する。
struct Finding {
    kind: &'static str,
    text: String,
    ids: Vec<String>,
}

fn discover_response(script: &str) -> String {
    let (mut egraph, order) = match build_egraph(script) {
        Ok(v) => v,
        Err(e) => return format!("error|{}\n", e),
    };
    // 作図された実体の代表元 -> ユーザーが付けた名前。マージで代表元が
    // 入れ替わっても、ユーザーの付けた名前で報告したいので自前で持つ。
    let mut label: HashMap<usize, String> = HashMap::new();
    for (name, id) in &order {
        label.entry(egraph.get_rep(*id).0).or_insert_with(|| name.clone());
    }
    let name_of = |eg: &EGraph, id: ClassId| -> String {
        label.get(&eg.get_rep(id).0).cloned()
            .unwrap_or_else(|| eg.entities[eg.get_rep(id).0].name.clone())
    };

    let findings = collect_findings(&mut egraph, &name_of);
    let mut out = format!("ok|{}\n", findings.len());
    for f in findings {
        out.push_str(&format!("finding|{}|{}|{}\n", f.kind, f.text, f.ids.join(",")));
    }
    out
}

fn collect_findings(egraph: &mut EGraph, name_of: &dyn Fn(&EGraph, ClassId) -> String) -> Vec<Finding> {
    use crate::padic_eval as pe;
    const SEEDS: [u64; 3] = [0xC0FFEE, 0xBEEF77, 0x1234ABCD];
    // 手で描く図はせいぜい数十個なので、総当たりの上限は緩くてよい。
    const CAP: usize = 64;
    let mut out: Vec<Finding> = Vec::new();

    // 1. 独立に作った2つの図形が常に一致する
    for (a, b) in pe::find_generic_coincidences(egraph, &SEEDS) {
        if crate::discover::has_degenerate_ancestor(egraph, a, b) { continue; }
        out.push(Finding {
            kind: "coincide",
            text: format!("{} と {} は常に同じ", name_of(egraph, a), name_of(egraph, b)),
            ids: vec![name_of(egraph, a), name_of(egraph, b)],
        });
    }

    // 2. 3点以上が共線
    let triples = pe::find_generic_collinear_triples(egraph, &SEEDS, CAP);
    let mut fresh: Vec<Vec<ClassId>> = Vec::new();
    for (a, b, c) in triples {
        let reps = [egraph.get_rep(a), egraph.get_rep(b), egraph.get_rep(c)];
        if egraph.find_common_line(&reps).is_some() { continue; }
        if crate::discover::has_degenerate_ancestor(egraph, a, b) { continue; }
        fresh.push(vec![a, b, c]);
    }
    for set in crate::discover::maximal_verified_sets(egraph, &SEEDS, fresh, pe::PropertyKind::Collinear) {
        let names: Vec<String> = set.iter().map(|&id| name_of(egraph, id)).collect();
        out.push(Finding { kind: "collinear", text: format!("{} は同一直線上にある", names.join(" , ")), ids: names });
    }

    // 3. 3直線以上が1点で交わる
    let conc = pe::find_generic_concurrent_lines(egraph, &SEEDS, CAP);
    let mut fresh_conc: Vec<Vec<ClassId>> = Vec::new();
    for (a, b, c) in conc {
        if crate::discover::shares_known_point(egraph, a, b, c) { continue; }
        if crate::discover::is_trivial_pencil(egraph, &[a, b, c]) { continue; }
        if crate::discover::pairwise_shared_point(egraph, a, b).is_some()
            || crate::discover::pairwise_shared_point(egraph, b, c).is_some()
            || crate::discover::pairwise_shared_point(egraph, a, c).is_some() { continue; }
        fresh_conc.push(vec![a, b, c]);
    }
    for set in crate::discover::maximal_verified_sets(egraph, &SEEDS, fresh_conc, pe::PropertyKind::Concurrent) {
        let names: Vec<String> = set.iter().map(|&id| name_of(egraph, id)).collect();
        out.push(Finding { kind: "concurrent", text: format!("{} は1点で交わる", names.join(" , ")), ids: names });
    }

    // 4. 3円が1点を共有する(ミケル点・根心型)
    for (a, b, c) in pe::find_generic_concurrent_circles(egraph, &SEEDS, CAP) {
        if crate::discover::shares_known_point(egraph, a, b, c) { continue; }
        let names: Vec<String> = [a, b, c].iter().map(|&id| name_of(egraph, id)).collect();
        out.push(Finding { kind: "circles", text: format!("円 {} は1点を共有する", names.join(" , ")), ids: names });
    }

    // 5. 点が直線・円の上にある
    //
    // 🌟 同じ曲線についての接続は1件にまとめる。まとめないと、九点円の図で
    // 「Haは円np上」「Hbは円np上」「Ha,Hbは円np上」の3件が並ぶ(前2つは
    // 接続検出から、最後は共円検出の言い換えから来る)。読む側にとっては
    // 「この円の上に、まだそうと分かっていなかった点がこれだけ乗る」という
    // 1つの事実なので、曲線ごとに集約する。
    let mut incidences: std::collections::BTreeMap<String, (String, Vec<String>)> =
        std::collections::BTreeMap::new();
    let mut note_incidence = |egraph: &EGraph, p: ClassId, c: ClassId| {
        let kind_word = if egraph.entities[egraph.get_rep(c).0].entity_type == EntityType::Conic { "円" } else { "直線" };
        let (pn, cn) = (name_of(egraph, p), name_of(egraph, c));
        let e = incidences.entry(cn).or_insert_with(|| (kind_word.to_string(), Vec::new()));
        if !e.1.contains(&pn) { e.1.push(pn); }
    };
    for (p, c) in pe::find_generic_point_on_curve(egraph, &SEEDS, CAP, CAP) {
        if egraph.is_natural_incidence(egraph.get_rep(p), egraph.get_rep(c)) { continue; }
        if crate::discover::has_duplicated_parent(egraph, p)
            || crate::discover::has_duplicated_parent(egraph, c) { continue; }
        note_incidence(egraph, p, c);
    }

    // 6. 4点以上が同一円周上
    let quads = pe::find_generic_concyclic_quadruples(egraph, &SEEDS, CAP);
    let mut fresh_quads: Vec<Vec<ClassId>> = Vec::new();
    for q in quads {
        if crate::discover::shares_known_conic(egraph, &q) { continue; }
        let mut degenerate = false;
        for i in 0..4 { for j in (i + 1)..4 { for k in (j + 1)..4 {
            if egraph.find_common_line(&[egraph.get_rep(q[i]), egraph.get_rep(q[j]), egraph.get_rep(q[k])]).is_some() {
                degenerate = true;
            }
        }}}
        if degenerate { continue; }
        fresh_quads.push(q.to_vec());
    }
    for set in crate::discover::maximal_verified_sets(egraph, &SEEDS, fresh_quads, pe::PropertyKind::Concyclic) {
        // 既知の円が3点以上を含むなら、主張の中身は「残りの点がその円の上にある」
        // (discover.rsの報告と同じ言い換え)。
        if let Some((circle, extra)) = crate::discover::known_circle_through_most(egraph, &set) {
            if !extra.is_empty() {
                for &id in &extra { note_incidence(egraph, id, circle); }
                continue;
            }
        }
        let names: Vec<String> = set.iter().map(|&id| name_of(egraph, id)).collect();
        out.push(Finding {
            kind: "concyclic",
            text: format!("{}点 {} は同一円周上にある", names.len(), names.join(" , ")),
            ids: names,
        });
    }

    for (curve, (kind_word, points)) in incidences {
        let mut ids = points.clone();
        ids.push(curve.clone());
        out.push(Finding {
            kind: "incident",
            text: format!("点 {} は{} {} の上にある", points.join(" , "), kind_word, curve),
            ids,
        });
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn script_builds_the_expected_construction() {
        let (egraph, order) = build_egraph("
            point A free
            point B free
            point C free
            line BC through B C
            line CA through C A
            circle O through A B C
            line tA tangent O A
        ").expect("素直な作図は読めるべき");
        assert_eq!(order.len(), 7);
        let by_name: HashMap<&str, ClassId> = order.iter().map(|(n, i)| (n.as_str(), *i)).collect();
        assert_eq!(egraph.entities[by_name["O"].0].entity_type, EntityType::Conic);
        assert_eq!(egraph.entities[by_name["tA"].0].entity_type, EntityType::Line);
        // 接点Aは接線の上にある、と構造的に登録されているべき。
        assert!(egraph.is_connected(by_name["A"], by_name["tA"]));
    }

    /// Result<EGraph, String> の Err だけ取り出す(EGraphはDebugを実装して
    /// いないので unwrap_err が使えない)。
    fn err_of(script: &str) -> String {
        match build_egraph(script) {
            Err(e) => e,
            Ok(_) => panic!("エラーになるはずの作図が通ってしまった: {}", script),
        }
    }

    #[test]
    fn script_errors_point_at_the_offending_line() {
        let e = err_of("point A free\nline L through A Z");
        assert!(e.contains("2行目") && e.contains("Z"), "何行目の何が悪いか分かるべき: {}", e);
        let e = err_of("point A free\npoint A free");
        assert!(e.contains("重複"), "同じ名前を二度使ったら止まるべき: {}", e);
        // 種類違い(点を要求する場所に直線)も、何が悪いか言えること。
        let e = err_of("point A free\npoint B free\nline L through A B\npoint M mid A L");
        assert!(e.contains("種類が違います"), "型の取り違えを説明できるべき: {}", e);
    }

    /// 退化した作図(同じ点を3つ通る円)でもパニックせず検出まで走り切ること
    /// ―― UIからは何でも送られてくるため。
    #[test]
    fn degenerate_constructions_do_not_panic() {
        let body = discover_response("point A free\ncircle C through A A A");
        assert!(body.starts_with("ok|") || body.starts_with("error|"),
            "何らかの応答を返すべき: {}", body);
    }

    /// 🌟 ブラウザで垂心の図を描いたときに、エンジンが「3本目の高さも
    /// その交点を通る」を見つけられること。UIから検出までの経路がひと続きに
    /// 動いていることの確認で、これが通らなければ画面上も何も出ない。
    #[test]
    fn discovers_the_third_altitude_through_the_orthocenter() {
        let script = "
            point A free
            point B free
            point C free
            line AB through A B
            line BC through B C
            line CA through C A
            line altA perp BC A
            line altB perp CA B
            line altC perp AB C
        ";
        let body = discover_response(script);
        assert!(body.starts_with("ok|"), "作図が通らなかった: {}", body);
        let found_concurrency = body.lines().any(|l| {
            l.starts_with("finding|concurrent|")
                && l.contains("altA") && l.contains("altB") && l.contains("altC")
        });
        assert!(found_concurrency, "3本の高さの共点性を見つけられるべき:\n{}", body);
    }

    #[test]
    fn reports_a_readable_error_for_a_broken_script() {
        let body = discover_response("line L through A B");
        assert!(body.starts_with("error|") && body.contains("1行目"),
            "壊れた作図はエラー行として返すべき: {}", body);
    }
}

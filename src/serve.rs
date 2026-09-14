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
// ブラウザから渡される設定
// ============================================================

/// 🌟 ユーザー要望「探索時間やパラメーターなどのコンフィグもブラウザから
/// 変更できるようにしたい」への対応。本文の先頭に
/// `config <キー> <値>` の行として混ぜて送られてくる。
/// 知らないキーは黙って無視する(古いUIと新しいサーバを繋いでも動くように)。
struct Config {
    /// 自由作図のラウンド数。0なら「描いた図のまま」調べる。
    rounds: usize,
    /// 自由作図で作ってよい実体数の上限。
    cap: usize,
    /// 1ラウンドで各種類から拾う「熱い」実体の数。
    per_kind: usize,
    /// 自由作図に使ってよい時間(秒)。
    seconds: u64,
    /// 総当たり検出で見る点・直線/円の数。
    sweep: usize,
    /// 返す発見の最大件数。
    top: usize,
    /// 1件あたり何秒まで証明を試すか。0なら試さない。
    prove_seconds: u64,
    /// 証明を試す件数の上限(件数 × 秒 が待ち時間になるため)。
    prove_max: usize,
}

impl Default for Config {
    fn default() -> Self {
        Config { rounds: 0, cap: 400, per_kind: 8, seconds: 20, sweep: 64, top: 30,
                 prove_seconds: 0, prove_max: 12 }
    }
}

/// 本文を (設定, 作図手順) に分ける。
fn split_config(body: &str) -> (Config, String) {
    let mut cfg = Config::default();
    let mut script = String::new();
    for raw in body.lines() {
        let line = raw.trim();
        if let Some(rest) = line.strip_prefix("config ") {
            let mut it = rest.split_whitespace();
            let (Some(key), Some(val)) = (it.next(), it.next()) else { continue };
            let n: usize = val.parse().unwrap_or(0);
            match key {
                "rounds" => cfg.rounds = n.min(8),
                "cap" => cfg.cap = n.clamp(20, 4000),
                "per_kind" => cfg.per_kind = n.clamp(3, 20),
                "seconds" => cfg.seconds = (n as u64).clamp(1, 600),
                "sweep" => cfg.sweep = n.clamp(8, 200),
                "top" => cfg.top = n.clamp(1, 200),
                "prove_seconds" => cfg.prove_seconds = (n as u64).min(120),
                "prove_max" => cfg.prove_max = n.clamp(1, 100),
                _ => {}
            }
            continue;
        }
        script.push_str(raw);
        script.push('\n');
    }
    (cfg, script)
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
///
/// refs は ids と同じ並びの実体ID。自由作図モードでは、発見に出てきた
/// 補助的な図形を作図手順として書き戻す必要があり、そのとき名前では
/// 引けない(自動生成の名前は作図式そのもので、EGraphの検索キーではない)
/// ため、IDをそのまま持ち回る。
struct Finding {
    kind: &'static str,
    text: String,
    ids: Vec<String>,
    refs: Vec<ClassId>,
}

/// 「エンジンがすぐ証明できたか」の結果。
#[derive(Clone, Copy, PartialEq)]
enum Proof {
    /// 試していない
    Untried,
    /// 名前付き定理の連鎖で導けた
    Proved,
    /// 制限時間内には導けなかった(偽という意味ではない)
    Open,
    /// この形の主張はまだ証明目標として表現していない
    Unsupported,
}

impl Proof {
    fn tag(self) -> &'static str {
        match self {
            Proof::Untried => "untried",
            Proof::Proved => "proved",
            Proof::Open => "open",
            Proof::Unsupported => "unsupported",
        }
    }
}

fn discover_response(body: &str) -> String {
    let (cfg, script) = split_config(body);
    let (mut egraph, order) = match build_egraph(&script) {
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

    // 🌟 自由作図モード: 与えられた図から機械的に作図を伸ばしてから探す。
    if cfg.rounds > 0 {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(cfg.seconds);
        crate::discover::systematic_closure_until(
            &mut egraph, cfg.rounds, cfg.cap, cfg.per_kind, Some(deadline));
    }

    let mut findings = collect_findings(&mut egraph, &name_of, cfg.sweep);

    // ユーザーが描いた図形に多く触れている発見を先に出す。自由作図は補助的な
    // 図形どうしだけで閉じた関係もたくさん作るが、まず見たいのは「自分の図に
    // ついて何が言えるか」なので。
    let is_user = |n: &String| order.iter().any(|(name, _)| name == n);
    findings.sort_by_key(|f| {
        let touched = f.ids.iter().filter(|n| is_user(n)).count();
        (std::cmp::Reverse(touched), f.ids.len())
    });
    findings.truncate(cfg.top);

    // 発見に出てくる補助的な図形を、ブラウザが描けるように作図手順として
    // 書き出す。これが無いと「x3 と x7 が共点」と言われても何のことか
    // 分からない。必要なものだけを、依存関係の順に返す。
    let mut emitter = AuxEmitter::new(&egraph, &order);
    let mut aux_lines: Vec<String> = Vec::new();
    let mut renamed: HashMap<String, String> = HashMap::new();
    for f in &findings {
        for (n, id) in f.ids.iter().zip(f.refs.iter()) {
            if is_user(n) || renamed.contains_key(n) { continue; }
            if let Some(short) = emitter.emit_id(&egraph, *id, &mut aux_lines) {
                renamed.insert(n.clone(), short);
            }
        }
    }

    // 🌟 「すぐ証明できるか」を試す(prove_seconds が 0 なら飛ばす)。
    // 自由作図で膨らませた図をそのまま使うので、補助的な図形を前提にした
    // 主張もそのまま目標にできる。
    let mut proofs: Vec<Proof> = vec![Proof::Untried; findings.len()];
    if cfg.prove_seconds > 0 {
        for (i, f) in findings.iter().enumerate().take(cfg.prove_max) {
            proofs[i] = attempt_proof(&egraph, f, cfg.prove_seconds);
        }
    }

    let mut out = format!("ok|{}\n", findings.len());
    for line in &aux_lines { out.push_str(&format!("aux|{}\n", line)); }
    for (i, f) in findings.iter().enumerate() {
        let ids: Vec<String> = f.ids.iter()
            .map(|n| renamed.get(n).cloned().unwrap_or_else(|| n.clone())).collect();
        // 表示用の文も、長い作図式のままだと読めないので短い名前に差し替える。
        let mut text = f.text.clone();
        let mut subs: Vec<(&String, &String)> = renamed.iter().collect();
        subs.sort_by_key(|(long, _)| std::cmp::Reverse(long.len()));
        for (long, short) in subs {
            if long != short { text = text.replace(long.as_str(), short.as_str()); }
        }
        out.push_str(&format!("finding|{}|{}|{}|{}\n",
            f.kind, text, ids.join(","), proofs[i].tag()));
    }
    out
}

// ============================================================
// 見つかった主張を、実際に証明できるか試す
// ============================================================

/// 🌟 ユーザー要望「エンジンですぐ証明できた性質はどれくらいあるのか
/// 調べるボタンも欲しい」への対応。
///
/// 検出器が出すのは「乱数座標で何度やっても成り立つ」という強い数値的根拠
/// だけで、証明ではない。ここで実際に定理の連鎖を短時間だけ走らせると、
/// 「今の定理集合ですぐ出る = だいたい既知・簡単」と「数値的には確かなのに
/// 出てこない = 面白い候補」を分けられる。
///
/// 証明できなかったことは偽である根拠には全くならない(制限時間と定理集合の
/// 都合でしかない)ので、UI側の表記もそのつもりで書いてある。
fn attempt_proof(base: &EGraph, f: &Finding, seconds: u64) -> Proof {
    // 主張の形ごとに、既存の証明目標(Identical / Connected / Concyclic)へ翻訳する。
    let mut egraph = base.clone();
    let r = &f.refs;
    let target: (String, Vec<ClassId>) = match f.kind {
        "coincide" if r.len() >= 2 => ("Identical".to_string(), vec![r[0], r[1]]),
        "incident" if r.len() >= 2 => {
            // ids は [点..., 曲線] の並び。最後が曲線。
            let curve = *r.last().unwrap();
            ("Connected".to_string(), vec![r[0], curve])
        }
        "concyclic" if r.len() >= 4 => ("Concyclic".to_string(), r.clone()),
        "collinear" if r.len() >= 3 => {
            // 「P,Q,R が共線」= 直線PQ と 直線PR が同じ。
            let l1 = egraph.create_entity("Goal_L1".into(), Definition::new_line(r[0], r[1]), EntityType::Line);
            let l2 = egraph.create_entity("Goal_L2".into(), Definition::new_line(r[0], r[2]), EntityType::Line);
            ("Identical".to_string(), vec![l1, l2])
        }
        "concurrent" if r.len() >= 3 => {
            // 「l1,l2,l3 が共点」= l1∩l2 と l1∩l3 が同じ点。
            let p1 = egraph.create_entity("Goal_P1".into(), Definition::Intersection(r[0], r[1]), EntityType::Point);
            let p2 = egraph.create_entity("Goal_P2".into(), Definition::Intersection(r[0], r[2]), EntityType::Point);
            ("Identical".to_string(), vec![p1, p2])
        }
        // 3円共点はまだ証明目標の語彙に無い。
        _ => return Proof::Unsupported,
    };
    egraph.apply_congruence_closure();

    let met = |eg: &EGraph| -> bool {
        match target.0.as_str() {
            "Identical" => eg.get_rep(target.1[0]) == eg.get_rep(target.1[1]),
            "Connected" => eg.is_connected(eg.get_rep(target.1[0]), eg.get_rep(target.1[1])),
            "Concyclic" => {
                let reps: Vec<ClassId> = target.1.iter().map(|&i| eg.get_rep(i)).collect();
                eg.points_share_a_circle(&reps)
            }
            _ => false,
        }
    };
    if met(&egraph) { return Proof::Proved; }

    let mut prover = crate::logic_core::ProverEngine::new(egraph);
    prover.theorems = crate::theorems::get_all_theorems()
        .into_iter().map(std::rc::Rc::new).collect();
    let mut engine = crate::logic_core::BlackboardEngine::new(prover);
    let goal = Some(target.clone());
    engine.schedule_full_sweep();
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(seconds);
    let mut idle = 0;
    while std::time::Instant::now() < deadline {
        let applied = engine.run_step(10000);
        if met(&engine.prover.egraph) { return Proof::Proved; }
        if applied { idle = 0; continue; }
        // 手詰まりなら、目標から逆算した補助構成を一度だけ要求してみる。
        if engine.resolve_target_demands(&goal) { idle = 0; continue; }
        idle += 1;
        if idle >= 2 { break; }   // これ以上は時間を使っても伸びない
    }
    if met(&engine.prover.egraph) { Proof::Proved } else { Proof::Open }
}

// ============================================================
// 自由作図で増えた図形を、ブラウザが描ける作図手順に書き戻す
// ============================================================

/// 自由作図が作った実体は「LineThrough(A, Midpoint(B, C))」のような作図式
/// そのものが名前になっていて、そのままでは画面に出せないし、ブラウザ側も
/// どう描けばよいか分からない。発見に出てきたものだけを x1, x2, … という
/// 短い名前に付け替え、依存する図形を先に並べた作図手順として返す。
struct AuxEmitter {
    /// 代表元 -> 既に決まっている名前(ユーザーの図形か、割り当て済みの補助図形)
    names: HashMap<usize, String>,
    counter: usize,
    in_progress: std::collections::HashSet<usize>,
    /// 既に使われている名前。補助作図を「図に取り込む」と x1, x2, … が
    /// ユーザーの作図の一部になるので、次に調べたときに同じ名前を振ると
    /// 画面上で別物が同じ名前になってしまう。それを避けるために持つ。
    used: std::collections::HashSet<String>,
}

impl AuxEmitter {
    fn new(egraph: &EGraph, order: &[(String, ClassId)]) -> Self {
        let mut names = HashMap::new();
        let mut used = std::collections::HashSet::new();
        for (n, id) in order {
            names.entry(egraph.get_rep(*id).0).or_insert_with(|| n.clone());
            used.insert(n.clone());
        }
        AuxEmitter { names, counter: 0, in_progress: std::collections::HashSet::new(), used }
    }

    fn emit_id(&mut self, egraph: &EGraph, id: ClassId, out: &mut Vec<String>) -> Option<String> {
        let rep = egraph.get_rep(id);
        if let Some(n) = self.names.get(&rep.0) { return Some(n.clone()); }
        // 無限遠の点(方向)と無限遠直線はアフィン平面に描けない。
        if rep == egraph.line_infinity { return None; }
        let ty = egraph.entities[rep.0].entity_type;
        if !matches!(ty, EntityType::Point | EntityType::Line | EntityType::Conic) { return None; }
        if ty == EntityType::Point && egraph.is_connected(rep, egraph.line_infinity) { return None; }
        if !self.in_progress.insert(rep.0) { return None; }   // 循環

        let defs: Vec<Definition> = egraph.entities[rep.0].components.first()
            .map(|c| c.definitions.clone()).unwrap_or_default();
        let mut produced: Option<String> = None;
        for def in &defs {
            // 親を全部書き出せる定義を1つ選ぶ。
            let mut arg_names = Vec::new();
            let mut ok = true;
            for p in def.get_parents() {
                match self.emit_id(egraph, p, out) {
                    Some(n) => arg_names.push(n),
                    None => { ok = false; break; }
                }
            }
            if !ok { continue; }
            if let Some(tail) = script_tail(def, &arg_names) { produced = Some(tail); break; }
        }
        self.in_progress.remove(&rep.0);
        let tail = produced?;
        let short = loop {
            self.counter += 1;
            let cand = format!("x{}", self.counter);
            if !self.used.contains(&cand) { break cand; }
        };
        self.used.insert(short.clone());
        let kind = match ty {
            EntityType::Point => "point",
            EntityType::Line => "line",
            _ => "circle",
        };
        out.push(format!("{} {} {}", kind, short, tail));
        self.names.insert(rep.0, short.clone());
        Some(short)
    }
}

/// Definition を作図手順の「opと引数」に戻す(build_egraph の逆)。
/// 書き戻せない定義(角度・複比など画面に描けないもの)は None。
fn script_tail(def: &Definition, args: &[String]) -> Option<String> {
    let joined = |op: &str| Some(format!("{} {}", op, args.join(" ")));
    match def {
        Definition::FreePoint | Definition::GivenPoint => Some("free".to_string()),
        Definition::LineThroughPoints(_, _) => joined("through"),
        Definition::Circumcircle(_, _, _) => joined("through"),
        Definition::Intersection(_, _) => joined("inter"),
        Definition::Midpoint(_, _) => joined("mid"),
        Definition::PerpendicularLine(_, _) => joined("perp"),
        Definition::ParallelLine(_, _) => joined("para"),
        Definition::TangentLine(_, _) => joined("tangent"),
        Definition::RadicalAxis(_, _) => joined("radical"),
        Definition::SecondIntersectionOfLineAndConic(_, _, _) => joined("second_lc"),
        Definition::SecondIntersectionOfCircles(_, _, _) => joined("second_cc"),
        _ => None,
    }
}

fn collect_findings(egraph: &mut EGraph, name_of: &dyn Fn(&EGraph, ClassId) -> String, cap: usize)
    -> Vec<Finding>
{
    use crate::padic_eval as pe;
    const SEEDS: [u64; 3] = [0xC0FFEE, 0xBEEF77, 0x1234ABCD];
    // 総当たりの上限。手で描いた図だけなら数十個で足りるが、自由作図を
    // 回した後は実体が数百になるので、ブラウザから調整できるようにしてある。
    let cap = cap.max(8);
    let mut out: Vec<Finding> = Vec::new();

    // 1. 独立に作った2つの図形が常に一致する
    for (a, b) in pe::find_generic_coincidences(egraph, &SEEDS) {
        if crate::discover::has_degenerate_ancestor(egraph, a, b) { continue; }
        out.push(Finding {
            kind: "coincide",
            text: format!("{} と {} は常に同じ", name_of(egraph, a), name_of(egraph, b)),
            ids: vec![name_of(egraph, a), name_of(egraph, b)],
            refs: vec![a, b],
        });
    }

    // 2. 3点以上が共線
    let triples = pe::find_generic_collinear_triples(egraph, &SEEDS, cap);
    let mut fresh: Vec<Vec<ClassId>> = Vec::new();
    for (a, b, c) in triples {
        let reps = [egraph.get_rep(a), egraph.get_rep(b), egraph.get_rep(c)];
        if egraph.find_common_line(&reps).is_some() { continue; }
        if crate::discover::has_degenerate_ancestor(egraph, a, b) { continue; }
        fresh.push(vec![a, b, c]);
    }
    for set in crate::discover::maximal_verified_sets(egraph, &SEEDS, fresh, pe::PropertyKind::Collinear) {
        let names: Vec<String> = set.iter().map(|&id| name_of(egraph, id)).collect();
        out.push(Finding { kind: "collinear", text: format!("{} は同一直線上にある", names.join(" , ")),
                           ids: names, refs: set.clone() });
    }

    // 3. 3直線以上が1点で交わる
    let conc = pe::find_generic_concurrent_lines(egraph, &SEEDS, cap);
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
        out.push(Finding { kind: "concurrent", text: format!("{} は1点で交わる", names.join(" , ")),
                           ids: names, refs: set.clone() });
    }

    // 4. 3円が1点を共有する(ミケル点・根心型)
    for (a, b, c) in pe::find_generic_concurrent_circles(egraph, &SEEDS, cap) {
        if crate::discover::shares_known_point(egraph, a, b, c) { continue; }
        let names: Vec<String> = [a, b, c].iter().map(|&id| name_of(egraph, id)).collect();
        out.push(Finding { kind: "circles", text: format!("円 {} は1点を共有する", names.join(" , ")),
                           ids: names, refs: vec![a, b, c] });
    }

    // 5. 点が直線・円の上にある
    //
    // 🌟 同じ曲線についての接続は1件にまとめる。まとめないと、九点円の図で
    // 「Haは円np上」「Hbは円np上」「Ha,Hbは円np上」の3件が並ぶ(前2つは
    // 接続検出から、最後は共円検出の言い換えから来る)。読む側にとっては
    // 「この円の上に、まだそうと分かっていなかった点がこれだけ乗る」という
    // 1つの事実なので、曲線ごとに集約する。
    struct Incidence { kind_word: String, curve: ClassId, points: Vec<(String, ClassId)> }
    let mut incidences: std::collections::BTreeMap<String, Incidence> =
        std::collections::BTreeMap::new();
    let mut note_incidence = |egraph: &EGraph, p: ClassId, c: ClassId| {
        let kind_word = if egraph.entities[egraph.get_rep(c).0].entity_type == EntityType::Conic { "円" } else { "直線" };
        let (pn, cn) = (name_of(egraph, p), name_of(egraph, c));
        let e = incidences.entry(cn).or_insert_with(|| Incidence {
            kind_word: kind_word.to_string(), curve: c, points: Vec::new() });
        if !e.points.iter().any(|(n, _)| n == &pn) { e.points.push((pn, p)); }
    };
    for (p, c) in pe::find_generic_point_on_curve(egraph, &SEEDS, cap, cap) {
        if egraph.is_natural_incidence(egraph.get_rep(p), egraph.get_rep(c)) { continue; }
        if crate::discover::has_duplicated_parent(egraph, p)
            || crate::discover::has_duplicated_parent(egraph, c) { continue; }
        note_incidence(egraph, p, c);
    }

    // 6. 4点以上が同一円周上
    let quads = pe::find_generic_concyclic_quadruples(egraph, &SEEDS, cap);
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
            refs: set.clone(),
        });
    }

    for (curve_name, inc) in incidences {
        let point_names: Vec<String> = inc.points.iter().map(|(n, _)| n.clone()).collect();
        let mut ids = point_names.clone();
        ids.push(curve_name.clone());
        let mut refs: Vec<ClassId> = inc.points.iter().map(|(_, id)| *id).collect();
        refs.push(inc.curve);
        out.push(Finding {
            kind: "incident",
            text: format!("点 {} は{} {} の上にある", point_names.join(" , "), inc.kind_word, curve_name),
            ids,
            refs,
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

    /// 🌟 自由作図モードの要: エンジンが図を勝手に伸ばして見つけた関係は、
    /// そこで使った補助的な図形も一緒に返さないと「x3とx7が共点」と言われた
    /// ところで何のことか分からない。返した補助作図が本当にその図形を指して
    /// いるかを、「補助作図を元の図に足して、自由作図なしでもう一度調べると
    /// 同じ関係が出る」ことで確かめる。
    #[test]
    fn exploration_returns_auxiliary_constructions_that_reproduce_the_findings() {
        let triangle = "point A free\npoint B free\npoint C free\nline AB through A B\nline BC through B C\nline CA through C A";
        let out = discover_response(&format!(
            "config rounds 2{n}config seconds 60{n}config cap 220{n}config sweep 34{n}config top 4{n}{}",
            triangle, n = "\n"));
        assert!(out.starts_with("ok|"), "自由作図が走らなかった: {}", out);
        let aux: Vec<&str> = out.lines().filter(|l| l.starts_with("aux|")).map(|l| &l[4..]).collect();
        let found: Vec<&str> = out.lines().filter(|l| l.starts_with("finding|")).collect();
        assert!(!found.is_empty(), "裸の三角形から自由作図すれば何か見つかるはず:{n}{}", out, n = "\n");
        assert!(!aux.is_empty(), "発見に使われた補助作図が返るべき:{n}{}", out, n = "\n");

        // 補助作図を足して、今度は自由作図なしで調べ直す。
        let mut replay = format!("config rounds 0{n}config sweep 34{n}config top 60{n}{}{n}",
            triangle, n = "\n");
        for l in &aux { replay.push_str(l); replay.push('\n'); }
        let out2 = discover_response(&replay);
        assert!(out2.starts_with("ok|"), "書き戻した作図が読めなかった: {}", out2);

        let texts2: Vec<&str> = out2.lines().filter(|l| l.starts_with("finding|"))
            .filter_map(|l| l.splitn(4, '|').nth(2)).collect();
        let reproduced = found.iter().filter_map(|l| l.splitn(4, '|').nth(2))
            .filter(|t| texts2.contains(t)).count();
        assert!(reproduced > 0,
            "補助作図を足し直しても同じ関係が1件も再現しなかった(書き戻しが図形を取り違えている)。{n}1回目:{n}{}{n}2回目:{n}{}",
            out, out2, n = "\n");
    }

    #[test]
    fn reports_a_readable_error_for_a_broken_script() {
        let body = discover_response("line L through A B");
        assert!(body.starts_with("error|") && body.contains("1行目"),
            "壊れた作図はエラー行として返すべき: {}", body);
    }
}

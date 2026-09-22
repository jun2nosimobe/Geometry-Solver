//! 🌟 serve: ブラウザで点・直線・円を自由に作図して自由点を動かし、その図で成り立つ定理をエンジンに探させる。
//! 役割分担:
//!   - 作図と描画・ドラッグはブラウザ側(web/app.js)。ドラッグのたびに図全体を作り直すので、サーバ往復は挟まない。
//!     JS 側の浮動小数点評価器は表示のためだけのもの。
//!   - 「この図で成り立つ定理は何か」はエンジン側。主張の真偽はすべて有限体上の乱数評価(padic_eval)で判定する。
//! ブラウザは「作図手順(DAG)」の編集器で、その手順をこちらへ送ると、EGraph 上に組み直して検出器を回し、見つかった
//! 関係をユーザーが付けた名前のまま返す。描いた位置は検出に使わない(その作図手順である限り常に成り立つ関係を探す)。
//! 依存を増やさないため、HTTP も JSON も使わず、std::net の TcpListener と行指向のテキストプロトコルだけで組んである。

use std::collections::HashMap;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};

use crate::mmp_core::{ClassId, Definition, EGraph, EntityType, GoalStatus};

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
    // 🌟 ユーザー要望「結果を1件ずつ返す方がよい」への対応。探索も証明も
    // 数十秒かかるので、全部終わってからまとめて返すと画面が固まったように
    // 見える。/discover だけは出来たものから1行ずつ流す。
    if method == "POST" && path == "/discover" {
        stream_discover(&mut stream, &body);
        return;
    }
    let (status, content_type, body) = match (method.as_str(), path.as_str()) {
        ("GET", "/") => ("200 OK", "text/html; charset=utf-8", INDEX_HTML.to_string()),
        ("GET", "/app.js") => ("200 OK", "text/javascript; charset=utf-8", APP_JS.to_string()),
        ("GET", "/app.css") => ("200 OK", "text/css; charset=utf-8", APP_CSS.to_string()),
        _ => ("404 Not Found", "text/plain; charset=utf-8", "not found".to_string()),
    };
    let head = format!(
        "HTTP/1.1 {}\r\nContent-Type: {}\r\nContent-Length: {}\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n",
        status, content_type, body.as_bytes().len());
    let _ = stream.write_all(head.as_bytes());
    let _ = stream.write_all(body.as_bytes());
    let _ = stream.flush();
}

/// 探索の途中経過を、出来た行から順にブラウザへ流す。
///
/// 長さを先に書けないので chunked 転送を使う(ブラウザ側は fetch の
/// ReadableStream で受けて、1行届くたびに画面へ足す)。ブラウザが途中で
/// 読むのをやめた(「中止」を押した/タブを閉じた)場合は書き込みが失敗
/// するので、そこで打ち切って無駄な計算を続けない。
fn stream_discover(stream: &mut TcpStream, body: &str) {
    let head = "HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\n\
                Transfer-Encoding: chunked\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n";
    if stream.write_all(head.as_bytes()).is_err() { return; }
    let mut alive = true;
    discover_stream(body, &mut |line: &str| {
        if !alive { return false; }
        let chunk = format!("{:x}\r\n{}\r\n", line.as_bytes().len(), line);
        if stream.write_all(chunk.as_bytes()).is_err() || stream.flush().is_err() {
            alive = false;
        }
        alive
    });
    let _ = stream.write_all(b"0\r\n\r\n");
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

/// ブラウザから変えられる探索時間などの設定。本文の先頭に `config <キー> <値>` の行として混ぜて送られてくる。
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
    /// 1件あたりの証明の仕事量(solve の --steps と同じ単位。100万でおよそ5秒)。0なら試さない。
    prove_steps: u64,
    /// 証明を試す件数の上限(件数 × 仕事量 が待ち時間になるため)。
    prove_max: usize,
}

impl Default for Config {
    fn default() -> Self {
        Config { rounds: 0, cap: 400, per_kind: 8, seconds: 20, sweep: 64, top: 30,
                 prove_steps: 0, prove_max: 12 }
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
                "prove_steps" => cfg.prove_steps = (n as u64).min(50_000_000),
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
    // 🌟 `fact <種類> <名前...>` は作図ではなく「前提として与える主張」。
    // 見つかった性質を前提に積んで先へ進む(UIの「前提にする」ボタン)ための行で、
    // 作図が全部揃ってから適用したいので、ここに集めておく。
    let mut facts: Vec<(usize, String, Vec<String>)> = Vec::new();

    for (lineno, raw) in script.lines().enumerate() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.is_empty() { continue; }
        let t: Vec<&str> = line.split_whitespace().collect();
        let err = |m: String| format!("{}行目: {}", lineno + 1, m);
        if t[0] == "fact" {
            if t.len() < 3 { return Err(err(format!("項目が足りません: 「{}」", line))); }
            facts.push((lineno, t[1].to_string(), t[2..].iter().map(|x| x.to_string()).collect()));
            continue;
        }
        order.push(apply_construction(&mut egraph, &mut env, lineno, line)?);
    }
    if order.is_empty() { return Err("作図が空です".to_string()); }
    egraph.apply_congruence_closure();
    // 🌟 前提として与えられた主張を、作図が揃ってから適用する。
    for (i, (lineno, kind, names)) in facts.iter().enumerate() {
        let err = |m: String| format!("{}行目: {}", lineno + 1, m);
        let mut ids = Vec::new();
        for n in names {
            ids.push(*env.get(n.as_str())
                .ok_or_else(|| err(format!("「{}」がまだ作図されていません", n)))?);
        }
        assert_fact(&mut egraph, kind, &ids, 900_000 + i)
            .ok_or_else(|| err(format!("前提にできない形です: 「fact {} …」", kind)))?;
        egraph.apply_congruence_closure();
    }
    Ok((egraph, order))
}


/// 🌟 作図の1行(`point X inter L1 L2` など)を既存の図に足す。
///
/// 元は build_egraph のループの中身だった。証明の筋書き(sketch.rs)が、
/// 問題ファイルで作った図に人間の証明の補助作図を同じ書き方で足せるように
/// 切り出した。名前は env で引き、作った図形も env に登録する。
pub(crate) fn apply_construction(egraph: &mut EGraph, env: &mut HashMap<String, ClassId>,
                                 lineno: usize, line: &str) -> Result<(String, ClassId), String> {
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
    Ok((name, id))
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
#[derive(Clone, Copy, PartialEq, Debug)]
enum Proof {
    /// 作図を組み直した時点で既に成り立っていた。つまり定理を1つも使わず、
    /// 作図の定義と接続関係の整理(合同閉包)だけで出る = 事実上「自明」。
    /// 検出器の側では「まだ知られていない関係」に見えていても、実際には
    /// 単に自由作図の途中でその接続が張られていなかっただけ、という場合が
    /// これに落ちる。証明できた組の中でも別扱いにしないと、「エンジンが
    /// どれだけ証明できたか」を過大評価してしまう。
    Trivial,
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
            Proof::Trivial => "trivial",
            Proof::Proved => "proved",
            Proof::Open => "open",
            Proof::Unsupported => "unsupported",
        }
    }
}

/// 🌟 発見の「面白さ」(熱・次数・退化したときの関係数)。検出器が出す順は単なる走査順なので、当たり前の話と非自明な
/// 話が混ざる。内訳の生の値は桁がまるで違う(次数は0〜6、退化の関係数は数十〜百超)ので、この回の発見全体での最大値で
/// 割って 0〜1 に揃えてから重みを掛ける。したがって点数は「この回の中での相対的な面白さ」で、別の図の点数とは比べられない。
struct Score {
    /// 主張に出てくる図形の、作図の代数的次数の最大値
    /// (EGraph::cached_degree。自由点を直線上で動かしたときに、その図形の
    /// 座標が何次の有理式で動くか)。中点や平行線は1次で、円と直線の交点や
    /// 垂心のような「本当に効いている」構成ほど高くなる。
    degree: usize,
    /// 熱(GeoEntity::heat_with_degree)の最大値。図の中でどれだけ多くの
    /// ものがその図形の上に建っているか = 図の要になっているか。
    heat: f64,
    /// 退化したときにその図形が他の図形と一致することが観測された相手の数
    /// (padic_eval::compute_degeneration_groups)の、主張に出てくる図形での
    /// 平均。多いほど、極限で他の話と繋がる「結び目」になっている。
    degen: f64,
    /// その種類の最小構成より何個多いか。5点共円は4点共円より強い主張。
    extra: usize,
    /// 主張に出てくる図形のうち、ユーザー自身が描いたものの割合。
    mine: f64,
    /// 上を 0〜1 に正規化して重み付けした合計(normalizeで埋める)。
    total: f64,
}

impl Score {
    /// その種類の主張が成立する最小の図形数。これを超えた分だけが
    /// 「主張が強い」ことを意味する。
    fn minimum_size(kind: &str) -> usize {
        match kind {
            "coincide" | "incident" => 2,
            "concyclic" | "equal_length" => 4,
            "cross_ratio" => 8,
            _ => 3,
        }
    }

    fn of(eg: &EGraph, f: &Finding, is_user: &dyn Fn(&String) -> bool,
          groups: &crate::padic_eval::DegenerationRelations) -> Score {
        let n = f.refs.len().max(1);
        let degree = f.refs.iter().filter_map(|&r| eg.cached_degree(r, 6)).max().unwrap_or(0);
        let heat = f.refs.iter()
            .map(|&r| eg.entities[eg.get_rep(r).0].heat_with_degree())
            .fold(0.0f64, f64::max);
        let degen = f.refs.iter()
            .map(|&r| groups.members_of(eg.get_rep(r)).len() as f64).sum::<f64>() / n as f64;
        let extra = f.refs.len().saturating_sub(Self::minimum_size(f.kind));
        let mine = f.ids.iter().filter(|x| is_user(x)).count() as f64 / n as f64;
        Score { degree, heat, degen, extra, mine, total: 0.0 }
    }

    /// この回の発見全体を見て、内訳を 0〜1 に揃えてから合計を入れる。
    ///
    /// 重みは実測で決めたものではなく、内訳を見て納得できる順になるよう
    /// 選んだ初期値。画面から内訳ごとに並べ替えられるようにしてあるので、
    /// 「この重みだと違う」と分かったら直せる。
    fn normalize(all: &mut [(Finding, Score)]) {
        let max_of = |get: &dyn Fn(&Score) -> f64| -> f64 {
            all.iter().map(|(_, sc)| get(sc)).fold(0.0f64, f64::max).max(1e-9)
        };
        let (md, mh, mg, me) = (
            max_of(&|sc| sc.degree as f64),
            max_of(&|sc| sc.heat),
            max_of(&|sc| sc.degen),
            max_of(&|sc| sc.extra as f64),
        );
        for (_, sc) in all.iter_mut() {
            sc.total = 3.0 * (sc.degree as f64 / md)
                + 1.5 * (sc.degen / mg)
                + 1.0 * (sc.heat / mh)
                + 1.0 * (sc.extra as f64 / me)
                + 1.5 * sc.mine;
        }
    }
}

/// 本文を受け取り、出来た結果から順に `emit` へ渡す。
/// `emit` が false を返したら(ブラウザが読むのをやめたら)そこで打ち切る。
///
/// 流す行:
///   `stage|<状況>`                                今どこを走っているか
///   `ok|<件数>`                                   ここから結果
///   `aux|<作図手順1行>`                            自由作図が足した図形
///   `finding|<番号>|<種類>|<文>|<名前csv>|<次数>|<熱>|<退化>|<点数>`
///   `proof|<番号>|<proved|open|unsupported>`       後から届く証明の結果
///   `error|<メッセージ>`
fn discover_stream(body: &str, emit: &mut dyn FnMut(&str) -> bool) {
    let (cfg, script) = split_config(body);
    let (mut egraph, order) = match build_egraph(&script) {
        Ok(v) => v,
        Err(e) => { emit(&format!("error|{}\n", e)); return; }
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
        if !emit(&format!("stage|図を広げています… ({}段, 最大{}秒)\n", cfg.rounds, cfg.seconds)) { return; }
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(cfg.seconds);
        crate::discover::systematic_closure_until(
            &mut egraph, cfg.rounds, cfg.cap, cfg.per_kind, Some(deadline));
    }

    if !emit(&format!("stage|{}個の図形から関係を探しています…\n", egraph.entities.len())) { return; }
    let findings = collect_findings(&mut egraph, &name_of, cfg.sweep);

    // 🌟 面白い順に並べる(Scoreのドキュメント参照)。退化の走査も次数の
    // 測定も実測で数十ミリ秒なので、毎回計算してよい。
    if !emit("stage|面白さを測っています…\n") { return; }
    let is_user = |n: &String| order.iter().any(|(name, _)| name == n);
    let groups = crate::padic_eval::compute_degeneration_groups(&egraph, 0x5EED_1234, 2);
    let mut scored: Vec<(Finding, Score)> = findings.into_iter()
        .map(|f| { let sc = Score::of(&egraph, &f, &is_user, &groups); (f, sc) })
        .collect();
    Score::normalize(&mut scored);
    scored.sort_by(|a, b| b.1.total.partial_cmp(&a.1.total).unwrap_or(std::cmp::Ordering::Equal));
    // 🌟 1つの検出器が上位を埋め尽くさないよう、種類ごとに取り分の上限を設ける(自由作図は中点や平行線を大量に作るので
    // 等長が山ほど出る)。あふれた分は捨てずに後ろへ回すだけで、点数順は各種類の中で保たれる。
    let per_kind_cap = (cfg.top / 3).max(3);
    let mut seen_of_kind: HashMap<&str, usize> = HashMap::new();
    let (mut kept, mut spill): (Vec<(Finding, Score)>, Vec<(Finding, Score)>) = (Vec::new(), Vec::new());
    for item in scored {
        let n = seen_of_kind.entry(item.0.kind).or_insert(0);
        if *n < per_kind_cap { *n += 1; kept.push(item); } else { spill.push(item); }
    }
    kept.append(&mut spill);
    let mut scored = kept;
    scored.truncate(cfg.top);

    // 発見に出てくる補助的な図形を、ブラウザが描けるように作図手順として
    // 書き出す。これが無いと「x3 と x7 が共点」と言われても何のことか
    // 分からない。必要なものだけを、依存関係の順に返す。
    let mut emitter = AuxEmitter::new(&egraph, &order);
    let mut aux_lines: Vec<String> = Vec::new();
    let mut renamed: HashMap<String, String> = HashMap::new();
    for (f, _) in &scored {
        for (n, id) in f.ids.iter().zip(f.refs.iter()) {
            if is_user(n) || renamed.contains_key(n) { continue; }
            if let Some(short) = emitter.emit_id(&egraph, *id, &mut aux_lines) {
                renamed.insert(n.clone(), short);
            }
        }
    }

    if !emit(&format!("ok|{}\n", scored.len())) { return; }
    for line in &aux_lines {
        if !emit(&format!("aux|{}\n", line)) { return; }
    }
    // 表示用の名前(長い作図式は x1, x2, … に差し替え済み)。証明のときに
    // 図を組み直すのにも、この名前をそのまま使う。
    let mut shown_ids: Vec<Vec<String>> = Vec::new();
    for (i, (f, sc)) in scored.iter().enumerate() {
        let ids: Vec<String> = f.ids.iter()
            .map(|n| renamed.get(n).cloned().unwrap_or_else(|| n.clone())).collect();
        let mut text = f.text.clone();
        let mut subs: Vec<(&String, &String)> = renamed.iter().collect();
        subs.sort_by_key(|(long, _)| std::cmp::Reverse(long.len()));
        for (long, short) in subs {
            if long != short { text = text.replace(long.as_str(), short.as_str()); }
        }
        let line = format!("finding|{}|{}|{}|{}|{}|{:.1}|{:.1}|{:.2}\n",
            i, f.kind, text, ids.join(","), sc.degree, sc.heat, sc.degen, sc.total);
        shown_ids.push(ids);
        if !emit(&line) { return; }
    }

    // 🌟 「すぐ証明できるか」を試す(prove_steps が 0 なら飛ばす)。
    if cfg.prove_steps > 0
        && !prove_and_report(&scored, &shown_ids, &script, &aux_lines, &cfg, emit) { return; }
    emit("stage|\n");
}

/// 見つかった主張を証明してみて、決まったものから順に流す。
///
/// 2段構えにしてある。まず上位の主張をまとめて1つの図に載せ、1回の推論を
/// 全部で共有する(同じ図の同じ基本的な事実を主張の数だけ導き直さない)。
/// そこで出なかったものだけを、必要な作図だけに絞った小さい図で1件ずつ
/// 本気で解く。戻り値は「ブラウザがまだ読んでいるか」。
/// 証明できたかは「今の定理集合ですぐ出る = だいたい既知・簡単」と「数値的には確かなのに出てこない = 面白い候補」を
/// 分ける目安で、証明できないことは偽である根拠にならない(制限時間と定理集合の都合でしかない)。
fn prove_and_report(scored: &[(Finding, Score)], shown_ids: &[Vec<String>],
                    script: &str, aux_lines: &[String], cfg: &Config,
                    emit: &mut dyn FnMut(&str) -> bool) -> bool
{
    // 🌟 証明を試す枠は種類ごとに順番に配る。点数順に上から取ると、数の多い検出器が枠を埋め、共点性のような種類が
    // 一度も試されない(共点性の目標でしか動かない resolve_cross_ratio_demands が一度も呼ばれなかった)。
    let mut by_kind: Vec<(&str, Vec<usize>)> = Vec::new();
    for (i, (f, _)) in scored.iter().enumerate() {
        match by_kind.iter_mut().find(|(k, _)| *k == f.kind) {
            Some((_, v)) => v.push(i),
            None => by_kind.push((f.kind, vec![i])),
        }
    }
    let mut order: Vec<usize> = Vec::new();
    let mut round = 0;
    while order.len() < scored.len() {
        let mut added = false;
        for (_, v) in by_kind.iter() {
            if let Some(&i) = v.get(round) { order.push(i); added = true; }
        }
        if !added { break; }
        round += 1;
    }
    let n = order.len().min(cfg.prove_max);
    let mut result: Vec<Proof> = vec![Proof::Unsupported; scored.len()];

    // --- 第1段: まとめて推論する ---
    if !emit(&format!("stage|{}件をまとめて推論しています…\n", n)) { return false; }
    let chosen: Vec<usize> = order[..n].to_vec();
    let all_ids: Vec<String> = chosen.iter().flat_map(|&i| shown_ids[i].clone()).collect();
    let mut shared: Vec<usize> = Vec::new();      // targets[k] は scored[shared[k]]
    if let Some((mut eg, names)) = proof_figure(script, aux_lines, &all_ids) {
        let mut targets = Vec::new();
        for &i in &chosen {
            let refs: Option<Vec<ClassId>> =
                shown_ids[i].iter().map(|x| names.get(x).copied()).collect();
            let refs = match refs { Some(r) => r, None => continue };
            if let Some(t) = goal_for(&mut eg, scored[i].0.kind, &refs, i) {
                shared.push(i);
                targets.push(t);
            }
        }
        let done = prove_together(eg, &targets, cfg.prove_steps);
        for (k, &i) in shared.iter().enumerate() { result[i] = done[k]; }
    }
    for &i in &chosen {
        if result[i] != Proof::Open
            && !emit(&format!("proof|{}|{}\n", i, result[i].tag())) { return false; }
    }

    // --- 第2段: 残りを1件ずつ、その主張のためだけの図で ---
    let rest: Vec<usize> = chosen.iter().copied().filter(|&i| result[i] == Proof::Open).collect();
    for (k, &i) in rest.iter().enumerate() {
        if !emit(&format!("stage|残りを1件ずつ確かめています… {}/{}\n", k + 1, rest.len())) {
            return false;
        }
        let refs_and_figure = proof_figure(script, aux_lines, &shown_ids[i])
            .and_then(|(mut eg, names)| {
                let refs: Option<Vec<ClassId>> =
                    shown_ids[i].iter().map(|x| names.get(x).copied()).collect();
                let t = goal_for(&mut eg, scored[i].0.kind, &refs?, i)?;
                Some((eg, t))
            });
        if let Some((eg, t)) = refs_and_figure {
            result[i] = prove_together(eg, &[t], cfg.prove_steps)[0];
        }
        if !emit(&format!("proof|{}|{}\n", i, result[i].tag())) { return false; }
    }
    true
}

#[cfg(test)]
fn discover_response(body: &str) -> String {
    let mut out = String::new();
    discover_stream(body, &mut |l: &str| { out.push_str(l); true });
    out
}

// ============================================================
// 見つかった主張を、実際に証明できるか試す
// ============================================================

/// この主張に実際に必要な補助作図だけを、依存関係を辿って選ぶ。
/// `aux` の各行は `<種類> <名前> <演算> <引数…>` という形なので、4つ目以降のトークンがその図形の材料になる。
/// ユーザーの図形の名前は `aux` に無いので、辿るのはそこで自然に止まる。
fn needed_aux_lines(ids: &[String], aux: &[String]) -> Vec<String> {
    let mut index: HashMap<&str, usize> = HashMap::new();
    for (i, l) in aux.iter().enumerate() {
        if let Some(n) = l.split_whitespace().nth(1) { index.insert(n, i); }
    }
    let mut want = vec![false; aux.len()];
    let mut stack: Vec<String> = ids.to_vec();
    while let Some(n) = stack.pop() {
        let i = match index.get(n.as_str()) { Some(&i) => i, None => continue };
        if want[i] { continue; }
        want[i] = true;
        for t in aux[i].split_whitespace().skip(3) { stack.push(t.to_string()); }
    }
    aux.iter().zip(want).filter(|(_, w)| *w).map(|(l, _)| l.clone()).collect()
}

/// 🌟 主張に出てくる図形と、その材料になる補助作図だけを選んで作図し直した小さい図を返す。自由作図で膨らませた
/// EGraph(実体数百)をそのまま証明に渡すと、schedule_full_sweep が主張と無関係な組み合わせを舐めるだけで時間が終わる。
fn proof_figure(user_script: &str, aux: &[String], ids: &[String])
    -> Option<(EGraph, HashMap<String, ClassId>)>
{
    let mut text = user_script.trim_end().to_string();
    for l in needed_aux_lines(ids, aux) {
        text.push('\n');
        text.push_str(&l);
    }
    let (eg, order) = build_egraph(&text).ok()?;
    Some((eg, order.into_iter().collect()))
}

/// 🌟 見つかった主張を「前提」として図に書き込む(UIの「前提にする」)。
///
/// 目標に翻訳する goal_for をそのまま使い、証明しに行く代わりに成り立つものと
/// して与える。これで「この性質を認めたら、次に何が出るか」を試せる ―
/// 人間が補題を1つ認めて先へ進むのと同じことを、画面の上でできるようにする。
/// 与えた根拠は Justification::Given なので、あとから証明を辿れば
/// 「ここは前提として置いた」と分かる。
pub(crate) fn assert_fact(egraph: &mut EGraph, kind: &str, r: &[ClassId], tag: usize) -> Option<()> {
    let (goal_kind, args) = goal_for(egraph, kind, r, tag)?;
    let given = crate::mmp_core::Justification::Given;
    match goal_kind.as_str() {
        "Identical" if args.len() >= 2 => { egraph.merge_entities_justified(args[0], args[1], given); }
        "Connected" if args.len() >= 2 => { egraph.link_logical_incidence_justified(args[0], args[1], given); }
        "Concyclic" if args.len() >= 4 => {
            let circ = egraph.create_entity(format!("FactCirc{}", tag),
                Definition::Circumcircle(args[0], args[1], args[2]), EntityType::Conic);
            for &p in &args[3..] {
                egraph.link_logical_incidence_justified(p, circ, given.clone());
            }
        }
        _ => return None,
    }
    Some(())
}

/// 主張の形ごとに、既存の証明目標(Identical / Connected / Concyclic)へ翻訳する。
/// 共線・共点は目標用の実体(2直線・2交点)をその図の上に作る。
pub(crate) fn goal_for(egraph: &mut EGraph, kind: &str, r: &[ClassId], tag: usize)
    -> Option<(String, Vec<ClassId>)>
{
    Some(match kind {
        "coincide" if r.len() >= 2 => ("Identical".to_string(), vec![r[0], r[1]]),
        "incident" if r.len() >= 2 => {
            // ids は [点..., 曲線] の並び。最後が曲線。
            ("Connected".to_string(), vec![r[0], *r.last().unwrap()])
        }
        "concyclic" if r.len() >= 4 => ("Concyclic".to_string(), r.to_vec()),
        // 🌟 スカラーの主張は、その量を実体として作ってから Identical を狙う。
        // これで初めて定理集合の計量側(方冪の定理など)が証明で試される。
        "equal_length" if r.len() >= 4 => {
            let s1 = egraph.create_entity(format!("Goal{}_Len1", tag),
                Definition::LengthSq(r[0], r[1]), EntityType::Scalar);
            let s2 = egraph.create_entity(format!("Goal{}_Len2", tag),
                Definition::LengthSq(r[2], r[3]), EntityType::Scalar);
            ("Identical".to_string(), vec![s1, s2])
        }
        "cross_ratio" if r.len() >= 8 => {
            let s1 = egraph.create_entity(format!("Goal{}_CR1", tag),
                Definition::CrossRatio(r[0], r[1], r[2], r[3]), EntityType::Scalar);
            let s2 = egraph.create_entity(format!("Goal{}_CR2", tag),
                Definition::CrossRatio(r[4], r[5], r[6], r[7]), EntityType::Scalar);
            ("Identical".to_string(), vec![s1, s2])
        }
        "collinear" if r.len() >= 3 => {
            // 「P,Q,R が共線」= 直線PQ と 直線PR が同じ。
            let l1 = egraph.create_entity(format!("Goal{}_L1", tag),
                Definition::new_line(r[0], r[1]), EntityType::Line);
            let l2 = egraph.create_entity(format!("Goal{}_L2", tag),
                Definition::new_line(r[0], r[2]), EntityType::Line);
            ("Identical".to_string(), vec![l1, l2])
        }
        "concurrent" if r.len() >= 3 => {
            // 「l1,l2,l3 が共点」= l1∩l2 と l1∩l3 が同じ点。
            let p1 = egraph.create_entity(format!("Goal{}_P1", tag),
                Definition::Intersection(r[0], r[1]), EntityType::Point);
            let p2 = egraph.create_entity(format!("Goal{}_P2", tag),
                Definition::Intersection(r[0], r[2]), EntityType::Point);
            ("Identical".to_string(), vec![p1, p2])
        }
        // 🌟 証明の筋書き(sketch.rs)で人間の証明の手順を書くための語彙。
        // 直線は「直線2本」でも「点4つ(AB と CD)」でも書ける。
        "parallel" => {
            let (l1, l2) = two_lines(egraph, r, tag)?;
            let d1 = egraph.create_entity(format!("Goal{}_D1", tag), Definition::DirectionOf(l1), EntityType::Point);
            let d2 = egraph.create_entity(format!("Goal{}_D2", tag), Definition::DirectionOf(l2), EntityType::Point);
            ("Identical".to_string(), vec![d1, d2])
        }
        "perpendicular" => {
            let (l1, l2) = two_lines(egraph, r, tag)?;
            let d1 = egraph.create_entity(format!("Goal{}_D1", tag), Definition::DirectionOf(l1), EntityType::Point);
            let d2 = egraph.create_entity(format!("Goal{}_D2", tag), Definition::DirectionOf(l2), EntityType::Point);
            let ang = egraph.create_entity(format!("Goal{}_A", tag), Definition::AnglePair(d1, d2), EntityType::Scalar);
            ("Identical".to_string(), vec![ang, egraph.ang90])
        }
        // 有向角 ∠(AB,CD) = ∠(EF,GH)。点8つか直線4本で書く。
        "equal_angle" => {
            let lines: Vec<ClassId> = if r.len() == 4 && r.iter().all(|&x| egraph.entities[egraph.get_rep(x).0].entity_type == EntityType::Line) {
                r.to_vec()
            } else if r.len() == 8 {
                (0..4).map(|i| egraph.create_entity(format!("Goal{}_L{}", tag, i),
                    Definition::new_line(r[2 * i], r[2 * i + 1]), EntityType::Line)).collect()
            } else {
                return None;
            };
            let d: Vec<ClassId> = lines.iter().enumerate().map(|(i, &l)| egraph.create_entity(
                format!("Goal{}_D{}", tag, i), Definition::DirectionOf(l), EntityType::Point)).collect();
            let a1 = egraph.create_entity(format!("Goal{}_A1", tag), Definition::AnglePair(d[0], d[1]), EntityType::Scalar);
            let a2 = egraph.create_entity(format!("Goal{}_A2", tag), Definition::AnglePair(d[2], d[3]), EntityType::Scalar);
            ("Identical".to_string(), vec![a1, a2])
        }
        // 3円共点はまだ証明目標の語彙に無い。
        _ => return None,
    })
}

/// 「直線2本」か「点4つ(AB と CD)」を2本の直線にする。
fn two_lines(egraph: &mut EGraph, r: &[ClassId], tag: usize) -> Option<(ClassId, ClassId)> {
    let is = |eg: &EGraph, x: ClassId, ty: EntityType| eg.entities[eg.get_rep(x).0].entity_type == ty;
    if r.len() == 2 && is(egraph, r[0], EntityType::Line) && is(egraph, r[1], EntityType::Line) {
        return Some((r[0], r[1]));
    }
    if r.len() == 4 && r.iter().all(|&x| is(egraph, x, EntityType::Point)) {
        let l1 = egraph.create_entity(format!("Goal{}_L1", tag), Definition::new_line(r[0], r[1]), EntityType::Line);
        let l2 = egraph.create_entity(format!("Goal{}_L2", tag), Definition::new_line(r[2], r[3]), EntityType::Line);
        return Some((l1, l2));
    }
    None
}

/// 🌟 目標をまとめて1つの図で解く。1件ずつ解くと、どれも同じ図の同じ基本的な事実をゼロから導き直すが、まとめれば
/// 導かれた事実が EGraph に溜まり、2件目以降はその続きから始まる。
/// 定理集合・手詰まりのときの回復・目標の判定は solve と共通(theorems::theorem_set / BlackboardEngine::recover /
/// EGraph::goal_status)。中点の需要は solve では既定で切っているが、自由作図の主張では中点1つが足りないだけの形が
/// 多いので使う。MCTS は入れない(結果が実行ごとにぶれ、決定的な回復手段で届くならその方が速く確実)。
/// 予算は solve と同じく仕事量(steps)で測るので、同じ図なら何度試しても同じ結果になる。秒は暴走を止める安全弁。
fn prove_together(mut egraph: EGraph, targets: &[(String, Vec<ClassId>)], steps: u64)
    -> Vec<Proof>
{
    egraph.apply_congruence_closure();
    // 定理を1つも使わずに出るもの(作図の定義と接続関係の整理だけで済むもの)は
    // 「作図から自明」として、証明できた件数とは別に数える。そうしないと
    // エンジンの証明能力を過大評価してしまう。
    let trivial: Vec<bool> = targets.iter().map(|t| egraph.goal_status(Some(t)) == GoalStatus::Reached).collect();
    let mut done: Vec<bool> = trivial.clone();
    let finish = |done: &[bool], trivial: &[bool]| -> Vec<Proof> {
        done.iter().zip(trivial).map(|(&d, &t)| {
            if t { Proof::Trivial } else if d { Proof::Proved } else { Proof::Open }
        }).collect()
    };
    if targets.is_empty() || done.iter().all(|d| *d) { return finish(&done, &trivial); }

    let mut prover = crate::logic_core::ProverEngine::new(egraph);
    prover.theorems = crate::theorems::theorem_set(&Default::default())
        .into_iter().map(std::rc::Rc::new).collect();
    let mut engine = crate::logic_core::BlackboardEngine::new(prover);
    engine.work_limit = steps;
    engine.schedule_full_sweep();
    let recovery = crate::logic_core::RecoveryOptions { midpoint_demands: true, skip: Vec::new() };
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(PROVE_TIME_CAP_SECS);
    let mut rotate = 0usize;
    while engine.prover.work_done() < steps && std::time::Instant::now() < deadline {
        let applied = engine.run_step(10000);
        // 図が潰れたら、そこから導いたものは何も信用できない。
        if engine.prover.egraph.merged_free_points().is_some() {
            return finish(&trivial, &trivial);
        }
        let mut all_done = true;
        for (i, t) in targets.iter().enumerate() {
            if !done[i] && engine.prover.egraph.goal_reached(t) { done[i] = true; }
            if !done[i] { all_done = false; }
        }
        if all_done { break; }
        if applied { continue; }

        // まだ導けていない目標を順に回して、逆算した補助線を要求する。
        let open: Vec<(String, Vec<ClassId>)> = targets.iter().zip(&done)
            .filter(|(_, d)| !**d).map(|(t, _)| t.clone()).collect();
        if engine.recover(&open, &mut rotate, &recovery) == crate::logic_core::Recovered::Exhausted {
            break;   // これ以上は予算を使っても伸びない
        }
    }
    for (i, t) in targets.iter().enumerate() {
        if !trivial[i] {
            done[i] = engine.prover.egraph.goal_status(Some(t)) == GoalStatus::Reached;
        }
    }
    finish(&done, &trivial)
}

/// 証明1回あたりの壁時計の上限(暴走を止める安全弁。本当の予算は仕事量)。
const PROVE_TIME_CAP_SECS: u64 = 15;

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
        if let Some((circle, extra)) = crate::discover::known_circle_through_most(egraph, &set)
            && !extra.is_empty() {
                for &id in &extra { note_incidence(egraph, id, circle); }
                continue;
            }
        let names: Vec<String> = set.iter().map(|&id| name_of(egraph, id)).collect();
        out.push(Finding {
            kind: "concyclic",
            text: format!("{}点 {} は同一円周上にある", names.len(), names.join(" , ")),
            ids: names,
            refs: set.clone(),
        });
    }

    // 🌟 7. 長さの二乗が等しい2つの線分
    for q in pe::find_generic_equal_lengths(egraph, &SEEDS, cap) {
        // 端点を共有する場合(|AB|=|AC|)は「AはB,Cから等距離」の言い換え。
        // どちらも報告する価値があるので、文だけ読みやすく分ける。
        let n: Vec<String> = q.iter().map(|&id| name_of(egraph, id)).collect();
        let text = if q[0] == q[2] || q[0] == q[3] || q[1] == q[2] || q[1] == q[3] {
            format!("{}{} と {}{} の長さは等しい", n[0], n[1], n[2], n[3])
        } else {
            format!("線分 {}{} と {}{} の長さは等しい", n[0], n[1], n[2], n[3])
        };
        out.push(Finding { kind: "equal_length", text, ids: n, refs: q.to_vec() });
    }

    // 🌟 8. 複比が等しい2つの4点組(射影的な主張)
    for q in pe::find_generic_equal_cross_ratios(egraph, &SEEDS, cap) {
        let n: Vec<String> = q.iter().map(|&id| name_of(egraph, id)).collect();
        out.push(Finding {
            kind: "cross_ratio",
            text: format!("({} , {} ; {} , {}) と ({} , {} ; {} , {}) の複比は等しい",
                n[0], n[1], n[2], n[3], n[4], n[5], n[6], n[7]),
            ids: n,
            refs: q.to_vec(),
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

    /// 応答は進捗の `stage|` 行から始まるので、先頭一致ではなく
    /// 「その印で始まる行があるか」で見る。
    fn has(out: &str, prefix: &str) -> bool {
        out.lines().any(|l| l.starts_with(prefix))
    }

    /// `finding|<番号>|<種類>|<文>|…` の <文> の部分。
    fn finding_text(line: &str) -> Option<&str> {
        line.split('|').nth(3)
    }

    /// 三角形と3本の高さ。エンジンが普通に解けるいちばんやさしい図。
    const ORTHOCENTER: &str = "point A free
point B free
point C free
        line AB through A B
line BC through B C
line CA through C A
        line altA perp BC A
line altB perp CA B
line altC perp AB C";

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
        assert!(has(&body, "ok|") || has(&body, "error|"),
            "何らかの応答を返すべき: {}", body);
    }

    /// 🌟 ブラウザで垂心の図を描いたときに、エンジンが「3本目の高さもその交点を通る」を見つけて証明できること。
    /// UIから検出・証明までの経路がひと続きに動いていることの確認。
    /// 🐛 証明を試す側が回復フェーズ(需要駆動の補助線・補助点・角度、候補capの拡張)を呼ばずに打ち切っていた取りこぼしの
    /// 回帰テストでもある。ここが未証明に戻ったら同じ取りこぼしの再発。
    #[test]
    fn the_easiest_theorem_is_actually_proved() {
        let out = discover_response(&format!(
            "config rounds 0{n}config prove_steps 6000000{n}config prove_max 4{n}{}",
            ORTHOCENTER, n = "\n"));
        assert!(has(&out, "ok|"), "作図が通らなかった: {}", out);
        let proofs: Vec<&str> = out.lines().filter(|l| l.starts_with("proof|")).collect();
        assert!(!proofs.is_empty(), "証明の結果が1件も返っていない:{n}{}", out, n = "\n");
        assert!(proofs.iter().any(|l| l.ends_with("proved")),
            "垂心の共点性は今の定理集合で普通に証明できるはず(回復フェーズが\
             呼ばれていない可能性が高い):{n}{}", out, n = "\n");
    }

    /// 🌟 発見の面白さの並べ替えの確認。「どれが本当に面白いか」は測れないので、(1)内訳が3つとも行に乗っていること、
    /// (2)合計点の降順で並んでいること、(3)退化の指標が自由作図の後でも値を持つこと(代表元の取り違えで0になっていた
    /// 不具合の回帰)を見る。
    #[test]
    fn findings_come_back_ranked_with_their_score_breakdown() {
        let out = discover_response(&format!(
            "config rounds 2{n}config seconds 45{n}config cap 240{n}config sweep 40{n}config top 10{n}{}",
            ORTHOCENTER, n = "\n"));
        assert!(has(&out, "ok|"), "自由作図が走らなかった: {}", out);
        let rows: Vec<Vec<&str>> = out.lines().filter(|l| l.starts_with("finding|"))
            .map(|l| l.split('|').collect()).collect();
        assert!(rows.len() >= 2, "並べ替えを見るには2件以上必要:{n}{}", out, n = "\n");

        let mut previous = f64::INFINITY;
        let mut any_degen = false;
        for r in &rows {
            assert_eq!(r.len(), 9, "内訳の欄が足りない: {:?}", r);
            let degen: f64 = r[7].parse().expect("退化の欄が数値でない");
            let total: f64 = r[8].parse().expect("点数の欄が数値でない");
            assert!(total <= previous + 1e-9, "面白さの降順になっていない:{n}{}", out, n = "\n");
            previous = total;
            if degen > 0.0 { any_degen = true; }
        }
        assert!(any_degen,
            "自由作図の後も退化の関係が測れているべき(自由点が代表元でなくなると\
             丸ごと0になる不具合があった):{n}{}", out, n = "\n");
    }

    /// 🐛 回帰テスト: 自由作図が見つけた「BC と、ABに平行でACの中点を通る直線と、CAに平行でABの中点を通る直線が1点で
    /// 交わる」(中点連結定理の形)。足りなかったのは探索の幅でも定理でもなく補助点(BCの中点)1つで、それを一般の手に
    /// したのが BlackboardEngine::resolve_midpoint_demands。自由作図はこの形(平行線を「垂線の垂線」として作る)で出して
    /// くるので、その形のまま確かめる。
    #[test]
    fn a_missing_midpoint_no_longer_blocks_the_proof() {
        // x14 は x13(ABへの垂線)への垂線 = ABに平行で、ACの中点を通る。
        // x16 は x1(CAへの垂線)への垂線 = CAに平行で、ABの中点を通る。
        let figure = "point A free\npoint B free\npoint C free\n\
            line AB through A B\nline BC through B C\nline CA through C A\n\
            circle O through A B C\n\
            line x13 perp AB B\npoint x8 mid A C\nline x14 perp x13 x8\n\
            line x1 perp CA A\npoint x15 mid A B\nline x16 perp x1 x15";
        let ids: Vec<String> = ["BC", "x14", "x16"].iter().map(|x| x.to_string()).collect();
        let (mut eg, names) = proof_figure(figure, &[], &ids).expect("図が組めるべき");
        let refs: Vec<ClassId> = ids.iter().map(|n| names[n]).collect();
        let target = goal_for(&mut eg, "concurrent", &refs, 0).expect("共点は目標にできるべき");
        let got = prove_together(eg, &[target], 6_000_000)[0];
        assert_eq!(got, Proof::Proved,
            "中点連結定理の形は証明できるべき(得られたのは {:?})。\
             needed な中点が補われていない可能性が高い。", got.tag());
    }

    /// 🌟 `fact <種類> <名前...>` で、見つかった性質を前提として図に与えられること(UIの「前提にする」)。与えた後はそれが
    /// 構造的に知られているので、同じ主張が「発見」としては二度と出ない。
    #[test]
    fn a_finding_can_be_given_as_an_assumption() {
        let base = "point A free
point B free
point C free
point D free
line l1 through A B
line l2 through C D
point P inter l1 l2";
        let cfg = "config rounds 0
config sweep 40
config top 30
";

        // 前提なし: A, B, C は共線では無い。
        let plain = discover_response(&format!("{}{}", cfg, base));
        assert!(has(&plain, "ok|"), "作図が通らなかった: {}", plain);

        // 前提を与えるとエラーにならず、その共線は以後「既知」になる。
        let with_fact = discover_response(&format!("{}{}
fact collinear A B C", cfg, base));
        assert!(has(&with_fact, "ok|"), "前提を与えたら作図が通らなくなった: {}", with_fact);
        let reported_again = with_fact.lines().any(|l| {
            l.starts_with("finding|") && l.split('|').nth(2) == Some("collinear")
                && { let ids = l.split('|').nth(4).unwrap_or("");
                     ids.contains('A') && ids.contains('B') && ids.contains('C') }
        });
        assert!(!reported_again,
            "前提として与えた共線が、まだ「発見」として報告されている:{n}{}", with_fact, n = "
");

        // 知らない名前を指す前提は、黙って無視せずエラーにする。
        let bad = discover_response(&format!("{}{}
fact collinear A B Z", cfg, base));
        assert!(!has(&bad, "ok|"), "存在しない名前を指す前提が通ってしまった: {}", bad);
    }

    /// 🐛 中点を作るだけで「AM = MB」が発見として上がってこないこと(Midpoint から LengthSq の相等を構造的に出すことと、
    /// 検出器が既知の相等を落とすことの両方の回帰)。
    #[test]
    fn a_plain_midpoint_is_not_reported_as_a_discovery() {
        let script = "point A free
point B free
point M mid A B";
        let out = discover_response(&format!(
            "config rounds 0{n}config sweep 40{n}config top 20{n}{}", script, n = "
"));
        assert!(has(&out, "ok|"), "作図が通らなかった: {}", out);
        let rows: Vec<&str> = out.lines()
            .filter(|l| l.starts_with("finding|") && l.split('|').nth(2) == Some("equal_length"))
            .collect();
        assert!(rows.is_empty(),
            "中点の定義から直に従う長さの等式が発見として報告されている:{n}{:?}",
            rows, n = "
");
    }

    /// 🌟 垂直二等分線上の点はその線分の両端から等距離、という素直な計量の主張で、(1)検出できること、(2)証明の目標に
    /// 翻訳して実際に証明が通ること(計量側の定理が実戦で使われること)を見る。
    #[test]
    fn finds_and_proves_an_equal_length_claim() {
        let script = "point A free
point B free
point C free
            line BC through B C
line CA through C A
            point M mid B C
line pb perp BC M
point Oc inter pb CA";
        let out = discover_response(&format!(
            "config rounds 0{n}config sweep 40{n}config top 20{n}             config prove_steps 6000000{n}config prove_max 10{n}{}", script, n = "
"));
        assert!(has(&out, "ok|"), "作図が通らなかった: {}", out);

        let rows: Vec<&str> = out.lines()
            .filter(|l| l.starts_with("finding|") && l.split('|').nth(2) == Some("equal_length"))
            .collect();
        assert!(!rows.is_empty(), "長さの等式が1件も検出されていない:{n}{}", out, n = "
");

        // 「Oc は B と C から等距離」が検出され、しかも証明できるはず。
        let target = rows.iter().find(|l| {
            let ids = l.split('|').nth(4).unwrap_or("");
            ids.contains("Oc") && ids.contains('B') && ids.contains('C')
        }).unwrap_or_else(|| panic!("垂直二等分線上の点の等距離が出ていない:{}", out));
        let idx = target.split('|').nth(1).unwrap();
        let proof = out.lines()
            .find(|l| l.starts_with(&format!("proof|{}|", idx)))
            .unwrap_or_else(|| panic!("この主張の証明結果が返っていない:{}", out));
        assert!(proof.ends_with("proved") || proof.ends_with("trivial"),
            "垂直二等分線の距離の等価性は証明できるはず(得られたのは {}):{n}{}",
            proof, out, n = "
");
    }

    /// 🌟 「複比の透視射影不変性の逆」(EGraph::propagate_cross_ratio_uniqueness)は、(A,B;C,P) と (A,B;C,Q) の2つの複比が
    /// 実体として存在しないと発火しない。目標が「同じ直線上の2点の一致」のときだけ、その直線上の他の3点を使って2つの複比を
    /// 作る(resolve_cross_ratio_demands)。その作図が実際に行われることを確かめる。
    #[test]
    fn a_point_identity_goal_builds_the_two_cross_ratios() {
        let script = "point A free
point B free
line L through A B
            point C on L
point X free
point Y free
point Z free
            line m1 through X Y
point P inter L m1
            line m2 through X Z
point Q inter L m2";
        let (egraph, order) = build_egraph(script).expect("図が組めるべき");
        let find = |n: &str| order.iter().find(|(nm, _)| nm == n).unwrap().1;
        let (p, q) = (find("P"), find("Q"));

        let before = egraph.entities.iter()
            .filter(|e| matches!(e.original_definition, Definition::CrossRatio(..))).count();
        assert_eq!(before, 0, "まだ複比は1つも作られていないはず");

        let mut prover = crate::logic_core::ProverEngine::new(egraph);
        prover.theorems = crate::theorems::theorem_set(&Default::default())
            .into_iter().map(std::rc::Rc::new).collect();
        let mut engine = crate::logic_core::BlackboardEngine::new(prover);
        let goal = Some(("Identical".to_string(), vec![p, q]));
        assert!(engine.resolve_cross_ratio_demands(&goal),
            "同じ直線上の2点の一致が目標なら、複比を作るはず");

        let after = engine.prover.egraph.entities.iter()
            .filter(|e| matches!(e.original_definition, Definition::CrossRatio(..))).count();
        assert_eq!(after, 2, "目標の2点それぞれについて複比が1つずつ作られるはず(作られたのは{}個)", after);
    }

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
        assert!(has(&body, "ok|"), "作図が通らなかった: {}", body);
        let found_concurrency = body.lines().any(|l| {
            l.starts_with("finding|") && l.split('|').nth(2) == Some("concurrent")
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
        assert!(has(&out, "ok|"), "自由作図が走らなかった: {}", out);
        let aux: Vec<&str> = out.lines().filter(|l| l.starts_with("aux|")).map(|l| &l[4..]).collect();
        let found: Vec<&str> = out.lines().filter(|l| l.starts_with("finding|")).collect();
        assert!(!found.is_empty(), "裸の三角形から自由作図すれば何か見つかるはず:{n}{}", out, n = "\n");
        assert!(!aux.is_empty(), "発見に使われた補助作図が返るべき:{n}{}", out, n = "\n");

        // 補助作図を足して、今度は自由作図なしで調べ直す。
        let mut replay = format!("config rounds 0{n}config sweep 34{n}config top 60{n}{}{n}",
            triangle, n = "\n");
        for l in &aux { replay.push_str(l); replay.push('\n'); }
        let out2 = discover_response(&replay);
        assert!(has(&out2, "ok|"), "書き戻した作図が読めなかった: {}", out2);

        let texts2: Vec<&str> = out2.lines().filter(|l| l.starts_with("finding|"))
            .filter_map(|l| finding_text(l)).collect();
        let reproduced = found.iter().filter_map(|l| finding_text(l))
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

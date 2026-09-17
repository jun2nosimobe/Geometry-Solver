//! 🌟 解けない問題が「人間の証明のどの手順で」詰まっているかを調べる。
//!
//! 動機(ユーザー要望「そろそろ個別の問題がどのステップで詰まっているのかを
//! 検証する必要もありそう」): 未解決の13問はどれも需要駆動の作図が尽きて止まる
//! ところまでは分かっている(atlas §05)。しかし「何が足りないのか」― 補助作図
//! なのか、特定の補題なのか、その補題を出す定理なのか ― は、ログを読むだけでは
//! 分からなかった。
//!
//! ここでは問題ごとに**証明の筋書き**(人間の証明の補助作図と中間の主張の列)を
//! 書いておき、次の梯子で順に試す:
//!
//!   素の図            問題文のまま。筋書きの各手順に自力で届いたかだけを見る
//!   補助作図          筋書きの補助作図を与える
//!   補助作図 + 手順1..k を前提として与える   (k = 1, 2, ...)
//!
//! 「手順 k は、手前の 1..k-1 を全部認めた段で自力で出たか」を並べれば、
//! 詰まっている手順がそのまま名指しできる。最後の段で目標が出るなら、
//! 筋書きの手順さえ揃えば残りは今のエンジンで閉じる、ということになる。
//!
//! 主張の書き方は作図インターフェース(serve.rs)の発見と前提と同じ語彙で、
//! 補助作図も同じ作図行で書く。問題ファイルで付けた名前をそのまま使える。
//!
//! 筋書きの書式(問題ファイルの `pub const SKETCH: &str`):
//!
//! ```text
//! # コメント
//! aux point G inter Med_B Med_C        # 補助作図(作図行そのまま)
//! step parallel Mc Mb B C | 中点連結定理 # 手順(主張の種類 名前... | 説明)
//! ```
//!
//! 主張の種類: coincide / incident / concyclic / equal_length / cross_ratio /
//! collinear / concurrent / parallel / perpendicular / equal_angle

use std::collections::HashMap;

use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};

pub struct Step {
    pub lineno: usize,
    pub kind: String,
    pub names: Vec<String>,
    pub note: String,
}

pub struct Sketch {
    pub aux: Vec<(usize, String)>,
    pub steps: Vec<Step>,
}

/// 梯子のどの段か。
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rung {
    /// 問題文のまま。
    Pure,
    /// 補助作図を与え、手順を k 個前提にする(k = 0 なら補助作図だけ)。
    Assume(usize),
}

impl Rung {
    pub fn parse(v: &str) -> Option<Rung> {
        match v {
            "pure" => Some(Rung::Pure),
            "aux" => Some(Rung::Assume(0)),
            _ => v.parse().ok().map(Rung::Assume),
        }
    }
    pub fn arg(&self) -> String {
        match self {
            Rung::Pure => "pure".to_string(),
            Rung::Assume(0) => "aux".to_string(),
            Rung::Assume(k) => k.to_string(),
        }
    }
}

pub fn parse(text: &str) -> Result<Sketch, String> {
    let mut sk = Sketch { aux: Vec::new(), steps: Vec::new() };
    for (lineno, raw) in text.lines().enumerate() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.is_empty() { continue; }
        let (head, rest) = line.split_once(char::is_whitespace)
            .ok_or_else(|| format!("筋書き{}行目: 中身がありません: 「{}」", lineno + 1, line))?;
        match head {
            "aux" => sk.aux.push((lineno, rest.trim().to_string())),
            "step" => {
                let (claim, note) = match rest.split_once('|') {
                    Some((c, n)) => (c.trim(), n.trim().to_string()),
                    None => (rest.trim(), String::new()),
                };
                let t: Vec<&str> = claim.split_whitespace().collect();
                if t.len() < 3 {
                    return Err(format!("筋書き{}行目: 主張の種類と名前が要ります: 「{}」", lineno + 1, line));
                }
                sk.steps.push(Step {
                    lineno,
                    kind: t[0].to_string(),
                    names: t[1..].iter().map(|s| s.to_string()).collect(),
                    note,
                });
            }
            _ => return Err(format!("筋書き{}行目: aux か step で始めてください: 「{}」", lineno + 1, line)),
        }
    }
    if sk.steps.is_empty() { return Err("筋書きに手順(step)がありません".to_string()); }
    Ok(sk)
}

/// 問題ファイルで付けた名前 → 実体。同じ名前が複数あれば先に作られた方。
pub fn names_of(eg: &EGraph) -> HashMap<String, ClassId> {
    let mut env = HashMap::new();
    for (i, e) in eg.entities.iter().enumerate() {
        env.entry(e.original_name.clone()).or_insert(ClassId(i));
    }
    env
}

fn ids_of(env: &HashMap<String, ClassId>, step: &Step) -> Result<Vec<ClassId>, String> {
    step.names.iter()
        .map(|n| env.get(n).copied().ok_or_else(|| n.clone()))
        .collect()
}

pub struct Prepared {
    pub sketch: Sketch,
    pub env: HashMap<String, ClassId>,
    pub rung: Rung,
}

/// 梯子の段に応じて、補助作図と前提を図に足す。問題を読み込んだ直後、
/// 探索を始める前に呼ぶ。
pub fn prepare(eg: &mut EGraph, text: &str, rung: Rung) -> Result<Prepared, String> {
    let sketch = parse(text)?;
    let mut env = names_of(eg);
    if let Rung::Assume(k) = rung {
        for (lineno, line) in &sketch.aux {
            crate::serve::apply_construction(eg, &mut env, *lineno, line)
                .map_err(|e| format!("筋書きの補助作図: {}", e))?;
        }
        eg.apply_congruence_closure();
        if k > sketch.steps.len() {
            return Err(format!("手順は{}個しかありません(--sketch={})", sketch.steps.len(), k));
        }
        for (i, step) in sketch.steps.iter().take(k).enumerate() {
            let ids = ids_of(&env, step)
                .map_err(|n| format!("筋書き{}行目: 「{}」が図にありません", step.lineno + 1, n))?;
            crate::serve::assert_fact(eg, &step.kind, &ids, 800_000 + i)
                .ok_or_else(|| format!("筋書き{}行目: 前提にできない形です: {}", step.lineno + 1, step.kind))?;
            eg.apply_congruence_closure();
        }
    }
    Ok(Prepared { sketch, env, rung })
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Status {
    /// 前提として与えた。
    Assumed,
    /// e-graph がこの主張に到達している。
    Reached,
    /// 到達していない(数値的には成り立つ)。
    NotReached,
    /// 乱数座標で成り立たない ― 筋書きの書き間違い。
    False,
    /// 主張に出てくる名前が図に無い(補助作図を与えない段など)。
    Missing(String),
    /// 語彙に無い形。
    Unsupported,
}

impl Status {
    pub fn code(&self) -> String {
        match self {
            Status::Assumed => "assumed".into(),
            Status::Reached => "reached".into(),
            Status::NotReached => "not_reached".into(),
            Status::False => "false".into(),
            Status::Missing(n) => format!("missing:{}", n),
            Status::Unsupported => "unsupported".into(),
        }
    }
}

/// 手順が今の図で成り立っているか。図そのものは汚さないよう複製の上で目標を
/// 作って確かめる(目標の図形を本物の図に作ると、それ自体が補助作図として
/// 探索を助けてしまい、「自力で届いたか」の判定にならない)。
pub fn status_of(eg: &EGraph, env: &HashMap<String, ClassId>, step: &Step, idx: usize) -> Status {
    let ids = match ids_of(env, step) {
        Ok(ids) => ids,
        Err(n) => return Status::Missing(n),
    };
    let mut probe = eg.clone();
    let Some(goal) = crate::serve::goal_for(&mut probe, &step.kind, &ids, 700_000 + idx) else {
        return Status::Unsupported;
    };
    probe.apply_congruence_closure();
    if crate::serve::goal_met(&probe, &goal) { return Status::Reached; }
    if holds_numerically(&mut probe, &goal) == Some(false) { return Status::False; }
    Status::NotReached
}

/// 主張が乱数座標で成り立つか(問題の目標の検算と同じやり方)。
fn holds_numerically(eg: &mut EGraph, goal: &(String, Vec<ClassId>)) -> Option<bool> {
    let (kind, a) = goal;
    match kind.as_str() {
        "Identical" if a.len() >= 2 => eg.numeric_plausibility_check(a[0], a[1], 4),
        "Concyclic" if a.len() >= 4 => {
            let c1 = eg.create_entity("__sketch_c1".into(), Definition::Circumcircle(a[0], a[1], a[2]), EntityType::Conic);
            let c2 = eg.create_entity("__sketch_c2".into(), Definition::Circumcircle(a[0], a[1], a[3]), EntityType::Conic);
            eg.numeric_plausibility_check(c1, c2, 4)
        }
        _ => None,
    }
}

/// 探索の前に、筋書きそのものが正しいか(各手順が乱数座標で成り立つか)を
/// 確かめて表示する。書き間違いの筋書きで「詰まっている」と結論しないため。
pub fn check_before_search(eg: &EGraph, p: &Prepared) {
    let assumed = match p.rung { Rung::Assume(k) => k, Rung::Pure => 0 };
    println!("📜 [筋書き] 段: {} (補助作図{}件、手順{}個)", p.rung.arg(), p.sketch.aux.len(), p.sketch.steps.len());
    for (i, step) in p.sketch.steps.iter().enumerate() {
        if i < assumed { continue; }
        if let Status::False = status_of(eg, &p.env, step, i) {
            println!("  ⚠️ 手順{}「{} {}」は乱数座標で成り立ちません。筋書きの書き間違いです。",
                i + 1, step.kind, step.names.join(" "));
        }
    }
}

/// 探索の後で、各手順に到達したかを表示する。`SKETCH\t` の行は diagnose が拾う。
pub fn report(eg: &EGraph, p: &Prepared) {
    let assumed = match p.rung { Rung::Assume(k) => k, Rung::Pure => 0 };
    println!("\n=== 📜 証明の筋書きのどこまで届いたか (段: {}) ===", p.rung.arg());
    for (i, step) in p.sketch.steps.iter().enumerate() {
        let st = if i < assumed { Status::Assumed } else { status_of(eg, &p.env, step, i) };
        let mark = match &st {
            Status::Assumed => "前提".to_string(),
            Status::Reached => "✅".to_string(),
            Status::NotReached => "❌".to_string(),
            Status::False => "⚠️偽".to_string(),
            Status::Missing(n) => format!("({}が無い)", n),
            Status::Unsupported => "(語彙に無い)".to_string(),
        };
        println!("  {:>2}. {} {} {}", i + 1, crate::cli::pad(&mark, 12),
            crate::cli::pad(&format!("{} {}", step.kind, step.names.join(" ")), 28), step.note);
        println!("SKETCH\t{}\t{}", i + 1, st.code());
    }
    println!("=============================\n");
}

/// `geom_solver diagnose <問題名> [オプション]`: 梯子の全段を子プロセスで回して表にする。
pub fn diagnose(args: &[String]) {
    let Some(problem) = args.get(2) else {
        println!("使い方: geom_solver diagnose <問題名> [--steps=N などの探索オプション]");
        return;
    };
    let Some(text) = crate::problems::sketch_for(problem) else {
        println!("⚠️ 「{}」には証明の筋書き(SKETCH)がまだありません。", problem);
        println!("   筋書きのある問題: {}", crate::problems::PROBLEMS_WITH_SKETCH.join(", "));
        return;
    };
    let sketch = match parse(text) {
        Ok(s) => s,
        Err(e) => { println!("⚠️ {}", e); return; }
    };
    let passthrough: Vec<String> = args.iter().skip(3).cloned().collect();
    let exe = match std::env::current_exe() {
        Ok(p) => p,
        Err(e) => { println!("⚠️ 自分自身の実行ファイルの場所が分かりませんでした: {}", e); return; }
    };

    let n = sketch.steps.len();
    let mut rungs = vec![Rung::Pure];
    if !sketch.aux.is_empty() { rungs.push(Rung::Assume(0)); }
    for k in 1..=n { rungs.push(Rung::Assume(k)); }

    println!("🔎 {} の筋書き(補助作図{}件、手順{}個)を {} 段で試します", problem, sketch.aux.len(), n, rungs.len());
    // 段ごとの (解けたか, 仕事量, 手順ごとの状態)
    // 🌟 段は互いに独立で、予算は壁時計ではなく仕事量なので、並べて走らせても結果は
    // 変わらない。1段ずつ順に回すと、解けない段が毎回予算を使い切るので1問に10分以上
    // かかっていた。コア数まで同時に走らせる。
    let width = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4).max(1);
    let mut outputs: Vec<Option<(bool, String)>> = vec![None; rungs.len()];
    for chunk in (0..rungs.len()).collect::<Vec<_>>().chunks(width) {
        std::thread::scope(|scope| {
            let handles: Vec<_> = chunk.iter().map(|&k| {
                let mut argv = vec![problem.clone(), format!("--sketch={}", rungs[k].arg())];
                argv.extend(passthrough.iter().cloned());
                let exe = &exe;
                (k, scope.spawn(move || {
                    let (solved, _secs, out) = crate::sweep::run_capture(exe, &argv, 600);
                    (solved, out)
                }))
            }).collect();
            for (k, h) in handles {
                outputs[k] = h.join().ok();
            }
        });
    }

    let mut rows: Vec<(Rung, bool, Option<u64>, Vec<String>)> = Vec::new();
    for (k, &rung) in rungs.iter().enumerate() {
        let (solved, out) = outputs[k].take().unwrap_or((false, String::new()));
        let work = out.lines().find_map(|l| l.split("消費した仕事量: ").nth(1))
            .and_then(|r| r.split_whitespace().next()).and_then(|v| v.parse().ok());
        let mut st = vec![String::from("?"); n];
        for l in out.lines() {
            let mut f = l.split('\t');
            if f.next() != Some("SKETCH") { continue; }
            if let (Some(i), Some(code)) = (f.next().and_then(|v| v.parse::<usize>().ok()), f.next())
                && (1..=n).contains(&i) { st[i - 1] = code.to_string(); }
        }
        if let Some(e) = out.lines().find(|l| l.contains("⚠️") && l.contains("筋書き")) {
            println!("  {}", e.trim());
        }
        println!("  段 {:<5} {} 仕事量 {}", rung.arg(), if solved { "🎉 解けた" } else { "   解けない" },
            work.map(|w: u64| w.to_string()).unwrap_or_else(|| "-".into()));
        rows.push((rung, solved, work, st));
    }

    let cell = |code: &str| -> &str {
        match code {
            "assumed" => "前提",
            "reached" => "✅",
            "not_reached" => "❌",
            "false" => "⚠️偽",
            "unsupported" => "語彙外",
            c if c.starts_with("missing:") => "図に無",
            _ => "?",
        }
    };
    println!("\n=== 🔎 {}: 手順 × 段 ===", problem);
    let header: Vec<String> = rows.iter().map(|r| format!("{:>6}", r.0.arg())).collect();
    println!("  {} {}", crate::cli::pad("手順", 44), header.join(""));
    for (i, step) in sketch.steps.iter().enumerate() {
        let label = format!("{}. {} {}", i + 1, step.kind, step.names.join(" "));
        let cells: Vec<String> = rows.iter().map(|r| format!("{:>6}", cell(&r.3[i]))).collect();
        println!("  {} {}", crate::cli::pad(&truncate(&label, 44), 44), cells.join(""));
    }
    let solved_cells: Vec<String> = rows.iter().map(|r| format!("{:>6}", if r.1 { "🎉" } else { "-" })).collect();
    println!("  {} {}", crate::cli::pad("目標", 44), solved_cells.join(""));

    // 判定: 手順 k は「補助作図 + 手順1..k-1 を前提」の段で自力で出たか。
    println!("\n=== 🔎 判定(各手順を、手前を全部認めた段で見る) ===");
    let at = |k: usize| rows.iter().find(|r| r.0 == Rung::Assume(k));
    let mut blockers = Vec::new();
    for (i, step) in sketch.steps.iter().enumerate() {
        // 探索は発見的なので単調ではない: 手前を前提として与えると探索の向きが変わり、
        // 素の図では届いていた手順に届かなくなることが実際にある(bench_2008armog10p6 の
        // 手順3)。どこかの段で自力で届いていれば、その手順は詰まり所ではない。
        let reached_somewhere = rows.iter().any(|r| r.3[i] == "reached");
        let verdict = match at(i).map(|r| r.3[i].as_str()) {
            Some("reached") => "自力で出る".to_string(),
            Some("not_reached") if reached_somewhere =>
                "自力で出る段もある(手前を前提にすると探索がそれて届かない)".to_string(),
            Some("not_reached") => { blockers.push(i + 1); "❌ 手前を全部認めても出ない ← 詰まり所".to_string() }
            Some("false") => "⚠️ 筋書きの書き間違い(乱数座標で成り立たない)".to_string(),
            Some(c) => format!("判定できない({})", c),
            None => "判定できない(段が無い)".to_string(),
        };
        println!("  手順{} {} {}  {}", i + 1, crate::cli::pad(&truncate(&format!("{} {}", step.kind, step.names.join(" ")), 36), 36), verdict, step.note);
    }
    match at(n) {
        Some(r) if r.1 => println!("  目標: 手順を全部認めれば解ける"),
        Some(_) => println!("  目標: ❌ 手順を全部認めても解けない ― 筋書きの最後から目標までにまだ隙間がある"),
        None => {}
    }
    if let Some(r) = rows.iter().find(|r| r.0 == Rung::Pure) {
        let reached = r.3.iter().filter(|c| c.as_str() == "reached").count();
        println!("  素の図で自力で届いた手順: {}/{}", reached, n);
    }
    if !blockers.is_empty() {
        println!("  詰まり所: 手順 {}", blockers.iter().map(|b| b.to_string()).collect::<Vec<_>>().join(", "));
    }
}

fn truncate(s: &str, n: usize) -> String {
    if s.chars().count() <= n { s.to_string() } else { s.chars().take(n - 1).collect::<String>() + "…" }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 筋書きの検算が素通りになっていないか。偽の主張は False、成り立つが
    /// まだ示していない主張は NotReached、図に無い名前は Missing になること。
    #[test]
    fn a_false_step_is_caught_and_a_true_one_is_not() {
        let text = "aux point Mab mid A B\n\
                    step parallel A B A C | 偽: ABとACは平行ではない\n\
                    step coincide G1 G2 | 真: 中線は1点で交わる(まだ示していない)\n\
                    step parallel Nope A B C | 名前が無い\n";
        let mut eg = EGraph::new();
        let _ = crate::problems::load_problem("centroid", &mut eg);
        let p = prepare(&mut eg, text, Rung::Assume(0)).expect("筋書きを適用できる");
        assert_eq!(status_of(&eg, &p.env, &p.sketch.steps[0], 0), Status::False);
        assert_eq!(status_of(&eg, &p.env, &p.sketch.steps[1], 1), Status::NotReached);
        assert_eq!(status_of(&eg, &p.env, &p.sketch.steps[2], 2), Status::Missing("Nope".into()));
    }

    /// 前提として与えた手順は、そのまま図で成り立っている。
    #[test]
    fn an_assumed_step_is_reached() {
        let text = "step coincide G1 G2 | 中線は1点で交わる\n";
        let mut eg = EGraph::new();
        let _ = crate::problems::load_problem("centroid", &mut eg);
        let p = prepare(&mut eg, text, Rung::Assume(1)).expect("筋書きを適用できる");
        assert_eq!(status_of(&eg, &p.env, &p.sketch.steps[0], 0), Status::Reached);
    }
}

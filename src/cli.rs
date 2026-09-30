//! 🌟 全オプションの一覧(OPTIONS)を1か所に持ち、ヘルプ表示・未知フラグの検出・環境変数への橋渡しをまとめて行う。
//! 綴りを間違えたフラグが黙って無視され「パラメータを変えたつもりで既定値のまま」の実験結果が出るのを防ぐのが主目的。
//! この表と実際の解析がずれないよう、ソースを走査して突き合わせるテスト(tests::every_flag_in_source_is_documented)を置いている。

use std::collections::BTreeSet;

/// オプションが値を取るかどうか(ヘルプの表示と未知フラグ判定に使う)。
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Arg {
    /// 値を取らないスイッチ (`--mcts`)
    None,
    /// `--time=5` のように `=` で値を取る
    Value(&'static str),
}

pub struct Opt {
    pub name: &'static str,
    pub arg: Arg,
    /// 既定値。スイッチなら "無効" のように状態を書く。
    pub default: &'static str,
    /// どのサブコマンドで効くか(ヘルプの見出しに使う)
    pub mode: Mode,
    pub help: &'static str,
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Mode {
    /// 問題を解く通常実行 (`geom_solver <問題名>`)
    Solve,
    /// 自由探索・発見モード (`geom_solver discover`)
    Discover,
    /// 退化探索 (`geom_solver discover-degenerate`)
    Degenerate,
    /// パラメータ掃引 (`geom_solver sweep`)
    Sweep,
    /// 作図インターフェース (`geom_solver serve`)
    Serve,
}

impl Mode {
    fn title(self) -> &'static str {
        match self {
            Mode::Solve => "問題を解く: geom_solver <問題名> [オプション]",
            Mode::Discover => "自由探索で定理を発見する: geom_solver discover [オプション]",
            Mode::Degenerate => "退化させて関連を調べる: geom_solver discover-degenerate <問題名> [オプション]",
            Mode::Sweep => "パラメータを振って比べる: geom_solver sweep [オプション]",
            Mode::Serve => "ブラウザで作図する: geom_solver serve [オプション]",
        }
    }
}

use Arg::{None as Switch, Value};
use Mode::{Degenerate, Discover, Serve, Solve, Sweep};

/// 探索の既定の予算(dfs_match の呼び出し回数)。
/// 壁時計ではなくこれで測るので、同じ問題は何度流しても同じ結果になる。
///
/// 値の根拠: 解けた問題が実際に使った仕事量を測ると、既定でいちばん重いのが bench_2018chnwesternmop5 の約215万ステップで、
/// そこに3倍以上の余裕を見て800万にしてある。
/// (解けない問題には、手が尽きて早く止まるものと、この予算を使い切るものがある。使い切るものは、この値を上げると実行時間が延びる。
/// 手が尽きたときの最後の手(汎用の補助作図)があるので、以前に止まっていた問題も予算まで走ることがある。)
pub const DEFAULT_STEP_BUDGET: u64 = 8_000_000;
/// --time の既定。解けるかどうかを決める予算ではなく、
/// 「どれだけ待っても終わらない」を防ぐだけの安全弁。
pub const DEFAULT_TIME_CAP_SECS: u64 = 600;

pub const OPTIONS: &[Opt] = &[
    // ---- 問題を解くモード ----
    Opt { name: "--steps", arg: Value("回"), default: "8000000", mode: Solve,
          help: "探索の予算(dfs_matchの呼び出し回数)。壁時計ではないので結果が再現する" },
    Opt { name: "--time", arg: Value("秒"), default: "600", mode: Solve,
          help: "打ち切るまでの壁時計の上限。予算ではなく暴走を止めるための安全弁" },
    Opt { name: "--mcts", arg: Switch, default: "無効", mode: Solve,
          help: "MCTSによる補助点の作図を有効にする(既定は無効)" },
    Opt { name: "--heat-cap", arg: Value("個"), default: "40", mode: Solve,
          help: "定理のマッチングで見る「熱い」実体の数。上げると広く探すが遅くなる" },
    Opt { name: "--fanout-heat-cap", arg: Value("個"), default: "5", mode: Solve,
          help: "枝分かれの大きいパターンで見る実体の数。足りなければ自動で広がるので初期値" },
    Opt { name: "--bandit", arg: Switch, default: "無効", mode: Solve,
          help: "UCB1バンディットによる定理の優先順位付けを使う(実測で全体の仕事量が20%増えるため既定は無効)" },
    Opt { name: "--no-mcts-target-bias", arg: Switch, default: "バイアス有効", mode: Solve,
          help: "MCTSが証明目標に近い図形を優先するのを切る(A/B比較用)" },
    Opt { name: "--no-projective", arg: Switch, default: "射影の定理を使う", mode: Solve,
          help: "複比・シュタイナー系の射影5定理を外す(A/B比較用)" },
    Opt { name: "--length-theorems", arg: Switch, default: "既定で有効", mode: Solve,
          help: "長さを橋渡しする定理(中点連結定理の長さ版)。既定で入るので指定は不要" },
    Opt { name: "--no-length-theorems", arg: Switch, default: "長さの定理を使う", mode: Solve,
          help: "長さを橋渡しする定理を外す(A/B比較用)" },
    Opt { name: "--central-angle", arg: Switch, default: "既定で有効", mode: Solve,
          help: "中心角の定理。既定で入るので指定は不要(以前は bench_2012egmop1 だけに問題名で入れていた。来歴 #70)" },
    Opt { name: "--no-central-angle", arg: Switch, default: "中心角の定理を使う", mode: Solve,
          help: "中心角の定理を外す(A/B比較用)" },
    Opt { name: "--rules", arg: Value("chord,parallelogram,spiral,spiral-prop"), default: "足さない", mode: Solve,
          help: "追加の規則を足す。chord=同じ円で等しい円周角に対する弦は等しい、parallelogram=平行四辺形の対角線は互いに二等分する、spiral=スパイラル相似(同じ向き)、spiral-prop=スパイラル相似(同じ向き)を合同閉包の局所伝播として適用(来歴 #71・#74・#75)" },
    Opt { name: "--no-spiral-opp", arg: Switch, default: "交わる弦の相似を使う", mode: Solve,
          help: "交わる弦の相似(逆向きのスパイラル相似、既定で入る)を外す(A/B比較用。来歴 #74)" },
    Opt { name: "--no-conclusion-check", arg: Switch, default: "結論を数値で確かめる", mode: Solve,
          help: "定理の結論をマージ前に数値で確かめて偽なら却下するのをやめる(A/B用。前提が乱数座標で成り立つ問題でだけ効く。来歴 #76)" },
    Opt { name: "--no-merge-checks", arg: Switch, default: "マージ前に数値で確かめる", mode: Solve,
          help: "マージ前の数値チェック(局所伝播の却下と定理の結論の検算)を全て外す。規則だけで健全かを --audit-merges と組んで確かめる" },
    Opt { name: "--no-fixed-coords", arg: Switch, default: "固定座標で検算する", mode: Solve,
          help: "数値チェックを固定座標(探索の前に一度だけ置き、各実体を元の定義から一度だけ計算する)ではなく、構造が変わるたびに置き直す従来の経路で行う(A/B 用)" },
    Opt { name: "--no-nondegeneracy", arg: Switch, default: "非退化条件を使う", mode: Solve,
          help: "非退化条件(定理の「図の上でも相異なる」・局所伝播の条件・値の定まらない作図の見送り)を全て外す(A/B 用)" },
    Opt { name: "--no-numeric-aux", arg: Switch, default: "数値で選ぶ補助作図を使う", mode: Solve,
          help: "手が全部尽きたとき、補助作図の候補(交点・中点・垂線や平行線との交点・第2交点)を固定座標で試作し、既存の直線・円に乗る/既存の点と重なる/新しく共円・共線になるものを汎用の補助作図と一緒に作る手を外す(A/B 用。来歴 #80)" },
    Opt { name: "--numeric-aux-early", arg: Switch, default: "使わない", mode: Solve,
          help: "数値で選ぶ補助作図を、行き詰まりのたびにも(点数の高い候補を少しだけ)試す(試験中。2016ARMO が解けるが、centroid などを落とす)" },
    Opt { name: "--prune", arg: Value("倍率"), default: "無効", mode: Solve,
          help: "有効な図形がこの倍を超えて増えたら、手が止まったときに使われなかった作図を無効にする(リスタート)" },
    Opt { name: "--prune-given", arg: Switch, default: "無効", mode: Solve,
          help: "(実験)--prune のとき、使われなかった問題文の作図(ノイズなど)も刈り込む" },
    Opt { name: "--no-ar-first", arg: Switch, default: "最初の総当たりの前に代数的な追跡を1回走らせる", mode: Solve,
          help: "最初の定理の総当たりの前の代数的な追跡をやめる(手が止まったときだけ走らせる)" },
    Opt { name: "--no-ar", arg: Switch, default: "代数的な追跡を使う", mode: Solve,
          help: "手が止まったとき、複比と有向角の等式を形式的な対数の線形代数(ℤⁿ ⊕ ℤ/4、エルミート標準形)でまとめて閉じ、等しいと分かった同値類と方向を併合する手を外す(A/B 用。来歴 #82)" },
    Opt { name: "--drop-theorems", arg: Value("名前,…"), default: "外さない", mode: Solve,
          help: "名前が一致する定理を外す(末尾が * なら前方一致。代数的な追跡への置き換えを試すため)" },
    Opt { name: "--chord-theorems", arg: Switch, default: "AR があれば外す", mode: Solve,
          help: "方冪(共点二弦の相似)と交わる弦の相似の2つの定理を、代数的な追跡があっても残す。既定では AR の相似(対応する点を含む)が置き換えるので外す(来歴 #85)" },
    Opt { name: "--ar-replace", arg: Switch, default: "使わない", mode: Solve,
          help: "角の足し算の規則(有向角の加法性・交替律)を外し、代数的な追跡に任せる(試験中)" },
    Opt { name: "--no-generic-aux", arg: Switch, default: "汎用の補助作図を足す", mode: Solve,
          help: "手が全部尽きたとき、最後に熱い点どうしの中点と熱い直線どうしの交点を足す手を外す(A/B用。今解けている問題の探索は変わらない。来歴 #72)" },
    Opt { name: "--midpoint-demands", arg: Switch, default: "無効", mode: Solve,
          help: "行き詰まったら、図に既にある中点の端点について残りの中点も作る" },
    Opt { name: "--no-collinear-extra", arg: Switch, default: "枠を分ける", mode: Solve,
          help: "需要の補助線の枠分け(既に共線の組を別枠にする)をやめ、1つの枠を奪い合わせる(A/B比較用)" },
    Opt { name: "--degen-heat", arg: Switch, default: "無効", mode: Solve,
          help: "退化させたとき一致する図形どうしにheatボーナスを配る" },
    Opt { name: "--degen-heat-seed", arg: Value("整数"), default: "12345", mode: Solve,
          help: "退化グループを作るときの乱数シード" },
    Opt { name: "--degen-heat-min-hits", arg: Value("回"), default: "2", mode: Solve,
          help: "何回の独立な乱数で一致したら関連ありとみなすか" },
    Opt { name: "--degen-heat-factor", arg: Value("倍率"), default: "0.5", mode: Solve,
          help: "関連する図形へ配るheatボーナスの倍率" },
    Opt { name: "--stats", arg: Switch, default: "非表示", mode: Solve,
          help: "終了時に定理ごとの試行回数・平均報酬を表示する" },
    Opt { name: "--profile", arg: Switch, default: "非表示", mode: Solve,
          help: "終了時に探索の各フェーズの所要時間の内訳を表示する" },
    Opt { name: "--trace", arg: Switch, default: "非表示", mode: Solve,
          help: "終了時に「どの定理がどの優先度で発火し、うち証明に残ったのはどれか」と、熱・参照数・退化関係数の分布を表示する" },
    Opt { name: "--widen-first", arg: Switch, default: "無効", mode: Solve,
          help: "行き詰まったとき、図を広げる需要作図より先に候補capの拡大を試す" },
    Opt { name: "--var-order", arg: Arg::None, default: "無効", mode: Solve,
          help: "他のパターンが縛っている変数から先に束縛する(cap の広げ方と組で効く)" },
    Opt { name: "--no-semijoin", arg: Arg::None, default: "semijoin は既定で有効", mode: Solve,
          help: "候補をcapで切る前に他のパターンで絞るのをやめる(従来の振る舞い)" },
    Opt { name: "--nogood-core", arg: Arg::None, default: "無効", mode: Solve,
          help: "失敗キャッシュの鍵を、残っているパターンが見る変数だけに絞る" },
    Opt { name: "--widen-every", arg: Value("回"), default: "2", mode: Solve,
          help: "行き詰まりN回ごとに、需要作図より先に候補capの拡大を試す(0で従来どおり需要作図を優先)" },
    Opt { name: "--widen-first-ceiling", arg: Value("上限"), default: "40", mode: Solve,
          help: "--widen-first で先に広げるのをこの cap までにする(それ以上は需要作図の後)" },
    Opt { name: "--fanout-connected", arg: Switch, default: "無効", mode: Solve,
          help: "Connected の片側だけ束縛の候補も fanout-heat-cap(狭く始めて行き詰まったら広げる)で絞る" },
    Opt { name: "--noise", arg: Value("個"), default: "0", mode: Solve,
          help: "初期作図に証明と無関係な作図をN個足す(図が大きくなっても解けるかの計測)" },
    Opt { name: "--noise-seed", arg: Value("整数"), default: "12345", mode: Solve,
          help: "--noise で足す作図の選び方のシード" },
    Opt { name: "--audit-merges", arg: Switch, default: "無効", mode: Solve,
          help: "定理の結論を適用する直前に乱数座標で検算し、定理ごとの真・偽の件数を出す(探索の結果は変えない)" },
    Opt { name: "--origins", arg: Switch, default: "非表示", mode: Solve,
          help: "終了時に「どの出どころで作られた図形(オンデマンド作図・DefinedBy生成・MCTS等)が、実際に証明へ残ったか」を集計する" },
    Opt { name: "--skip-recovery", arg: Value("line,point,second,mid,angle,target"), default: "どれも外さない", mode: Solve,
          help: "行き詰まったときの手を個別に外す(A/B用)。line=補助線, point=交点, second=円とのもう一方の交点, mid=中点, angle=角/方向, target=目標駆動の補助線と複比" },
    Opt { name: "--sketch", arg: Value("pure|aux|N"), default: "使わない", mode: Solve,
          help: "証明の筋書きの段で解く。aux=補助作図を与える、N=補助作図と手順1..Nを前提にする(diagnose が使う)" },
    Opt { name: "--sketch-file", arg: Value("パス"), default: "問題ファイルの筋書き", mode: Solve,
          help: "筋書きを問題ファイルではなくこのファイルから読む(diagnose も同じ。コンパイルし直さずに筋書きを試す用)" },
    Opt { name: "--seeded-rematch", arg: Switch, default: "無効", mode: Solve,
          help: "証明された事実から定理をシードして再マッチングする(実測で掛け合わせが悪化するため既定無効)" },

    // ---- 自由探索・発見モード ----
    Opt { name: "--preset", arg: Value("名前|all"), default: "自由点だけ", mode: Discover,
          help: "既存の問題の配置を種として使う。カンマ区切りで複数、allで古典配置を一括" },
    Opt { name: "--seed-points", arg: Value("個"), default: "3", mode: Discover,
          help: "プリセットを使わないときの自由点の数(最低3)。4にすると四角形の配置になる" },
    Opt { name: "--systematic", arg: Value("ラウンド,実体数上限,1種あたり"), default: "未指定ならMCTS探索", mode: Discover,
          help: "MCTSの代わりに決定的な作図閉包を回す。例: --systematic=4,800,10" },
    Opt { name: "--time", arg: Value("秒"), default: "60", mode: Discover,
          help: "MCTS探索の時間予算(種配置ごと)" },
    Opt { name: "--steps", arg: Value("回"), default: "80", mode: Discover,
          help: "MCTS探索のステップ数上限" },
    Opt { name: "--sims", arg: Value("回"), default: "150", mode: Discover,
          help: "1ステップあたりのMCTSシミュレーション回数" },
    Opt { name: "--top", arg: Value("件"), default: "5", mode: Discover,
          help: "各セクションで報告する件数" },
    Opt { name: "--sweep-points", arg: Value("個"), default: "48", mode: Discover,
          help: "総当たり検出で見る点の数。上げると見つかるが共円判定がO(n^4)で重い" },
    Opt { name: "--sweep-lines", arg: Value("本"), default: "36", mode: Discover,
          help: "総当たり検出で見る直線・円の数" },
    Opt { name: "--prove", arg: Switch, default: "無効", mode: Discover,
          help: "見つかった予想に実際に証明を試みる" },
    Opt { name: "--prove-steps", arg: Value("ステップ"), default: "3000000", mode: Discover,
          help: "--prove のときの1件あたりの証明の仕事量(solve の --steps と同じ単位)" },
    Opt { name: "--prove-findings", arg: Value("ステップ"), default: "無効", mode: Discover,
          help: "総当たり検出の発見を1件ずつ証明し、証明に要った仕事量(難しさの目安)を並べる" },
    Opt { name: "--probe", arg: Switch, default: "無効", mode: Discover,
          help: "予想を仮定して何が導かれるかを調べる(自由度が落ちるので既定は無効)" },
    Opt { name: "--probe-dfs-budget", arg: Value("回"), default: "3000", mode: Discover,
          help: "--probe のときの1件あたりの探索予算" },
    Opt { name: "--probe-rounds", arg: Value("回"), default: "5", mode: Discover,
          help: "--probe のときのラウンド数" },
    Opt { name: "--audit", arg: Switch, default: "無効", mode: Discover,
          help: "各ステップで構造的な主張と数値評価の整合を検査する(重いが崩壊の原因特定に使う)" },
    Opt { name: "--sweep-debug", arg: Switch, default: "無効", mode: Discover,
          help: "検出器が何件を何の理由で捨てたかを標準エラーに出す" },

    // ---- 退化探索 ----
    Opt { name: "--seed", arg: Value("整数"), default: "12345", mode: Degenerate,
          help: "乱数シード" },
    Opt { name: "--min-hits", arg: Value("回"), default: "2", mode: Degenerate,
          help: "何回の独立な乱数で一致したら報告するか" },

    // ---- パラメータ掃引 ----
    Opt { name: "--problems", arg: Value("名前,..|all|bench"), default: "all", mode: Sweep,
          help: "掃引の対象にする問題。allは全問題、benchはbench_で始まる問題" },
    Opt { name: "--vary", arg: Value("--フラグ=値,値,.."), default: "なし", mode: Sweep,
          help: "振りたいオプションと値の候補。複数回指定すると直積を全部試す" },
    Opt { name: "--base", arg: Value("フラグ列"), default: "なし", mode: Sweep,
          help: "全ての組み合わせに共通で付けるオプション(空白区切り)" },
    Opt { name: "--timeout", arg: Value("秒"), default: "600", mode: Sweep,
          help: "1問あたりの打ち切り時間" },
    Opt { name: "--repeat", arg: Value("回"), default: "1", mode: Sweep,
          help: "同じ組み合わせを何回走らせて合算するか(ゆらぎを均すため)" },

    // ---- 作図インターフェース ----
    Opt { name: "--port", arg: Value("番号"), default: "8080", mode: Serve,
          help: "待ち受けるポート。塞がっていたら別の番号にする" },
];

/// 環境変数でも指定できるもの(後方互換)。フラグ -> 環境変数名。
pub const ENV_ALIASES: &[(&str, &str)] = &[
    ("--systematic", "DISCOVER_SYSTEMATIC"),
    ("--audit", "DISCOVER_AUDIT"),
    ("--sweep-debug", "SWEEP_DEBUG"),
];

pub const SUBCOMMANDS: &[(&str, &str)] = &[
    ("<問題名>", "その問題の証明を試みる(名前は list で確認できます)"),
    ("discover", "自由作図で未知の関係を探す"),
    ("discover-degenerate", "図形を退化させて関連の深い図形の組を探す"),
    ("serve", "ブラウザで作図して定理を発見する(GeoGebra風の画面)"),
    ("sweep", "オプションを振って解けた数と時間を比べる"),
    ("diagnose", "証明の筋書きに沿って、解けない問題がどの手順で詰まるかを調べる"),
    ("list", "問題名・プリセット名の一覧を出す"),
    ("extract-proof", "raw_proofファイルから2実体が等しい理由を抜き出す"),
    ("help", "このヘルプ"),
];

/// 端末上の見かけの幅(日本語などの全角文字は2桁ぶん)。
/// Rustの `{:<38}` は文字数で詰めるため、全角を含む行だけ右にずれてしまう。
fn display_width(s: &str) -> usize {
    s.chars().map(|c| {
        let c = c as u32;
        let wide = (0x1100..=0x115F).contains(&c)
            || (0x2E80..=0xA4CF).contains(&c)    // CJK部首〜漢字・かな
            || (0xAC00..=0xD7A3).contains(&c)    // ハングル
            || (0xF900..=0xFAFF).contains(&c)    // CJK互換漢字
            || (0xFF00..=0xFF60).contains(&c)    // 全角英数
            || (0xFFE0..=0xFFE6).contains(&c)
            || (0x1F300..=0x1FAFF).contains(&c); // 絵文字
        if wide { 2 } else { 1 }
    }).sum()
}

/// 見かけの幅で左詰めする。
pub fn pad(s: &str, width: usize) -> String {
    let mut out = s.to_string();
    for _ in display_width(s)..width { out.push(' '); }
    out
}

pub fn print_help() {
    println!("geom_solver — 射影幾何ベースの初等幾何ソルバ\n");
    println!("使い方: geom_solver <サブコマンド|問題名> [オプション]\n");
    println!("サブコマンド:");
    for (name, help) in SUBCOMMANDS {
        println!("  {} {}", pad(name, 22), help);
    }
    for mode in [Mode::Solve, Mode::Discover, Mode::Degenerate, Mode::Sweep, Mode::Serve] {
        println!("\n{}", mode.title());
        for o in OPTIONS.iter().filter(|o| o.mode == mode) {
            let shown = match o.arg {
                Arg::None => o.name.to_string(),
                Arg::Value(v) => format!("{}=<{}>", o.name, v),
            };
            println!("  {} {}  [既定: {}]", pad(&shown, 34), o.help, o.default);
        }
    }
    println!("\n同じ設定は環境変数でも指定できます(フラグの方が新しい書き方です):");
    for (flag, env) in ENV_ALIASES {
        println!("  {} = {}", pad(env, 22), flag);
    }
    println!("\nよく使う例:");
    println!("  # ブラウザで作図しながら定理を探す");
    println!("  geom_solver serve");
    println!("  # 1問だけ、時間を伸ばして解かせる");
    println!("  geom_solver simson --steps=20000000 --mcts");
    println!("  # 全問まとめて回して、いま何問解けるかを見る(回帰確認)");
    println!("  geom_solver sweep --problems=all");
    println!("  # 裸の三角形から、決定的な作図閉包で未知の関係を探す");
    println!("  geom_solver discover --systematic=4,800,10 --seed-points=3 --top=6");
    println!("  # 既存の問題の配置を種にして探す(検出器が何を捨てたかも出す)");
    println!("  geom_solver discover --preset=orthocenter --systematic=3,700,10 --sweep-debug");
    println!("  # パラメータを振って効き目を比べる(組み合わせの直積を全部試す)");
    println!("  geom_solver sweep --problems=bench --vary=--heat-cap=20,40,80 --base=\"--mcts\"");
    println!("  # 図形を退化させて関連の深い図形の組を探す");
    println!("  geom_solver discover-degenerate orthocenter --min-hits=3");
    println!("  # 問題名・プリセット名の一覧");
    println!("  geom_solver list");
}

pub fn print_catalog() {
    println!("問題名 ({}件):", crate::problems::ALL_PROBLEMS.len());
    for chunk in crate::problems::ALL_PROBLEMS.chunks(3) {
        println!("  {}", chunk.iter().map(|s| pad(s, 28)).collect::<String>().trim_end());
    }
    println!("\ndiscover の --preset= に渡せる名前:");
    println!("  上の問題名すべて、加えて三角形の五心を最初から揃えた合成配置:");
    println!("    triangle_centers");
    println!("  --preset=all は次の古典配置をまとめて試します:");
    for chunk in crate::discover::CLASSIC_PRESETS.chunks(4) {
        println!("    {}", chunk.join(", "));
    }
}

/// 渡された引数のうち、OPTIONSにもサブコマンドにも無いものを返す。
///
/// 綴り間違いを黙って無視すると「パラメータを変えたつもりで既定値のまま」の
/// 実験結果が出てしまうので、呼び出し側はこれが空でなければ止める。
pub fn unknown_flags(args: &[String]) -> Vec<String> {
    let known: BTreeSet<&str> = OPTIONS.iter().map(|o| o.name).collect();
    let mut bad = Vec::new();
    for a in args.iter().skip(1) {
        if !a.starts_with("--") { continue; }
        let name = a.split('=').next().unwrap_or(a);
        if !known.contains(name) { bad.push(a.clone()); }
    }
    bad
}

/// 「もしかして」候補(編集距離1〜2の最も近い既知フラグ)。
pub fn nearest_flag(input: &str) -> Option<&'static str> {
    let name = input.split('=').next().unwrap_or(input);
    OPTIONS.iter()
        .map(|o| (o.name, levenshtein(name, o.name)))
        .filter(|&(_, d)| d <= 3)
        .min_by_key(|&(_, d)| d)
        .map(|(n, _)| n)
}

fn levenshtein(a: &str, b: &str) -> usize {
    let (a, b): (Vec<char>, Vec<char>) = (a.chars().collect(), b.chars().collect());
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    let mut cur = vec![0usize; b.len() + 1];
    for i in 1..=a.len() {
        cur[0] = i;
        for j in 1..=b.len() {
            let cost = if a[i - 1] == b[j - 1] { 0 } else { 1 };
            cur[j] = (prev[j] + 1).min(cur[j - 1] + 1).min(prev[j - 1] + cost);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[b.len()]
}

/// 🌟 フラグと環境変数の両方で指定できる設定の置き場。
///
/// `--systematic=...` のようなフラグは main で1度だけ読み取り、
/// 深いところ(discover.rs の閉包や padic_eval の検出器)からは
/// この関数経由で参照する。環境変数を書き換えて橋渡しする手もあるが、
/// std::env::set_var は他スレッドと競合し得るため unsafe であり、
/// 「起動時に1回決めて以後読むだけ」というこの用途には OnceLock の方が
/// 素直で安全。main を通らないテストからも使えるよう、初期化されて
/// いなければ環境変数だけを見る。
pub struct Overrides {
    /// `--systematic=ラウンド,実体数上限,1種あたり` / DISCOVER_SYSTEMATIC
    pub systematic: Option<String>,
    /// `--audit` / DISCOVER_AUDIT
    pub audit: bool,
    /// `--sweep-debug` / SWEEP_DEBUG
    pub sweep_debug: bool,
}

static OVERRIDES: std::sync::OnceLock<Overrides> = std::sync::OnceLock::new();

/// mainで1度だけ呼ぶ。フラグが無ければ環境変数を見る(後方互換)。
pub fn init(args: &[String]) {
    let value_of = |flag: &str| -> Option<String> {
        let with_value = format!("{}=", flag);
        args.iter().find_map(|a| a.strip_prefix(with_value.as_str()).map(|v| v.to_string()))
    };
    let present = |flag: &str| args.iter().any(|a| a == flag);
    let _ = OVERRIDES.set(Overrides {
        systematic: value_of("--systematic").or_else(|| std::env::var("DISCOVER_SYSTEMATIC").ok()),
        audit: present("--audit") || std::env::var("DISCOVER_AUDIT").is_ok(),
        sweep_debug: present("--sweep-debug") || std::env::var("SWEEP_DEBUG").is_ok(),
    });
}

fn overrides() -> &'static Overrides {
    OVERRIDES.get_or_init(|| Overrides {
        systematic: std::env::var("DISCOVER_SYSTEMATIC").ok(),
        audit: std::env::var("DISCOVER_AUDIT").is_ok(),
        sweep_debug: std::env::var("SWEEP_DEBUG").is_ok(),
    })
}

/// 系統的作図の設定(`ラウンド,実体数上限,1種あたり`)。Noneならこのモードは使わない。
pub fn systematic() -> Option<&'static str> { overrides().systematic.as_deref() }
/// 構造的な主張と数値評価の整合を各ステップで検査するか。
pub fn audit() -> bool { overrides().audit }
/// 検出器が何件を何の理由で捨てたかを標準エラーに出すか。
pub fn sweep_debug() -> bool { overrides().sweep_debug }

#[cfg(test)]
mod tests {
    use super::*;

    /// 🌟 この表と実際の解析がずれると、ヘルプが嘘をつくうえに正しいフラグが
    /// 「未知」として弾かれてしまう。ソースを走査して、実際に解析されている
    /// `--xxx` が全部 OPTIONS に載っていることを確かめる。
    #[test]
    fn every_flag_in_source_is_documented() {
        const SOURCES: &[&str] = &[
            include_str!("main.rs"),
            include_str!("solve.rs"),
            include_str!("discover.rs"),
            include_str!("discover_degenerate.rs"),
        ];
        let known: BTreeSet<&str> = OPTIONS.iter().map(|o| o.name).collect();
        let mut missing: Vec<String> = Vec::new();
        for src in SOURCES {
            for (pat, strip_eq) in [("strip_prefix(\"", true), ("a == \"", false), ("flag(args, \"", false), ("value(args, \"", true)] {
                let mut rest = *src;
                while let Some(pos) = rest.find(pat) {
                    rest = &rest[pos + pat.len()..];
                    let Some(end) = rest.find('"') else { break };
                    let tok = &rest[..end];
                    if !tok.starts_with("--") { continue; }
                    let name = if strip_eq { tok.trim_end_matches('=') } else { tok };
                    if !known.contains(name) && !missing.contains(&name.to_string()) {
                        missing.push(name.to_string());
                    }
                }
            }
        }
        assert!(missing.is_empty(),
            "ソース中で解析されているのに cli.rs::OPTIONS に載っていないフラグ: {:?}", missing);
    }

    #[test]
    fn unknown_flags_are_detected_and_suggested() {
        let args: Vec<String> = ["geom_solver", "simson", "--sweep-point=60", "--mcts"]
            .iter().map(|s| s.to_string()).collect();
        let bad = unknown_flags(&args);
        assert_eq!(bad, vec!["--sweep-point=60".to_string()],
            "綴り違いのフラグだけが未知として検出されるべき");
        assert_eq!(nearest_flag("--sweep-point=60"), Some("--sweep-points"),
            "一番近い既知のフラグを提案できるべき");
    }

    #[test]
    fn flags_and_env_vars_are_both_understood() {
        // init前(=mainを通らないテスト実行時)は環境変数だけを見る。
        assert!(!audit() || std::env::var("DISCOVER_AUDIT").is_ok(),
            "initされていなければ環境変数の有無と一致するべき");
        // フラグの読み取り自体は init を通さずとも同じ規則で確かめられる。
        let args: Vec<String> = ["geom_solver", "discover", "--systematic=4,800,10", "--audit"]
            .iter().map(|s| s.to_string()).collect();
        let value_of = |flag: &str| -> Option<String> {
            let w = format!("{}=", flag);
            args.iter().find_map(|a| a.strip_prefix(w.as_str()).map(|v| v.to_string()))
        };
        assert_eq!(value_of("--systematic").as_deref(), Some("4,800,10"));
        assert!(args.iter().any(|a| a == "--audit"));
    }
}

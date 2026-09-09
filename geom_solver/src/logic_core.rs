use crate::mmp_core::{ClassId, Definition, EGraph, EntityType, Fact};
use rustc_hash::FxHashMap;
use std::collections::{BinaryHeap, VecDeque};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// 🌟 dfs_matchの探索木を1ノード進むたびに bind/flip_states を丸ごと
// ディープコピーしていた問題を解消するため、通常のHashMapではなく
// 構造共有型(永続データ構造)のHashMapを使う。要素を1つ追加しても
// 変更されたごく一部のノードだけを複製し、残りは元のインスタンスと
// ポインタ(Rc)を共有するので、.clone()の実質コストがO(1)に近くなる。
// 呼び出し側の書き方(.clone()や.insert())は通常のHashMapと同じままで良い。
// 🌟 検証メモ: FxHashに差し替えると(im::HashMap<..., FxBuild>)、内部のHAMT構造との
// 相性が悪いのか実測でむしろ悪化した(miquel: 0.36s→1.12s)ため、以前は既定の
// RandomStateのままにしていた。しかしRandomStateはプロセスごとに異なる
// ランダムなシードで初期化されるため、bind.iter()の反復順序(ひいては定理
// マッチングが候補を試す順序)がプロセス起動のたびに変わってしまい、
// 「同じ問題を2回実行すると異なる長さの証明が見つかる」という再現性の
// 無さの原因になっていた(extract_proofの調査で発覚)。
// 🌟 FIX: BuildHasherDefault<DefaultHasher>(SipHash系だがFxHashとは異なる
// アルゴリズムで、シードが固定・決定的)に差し替えることで、FxHash+HAMTの
// 相性問題を避けつつ決定性を得る。miquel等での実測では有意な性能劣化は
// 見られなかった(検証手順はコミットメッセージ参照)。
pub type Bind = im::HashMap<String, ClassId, std::hash::BuildHasherDefault<std::collections::hash_map::DefaultHasher>>;
pub type FlipStates = im::HashMap<String, bool, std::hash::BuildHasherDefault<std::collections::hash_map::DefaultHasher>>;

/// 🌟 ユーザー提案(定理マッチングの最適化)への対応その2: 定理の型シグネチャに
/// よる事前フィルタで使う、「この変数はこの定理の前提(patterns)の中で
/// 実際に照合される」変数名だけを集めるヘルパー。Pattern::Fact の args に加え、
/// Order/Distinctの対象変数、Not の中身も再帰的に辿る。constructions/conclusions
/// にしか出てこない変数(この定理自身が作図で新規生成するだけの図形、例えば
/// スパイラル相似の中点対応定理のM,N)はここには含まれない――そうした変数は
/// 「今グラフに存在しなくても、この定理自身が後で作るから問題ない」ため、
/// 事前フィルタの対象から除外する必要があるのが理由(詳細はrequired_hard_typesの
/// ドキュメント参照)。
fn collect_pattern_vars<'a>(pat: &'a Pattern, out: &mut Vec<&'a str>) {
    match pat {
        Pattern::Fact(def) => { for v in &def.args { out.push(v.as_str()); } }
        Pattern::Distinct(vars) | Pattern::Order(vars) | Pattern::OrderNonStrict(vars) => { for v in vars { out.push(v.as_str()); } }
        Pattern::Not(inner) => collect_pattern_vars(inner, out),
    }
}

/// 🌟 backlog#1「二重自己束縛/自己束縛×DefinedByペアリングの掛け合わせを
/// 熱量駆動で絞る」のドキュメント参照(match_identical_factの(None,None)
/// 自己束縛分岐で使う)。診断の結果、「有向角の加法性」(2つの独立した
/// (None,None)自己束縛の掛け合わせ)だけでなく、「円周角の定理の逆」
/// (1つの自己束縛Identical(v1,v2)から、v1・v2それぞれを結果変数とする
/// 同じtarget_typeのDefinedByパターンが独立に2本ぶら下がる)でも、
/// 自己束縛の候補数(cap)がそのまま下流全体の分岐係数になっていた
/// (実測: Distinct(L1,L2,L3,L4)が最多選択パターンになるほど下流の
/// Connectedチェーンまで含めて膨らむ)。この関数は後者の構造――
/// 「Identical(v1,v2)のv1・v2それぞれに、同じtarget_typeのDefinedBy
/// パターンがぶら下がっているか」――を定理の静的なパターン列だけから
/// 判定する。定理名のハードコードはしない。
fn has_paired_defined_by_fanout(theorem: &TheoremDef, v1: &str, v2: &str) -> bool {
    let mut types_for_v1: rustc_hash::FxHashSet<&str> = rustc_hash::FxHashSet::default();
    let mut types_for_v2: rustc_hash::FxHashSet<&str> = rustc_hash::FxHashSet::default();
    for p in &theorem.patterns {
        if let Pattern::Fact(d) = p {
            if d.fact_type == "DefinedBy" {
                if let (Some(result), Some(tt)) = (d.args.last(), d.target_type.as_deref()) {
                    if result == v1 { types_for_v1.insert(tt); }
                    if result == v2 { types_for_v2.insert(tt); }
                }
            }
        }
    }
    types_for_v1.intersection(&types_for_v2).next().is_some()
}

/// 🌟 定理の型シグネチャ事前フィルタ本体: この定理のpatternsの中で実際に
/// 照合される変数のうち、「DefinedByのマッチング中には自動生成されない型
/// (=既にグラフ上に実体が無ければ絶対にマッチしようがない型)」だけを集めて
/// 返す。
///
/// 背景: defined_by_valid_nodes の自動生成ホワイトリスト
/// (`"AnglePair" | "DirectionOf" | "LengthSq" | "CrossRatio" | "CrossRatioOfLines" | "Product"`)
/// に載っている型(Angle/Direction/Scalar)は、親変数さえ既存であれば
/// マッチングの最中にその場で新規生成される「軟らかい」型なので、対象外
/// (=グラフに1つも無くても、親さえあれば定理は普通にマッチし得る)。
/// 一方Point/Line/Circle/Conicはこのホワイトリストに無く、既存のmemo/
/// 全件スキャンでしか見つからない「硬い」型なので、そのうちどれか1つでも
/// グラフに実体が1つも存在しなければ、この定理はどう頑張っても
/// マッチしようがない(必要条件であり、偽陰性を生まない安全なフィルタ)。
///
/// 定理が増えるほど「一度は素の全探索で試してみる」というUCB1のコストが
/// 無関係な問題にまで課税される問題(このセッションで円の一意性・
/// スパイラル相似の両方で実際に観測した既知のトレードオフ)に対し、
/// 「そもそも必要な型の実体が1つも無い」という自明に無駄な試行だけでも
/// スケジューリングの時点で弾くことで軽減する。
fn required_hard_types(theorem: &TheoremDef) -> Vec<crate::mmp_core::EntityType> {
    use crate::mmp_core::EntityType;
    let mut names = Vec::new();
    for pat in &theorem.patterns {
        collect_pattern_vars(pat, &mut names);
    }
    let mut set: std::collections::HashSet<EntityType> = std::collections::HashSet::new();
    for name in names {
        if let Some(&t) = theorem.entities.get(name) {
            // 🌟 EntityType::Direction/Angle撤廃に伴い、旧Direction(今はPoint)・
            // 旧Angle(今はScalar)はこのExcalar除外の対象に含まれる(方向・角度は
            // 常にDefinedBy/Connected経由で導出され、自由点のようにあらかじめ
            // 十分な数が存在するとは限らないため、元々Scalarと同じく「必須の
            // 事前存在チェック」の対象外だった――撤廃の前後でこの判定自体の
            // 意味は変わらない: 単にEntityType::Scalarを素通しするだけ)。
            if !matches!(t, EntityType::Scalar) {
                set.insert(t);
            }
        }
    }
    set.into_iter().collect()
}

/// 🌟 探索木キャッシュの型依存追跡(ユーザー提案「新規作図でfailed pathが
/// 破棄されるのはある程度どうしようもないが、接続が弱い(=特定の型の
/// プール列挙に依存しない)failed pathは定理によっては保持できるのでは」
/// への対応)。EntityTypeは4種類しかないため、u8のビットマスク1つで
/// 「この失敗が実際にどの型のプール列挙に依存したか」を表現できる。
/// 以前は定理全体が使う型の和集合(theorem_all_types、今は撤去)という
/// 定理単位の粗い粒度で「1つでも変わったらfailed_paths全体を破棄」して
/// いたが、これを「個々のキャッシュ済み失敗状態ごとに、実際に依存した
/// 型だけ」という細かい粒度に変える。Distinct/Order/両方束縛済みの
/// チェックだけで確定した失敗はどの型のプールも覗いていない(マスク0)ため、
/// 新規エンティティがいくつ生まれようと永続的に有効であり続ける。
pub(crate) fn entity_type_bit(t: crate::mmp_core::EntityType) -> u8 {
    use crate::mmp_core::EntityType::*;
    match t {
        Point => 0b0001,
        Line => 0b0010,
        Scalar => 0b0100,
        Conic => 0b1000,
    }
}
/// 🌟 「型が不明なフォールバック」など、依存先を型単位で特定できない
/// 経路が安全側に倒すときに使う、全型への依存を表すマスク。
pub(crate) const ALL_TYPES_MASK: u8 = 0b1111;
/// 🌟 MatchTask再開時に、現在のtype_generationスナップショットを取る
/// ための固定順序の全型リスト。以前は定理ごとに使う型を絞っていた
/// (theorem_all_types)が、判定自体を個々のキャッシュ済み失敗状態の
/// マスク単位に移したことで、スナップショットは常に全4型で十分かつ
/// 単純になった(4回のHashMapルックアップなので絞る動機自体が薄い)。
const ALL_ENTITY_TYPES: [crate::mmp_core::EntityType; 4] = [
    crate::mmp_core::EntityType::Point,
    crate::mmp_core::EntityType::Line,
    crate::mmp_core::EntityType::Scalar,
    crate::mmp_core::EntityType::Conic,
];

/// 🌟 指定した型それぞれについて、現在のEGraph::type_generationの値を
/// 記録したスナップショットを作る。MatchTaskがdfs_cap到達で再キューされる
/// 際にこれを保存しておき、再開時に現在値と比較することで、「この型で
/// キャッシュ時点以降に変化(マージ・新規生成・接続関係の追加・memoの
/// 事後登録のいずれか)が起きたか」を判定する。
///
/// 🌟 この判定が安全であるための前提(mmp_core::EGraph::type_generationの
/// ドキュメント参照): e-graphの生の構造フィールド(components/subobjects/
/// uses/memo)を書き換える操作はcreate_entity/merge_entities/
/// link_logical_incidence/insert_memoの4つのゲートウェイだけに集約されており、
/// それぞれが必ずtype_generationを更新する。この不変条件が崩れる(=新しい
/// ゲートウェイ相当の直接書き込みが追加され、type_generationの更新を
/// 忘れる)と、ここでの判定が古い(既に無効な)failed_pathsを誤って再利用
/// してしまい、本来見つかるはずのマッチを静かに逃す――過去に実際にこの
/// 見落としで複数のベンチマーク問題が回帰したことがある。今後EGraphに
/// 新しい構造変更手段を追加する際は、必ずこの4つのゲートウェイのどれかを
/// 経由するか、新規に追加してnote_type_changedを呼ぶこと。
fn snapshot_type_generations(egraph: &EGraph) -> [u64; 4] {
    std::array::from_fn(|i| egraph.type_generation.get(&ALL_ENTITY_TYPES[i]).copied().unwrap_or(0))
}

fn get_permutations(items: &[ClassId]) -> Vec<Vec<ClassId>> {
    if items.len() <= 1 { return vec![items.to_vec()]; }
    let mut result = Vec::new();
    for i in 0..items.len() {
        let mut rest = items.to_vec();
        let val = rest.remove(i);
        for mut sub in get_permutations(&rest) {
            sub.insert(0, val);
            result.push(sub);
        }
    }
    result
}

#[derive(Debug, Clone)]
pub struct FactPatternDef {
    pub fact_type: String,
    pub args: Vec<String>,
    pub target_type: Option<String>,
    pub sub_type: Option<String>,
    pub allow_flip: bool,
    pub flip_group: Option<String>,
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Fact(FactPatternDef),
    Distinct(Vec<String>),
    Order(Vec<String>),
    // 🌟 ユーザー要望「TheoremDefの改善(Simson級を1秒未満に)」への対応:
    // Order(厳密な "<") は、隣接する2変数が「本質的に等しくなり得ない」場合
    // (例: distinctが別途要求されている)にしか安全に使えない。角の加法性
    // ([D1,D2,D3] と [D4,D5,D6] という2組の方向トリプルを入れ替えても
    // 同じ結論(Ang13≡Ang46、Identicalは順序を問わない)になる)のような
    // 「2つの役割を丸ごと入れ替えても同じ結論になる」対称性を潰したい
    // だけの場合、Orderの厳密な "<" だと D1==D4(方向を共有する、まさに
    // 角度チェイスの本来のユースケース)の場合に両方向とも弾かれ、
    // その代表元ペアだけ結論に到達できなくなる致命的なバグになる。
    // OrderNonStrict は "<=" (等しい場合は許可)で判定し、非自明な
    // (D1≠D4)ケースの入れ替え対称性だけを半分に間引く。数学的な証明:
    // D1>D4を満たす任意の充足解は、[D1..D3]と[D4..D6]をまるごと入れ替えた
    // 解(結論のIdenticalは順序を問わないので同じ結論を生む)が必ず存在し、
    // その入れ替え解は D1'=D4<D4'=D1 なので D1'<=D4' を満たす。
    // つまりD1==D4の解を一切失わずに、対称な重複探索だけを削減できる。
    OrderNonStrict(Vec<String>),
    Not(Box<Pattern>),
}

#[derive(Debug, Clone)]
pub struct ConstructTemplate {
    pub def_type: String,
    pub args: Vec<String>,
    pub target_type: String,
    pub bind_to: String,
}

#[derive(Debug, Clone)]
pub struct FactTemplate {
    pub fact_type: String,
    pub args: Vec<String>,
    pub target_type: Option<String>,
    pub sub_type: Option<String>,
}

#[derive(Debug, Clone)]
pub struct TheoremDef {
    pub name: String,
    pub entities: FxHashMap<String, EntityType>,
    pub patterns: Vec<Pattern>,
    pub constructions: Vec<ConstructTemplate>,
    pub conclusions: Vec<FactTemplate>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    FactProven(Fact),
    NodeMerged,
}

#[derive(Debug, Clone)]
pub struct MatchTask {
    pub priority: i32,
    pub theorem_idx: usize,
    pub bind: Bind,
    pub flip_states: FlipStates,
    // 🌟 Rc化: タスクの複製・再キュー時に Vec<Pattern> をディープコピーせず、
    // ポインタ共有だけで済ませる(パターン列自体は不変なので安全)
    pub remaining_patterns: Rc<Vec<crate::logic_core::Pattern>>,
    // 🌟 UCB1バンディット用: このタスクが schedule_matcher_task 由来の
    // シード済みタスク(発見済みの事実から変数の多くを具体的に束縛済み、
    // 速く失敗/成功する)か、schedule_full_sweep 由来のシードなしタスク
    // (変数が全て未束縛、定理によっては膨大な探索の末にしか成否が
    // 分からない)かを区別する。priorityはcap到達時のペナルティで
    // 実行中に減算されて変動するため、"どちらの経路で生まれたか"という
    // 由来はpriorityの値から逆算せず、この専用フラグで明示的に持つ。
    // バンディット統計(TheoremBanditStats)はシードなしタスクの成否だけを
    // 学習対象にする(シード済みタスクは既に高確率で成功するとわかっている
    // 別種の試行なので、混ぜると「シードでよく呼ばれるが素の全探索では
    // ほぼ失敗する定理」の見込みスコアを不当に引き上げてしまう)。
    pub is_seeded: bool,
    // 🌟 failed_pathsは、以前はここ(MatchTask)にタスク単位の寿命で
    // 持たせていたが、docs/atlas.html §04-#3「タスクをまたいだグローバル
    // 化」への対応でProverEngine::global_failed_paths(theorem_idxで引く
    // 永続マップ)に昇格した。UCB1がschedule_full_sweepのたびに同じ定理を
    // 新しいtask/新しいbindで何度も試す(診断計測で判明した再訪問の主因)
    // ケースも、こちらならタスクをまたいで共有キャッシュとして機能する。
    // MatchTask自身はもうfailed_pathsを一切保持しない。
}

impl PartialEq for MatchTask { fn eq(&self, other: &Self) -> bool { self.priority == other.priority } }
impl Eq for MatchTask {}
impl PartialOrd for MatchTask { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) } }
impl Ord for MatchTask { fn cmp(&self, other: &Self) -> Ordering { self.priority.cmp(&other.priority) } }

/// 🌟 定理マッチングのUCB1バンディット統計。theorem_idxごとに、
/// schedule_full_sweep由来のシードなしタスクを実際にdfs_matchまで走らせた
/// 回数(attempts)と、その報酬の累積(total_reward)を数える。
///
/// 🐛 以前はsuccesses(結論を適用できた回数)を単純にカウントするだけの
/// 二値報酬だったため、「dfs_cap一杯まで探索してようやく1回成功した定理」と
/// 「一瞬で成功した定理」が同じ扱いになってしまい、まさに元々問題視していた
/// 「有向角の加法性」のような重い定理を正しく罰せなかった(A/B測定で
/// nine_point_fullにおいて有効化がむしろ約11%遅くなるという結果になった
/// 一因と見ている)。record_theorem_reward側でdfs_calls_used/dfs_capの
/// 比率をコストとして報酬に織り込むことで、「成功はしたが高くついた」
/// 定理と「安く成功した」定理を区別できるようにする。
#[derive(Debug, Clone, Copy, Default)]
pub struct TheoremBanditStats {
    pub attempts: u64,
    pub total_reward: f64,
    // 🌟 ProverEngine::ProfileStatsと同じ動機: schedule_full_sweepの実測が
    // 「そこ自体は安い」ことを示した以上、実際に壁時計時間を食っているのは
    // dfs_match本体側だという仮説を裏付けるための、定理ごとの内訳。
    // 1回の試行(シードなしタスク)がdfs_capにほぼ到達した(=ほぼ確実に
    // 100,000回のdfs_call、すなわち相応の壁時計時間を1回で消費した)回数。
    // --statsでattempts列と併記し、「試行回数は少ないのに時間を食っている」
    // 定理を名指しできるようにする。
    pub cap_hits: u64,
    // 🌟 Simsonクラスの問題を1秒未満で解く目標のための一時的な内訳計測:
    // この定理のシードなしタスク1回あたりが実際に何dfs_call消費したかの
    // 累計。cap_hitsだけだと「上限に張り付いた回数」しか分からず、
    // 上限未満でも1回あたり数千〜数万callを毎回消費するような定理を
    // 名指しできないため追加した。attempts で割れば平均コストになる。
    pub total_dfs_calls: u64,
}

impl TheoremBanditStats {
    /// UCB1スコア = 経験的な平均報酬 + 探索ボーナス。一度も試していない定理は
    /// 常に無限大を返し、必ず一度は(素の全探索からでも)試されるようにする
    /// (標準的なUCB1の初期化: 全アームを1回ずつ引いてから本題に入る)。
    fn ucb1_score(&self, total_attempts: u64, exploration_c: f64) -> f64 {
        if self.attempts == 0 { return f64::INFINITY; }
        let mean = self.total_reward / self.attempts as f64;
        let bonus = exploration_c * ((total_attempts.max(1) as f64).ln() / self.attempts as f64).sqrt();
        mean + bonus
    }
}

pub struct ProverEngine {
    pub egraph: EGraph,
    pub facts: Vec<Fact>,
    // 🌟 Rc化: 定理定義(文字列・パターン列を大量に持つ重い構造体)は実行中不変なので、
    // タスク処理のたびに丸ごとディープコピーする代わりに Rc でポインタ共有する
    pub theorems: Vec<Rc<TheoremDef>>,
    pub dfs_calls: u64,
    // 🐛 バグ修正: 以前は dfs_match の探索上限が常に100,000固定だった。
    // schedule_full_sweep() から生成される「シードなし(priority<=0)」タスクは、
    // 変数が全て未束縛のまま定理を試すため、変数の多い定理(例: 有向角の加法性)では
    // ほぼ必ず失敗するのに毎回上限いっぱいまで探索してしまい、しかも
    // schedule_full_sweep() は要求解決のたびに何度も呼ばれるため、
    // 同じ「失敗するだけの巨大探索」を繰り返して秒単位の時間を浪費していた
    // (simsonで実測: この1定理だけで5秒中3秒以上を消費)。
    // schedule_matcher_task() 由来のシード済みタスク(priority>=10)は
    // 既に変数の多くが具体的な値に束縛されているため速く失敗/成功するので
    // 上限は据え置き、シードなしタスクだけ上限を大幅に下げて早期に諦めさせる。
    pub dfs_cap: u64,
    // 🌟 ユーザー提案(「マッチングを熱の上位だけを見るようにしていた
    // パラメータを調整できないか」)への対応。熱で降順ソートした後に
    // 候補を打ち切る上限が複数箇所(match_identical_factの(None,None)
    // 自己束縛、match_connected_factの局所スキャン/(None,None)ジョイン)に
    // 40というマジックナンバーでハードコードされていたのを、CLIから
    // --heat-cap=Nで一括調整できるフィールドに切り出した(既定は従来通り
    // 40)。既存の3箇所は全て同じ値を共有してきた経緯があるため、当面は
    // 分離せず1つのつまみにまとめる。
    pub heat_cap: usize,
    // 🌟 同じ提案への対応。「二重自己束縛」定理(有向角の加法性のように
    // 同じ型への(None,None)自己束縛を2つ以上持つ、または円周角の定理の逆
    // のように自己束縛の下流に同じtarget_typeのDefinedByペアリングが
    // ぶら下がる定理)は、自己束縛のcapがそのまま下流の分岐係数(cap×cap)
    // になるため、通常より大きく絞った専用のcapを使ってきた(既定10)。
    // --fanout-heat-cap=Nで調整できる。
    pub fanout_heat_cap: usize,
    pub construction_demands: FxHashMap<(ClassId, ClassId), f64>, // 🌟 Blackboardから移動
    // 🌟 「2直線は既にあるが、その交点がまだ図形として存在しない」ことへの
    // 需要。キーは2直線(ソート済み)。construction_demandsと同じ役割を
    // Intersection(点)に対して果たす。resolve_point_demandsが消費する。
    pub point_construction_demands: FxHashMap<(ClassId, ClassId), f64>,
    // 🌟 UCB1バンディット統計。theorems と同じインデックス(theorem_idx)で
    // 引く。theoremsはProverEngine::new後にmain.rs側で流し込まれるため、
    // ここでは空のまま初期化し、実際に使う直前にensure_theorem_statsで
    // theorems.len()に合わせてリサイズする。
    pub theorem_stats: Vec<TheoremBanditStats>,
    // 🌟 required_hard_typesのドキュメント参照。theoremsと同じインデックス
    // (theorem_idx)で引く。theorem_statsと同じく、theoremsが確定した後に
    // ensure_theorem_required_typesで遅延計算する(theorem.patternsは実行中
    // 不変なので、一度計算すれば使い回せる)。
    pub theorem_required_types: Vec<Vec<crate::mmp_core::EntityType>>,
    // 🌟 ユーザー提案(定理マッチングの最適化・案4): 定理横断の共有部分マッチ
    // キャッシュ、第一弾。match_connected_fact の Connected(child, parent)
    // 両方未束縛分岐は、実は「bindの中身に一切依存せず、(child_type, parent_type)
    // という型の組み合わせだけで結果が決まるジョイン演算」になっている
    // ――どの定理・どのタスクから呼ばれても、同じ型の組み合わせなら
    // 全く同じ (child_rep, parent_rep) のペア集合が返る。RETEのアルファ/
    // ベータメモリと同じ発想で、この結果を定理をまたいで共有キャッシュする。
    // キーは(child_type, parent_type)、値は(結果, キャッシュ時点での
    // child_typeのtype_generation, 同parent_typeのtype_generation)。
    // 案3で導入したEGraph::type_generationが「この型の候補集合・接続関係が
    // 変わったら必ず上がる」という健全な不変条件を満たすようになった
    // (4つのゲートウェイに集約済み)ため、そのままこのキャッシュの
    // 無効化判定に使い回せる。
    pub connected_join_cache: FxHashMap<(crate::mmp_core::EntityType, crate::mmp_core::EntityType), (Rc<Vec<(ClassId, ClassId)>>, u64, u64)>,
    // 🌟 同じ発想の第二弾: match_identical_fact の Identical(v1, v2) 両方
    // 未束縛(自己束縛)分岐も、「期待される型」だけで決まる候補列挙
    // (heatによる並べ替え前の生の候補集合)を、定理をまたいで共有できる。
    // キーはexpected_type、値は(結果, キャッシュ時点でのtype_generation)。
    // heat_bonusはバッチ中にも動的に変わるため、並べ替え・上位40件への
    // 絞り込みは呼び出しのたびに毎回この生のリストに対して行う
    // (キャッシュするのは「型で絞り込んだ後・heat基準で並べ替える前」の
    // 集合だけ)。
    pub identical_self_bind_cache: FxHashMap<crate::mmp_core::EntityType, (Rc<Vec<ClassId>>, u64)>,
    // 🌟 identical_self_bind_cacheをEntityType::Scalarについてだけ、
    // さらに「角度(AnglePair)由来かどうか」で2分割した専用キャッシュ。
    // EGraph::angle_generation/plain_scalar_generationのドキュメント
    // (mmp_core/mod.rs)参照。EntityType::Angle撤廃により長さ・積・複比・
    // 角度が全てEntityType::Scalarを共有するようになった結果、
    // identical_self_bind_cache(Scalar)はこれらどれか1つが新規生成
    // されるだけで無効化されてしまい、角度連鎖定理の自己束縛が
    // (逆に非角度の自己束縛も)キャッシュヒットしなくなっていた
    // (実測でベンチマーク合格率が69/96→57/96に悪化する回帰として
    // 顕在化した)。type_generation[Scalar]ではなくangle_generation/
    // plain_scalar_generationという、それぞれ角度側・非角度側の変化にしか
    // 反応しない専用カウンタで無効化判定することで、無関係な側の
    // 生成イベントに引きずられて再計算されるのを防ぐ。
    pub identical_self_bind_angle_cache: Option<(Rc<Vec<ClassId>>, u64)>,
    pub identical_self_bind_plain_scalar_cache: Option<(Rc<Vec<ClassId>>, u64)>,
    // 🌟 同じ発想の第三弾: defined_by_valid_nodes の「両方未束縛」分岐
    // (親変数もresult_varも未束縛で、期待される結果の型だけで全代表元を
    // 列挙するフォールバック)も、identical_self_bind_cacheと全く同じ形の
    // 「型→代表元集合」の問い合わせで、bindの中身にもtarget_typeにも依存
    // しない(target_typeはこの後defined_by_collect_matchesが実際の
    // Definitionで絞り込むための情報で、valid_nodesの列挙自体には使われて
    // いない)。よってキーはexpected_r_type(EntityType)のみでよく、
    // identical_self_bind_cacheと同じtype_generation方式でそのまま
    // 定理をまたいで共有できる。ただしidentical_self_bind_cacheは
    // base_importance>0.0のフィルタをかけているのに対し、この分岐は
    // フィルタなしで全代表元を返す(既存の挙動を変えないための別キャッシュ)。
    pub defined_by_full_scan_cache: FxHashMap<crate::mmp_core::EntityType, (Rc<Vec<ClassId>>, u64)>,
    // 🌟 ユーザー提案(「探索木のメモ化」の続き、docs/atlas.html §04-#3
    // 参照)への対応: 以前はMatchTask::cached_failed_pathsという
    // タスク単位の寿命でfailed_pathsを持ち越していたため、UCB1が同じ
    // 定理をschedule_full_sweepのたびに新しいtask/新しいbindで何度も
    // 試す(診断計測で判明した「dfs_matchの再訪問の38%がタスクをまたぐ」
    // 主因)ケースを一切捕捉できなかった。state_sig(dfs_match参照)は
    // 元々「このタスクのbind内容+flip状態」だけで決まる内容ベースの
    // ハッシュで、特定のMatchTaskインスタンスとは無関係だったため、
    // これをtheorem_idxごとの永続マップに昇格させるだけで、同じ定理への
    // 異なるタスクからの再訪問もそのまま共有キャッシュとして機能する。
    // 無効化はもうタスク単位の一括判定ではなく、エントリ自身が持つ
    // (mask, 挿入時の型generationスナップショット)を参照時に個別検証する
    // 方式(u8依存マスクの細分化と同じ発想をタスクをまたいで適用しただけ)。
    // 値の(u8, [u64;4])は(依存マスク, その時点でのALL_ENTITY_TYPES順の
    // type_generationスナップショット)――マスクが立っている型だけを
    // 比較すればよい。
    pub global_failed_paths: Vec<rustc_hash::FxHashMap<u64, (u8, [u64; 4])>>,
    // 🌟 ユーザー提案(「schedule_full_sweepの改善を続ける」)への対応: 2度の
    // 撤回(DefinedBy遅延構築・スケジューラ精密化)がいずれも「schedule_
    // full_sweepが重いはず」という推測から出発し、実測せずに手を入れて
    // 原因を特定できないまま終わった反省を踏まえ、まず実測用のカウンタを
    // 用意する。main.rsのメインループが各フェーズ(dfs_match本体・回復
    // フェーズ・MCTS)の実行時間を計測してここに積み上げ、--profileで
    // 終了時に集計を表示する(ProfileStatsのドキュメント参照)。
    pub profile: ProfileStats,
}

/// 🌟 ProverEngine::profileのドキュメント参照。schedule_full_sweep自体の
/// 呼び出し回数・所要時間・生成したシードなしタスク数、および
/// メインループの3大フェーズ(dfs_match本体/回復フェーズ/MCTS)の
/// 所要時間を集計する、実行時プロファイリング専用の構造体。
/// 証明の正しさには一切影響しない、純粋な計測用の副産物。
#[derive(Debug, Clone, Copy, Default)]
pub struct ProfileStats {
    pub sfs_calls: u64,
    pub sfs_time: std::time::Duration,
    pub sfs_tasks_created: u64,
    pub run_step_time: std::time::Duration,
    pub recovery_time: std::time::Duration,
    pub mcts_time: std::time::Duration,
    // 🌟 --statsの定理別UCB1統計はis_seeded=falseのタスクしか数えていない
    // (MatchTask::is_seededのドキュメント参照)。schedule_matcher_task由来の
    // シード済みタスクは新事実が証明されるたびに(理論上は該当する全定理×
    // 全パターン×全順列の分だけ)大量に生成され得るため、実際の総dfs_call数の
    // 内訳がシード済み側に偏っている可能性がある。ここでシード済み/シード
    // なし双方のタスクポップ数とdfs_call消費量を種別ごとに集計し、
    // 「少数の高コストな試行」なのか「大量の小さな試行の積み重ね」なのかを
    // 実測で切り分けられるようにする。
    pub seeded_pops: u64,
    pub seeded_dfs_calls: u64,
    pub unseeded_pops: u64,
    pub unseeded_dfs_calls: u64,
}

impl ProverEngine {
    pub fn new(egraph: EGraph) -> Self {
        Self {
            egraph,
            facts: Vec::new(),
            theorems: Vec::new(),
            dfs_calls: 0,
            dfs_cap: 100_000,
            heat_cap: 40,
            fanout_heat_cap: 10,
            construction_demands: FxHashMap::default(), // 🌟 追加
            point_construction_demands: FxHashMap::default(),
            theorem_stats: Vec::new(),
            theorem_required_types: Vec::new(),
            connected_join_cache: FxHashMap::default(),
            identical_self_bind_cache: FxHashMap::default(),
            identical_self_bind_angle_cache: None,
            identical_self_bind_plain_scalar_cache: None,
            defined_by_full_scan_cache: FxHashMap::default(),
            global_failed_paths: Vec::new(),
            profile: ProfileStats::default(),
        }
    }

    /// 🌟 global_failed_pathsのドキュメント参照。theorem_stats/theorem_
    /// required_typesと同じ「theoremsが確定してから初めて呼ばれた時点で
    /// theorems.len()に合わせて遅延リサイズする」パターン。
    fn ensure_global_failed_paths(&mut self) {
        if self.global_failed_paths.len() != self.theorems.len() {
            self.global_failed_paths.resize_with(self.theorems.len(), rustc_hash::FxHashMap::default);
        }
    }

    /// 🌟 connected_join_cacheのドキュメント参照。Connected(child, parent)の
    /// 両方未束縛分岐が問い合わせる、型だけで決まる(child_rep, parent_rep)
    /// ペアの共有ジョイン結果を返す。type_generationが前回計算時と
    /// 変わっていなければキャッシュをそのまま返し(定理をまたいだ再利用)、
    /// 変わっていれば再計算してキャッシュを更新する。
    fn connected_pairs_for_types(&mut self, c_type: crate::mmp_core::EntityType, p_type: crate::mmp_core::EntityType) -> Rc<Vec<(ClassId, ClassId)>> {
        let cur_c_gen = self.egraph.type_generation.get(&c_type).copied().unwrap_or(0);
        let cur_p_gen = self.egraph.type_generation.get(&p_type).copied().unwrap_or(0);
        if let Some((cached, gen_c, gen_p)) = self.connected_join_cache.get(&(c_type, p_type)) {
            if *gen_c == cur_c_gen && *gen_p == cur_p_gen {
                return cached.clone();
            }
        }
        let mut pairs = Vec::new();
        for p_rep in self.egraph.iter_reps_of_type(p_type) {
            if !self.egraph.entities[p_rep.0].is_active() { continue; }
            if let Some(comp) = self.egraph.entities[p_rep.0].components.first() {
                for &sub in &comp.subobjects {
                    let c_rep = self.egraph.get_rep(sub);
                    if c_rep == p_rep { continue; }
                    if !self.egraph.entities[c_rep.0].is_active() { continue; }
                    if self.egraph.entities[c_rep.0].entity_type != c_type { continue; }
                    pairs.push((c_rep, p_rep));
                }
            }
        }
        let result = Rc::new(pairs);
        self.connected_join_cache.insert((c_type, p_type), (result.clone(), cur_c_gen, cur_p_gen));
        result
    }

    /// 🌟 identical_self_bind_cacheのドキュメント参照。Identical(v1, v2)の
    /// 両方未束縛(自己束縛)分岐が問い合わせる、型だけで決まる候補代表元の
    /// 共有列挙結果を返す(heatによる並べ替え・上位40件への絞り込みは
    /// 呼び出し側が毎回この結果に対して行う)。
    fn identical_self_bind_candidates(&mut self, et: crate::mmp_core::EntityType) -> Rc<Vec<ClassId>> {
        let cur_gen = self.egraph.type_generation.get(&et).copied().unwrap_or(0);
        if let Some((cached, cached_gen)) = self.identical_self_bind_cache.get(&et) {
            if *cached_gen == cur_gen { return cached.clone(); }
        }
        let mut reps = Vec::new();
        for id in self.egraph.iter_reps_of_type(et) {
            if self.egraph.entities[id.0].is_active() { reps.push(id); }
        }
        let result = Rc::new(reps);
        self.identical_self_bind_cache.insert(et, (result.clone(), cur_gen));
        result
    }

    /// 🌟 identical_self_bind_angle_cache/identical_self_bind_plain_scalar_cache
    /// のドキュメント参照。EntityType::Scalarの自己束縛候補を「角度
    /// (AnglePair)由来のものだけ」に絞った専用キャッシュ。angle_generation
    /// (mmp_core/mod.rs)が変わっていなければ(=角度が絡む生成・併合が
    /// 一度も起きていなければ)、無関係な長さ・積・複比の生成では
    /// 再計算しない。
    fn identical_self_bind_angle_candidates(&mut self) -> Rc<Vec<ClassId>> {
        let cur_gen = self.egraph.angle_generation;
        if let Some((cached, cached_gen)) = &self.identical_self_bind_angle_cache {
            if *cached_gen == cur_gen { return cached.clone(); }
        }
        let mut reps = Vec::new();
        for id in self.egraph.iter_reps_of_type(crate::mmp_core::EntityType::Scalar) {
            if self.egraph.entities[id.0].is_active() && self.egraph.is_angle_value(id) {
                reps.push(id);
            }
        }
        let result = Rc::new(reps);
        self.identical_self_bind_angle_cache = Some((result.clone(), cur_gen));
        result
    }

    /// 🌟 上のidentical_self_bind_angle_candidatesの裏返し: EntityType::Scalarの
    /// うち角度(AnglePair)由来ではないもの(長さ・積・複比等)だけに絞った
    /// 専用キャッシュ。plain_scalar_generation(mmp_core/mod.rs)が変わって
    /// いなければ再計算しない――角度側の生成・併合だけが起きた場合に、
    /// こちらまで無駄に無効化されるのを防ぐ。EntityType::Angle撤廃より前は
    /// EntityType::Scalarに角度が混ざること自体が無かったので、この絞り込みは
    /// 撤廃前の挙動をそのまま再現するためのものでもある(絞り込まずに
    /// 返すと、角度に無関係なIdentical自己束縛のheatソート済みcapが
    /// 角度候補に食われてしまう)。
    fn identical_self_bind_plain_scalar_candidates(&mut self) -> Rc<Vec<ClassId>> {
        let cur_gen = self.egraph.plain_scalar_generation;
        if let Some((cached, cached_gen)) = &self.identical_self_bind_plain_scalar_cache {
            if *cached_gen == cur_gen { return cached.clone(); }
        }
        let mut reps = Vec::new();
        for id in self.egraph.iter_reps_of_type(crate::mmp_core::EntityType::Scalar) {
            if self.egraph.entities[id.0].is_active() && !self.egraph.is_angle_value(id) {
                reps.push(id);
            }
        }
        let result = Rc::new(reps);
        self.identical_self_bind_plain_scalar_cache = Some((result.clone(), cur_gen));
        result
    }

    /// 🌟 defined_by_full_scan_cacheのドキュメント参照。DefinedByパターンの
    /// 親変数・result_varがどちらも未束縛の場合に問い合わせる、期待される
    /// 結果の型だけで決まる全代表元の共有列挙結果を返す。
    fn defined_by_type_scan_candidates(&mut self, et: crate::mmp_core::EntityType) -> Rc<Vec<ClassId>> {
        let cur_gen = self.egraph.type_generation.get(&et).copied().unwrap_or(0);
        if let Some((cached, cached_gen)) = self.defined_by_full_scan_cache.get(&et) {
            if *cached_gen == cur_gen { return cached.clone(); }
        }
        let result = Rc::new(self.egraph.iter_reps_of_type(et).collect::<Vec<_>>());
        self.defined_by_full_scan_cache.insert(et, (result.clone(), cur_gen));
        result
    }

    fn ensure_theorem_stats(&mut self) {
        if self.theorem_stats.len() != self.theorems.len() {
            self.theorem_stats.resize(self.theorems.len(), TheoremBanditStats::default());
        }
    }

    /// 🌟 required_hard_typesのドキュメント参照。theoremsが確定してから最初に
    /// 呼ばれた時点で1回だけ全定理分をまとめて計算し、以降は使い回す。
    fn ensure_theorem_required_types(&mut self) {
        if self.theorem_required_types.len() != self.theorems.len() {
            self.theorem_required_types = self.theorems.iter()
                .map(|t| required_hard_types(t))
                .collect();
        }
    }

    /// 🌟 定理の型シグネチャ事前フィルタ: この定理が前提の中で参照する
    /// 「軟らかくない(オンデマンド生成されない)」型のうち、e-graphに
    /// 実体が1つも無い型が1つでもあれば、この定理は全探索を試すだけ無駄
    /// なので false を返す(呼び出し側はタスクのスケジューリング自体を
    /// スキップする)。
    pub fn theorem_types_available(&mut self, idx: usize) -> bool {
        self.ensure_theorem_required_types();
        match self.theorem_required_types.get(idx) {
            Some(types) => types.iter().all(|&t| self.egraph.has_entity_of_type(t)),
            None => true,
        }
    }

    /// 🌟 UCB1スコアを MatchTask.priority (i32) に足し込める小さな整数
    /// ボーナスに変換する。schedule_matcher_task由来のシード済みタスク
    /// (priority=10)よりは必ず低くなるレンジ(-5..=5)にクランプすることで、
    /// 「発見済みの事実に基づく具体的な一手」を常に最優先しつつ、
    /// 同格のシードなし全探索タスクどうしの中では経験的に見込みの高い
    /// 定理から先に試せるようにする。
    pub fn theorem_priority_bonus(&mut self, idx: usize) -> i32 {
        self.ensure_theorem_stats();
        if idx >= self.theorem_stats.len() { return 0; }
        let total: u64 = self.theorem_stats.iter().map(|s| s.attempts).sum();
        let score = self.theorem_stats[idx].ucb1_score(total, 1.0);
        if !score.is_finite() { return 5; } // 未試行の定理は最優先で一度試す
        ((score * 5.0).round() as i32).clamp(-5, 5)
    }

    /// 🌟 schedule_full_sweep由来のシードなしタスクを実際にdfs_matchまで
    /// 走らせた結果をバンディット統計に反映する。シード済みタスク
    /// (is_seeded=true)はここでは記録しない(MatchTask::is_seededの
    /// ドキュメント参照)。
    ///
    /// コスト考慮型の報酬: dfs_calls_used(このタスク1回のdfs_match呼び出しが
    /// 実際に消費したdfs_call数)をdfs_capに対する比率(cost_ratio)として、
    /// - 成功時: 1.0 - 0.5*cost_ratio を 0.1 を下限にクランプ
    ///   (一瞬で成功すれば報酬1.0に近く、cap一杯まで探索してようやく
    ///   成功しても最低0.1は残る = 成功は常に失敗より高評価だが、
    ///   探索コストが高いほど徐々に割り引かれる)
    /// - 失敗時: -0.5*cost_ratio (0以下)
    ///   (何も見つからずに終わった場合、安く諦めたなら0に近く、
    ///   dfs_cap一杯まで無駄に探索したなら-0.5まで下がる)
    /// この結果、「dfs_cap一杯まで探索した末にようやく1回成功する」定理
    /// (以前の二値報酬では"成功"として高く評価されていた)を、実際の
    /// 探索コストに見合った低めのスコアに補正できる。
    pub fn record_theorem_attempt(&mut self, idx: usize, succeeded: bool, dfs_calls_used: u64) {
        self.ensure_theorem_stats();
        let cost_ratio = (dfs_calls_used as f64 / self.dfs_cap.max(1) as f64).min(1.0);
        let reward = if succeeded {
            (1.0 - 0.5 * cost_ratio).max(0.1)
        } else {
            -0.5 * cost_ratio
        };
        if let Some(stats) = self.theorem_stats.get_mut(idx) {
            stats.attempts += 1;
            stats.total_reward += reward;
            stats.total_dfs_calls += dfs_calls_used;
            if dfs_calls_used >= self.dfs_cap {
                stats.cap_hits += 1;
            }
        }
    }
    fn calc_bind_heat(&self, bind: &Bind) -> f64 {
        let mut heat = 0.0;
        for &id in bind.values() {
            let rep = self.egraph.get_rep(id);
            heat += self.egraph.entities[rep.0].heat_with_degree();
        }
        heat
    }

    fn estimate_cost(&self, pat: &Pattern, bind: &Bind, theorem: &TheoremDef) -> f64 {
        match pat {
            Pattern::Fact(def) => {
                let unbound_count = def.args.iter().filter(|v| !bind.contains_key(*v)).count();
                if unbound_count == 0 { return 0.0; }

                let base_cost = if def.fact_type == "Identical" {
                    if unbound_count == 1 { 1.0 } else { 15.0 }
                } else if def.fact_type == "Connected" {
                    if unbound_count == 1 { 5.0 } else {
                        // 🐛 FIX: 以前は両方未束縛のConnectedを「(None,None)は何もしない」
                        // 前提でコスト10000(=事実上最後回し)にしていたが、(None,None)を
                        // きちんと実装した今は「親の型で絞り込んだ局所探索」でしかない。
                        // 固定値のままだと、円のように個体数が少ない型を親に持つ場合
                        // (安く見積もるべき)と、点のように個体数が多い型を親に持つ場合
                        // (高く見積もるべき)を区別できない。親変数の宣言型を引いて、
                        // 実際にその型が今グラフに何個あるかで見積もる。
                        let parent_var = &def.args[1];
                        match theorem.entities.get(parent_var) {
                            Some(&expected_type) => {
                                let count = self.egraph.entities.iter()
                                    .filter(|e| e.entity_type == expected_type)
                                    .count();
                                (count as f64) * 5.0 + 10.0
                            }
                            None => 10000.0, // 型情報すら無ければ従来通り最後回し
                        }
                    }
                } else if def.fact_type == "DefinedBy" {
                    if unbound_count == def.args.len() { 
                        let penalty = match def.target_type.as_deref().unwrap_or("") {
                            "Midpoint" | "LengthSq" | "Intersection" => 0.0,
                            "LineThroughPoints" | "PerpendicularLine" | "TangentLine" => 10.0,
                            "DirectionOf" | "AnglePair" | "Circumcircle" => 20.0,
                            _ => 5.0,
                        };
                        100.0 + (unbound_count as f64) + penalty 
                    } else {
                        10.0 + (unbound_count as f64) * 20.0
                    }
                } else {
                    100.0
                };

                // バインド済み変数の熱と次数が高いほどコストを下げる(優先探索)
                let mut heat = 0.0;
                for v in &def.args {
                    if let Some(&id) = bind.get(v) {
                        let rep = self.egraph.get_rep(id);
                        heat += self.egraph.entities[rep.0].heat_with_degree();
                    }
                }
                
                (base_cost - heat).max(0.1) // 完全に0にはせず僅かなコストを残す[cite: 5]
            }
            Pattern::Order(vars) | Pattern::Distinct(vars) | Pattern::OrderNonStrict(vars) => {
                if vars.iter().any(|v| !bind.contains_key(v)) { std::f64::INFINITY } else { 0.0 }
            }
            Pattern::Not(inner_pat) => self.estimate_cost(inner_pat, bind, theorem),
        }
    }
    
    pub fn is_already_proven(&self, conclusions: &[FactTemplate], bind: &Bind, flips: &FlipStates) -> bool {
        for conc in conclusions {
            match conc.fact_type.as_str() {
                "Identical" => {
                    if let (Some(&id1), Some(&id2)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1])) {
                        let rep1 = self.egraph.get_rep(id1);
                        let rep2 = self.egraph.get_rep(id2);
                        // 🌟 FIX: 型に関わらず、代表元が同じなら証明済みとみなす
                        if rep1 != rep2 { return false; }

                        // 🌟 EntityType::Angle撤廃(mmp_core/mod.rs::EntityTypeの
                        // ドキュメント参照)により、以前ここにあった
                        // 「entity_type==Angleの場合だけフリップの向きを確認する」
                        // という型による絞り込みは撤廃した。FlipStates自体が
                        // match_defined_by(target_type=="AnglePair"の場合だけ)で
                        // しか populate されない、既に型非依存な文字列ベースの
                        // 仕組みだったため、非角度のIdentical比較では
                        // flips.get(...)が常にNone(→false)になり、
                        // f1==f2(false==false)は自動的に成り立つ――つまり
                        // 型チェックは元々冗長で、外しても角度以外の判定は
                        // 一切変わらない。
                        let f1 = flips.get(&conc.args[0]).copied().unwrap_or(false);
                        let f2 = flips.get(&conc.args[1]).copied().unwrap_or(false);
                        if f1 != f2 { return false; }
                    } else { return false; }
                },
                "Connected" => {
                    if let (Some(&child), Some(&parent)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1])) {
                        if !self.egraph.is_connected(child, parent) { return false; }
                    } else { return false; }
                },
                _ => return false,
            }
        }
        true
    }

    /// 🌟 dep_mask引数のドキュメント参照(entity_type_bit/ALL_TYPES_MASK、
    /// mod冒頭)。「呼び出し元が本来欲しいのは戻り値」だが全ての中間関数
    /// (match_fact_pattern以下)のシグネチャを戻り値ありに変えるのは
    /// 侵襲が大きいため、代わりに末尾の&mut u8引数として同じ情報を運ぶ。
    /// 各呼び出しは以下の規約を守る:
    ///   1. 受け取ったdep_maskは「呼び出し元(親)が集計したい先」を指す。
    ///   2. 自分自身の探索(このstate_sig1つ分)にはローカルなmy_maskを
    ///      新たに作り、子への再帰呼び出しにはdep_maskではなく&mut my_mask
    ///      を渡す(自分の探索に閉じた集計にするため)。
    ///   3. 末尾で、matched_anyがfalseならfailed_pathsにmy_maskを添えて
    ///      記録し、成功/失敗を問わずmy_maskを親のdep_maskへORして返す。
    pub fn dfs_match(
        &mut self,
        theorem: &TheoremDef,
        remaining: Rc<Vec<Pattern>>,
        bind: Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashMap<u64, (u8, [u64; 4])>,
        dep_mask: &mut u8,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
        self.dfs_calls += 1;
        if self.dfs_calls > self.dfs_cap { return; }

        // 🌟 失敗パスのキャッシュチェック
        let state_sig = {
            let mut hasher = rustc_hash::FxHasher::default();
            remaining.len().hash(&mut hasher);

            let mut pairs: Vec<_> = bind.iter().collect();
            pairs.sort_unstable_by_key(|k| k.0);
            for (k, v) in pairs {
                k.hash(&mut hasher);
                self.egraph.get_rep(*v).0.hash(&mut hasher);
            }

            // 🌟 FIX: フリップ状態もハッシュに含めないと、向き違いの正当な探索が枝刈りされてしまう
            let mut flips: Vec<_> = flip_states.iter().collect();
            flips.sort_unstable_by_key(|k| k.0);
            for (k, v) in flips {
                k.hash(&mut hasher);
                v.hash(&mut hasher);
            }

            hasher.finish()
        };

        // 🌟 global_failed_pathsのドキュメント参照(ProverEngine)。エントリは
        // (依存マスク, 挿入時点でのALL_ENTITY_TYPES順type_generation
        // スナップショット)。タスクをまたいで永続化されるようになった今、
        // 「取り出した時点でまだ有効か」をエントリごとに都度検証する必要が
        // ある――マスクが立っている型についてだけ、挿入時のスナップショット
        // と現在値を比較する(マスク0のエントリは何と比較するまでもなく
        // 常に有効)。無効なら通常のキャッシュミスとして扱い、探索し直す
        // (再度失敗すれば新しいスナップショット付きで上書きされる)。
        if let Some(&(cached_mask, cached_gens)) = failed_paths.get(&state_sig) {
            let still_valid = (0..4).all(|i| {
                (cached_mask & (1 << i)) == 0
                    || self.egraph.type_generation.get(&ALL_ENTITY_TYPES[i]).copied().unwrap_or(0) == cached_gens[i]
            });
            if still_valid {
                *dep_mask |= cached_mask;
                return;
            }
        }

        if remaining.is_empty() {
            for (v_name, id) in &bind {
                if let Some(expected_type) = theorem.entities.get(v_name) {
                    let actual_type = self.egraph.entities[self.egraph.get_rep(*id).0].entity_type;
                    if *expected_type != actual_type { return; }
                }
            }
            on_match(&bind, &flip_states);
            return;
        }

        let mut best_idx = 0;
        let mut best_cost = std::f64::INFINITY;
        for (i, pat) in remaining.iter().enumerate() {
            let cost = self.estimate_cost(pat, &bind, theorem);
            if cost < best_cost { best_cost = cost; best_idx = i; }
        }

        // 🌟 以前は `remaining: Vec<Pattern>` を分岐のたびに丸ごと clone() していたため、
        // 候補が複数ある(順列展開やマッチ候補が多い)ケースで同じパターン列が何度も
        // ディープコピーされていた。ここで一度だけ「評価対象を除いた残り」を作り、
        // Rc に包んで以降は全てポインタコピーで共有する。
        let pat_to_eval = remaining[best_idx].clone();
        let remaining: Rc<Vec<Pattern>> = if remaining.len() == 1 {
            Rc::new(Vec::new())
        } else {
            let mut owned = Vec::with_capacity(remaining.len() - 1);
            for (i, p) in remaining.iter().enumerate() {
                if i != best_idx { owned.push(p.clone()); }
            }
            Rc::new(owned)
        };
        let mut matched_any = false;
        // 🌟 このstate_sig(このdfs_match呼び出し1回分)の探索が実際に
        // 依存した型の集計。子への再帰にはdep_maskではなくこちらを渡す。
        let mut my_mask: u8 = 0;

        // クロージャをラップして、1度でもマッチしたかを記録する
        let mut wrapped_on_match = |b: &Bind, f: &FlipStates| {
            matched_any = true;
            on_match(b, f);
        };

        match pat_to_eval {
            Pattern::Order(vars) => {
                let mut is_ordered = true;
                for i in 0..vars.len().saturating_sub(1) {
                    if let (Some(id1), Some(id2)) = (bind.get(&vars[i]), bind.get(&vars[i+1])) {
                        if self.egraph.get_rep(*id1).0 >= self.egraph.get_rep(*id2).0 { is_ordered = false; break; }
                    }
                }
                if is_ordered { self.dfs_match(theorem, remaining.clone(), bind, flip_states, failed_paths, &mut my_mask, &mut wrapped_on_match); }
            }
            // 🌟 Pattern::OrderNonStrictのドキュメント参照。Orderとの違いは
            // "<"ではなく"<="(等しい場合は許可)で判定する点のみ。
            Pattern::OrderNonStrict(vars) => {
                let mut is_ordered = true;
                for i in 0..vars.len().saturating_sub(1) {
                    if let (Some(id1), Some(id2)) = (bind.get(&vars[i]), bind.get(&vars[i+1])) {
                        if self.egraph.get_rep(*id1).0 > self.egraph.get_rep(*id2).0 { is_ordered = false; break; }
                    }
                }
                if is_ordered { self.dfs_match(theorem, remaining.clone(), bind, flip_states, failed_paths, &mut my_mask, &mut wrapped_on_match); }
            }
            Pattern::Distinct(vars) => {
                let mut unique_ids = rustc_hash::FxHashSet::default();
                let mut is_distinct = true;
                for v in &vars {
                    if let Some(&id) = bind.get(v) {
                        let rep_id = self.egraph.get_rep(id);
                        if !unique_ids.insert(rep_id.0) { is_distinct = false; break; }
                    }
                }
                if is_distinct { self.dfs_match(theorem, remaining.clone(), bind, flip_states, failed_paths, &mut my_mask, &mut wrapped_on_match); }
            }
            Pattern::Fact(def) => {
                self.match_fact_pattern(theorem, &def, remaining.clone(), &bind, flip_states, failed_paths, &mut my_mask, &mut wrapped_on_match);
            }
            Pattern::Not(inner_pat) => {
                let mut inner_matched = false;
                self.dfs_match(theorem, Rc::new(vec![*inner_pat.clone()]), bind.clone(), flip_states.clone(), failed_paths, &mut my_mask, &mut |_, _| {
                    inner_matched = true;
                });
                if !inner_matched {
                    self.dfs_match(theorem, remaining.clone(), bind, flip_states, failed_paths, &mut my_mask, &mut wrapped_on_match);
                }
            }
        }

        // 🌟 どこにも進めなかった場合、この状態を失敗として記録する
        // (実際に依存した型マスクmy_maskと、その時点でのtype_generation
        // スナップショットを添えて――Distinct/Order/両方束縛済みのチェック
        // だけで確定した失敗はmy_mask=0のままなので、型がいくつ変化しても
        // 永続的に有効なエントリとして残る。global_failed_pathsに昇格した
        // 今、このスナップショットが「取り出し側での有効性の再検証」の
        // 基準になる)。
        if !matched_any {
            failed_paths.insert(state_sig, (my_mask, snapshot_type_generations(&self.egraph)));
        }
        // 🌟 成功・失敗を問わず、この部分木が触れた型を呼び出し元(親)へ
        // 伝播する。親が(この呼び出しとは別の枝の失敗を含めて)最終的に
        // 失敗してfailed_pathsに記録する際、この情報も正しく合算される。
        *dep_mask |= my_mask;
    }
    /// 🌟 match_fact_pattern はfact_typeごとの処理を振り分けるだけの薄いディスパッチャ。
    /// 以前はこの関数自体が360行あり(Identical/Connected/DefinedBy/汎用の4種の
    /// マッチングロジックが全て1つのmatchの中に同居していた)、可読性の観点から
    /// fact_typeごとの専用メソッドに分割した。挙動は一切変えていない。
    pub fn match_fact_pattern(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef,
        remaining: Rc<Vec<Pattern>>,
        bind: &Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashMap<u64, (u8, [u64; 4])>,
        dep_mask: &mut u8,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
        match def.fact_type.as_str() {
            "Identical" => self.match_identical_fact(theorem, def, remaining, bind, flip_states, failed_paths, dep_mask, on_match),
            "Connected" => self.match_connected_fact(theorem, def, remaining, bind, flip_states, failed_paths, dep_mask, on_match),
            "DefinedBy" => self.match_defined_by_fact(theorem, def, remaining, bind, flip_states, failed_paths, dep_mask, on_match),
            _ => self.match_generic_fact(theorem, def, remaining, bind, flip_states, failed_paths, dep_mask, on_match),
        }
    }

    /// 🌟 "Identical" パターン: v1, v2 の束縛状況(両方束縛済み/片方だけ/どちらも未束縛)
    /// に応じて分岐する。
    fn match_identical_fact(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef,
        remaining: Rc<Vec<Pattern>>,
        bind: &Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashMap<u64, (u8, [u64; 4])>,
        dep_mask: &mut u8,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
        let v1 = &def.args[0];
        let v2 = &def.args[1];
        let expected_type = theorem.entities.get(v1).copied(); // 🌟 型情報取得

        match (bind.get(v1).copied(), bind.get(v2).copied()) {
            // 🌟 dep_maskのドキュメント参照(dfs_match)。両方束縛済み/片方だけ
            // 束縛済みの分岐は、既に束縛済みの代表元を直接見るだけで
            // どの型のプールも列挙しないため、依存マスクを一切追加しない
            // (=dep_maskをそのまま子に渡す、new my_maskを作らない)。
            (Some(id1), Some(id2)) => {
                if self.egraph.get_rep(id1) == self.egraph.get_rep(id2) {
                    self.dfs_match(theorem, remaining.clone(), bind.clone(), flip_states.clone(), failed_paths, dep_mask, on_match);
                }
            }
            (Some(id), None) | (None, Some(id)) => {
                let unbound_var = if bind.get(v1).is_none() { v1 } else { v2 };
                let mut next_bind = bind.clone();
                next_bind.insert(unbound_var.clone(), self.egraph.get_rep(id));
                self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
            }
            (None, None) => {
                // 🌟 dep_maskのドキュメント参照。ここから先は「型のプールを
                // 列挙する」分岐なので、実際に問い合わせた型をdep_maskへ
                // 記録する(全ての候補に対する再帰呼び出しで共有する)。
                // 🐛 移植バグ修正: 以前はここで「同じ代表元(=既にマージ済み)を持つ
                // 異なる ClassId のペア」を全列挙しており、1つの等価クラスに
                // N個のエンティティが吸収されていると N*(N-1) 通りに爆発していた
                // (「有向角の加法性」のように、この分岐から探索を始める定理で
                // simsonのタイムアウトの主因になっていた)。
                //
                // Python版の対応する _match_identical (両方未束縛) は、対象の型を
                // 持つ「異なる代表元」それぞれについて v1=v2=その代表元、という
                // 自己束縛を O(代表元の数) で列挙するだけだった。この定理は本来
                // schedule_matcher_task によるシード付き起動(実際に発見された
                // Identical事実からD1..D6を具体的に束縛する経路)で使われる前提であり、
                // シード無しの全探索(schedule_full_sweep)から来た場合はこの程度の
                // 軽い足がかりで十分。Python版と同じ挙動に合わせて計算量を落とす。
                // 🌟 RETE的な共有列挙キャッシュ(ユーザー提案「案4」、
                // identical_self_bind_cacheのドキュメント参照): 期待される型が
                // 分かっている場合、この生の候補集合はbindの中身に依存せず
                // 型だけで決まるので、定理をまたいで共有する(型が不明な稀な
                // フォールバックでは従来通りのフルスキャン)。heatによる
                // 並べ替えは共有前の生の集合に対してではなく、キャッシュから
                // 取り出した後に(常に最新のheat_bonusで)行う。
                // 🌟 EntityType::Angle撤廃(mmp_core/mod.rs::EntityTypeの
                // ドキュメント参照)への対応: 角度追跡系定理のIdentical(Ang1,Ang2)
                // シード(theorems.rsで既にtarget_type=Some("Angle")が付いている、
                // 元々は記録目的だけの慣習だったマーカー)は、統合後の
                // EntityType::Scalarの自己束縛候補プールが長さ・積・複比まで
                // 無差別に含むようになった影響を受けやすい――「有向角の加法性」
                // のようにこの分岐から始まる定理で、無関係なScalarまで候補に
                // 混ざるとheatソート済みcapを無駄に消費し、証明が届かなくなる
                // (miquel_quadrilateralで実際に観測)。
                // 🌟 当初はidentical_self_bind_candidates(Scalar)の共有結果を
                // 取り出した後にis_angle_valueで絞り込むだけの実装だったが、
                // それだと絞り込む「前」の共有キャッシュ自体が
                // type_generation[Scalar]で無効化判定されたままなので、
                // 無関係な長さ・積・複比の新規生成のたびに(角度候補を
                // 一切含まない場合でも)このキャッシュが丸ごと無効化・
                // 再列挙され続け、期待したキャッシュ効果が得られなかった
                // (3回集計でベンチマーク合格率69/96→57/96に悪化する回帰と
                // して実測された)。identical_self_bind_angle_candidates/
                // identical_self_bind_plain_scalar_candidatesという、
                // angle_generation/plain_scalar_generationという互いに
                // 独立した専用カウンタで無効化判定する2つの専用キャッシュに
                // 分離し、角度側・非角度側どちらの生成イベントも「無関係な
                // もう一方」のキャッシュを無効化しないようにする。
                let wants_angle = def.target_type.as_deref() == Some("Angle");
                // 🌟 is_cross_ratio_of_lines_valueのドキュメント(mmp_core/query.rs)
                // 参照。同じ理由(自己束縛プールの無関係な値による汚染)で、
                // sub_type="CrossRatioOfLines"マーカーが付いているパターンは
                // さらにCrossRatioOfLines由来のものだけに絞る。
                let wants_cr_of_lines = def.sub_type.as_deref() == Some("CrossRatioOfLines");
                let mut reps: Vec<ClassId> = match expected_type {
                    Some(EntityType::Scalar) if wants_angle => (*self.identical_self_bind_angle_candidates()).clone(),
                    Some(EntityType::Scalar) if wants_cr_of_lines => {
                        (*self.identical_self_bind_plain_scalar_candidates()).iter()
                            .copied()
                            .filter(|&id| self.egraph.is_cross_ratio_of_lines_value(id))
                            .collect()
                    }
                    Some(EntityType::Scalar) => (*self.identical_self_bind_plain_scalar_candidates()).clone(),
                    Some(et) => {
                        (*self.identical_self_bind_candidates(et)).clone()
                    }
                    None => {
                        let mut reps = Vec::new();
                        for i in 0..self.egraph.entities.len() {
                            let id = ClassId(i);
                            if self.egraph.get_rep(id) != id { continue; } // 代表元のみ
                            if self.egraph.entities[i].is_active() {
                                reps.push(id);
                            }
                        }
                        reps
                    }
                };
                // 🐛 実測に基づくFIX: このシード無し(両変数未束縛)経路は、
                // apply_conclusionsが直後にheat_bonusを加算した「たった今マージ
                // されたばかりの代表元」(=この定理が本来欲しがっている候補で
                // ある可能性が高い)を、生成順(ClassId順)のまま辿っていたため
                // 後回しにしてしまい、無関係な候補を大量に試してからようやく
                // 正解に辿り着く(あるいはdfs_cap/持ち時間の方が先に尽きる)、
                // という実際の性能問題を「共点二弦の相似」定理のテストで観測した。
                // heat(base_importance+heat_bonus)の降順に並べ替えるだけで、
                // 直近にマージされた=熱い代表元から先に試せるようになる
                // (match_defined_by_factの全件スキャンで既に使われているのと
                // 同じ「熱で優先順位を付ける」考え方をこちらにも適用しただけ)。
                reps.sort_by(|&a, &b| {
                    let ha = self.egraph.entities[a.0].heat();
                    let hb = self.egraph.entities[b.0].heat();
                    hb.partial_cmp(&ha).unwrap_or(std::cmp::Ordering::Equal)
                });
                // 🌟 この経路は本来「シードが来なかった時の保険」に過ぎず
                // (本命はschedule_matcher_task/DefinedByシード)、候補が
                // 大量にある問題(例: 複比が大量生成されるtest_cross_ratio)では
                // 無関係なエンティティまで大量に自己束縛して試すコストが
                // 無視できなくなり得る。上のheatソートで関係のある候補は
                // ほぼ確実に先頭付近に来るため、候補数を適当な上限で打ち切っても
                // 正解を逃すリスクは小さい――ワーストケースの青天井を防ぐ
                // 安全弁として導入する(全問題で悪影響が無いことを確認済み)。
                //
                // 🌟 ユーザー提案(人間の解き方=角度追跡→長さ比→構図の反復。
                // その中で「今まさにhotな」対象から芋づる式に辿る)への対応:
                // 「有向角の加法性」のように、同じ型に対する(None,None)自己束縛
                // パターンをこの定理が2つ以上持つ場合(Ang12≡Ang45とAng23≡Ang56)、
                // それぞれ独立に候補集合を列挙して掛け合わせる(cap×cap通り)ため、
                // 固定cap=40のままだと最悪1,600通りの組み合わせを生み、simsonの
                // dfs_call消費量トップの直接原因になっていた(実測で確認済み)。
                // 熱で降順ソート済みの列に対し「本当にhotな候補は少数のはず」という
                // 前提で、こういう「二重自己束縛」定理に限ってcapを大きく絞り、
                // 全角度を無差別スキャンする代わりに直近heat_bonusが乗った少数の
                // 候補だけから辿らせる。単独の自己束縛(cap×1)しか持たない定理は
                // 従来通り40のままなので、他の定理への影響は無い。
                let self_bind_pattern_count = theorem.patterns.iter().filter(|p| {
                    matches!(p, Pattern::Fact(d) if d.fact_type == "Identical"
                        && d.args.len() == 2
                        && theorem.entities.get(&d.args[0]).copied() == expected_type)
                }).count();
                // 🌟 診断(円周角の定理の逆)で判明した追加ケース: 自己束縛
                // パターン自体は1つでも、そのIdentical(v1,v2)のv1・v2それぞれに
                // 同じtarget_typeのDefinedByパターンが独立にぶら下がっている
                // 場合(has_paired_defined_by_fanoutのドキュメント参照)、
                // 自己束縛のcapがそのまま下流(DefinedByペアリング→Connected
                // チェーン全体)の分岐係数になる。こちらも同じcap=10で絞る。
                let squared_fanout = self_bind_pattern_count >= 2
                    || has_paired_defined_by_fanout(theorem, v1, v2);
                let max_candidates = if squared_fanout { self.fanout_heat_cap } else { self.heat_cap };
                reps.truncate(max_candidates);
                // 🌟 dep_maskのドキュメント参照。expected_typeが分かっていれば
                // その型のプールを列挙したことになる。Noneの(稀な)フォール
                // バックは全エンティティを舐めるので安全側に倒して全型を
                // 依存対象にする。
                *dep_mask |= match expected_type {
                    Some(et) => entity_type_bit(et),
                    None => ALL_TYPES_MASK,
                };
                for rep in reps {
                    let mut next_bind = bind.clone();
                    next_bind.insert(v1.clone(), rep);
                    next_bind.insert(v2.clone(), rep);
                    self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
                }
            }
        }
    }

    /// 🌟 match_connected_fact の局所スキャン分岐((Some,None)/(None,Some))
    /// 向けの熱量駆動cap。これらの分岐は「ある実体自身に繋がっている
    /// (少数のはずの)候補」を集めるので、通常は無条件で全件試して問題
    /// なかった。しかし診断計測(円周角の定理)で、多くの点が乗っている円
    /// のような「ハブ」実体では数十件になり得ると判明した――(None,None)
    /// 分岐(identical_self_bind_candidates/connected_pairs_for_types)に
    /// 既に入れているのと同じ熱降順cap(=40)を、候補が実際に多い場合に
    /// 限って適用する(少ない場合はソートのコストも省き従来通り全件試す)。
    fn heat_capped_connected_candidates(&self, candidates: rustc_hash::FxHashSet<ClassId>) -> Vec<ClassId> {
        let mut v: Vec<ClassId> = candidates.into_iter().collect();
        if v.len() > self.heat_cap {
            v.sort_by(|&a, &b| {
                let ha = self.egraph.entities[a.0].heat();
                let hb = self.egraph.entities[b.0].heat();
                hb.partial_cmp(&ha).unwrap_or(std::cmp::Ordering::Equal)
            });
            v.truncate(self.heat_cap);
        }
        v
    }

    /// 🌟 "Connected" パターン: child/parent の束縛状況の4通り(両方/片方×2/どちらも未束縛)
    /// で分岐する。
    ///
    /// 🐛 FIX(EntityType::Direction撤廃で新たに生まれたバグ): 「方向」が独立した
    /// 型で無くなり、L∞に繋がっただけのPointになったため、「この直線に乗っている
    /// 点を探す」という(Line,Point)型の"Connected"パターンが、以前は型で
    /// 自動的に除外されていたその直線自身の方向(=L∞上の点)まで有効な候補として
    /// 拾ってしまうようになった。逆に「この直線の方向を求める」という
    /// (Line,Direction)パターンは、その直線上の"普通の"点(A,Bなど)まで候補に
    /// 混ざってしまう。どちらも実際にcyclic_quad等で観測された(候補が2〜3倍に
    /// 水増しされ、DFS予算を無駄食いして証明が届かなくなる/大幅に遅くなる)。
    /// これまで一度も読まれていなかったFactPatternDef::target_type/sub_type
    /// (「円周角の定理」のtarget_type=Some("Line")/sub_type=Some("Point")のような
    /// 記述が既にコメント的に付いていた慣習)を、ここで初めて実際の判定に使う:
    /// target_type=="Direction"ならparent側、sub_type=="Direction"ならchild側の
    /// Point候補を「L∞上にある点だけ」に絞り、それ以外(既定)は逆に「L∞上に
    /// ない点だけ」に絞る(型撤廃前と同じ、有限点だけを候補にする挙動)。
    fn match_connected_fact(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef,
        remaining: Rc<Vec<Pattern>>,
        bind: &Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashMap<u64, (u8, [u64; 4])>,
        dep_mask: &mut u8,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
        use crate::mmp_core::EntityType;
        let child_var = &def.args[0];
        let parent_var = &def.args[1];
        let expected_c_type = theorem.entities.get(child_var).copied();
        let expected_p_type = theorem.entities.get(parent_var).copied();
        let wants_child_direction = def.sub_type.as_deref() == Some("Direction");
        let wants_parent_direction = def.target_type.as_deref() == Some("Direction");
        // 🌟 EntityType::Circle撤廃(mmp_core/mod.rs::EntityTypeのドキュメント
        // 参照)により、"Circle"マーカーもここに追加する: target_type/sub_type
        // =="Circle"ならこのPoint型変数(Conicの間違いではなく、こちらは
        // Connectedのchild/parentそれぞれの"宣言型"のことなので、ここでの
        // Circleは実際にはConic型変数に対して使う)が実際にI,Jを両方通る
        // (=本物の円である)ものだけを受理し、無い場合は逆にI,Jを通らない
        // (=一般の非円二次曲線)ものだけを受理する――Direction/Pointの
        // 場合と全く同じ「マーカー無し=旧来の狭い方の型」という既定にする。
        let wants_child_circle = def.sub_type.as_deref() == Some("Circle");
        let wants_parent_circle = def.target_type.as_deref() == Some("Circle");
        // 🌟 候補id(宣言型et)がこのパターン変数として受理できるかを判定する。
        // et が Point/Conic 以外なら型一致だけで従来通り。
        // et が Point なら、「L∞上にあるか」がwants_direction(このパターン
        // 変数が方向を欲しがっているか)と一致する場合だけ受理する。
        // et が Conic なら、「I,Jを両方通るか(=円か)」がwants_circleと
        // 一致する場合だけ受理する(旧EntityType::Circle/Conicの分離を
        // incidenceで再現する)。
        let accept_point = |egraph: &crate::mmp_core::EGraph, id: ClassId, et: EntityType, wants_direction: bool, wants_circle: bool| -> bool {
            if egraph.entities[id.0].entity_type != et { return false; }
            match et {
                EntityType::Point => egraph.is_connected(id, egraph.line_infinity) == wants_direction,
                EntityType::Conic => {
                    let is_circle = egraph.is_connected(id, egraph.circ_i) && egraph.is_connected(id, egraph.circ_j);
                    is_circle == wants_circle
                }
                _ => true,
            }
        };

        match (bind.get(child_var).copied(), bind.get(parent_var).copied()) {
            // 🐛 実装時に見落としかけたバグ: match_identical_factの(Some,Some)と
            // 違い、こちらはis_connected(=incidenceという、state_sigのハッシュ
            // (bindの値=代表元IDだけ)には含まれない"追加の状態")を見ている。
            // 同じ2つの代表元のまま、後からlink_logical_incidenceで新たに
            // 接続されると(それ自体はマージではないのでstate_sigは変わらない)、
            // この判定結果は変わり得る。link_logical_incidenceは接続する
            // 両実体の型を必ずnote_type_changedするので、その型を依存対象に
            // しておけば正しく無効化できる。
            (Some(c_id), Some(p_id)) => {
                let c_type = self.egraph.entities[self.egraph.get_rep(c_id).0].entity_type;
                let p_type = self.egraph.entities[self.egraph.get_rep(p_id).0].entity_type;
                *dep_mask |= entity_type_bit(c_type) | entity_type_bit(p_type);
                // 🌟 FIX
                if self.egraph.is_connected(c_id, p_id) {
                    self.dfs_match(theorem, remaining.clone(), bind.clone(), flip_states.clone(), failed_paths, dep_mask, on_match);
                }
            }
            (Some(c_id), None) => {
                // 🌟 dep_maskのドキュメント参照。このローカルスキャンはc_repに
                // 実際に繋がっている候補をexpected_p_typeで絞り込むので、
                // 新たにその型の実体がc_repへ接続されると結果が変わりうる
                // (link_logical_incidenceは接続する両実体の型を必ずnote_type_
                // changedするので、これで正しく捕捉できる)。型が不明なら
                // 安全側に倒して全型に依存するとみなす。
                // 🌟 最適化: 以前はここが「全エンティティを舐めてis_connectedで
                // 判定する」O(全エンティティ数)の総当たりになっていた
                // ((None, Some(p_id))側の分岐は既にp_rep自身のsubobjectsだけを
                // 見る局所探索に最適化済みで、この分岐だけ非対称に取り残されて
                // いた)。link_logical_incidenceは常に双方向にリンクを張るので
                // (is_connectedの実装もこれを前提に両側を見ている)、c_rep自身の
                // subobjects(局所的で少数)だけを見れば取りこぼしなく同じ結果が
                // 得られる。大きい問題(entities数が多い)ほど効果が大きい。
                let c_rep = self.egraph.get_rep(c_id);
                // 🌟 (None, Some(p_id))側の分岐と同じく、まず候補を(重複除去しつつ)
                // 集め切ってから、egraphへの不変借用を終わらせた後でdfs_matchを呼ぶ
                // (dfs_matchは&mut selfを要求するため)。
                let mut candidates = rustc_hash::FxHashSet::default();
                for comp in &self.egraph.entities[c_rep.0].components {
                    for &sub in &comp.subobjects {
                        let p_rep = self.egraph.get_rep(sub);
                        if p_rep == c_rep || !self.egraph.entities[p_rep.0].is_active() { continue; }
                        if let Some(et) = expected_p_type {
                            if !accept_point(&self.egraph, p_rep, et, wants_parent_direction, wants_parent_circle) { continue; }
                        }
                        candidates.insert(p_rep);
                    }
                }
                // 🌟 診断計測(円周角の定理)で判明: この「局所」スキャンは通常は
                // 少数(その実体自身に繋がっているものだけ)だが、多くの点が
                // 乗っている円のような「ハブ」実体では数十件になり得る。
                // (None,None)分岐に加えたのと同じ熱降順cap(=40)を、候補が
                // 実際に多い場合に限って適用する(heat_capped_connected_
                // candidatesのドキュメント参照)。
                *dep_mask |= match expected_p_type {
                    Some(et) => entity_type_bit(et),
                    None => ALL_TYPES_MASK,
                };
                for p_rep in self.heat_capped_connected_candidates(candidates) {
                    let mut next_bind = bind.clone();
                    next_bind.insert(parent_var.clone(), p_rep);
                    self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
                }
            }
            // 🌟 dep_maskのドキュメント参照。(Some,None)と対称。
            (None, Some(p_id)) => {
                let p_rep = self.egraph.get_rep(p_id);
                let mut child_candidates = rustc_hash::FxHashSet::default();
                for comp in &self.egraph.entities[p_rep.0].components {
                    for &sub in &comp.subobjects {
                        // 🌟 FIX: 必ず rep を通す
                        let s_rep = self.egraph.get_rep(sub);
                        if self.egraph.entities[s_rep.0].is_active() { child_candidates.insert(s_rep); }
                    }
                }
                child_candidates.retain(|&c_rep| {
                    expected_c_type.map_or(true, |et| accept_point(&self.egraph, c_rep, et, wants_child_direction, wants_child_circle))
                });
                *dep_mask |= match expected_c_type {
                    Some(et) => entity_type_bit(et),
                    None => ALL_TYPES_MASK,
                };
                for c_rep in self.heat_capped_connected_candidates(child_candidates) {
                    let mut next_bind = bind.clone();
                    next_bind.insert(child_var.clone(), c_rep);
                    self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
                }
            }
            // 🐛 FIX: 以前は子・親どちらも未束縛の場合に何もせず候補ゼロで
            // 諦めていた(Concyclicを専用Factから「N点が同じ円にConnected」
            // という形に置き換えたことで、この分岐が実際に必要になり発覚した)。
            // 親の型(例:Circle)で絞り込み、各親候補についてはその親自身が
            // 繋がっている子(局所的で少数)だけを見る形で列挙する。
            (None, None) => {
                // 🌟 RETE的な共有ジョインキャッシュ(ユーザー提案「案4」、
                // connected_join_cacheのドキュメント参照): この分岐は
                // bindの中身に依存せず(child_type, parent_type)という
                // 型の組み合わせだけで結果が決まるので、複数の定理・タスクが
                // 同じ型の組み合わせを問い合わせる場合に定理をまたいで
                // 共有できる。両方の型が分かっている(ほぼ全ての定理で
                // そうである)場合のみキャッシュを使い、型が不明な稀な
                // フォールバックでは従来通りのフルスキャンを行う。
                // 🌟 dep_maskのドキュメント参照。以下の全ての分岐(型が既知の
                // キャッシュ済みジョイン/型不明のフルスキャン)がここで
                // プールを列挙するので、まとめて記録する。
                *dep_mask |= match (expected_c_type, expected_p_type) {
                    (Some(ct), Some(pt)) => entity_type_bit(ct) | entity_type_bit(pt),
                    _ => ALL_TYPES_MASK,
                };
                if let (Some(ct), Some(pt)) = (expected_c_type, expected_p_type) {
                    let raw_pairs = self.connected_pairs_for_types(ct, pt);
                    // 🌟 connected_pairs_for_typesは(child_type, parent_type)の
                    // 組み合わせだけで結果を共有キャッシュするため、L∞上の点/
                    // I,Jを通る円かどうかを含めるか除外するかはここで結果を
                    // 受け取った後にふるいにかける(キャッシュ自体は複数の
                    // 定理・向きで安全に共有され続ける)。
                    let needs_filter = ct == EntityType::Point || pt == EntityType::Point
                        || ct == EntityType::Conic || pt == EntityType::Conic;
                    let pairs: Rc<Vec<(ClassId, ClassId)>> = if needs_filter {
                        Rc::new(raw_pairs.iter().copied().filter(|&(c, p)| {
                            (ct != EntityType::Point || self.egraph.is_connected(c, self.egraph.line_infinity) == wants_child_direction)
                                && (pt != EntityType::Point || self.egraph.is_connected(p, self.egraph.line_infinity) == wants_parent_direction)
                                && (ct != EntityType::Conic || (self.egraph.is_connected(c, self.egraph.circ_i) && self.egraph.is_connected(c, self.egraph.circ_j)) == wants_child_circle)
                                && (pt != EntityType::Conic || (self.egraph.is_connected(p, self.egraph.circ_i) && self.egraph.is_connected(p, self.egraph.circ_j)) == wants_parent_circle)
                        }).collect())
                    } else {
                        raw_pairs
                    };
                    // 🌟 ユーザー提案(「複比の透視射影不変性」を熱量駆動の考え方で
                    // 高速化したい)への対応: この分岐(Connected両方未束縛)は
                    // match_identical_fact/match_defined_by_factの類似分岐と違い、
                    // これまで熱による並べ替えもcapも一切無く、connected_pairs_
                    // for_typesが返す全ペアを無差別に試していた。「複比の透視射影
                    // 不変性(点→線束)」はO,A,B,C,D等9自由変数を持つが天然のシードが
                    // 無く、先頭のConnected(A,L)(点,直線どちらも未束縛)がまさに
                    // この分岐から始まるため、点や直線が多い問題ではこの1パターン
                    // だけで全(点,直線)接続ペアを総当たりすることになっていた。
                    // identical_self_bind_candidates(cap=40、熱降順)と同じ発想を
                    // ここにも適用する: 候補が多い場合のみ熱(base_importance+
                    // heat_bonus、両端の合計)で降順ソートしてから絞り、少数の
                    // 場合はこれまで通り全件試す(ソートのコストも省く)。
                    if pairs.len() <= self.heat_cap {
                        for &(c_rep, p_rep) in pairs.iter() {
                            let mut next_bind = bind.clone();
                            next_bind.insert(child_var.clone(), c_rep);
                            next_bind.insert(parent_var.clone(), p_rep);
                            self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
                        }
                    } else {
                        let mut ordered: Vec<(ClassId, ClassId)> = (*pairs).clone();
                        let heat_of = |id: ClassId| -> f64 { self.egraph.entities[id.0].heat() };
                        ordered.sort_by(|&(c1, p1), &(c2, p2)| {
                            let h1 = heat_of(c1) + heat_of(p1);
                            let h2 = heat_of(c2) + heat_of(p2);
                            h2.partial_cmp(&h1).unwrap_or(std::cmp::Ordering::Equal)
                        });
                        ordered.truncate(self.heat_cap);
                        for (c_rep, p_rep) in ordered {
                            let mut next_bind = bind.clone();
                            next_bind.insert(child_var.clone(), c_rep);
                            next_bind.insert(parent_var.clone(), p_rep);
                            self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
                        }
                    }
                } else {
                    let mut parent_candidates: Vec<ClassId> = Vec::new();
                    if let Some(et) = expected_p_type {
                        for p_rep in self.egraph.iter_reps_of_type(et) {
                            if self.egraph.entities[p_rep.0].is_active()
                                && accept_point(&self.egraph, p_rep, et, wants_parent_direction, wants_parent_circle) {
                                parent_candidates.push(p_rep);
                            }
                        }
                    } else {
                        for i in 0..self.egraph.entities.len() {
                            let p_id = ClassId(i);
                            let p_rep = self.egraph.get_rep(p_id);
                            if p_rep != p_id || !self.egraph.entities[i].is_active() { continue; }
                            parent_candidates.push(p_rep);
                        }
                    }

                    for p_rep in parent_candidates {
                        let child_candidates: Vec<ClassId> = match self.egraph.entities[p_rep.0].components.first() {
                            Some(comp) => comp.subobjects.iter()
                                .map(|&id| self.egraph.get_rep(id))
                                .filter(|&id| {
                                    if !self.egraph.entities[id.0].is_active() { return false; }
                                    match expected_c_type {
                                        Some(et) => accept_point(&self.egraph, id, et, wants_child_direction, wants_child_circle),
                                        None => true,
                                    }
                                })
                                .collect(),
                            None => vec![],
                        };
                        for c_rep in child_candidates {
                            let mut next_bind = bind.clone();
                            next_bind.insert(child_var.clone(), c_rep);
                            next_bind.insert(parent_var.clone(), p_rep);
                            self.dfs_match(theorem, remaining.clone(), next_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
                        }
                    }
                }
            }
        }
    }

    /// 🌟 "DefinedBy" パターン: result_var(定義された図形そのもの)の束縛状況から
    /// 候補ノードを絞り込み(defined_by_valid_nodes)、それぞれの候補が実際に
    /// target_type型の定義を持っているかを親変数との整合性込みで展開する
    /// (defined_by_collect_matches)。どちらも元は1つの巨大なmatchアームだった。
    fn match_defined_by_fact(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef,
        remaining: Rc<Vec<Pattern>>,
        bind: &Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashMap<u64, (u8, [u64; 4])>,
        dep_mask: &mut u8,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
        let target_type = def.target_type.as_deref().unwrap_or("");
        let result_var = &def.args[def.args.len() - 1];
        let parent_vars = &def.args[0..def.args.len() - 1];
        let expected_r_type = theorem.entities.get(result_var).copied();

        let valid_nodes = self.defined_by_valid_nodes(target_type, result_var, parent_vars, expected_r_type, bind, dep_mask);
        let mut matches = self.defined_by_collect_matches(def, target_type, parent_vars, result_var, &valid_nodes, bind, &flip_states);

        if matches.is_empty() && target_type == "LineThroughPoints" && parent_vars.len() == 2 {
            if let (Some(&p1), Some(&p2)) = (bind.get(&parent_vars[0]), bind.get(&parent_vars[1])) {
                let r1 = self.egraph.get_rep(p1);
                let r2 = self.egraph.get_rep(p2);
                if r1 != r2 {
                    *self.construction_demands.entry((r1, r2)).or_insert(0.0) += 1.0;
                }
            }
        }
        // 🌟 NEW: 「2直線が既に存在するのに、その交点(Intersection)がまだ
        // 図形として存在しない」場合の需要記録。LineThroughPointsの需要
        // (「2点はあるのに、それを結ぶ直線がない」)と対称な仕組みで、
        // 「垂線の足」「補助円との交点」のような、問題文に最初から
        // 登録されていない補助点をDFS/需要駆動だけで発見できるようにする
        // (ユーザー要望: orthocenter/orthocenter_altでE,Fのような補助点を
        // 手で問題文に書かなくても発見できるようにしたい)。
        // resolve_point_demands(main.rsのリカバリーフェーズ)が実際に
        // Definition::Intersectionとして作図する。ここではLineThroughPoints
        // と同様、「需要はあるが今は作らない」――大量の無関係な直線ペアの
        // 交点まで無差別に作ってしまう爆発を避けるため、実際に定理が
        // 欲しがった(=パターンマッチで必要とされた)組み合わせだけを
        // 需要として記録し、実際の作図は頻度上位の少数に限定する。
        if matches.is_empty() && target_type == "Intersection" && parent_vars.len() == 2 {
            if let (Some(&l1), Some(&l2)) = (bind.get(&parent_vars[0]), bind.get(&parent_vars[1])) {
                let r1 = self.egraph.get_rep(l1);
                let r2 = self.egraph.get_rep(l2);
                if r1 != r2
                    && self.egraph.entities[r1.0].entity_type == EntityType::Line
                    && self.egraph.entities[r2.0].entity_type == EntityType::Line
                {
                    let key = if r1.0 < r2.0 { (r1, r2) } else { (r2, r1) };
                    *self.point_construction_demands.entry(key).or_insert(0.0) += 1.0;
                }
            }
        }

        // 🌟 ユーザー要望: 「複比の透視射影不変性のように関連するオブジェクトが
        // 非常に多い定理を、次数(MMP/動点法)をヒューリスティックに使って
        // 最適な順序でマッチングしたい」。
        //
        // 背景: DefinedByパターンの親変数が全て未束縛のフルスキャン
        // (defined_by_valid_nodes)では、既存の全エンティティ(例: 全ての直線)を
        // 候補として試すため、9自由変数の透視射影不変性のような定理では
        // 候補数がそのままdfs_matchの分岐数になる。dfs_capは全体で共有される
        // 有限予算なので、「正しい(=証明に必要な)候補」がこの分岐の中で早く
        // 試されるかどうかが、他の定理へ回る予算を食い潰すかどうかを左右する。
        // 次数は「その候補がどれだけ単純な構成か」の目安になり(実測: 中点や
        // 素直な2点直線は低次数、無関係な直線同士を繰り返し交差させた構成は
        // 高次数)、多くの名前付き定理は問題の基本的な図形(低次数)に対して
        // 使われることが多いため、次数の低い候補から先に試すことで「早く
        // 見つかるか、安く諦めるか」のどちらかになりやすい。
        //
        // 候補が少ない(=そもそも分岐が爆発しない)通常のケースでは次数測定
        // 自体のコストが無駄になるため、候補数がある程度多い場合のみ計算する
        // (DEGREE_HEURISTIC_THRESHOLD件以下ならこれまで通り熱だけで並べる)。
        // 次数はGeoEntity::degree_cacheでエンティティ単位にメモ化されるため、
        // 同じ問題内で繰り返しこの分岐に来ても実測コストは初回だけで済む。
        //
        // 🐛 実測に基づくFIX: 当初はTHRESHOLD=4, MAX_D=2で試したところ、
        // (a) simsonのような「候補が5〜10件程度」の中規模スキャンにまで
        // 次数測定が発動してしまい、既存12問題+orthocenter/orthocenter_altの
        // 合計実行時間が全体的に悪化した(simson: 3.9s→7.9〜8.1s、複数回
        // 再現)。(b) MAX_D=2(サンプル数k=2*2+2=6)は次数0/1/2を区別する
        // ぎりぎりの点数しかなく、random_mover_line(真の乱数)が引く方向に
        // よってランク判定が数値的にぶれやすく、同じ問題を実行するたびに
        // (プロセスごとに乱数シードが変わるため)測定される次数が変わり得て、
        // マッチ順序ひいては探索時間そのものが再現しない(orthocenterで
        // 実行毎に6秒/14秒/19秒とばらつくのを確認)という、まさにこのセッション
        // 冒頭でim::HashMapのRandomStateを潰して排除したのと同種の
        // 非決定性を、次数測定の乱数サンプリング経由で再び持ち込んでしまって
        // いた。THRESHOLD=10(=既存12問題+orthocenter/orthocenter_altでは
        // ほぼ発動しない)・MAX_D=4(=resolve_point_demandsで既に実績のある値、
        // k=10点でランク判定に十分な余裕がある)に調整することで、既存の
        // 全問題(cargo test 23/23 + 12問題+orthocenter/orthocenter_alt+
        // test_cross_ratioの計16問題)の実行時間・成否を完全に元通りに保ちつつ、
        // 複比の透視射影不変性(9自由変数、cross_ratio系のみで有効)を
        // 全問題のデフォルト定理集合へ強制的に加える実験では、この次数
        // ヒューリスティック無しだと壊れていたnine_point/orthic_incenter/
        // miquel_quadrilateralが(遅いながらも)全て正しく証明に到達できる
        // ことを確認した――「壊れる」を「遅いが正しい」まで改善できたが、
        // デフォルト採用に足るほどの速さにはまだ届いていない(今後の課題)。
        const DEGREE_HEURISTIC_THRESHOLD: usize = 10;
        const DEGREE_MAX_D_FOR_ORDERING: usize = 4;
        const DEGREE_WEIGHT: f64 = 3.0;
        let use_degree_heuristic = matches.len() > DEGREE_HEURISTIC_THRESHOLD;
        let degree_score = |b: &Bind| -> f64 {
            if !use_degree_heuristic { return 0.0; }
            b.get(result_var)
                .and_then(|&id| self.egraph.cached_degree(id, DEGREE_MAX_D_FOR_ORDERING))
                .unwrap_or(0) as f64
        };
        matches.sort_by(|(b1, _), (b2, _)| {
            let heat1 = self.calc_bind_heat(b1) - DEGREE_WEIGHT * degree_score(b1);
            let heat2 = self.calc_bind_heat(b2) - DEGREE_WEIGHT * degree_score(b2);
            // 熱(次数で調整済み)が高い(降順)ものを優先し、同値の場合はIDで決定論的にソート[cite: 5]
            heat2.partial_cmp(&heat1).unwrap_or(Ordering::Equal)
                .then_with(|| {
                    let mut k1: Vec<_> = b1.iter().collect(); k1.sort_by_key(|k| k.0);
                    let mut k2: Vec<_> = b2.iter().collect(); k2.sort_by_key(|k| k.0);
                    format!("{:?}", k1).cmp(&format!("{:?}", k2))
                })
        });
        matches.dedup_by_key(|(b, _)| {
            let mut keys: Vec<_> = b.iter().collect();
            keys.sort_by_key(|k| k.0);
            format!("{:?}", keys)
        });
        for (new_bind, new_flip) in matches {
            self.dfs_match(theorem, remaining.clone(), new_bind, new_flip, failed_paths, dep_mask, on_match);
        }
    }

    /// 🌟 "DefinedBy" の候補ノード列挙: result_var が既に束縛されていればそれ1つ、
    /// 親変数が全て束縛されていれば対応する定義をmemoから探す(無ければ
    /// AnglePair/DirectionOf/LengthSqに限り新規生成する)、どちらでもなければ
    /// 型が合う全エンティティをフルスキャンする。
    fn defined_by_valid_nodes(
        &mut self,
        target_type: &str,
        result_var: &String,
        parent_vars: &[String],
        expected_r_type: Option<EntityType>,
        bind: &Bind,
        dep_mask: &mut u8,
    ) -> Vec<ClassId> {
        let mut valid_nodes = Vec::new();

        // 🐛 実装時に見落としかけたバグ(match_connected_factの(Some,Some)と
        // 同種): この候補は「res_idという特定の1実体」を直接見るだけに
        // 見えるが、defined_by_collect_matches側がres_idのcomponents[0].
        // definitions(target_typeの定義を実際に持つか)を検証する。
        // GeoEntity::componentsは生成時にしか新規の定義を追加されず、
        // 唯一の例外はmerge_entitiesが吸収した側の定義を合流させる場合
        // ――つまりres_idが後から(同じEntityType同士としか併合されない)
        // 別の実体とマージされると、新しく目的の定義を獲得しうる。
        // res_idの型を依存対象にしておけば正しく無効化できる。
        if let Some(&res_id) = bind.get(result_var) {
            let res_rep = self.egraph.get_rep(res_id);
            *dep_mask |= entity_type_bit(self.egraph.entities[res_rep.0].entity_type);
            valid_nodes.push(res_rep);
        }
        // 🌟 FIX: *v ではなく v をそのまま渡す
        else if parent_vars.iter().all(|v| bind.contains_key(v)) {
            // 🌟 dep_maskのドキュメント参照。この枝は「(全親から決まる)この
            // 正確なDefinitionを持つ実体が既に存在するか」を見る。無ければ
            // 生成する(ホワイトリスト対象)か諦めるかのどちらだが、いずれの
            // 結果も「結果の型に新しい実体が現れたかどうか」に依存するため、
            // 結果の型を依存対象とする(型が不明な場合だけ安全側に倒す)。
            *dep_mask |= expected_r_type.map(entity_type_bit).unwrap_or(ALL_TYPES_MASK);
            let parent_ids: Vec<ClassId> = parent_vars.iter().map(|v| self.egraph.get_rep(bind[v])).collect();

            // 🌟 FIX: 全ての DefinedBy 対象型を網羅する
            let temp_def = match target_type {
                "AnglePair" => Definition::AnglePair(parent_ids[0], parent_ids[1]),
                "DirectionOf" => Definition::DirectionOf(parent_ids[0]),
                "LineThroughPoints" => Definition::new_line(parent_ids[0], parent_ids[1]),
                "Midpoint" => {
                    let (a,b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::Midpoint(a, b)
                },
                "Intersection" => {
                    let (a,b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::Intersection(a, b)
                },
                "LengthSq" => {
                    let (a,b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::LengthSq(a, b)
                },
                // 🌟 スパイラル相似の中点対応のために追加: LengthSqと全く同じく
                // 可換(normalize_definitionがClassId順にソートする)なので同じ
                // パターンで正規化する。以前はProductがDefinedByパターンの
                // 前提として参照されたことが無かった(共点二弦の相似は
                // constructionsでのみProductを作り、前提としては使わない)ため
                // この分岐が無くても困らなかったが、「比の等式を前提として
                // 要求する」定理(スパイラル相似)を書くにはProduct自体を
                // DefinedByで前提チェックできる必要がある。
                "Product" => {
                    let (a,b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::Product(a, b)
                },
                "PerpendicularLine" => Definition::PerpendicularLine(parent_ids[0], parent_ids[1]),
                "ParallelLine" => Definition::ParallelLine(parent_ids[0], parent_ids[1]),
                "TangentLine" => Definition::TangentLine(parent_ids[0], parent_ids[1]),
                "Circumcircle" => {
                    let mut arr = [parent_ids[0].0, parent_ids[1].0, parent_ids[2].0];
                    arr.sort_unstable();
                    Definition::Circumcircle(ClassId(arr[0]), ClassId(arr[1]), ClassId(arr[2]))
                }
                // 🌟 mmp_core/mod.rs::Definition::SecondIntersectionOfLineAndConic
                // のドキュメント参照。TangentLine/Circumcircleと同じく自動生成
                // ホワイトリスト(下のmatches!)には含めない――既知の点・直線・
                // 曲線の組み合わせから無差別に生成すると全件スキャン時に無駄な
                // 補助点が量産されかねないため、既存のエンティティ(MCTSが
                // 既に作ったもの、または定理のconstructionsが明示的に作った
                // もの)を探すだけに留める。
                "SecondIntersectionOfLineAndConic" if parent_ids.len() == 3 =>
                    Definition::SecondIntersectionOfLineAndConic(parent_ids[0], parent_ids[1], parent_ids[2]),
                // 🌟 CrossRatioのV4正規化はここで手書きで複製せず、mod.rs側の
                // normalize_definitionをそのまま呼ぶ(4元クライン群の畳み込みは
                // 単純なソートより複雑なので、ロジックを1箇所に保つ)。
                "CrossRatio" if parent_ids.len() == 4 => self.egraph.normalize_definition(
                    &Definition::CrossRatio(parent_ids[0], parent_ids[1], parent_ids[2], parent_ids[3])
                ),
                // 🌟 CrossRatioOfLines(線束の複比)もCrossRatioと同じV4正規化。
                "CrossRatioOfLines" if parent_ids.len() == 4 => self.egraph.normalize_definition(
                    &Definition::CrossRatioOfLines(parent_ids[0], parent_ids[1], parent_ids[2], parent_ids[3])
                ),
                _ => Definition::GivenPoint,
            };

            if let Some(&existing) = self.egraph.memo.get(&temp_def) {
                valid_nodes.push(self.egraph.get_rep(existing));
            } else if matches!(target_type, "AnglePair" | "DirectionOf" | "LengthSq" | "CrossRatio" | "CrossRatioOfLines" | "Product") {
                // 🌟 ユーザー提案:「複比の定理を使うときは複比自体を次数を用いて
                // 生成に制限をかけて」への対応。複比は4点(または4直線)から
                // 作られるため、無関係な組み合わせ(透視射影不変性のような
                // 多自由変数の定理が、DFSの中で偶然束縛してしまった無関係な
                // 4点/4直線)では次数が際限なく積み上がり得る。生成前に次数を
                // 測定し、異常に高い候補は(この特定の束縛での生成だけを諦める
                // ――failed_pathsによりこのDFS枝は自然に打ち切られる)ことで、
                // 無駄な複比エンティティの増殖と、それに続く
                // detect_cross_ratio_coincidencesの比較コストの増大を防ぐ。
                // 次数が測定不能(None)な場合は安全側に倒し、制限しない。
                // 🌟 CrossRatioOfLinesもmeasure_cross_ratio_affinityでそのまま
                // 測定できる(4引数をpointかlineかを区別せずevaluate_nodeに
                // 渡すだけなので、entity_typeによらず動く)。
                if matches!(target_type, "CrossRatio" | "CrossRatioOfLines") {
                    let cr_parents = match temp_def {
                        Definition::CrossRatio(a, b, c, d) | Definition::CrossRatioOfLines(a, b, c, d) => Some((a, b, c, d)),
                        _ => None,
                    };
                    if let Some((a, b, c, d)) = cr_parents {
                        const CR_DEGREE_CAP: usize = 8;
                        const CR_MAX_D: usize = 6;
                        if let Some((da, db, dc, dd, d_cr)) = self.egraph.measure_cross_ratio_affinity(a, b, c, d, CR_MAX_D) {
                            if d_cr > CR_DEGREE_CAP {
                                println!("  🚫 [複比の生成を制限] 次数{}(次数{}+{}+{}+{})が高すぎるため、{}の生成を見送りました", d_cr, da, db, dc, dd, target_type);
                                return valid_nodes;
                            }
                        }
                    }
                }

                let e_type = match target_type {
                    "AnglePair" => EntityType::Scalar,
                    "DirectionOf" => EntityType::Point,
                    _ => EntityType::Scalar
                };

                // 🌟 FIX: 親図形の名前を取得して結合し、誰と誰の角(方向)なのかを明示する
                let p_names: Vec<String> = parent_ids.iter()
                    .map(|&id| self.egraph.entities[id.0].name.clone())
                    .collect();

                let prefix = if target_type == "DirectionOf" { "Dir" } else { target_type };
                let name = format!("{}_{}_(Auto)", prefix, p_names.join("_"));

                let new_id = self.egraph.create_entity(name, temp_def.clone(), e_type);
                self.egraph.apply_trivial_relations(new_id, &temp_def);
                // 🌟 ユーザー提案:「複比同士の関係式からconjectureを発行して、
                // そこから定理適用の形を見つける」への対応。新しく作られた
                // 複比(点の複比・線束の複比のどちらでも)の値を既存の他の
                // 複比と数値的に比較し、一致するものがあれば予想(conjecture)
                // として記録する(detect_cross_ratio_coincidences側がCrossRatio/
                // CrossRatioOfLines両方を対象にスキャンするので、点の複比と
                // 線束の複比が一致する、というまさに定理A/Bが探している
                // 組み合わせも検出できる)。
                if matches!(target_type, "CrossRatio" | "CrossRatioOfLines") {
                    self.egraph.detect_cross_ratio_coincidences(new_id);
                }
                valid_nodes.push(new_id);
            }
        }
        // 🌟 高速化(ユーザー要望「TheoremDefの改善、Simson級を1秒未満に」への
        // 対応): 親変数の一部だけが束縛されている場合(例: AnglePair(D2,D3,Ang23)
        // でD2だけ既知)。以前はこのケースを見落として下のフルスキャン
        // (期待される結果の型の全代表元、または全エンティティ)にそのまま
        // フォールバックしていた。実測(--profileの診断カウンタで「有向角の
        // 加法性」の探索木を追跡)で、この見落としがsimson全体のdfs_call
        // 消費量トップ(平均19,000回超/試行、全体の約1/4)の直接の原因だと
        // 判明した。
        //
        // 束縛済みの親(anchor)のGeoEntity::usesは「anchorをDefinitionの
        // 親として参照する実体」の集合で、create_entity時に登録され
        // (mod.rs参照)、mergeのたびにcongruence.rs::merge_entitiesが
        // 生き残った側へ正しく引き継ぐ(=マージを経ても取りこぼさない)。
        // 安全性: ここで返すvalid_nodesはdefined_by_collect_matchesが
        // 実際のDefinition(target_type・全親の一致)で改めて検証する
        // 「候補プール」に過ぎないため、真に有効な候補を含む上位集合
        // (superset)でありさえすれば正しい――そしてtarget_typeの定義上、
        // 真に有効な結果ノードは必ずanchorを親の1つとして持つ(=create_entity
        // 時にanchorのusesへ登録済み)ため、この絞り込みは取りこぼしが起きない。
        else if let Some(&anchor_raw) = parent_vars.iter().find_map(|v| bind.get(v)) {
            // 🌟 dep_maskのドキュメント参照。anchorのusesは新しい結果型の
            // 実体がanchorを親として作られるたびに増える。
            *dep_mask |= expected_r_type.map(entity_type_bit).unwrap_or(ALL_TYPES_MASK);
            let anchor = self.egraph.get_rep(anchor_raw);
            let mut seen = rustc_hash::FxHashSet::default();
            for &used_id in &self.egraph.entities[anchor.0].uses {
                let u_rep = self.egraph.get_rep(used_id);
                if let Some(et) = expected_r_type {
                    if self.egraph.entities[u_rep.0].entity_type != et { continue; }
                }
                if seen.insert(u_rep) {
                    valid_nodes.push(u_rep);
                }
            }
        }
        // 🌟 FIX 3: どちらも未バインドの場合のみフルスキャン
        // 🌟 型インデックス化: 期待される結果の型が分かっていれば
        // type_index経由でその型の代表元だけを引く(理由は
        // match_identical_fact/match_connected_factの(None,None)分岐と同じ)。
        else if let Some(et) = expected_r_type {
            *dep_mask |= entity_type_bit(et);
            let cached = self.defined_by_type_scan_candidates(et);
            valid_nodes.extend(cached.iter().copied());
        } else {
            *dep_mask |= ALL_TYPES_MASK;
            for i in 0..self.egraph.entities.len() {
                let id = ClassId(i);
                if self.egraph.get_rep(id) == id {
                    valid_nodes.push(id);
                }
            }
        }

        valid_nodes
    }

    /// 🌟 "DefinedBy" の候補ノードそれぞれについて、実際にtarget_type型の定義を
    /// 持っているかを確認し、親変数との束縛の整合性(順不同図形は順列展開、
    /// 有向角のフリップ許可時は両方向)を取りながら (Bind, FlipStates) の
    /// 候補列を作る。読み取り専用(egraphを変更しない)。
    fn defined_by_collect_matches(
        &self,
        def: &FactPatternDef,
        target_type: &str,
        parent_vars: &[String],
        result_var: &String,
        valid_nodes: &[ClassId],
        bind: &Bind,
        flip_states: &FlipStates,
    ) -> Vec<(Bind, FlipStates)> {
        let mut matches = Vec::new();
        for &node_id in valid_nodes {
            for comp in &self.egraph.entities[node_id.0].components {
                for d in &comp.definitions {
                    if d.get_type_name() == target_type {
                        let d_parents = d.get_parents();
                        if d_parents.len() == parent_vars.len() {
                            let is_unordered = matches!(target_type, "Midpoint" | "LineThroughPoints" | "Intersection" | "LengthSq" | "Circumcircle");

                            let perms = if is_unordered {
                                if d_parents.len() == 2 {
                                    vec![(vec![d_parents[0], d_parents[1]], None), (vec![d_parents[1], d_parents[0]], None)]
                                } else if d_parents.len() == 3 {
                                    // 🌟 FIX: Python版にあった3変数の全順列展開を復活
                                    vec![
                                        (vec![d_parents[0], d_parents[1], d_parents[2]], None),
                                        (vec![d_parents[0], d_parents[2], d_parents[1]], None),
                                        (vec![d_parents[1], d_parents[0], d_parents[2]], None),
                                        (vec![d_parents[1], d_parents[2], d_parents[0]], None),
                                        (vec![d_parents[2], d_parents[0], d_parents[1]], None),
                                        (vec![d_parents[2], d_parents[1], d_parents[0]], None),
                                    ]
                                } else { vec![(d_parents.clone(), None)] }
                            } else if matches!(target_type, "CrossRatio" | "CrossRatioOfLines") && d_parents.len() == 4 {
                                // 🌟 複比の値を厳密に保つ4元クライン群V4の4通りだけを試す
                                // (mod.rs::normalize_definitionのCrossRatio/CrossRatioOfLines
                                // 正規化と対になる唯一の正しい順列集合――全24順列や、
                                // Circumcircle等と同じ「完全な順不同」ではないことに注意。
                                // 他の20順列は値そのものが変わるので、ここで一緒に試して
                                // しまうと異なる複比を誤って同一視することになる)。
                                let p = &d_parents;
                                vec![
                                    (vec![p[0], p[1], p[2], p[3]], None),
                                    (vec![p[1], p[0], p[3], p[2]], None),
                                    (vec![p[2], p[3], p[0], p[1]], None),
                                    (vec![p[3], p[2], p[1], p[0]], None),
                                ]
                            } else if target_type == "AnglePair" && def.allow_flip && d_parents.len() == 2 {
                                let mut valid_perms = Vec::new();
                                let state = def.flip_group.as_ref().and_then(|g| flip_states.get(g).copied());
                                if state != Some(true) { valid_perms.push((vec![d_parents[0], d_parents[1]], Some(false))); }
                                if state != Some(false) { valid_perms.push((vec![d_parents[1], d_parents[0]], Some(true))); }
                                valid_perms
                            } else {
                                vec![(d_parents.clone(), None)]
                            };

                            for (p_ids, flip_val) in perms {
                                let mut next_bind = bind.clone();
                                let mut conflict = false;
                                for (v_name, &p_id) in parent_vars.iter().zip(p_ids.iter()) {
                                    if let Some(&existing) = next_bind.get(v_name) {
                                        if self.egraph.get_rep(existing) != self.egraph.get_rep(p_id) { conflict = true; break; }
                                    }
                                    next_bind.insert(v_name.clone(), p_id);
                                }
                                if let Some(&existing) = next_bind.get(result_var) {
                                    if self.egraph.get_rep(existing) != node_id { conflict = true; }
                                }
                                next_bind.insert(result_var.clone(), node_id);

                                if !conflict {
                                    let mut next_flip = flip_states.clone();
                                    if let (Some(group), Some(val)) = (&def.flip_group, flip_val) {
                                        next_flip.insert(group.clone(), val);
                                    }
                                    // 🌟 個別の角度のフリップ状態も記憶させる
                                    if let Some(val) = flip_val {
                                        next_flip.insert(result_var.clone(), val);
                                    }
                                    matches.push((next_bind, next_flip));
                                }
                            }
                        }
                    }
                }
            }
        }
        matches
    }

    /// 🌟 "Identical"/"Connected"/"DefinedBy" 以外の汎用フォールバック:
    /// 既知の事実(self.facts)一覧から get_fact_bindings で束縛候補を集める。
    fn match_generic_fact(
        &mut self,
        theorem: &TheoremDef,
        def: &FactPatternDef,
        remaining: Rc<Vec<Pattern>>,
        bind: &Bind,
        flip_states: FlipStates,
        failed_paths: &mut rustc_hash::FxHashMap<u64, (u8, [u64; 4])>,
        dep_mask: &mut u8,
        on_match: &mut dyn FnMut(&Bind, &FlipStates)
    ) {
        // 🌟 dep_maskのドキュメント参照(dfs_match)。ここはself.facts(任意の
        // fact_typeを持ち得る、動的に増減する事実ストア)を舐める稀な
        // フォールバック経路で、依存先を型単位で正確に特定できないため
        // 安全側に倒して全型に依存するとみなす。
        *dep_mask |= ALL_TYPES_MASK;
        let mut matches = Vec::new();
        for fact in &self.facts {
            matches.extend(self.get_fact_bindings(theorem, fact, &def.fact_type, &def.args, bind));
        }

        matches.sort_by(|b1, b2| {
            let heat1 = self.calc_bind_heat(b1);
            let heat2 = self.calc_bind_heat(b2);
            heat2.partial_cmp(&heat1).unwrap_or(Ordering::Equal)
                .then_with(|| {
                    let mut k1: Vec<_> = b1.iter().collect(); k1.sort_by_key(|k| k.0);
                    let mut k2: Vec<_> = b2.iter().collect(); k2.sort_by_key(|k| k.0);
                    format!("{:?}", k1).cmp(&format!("{:?}", k2))
                })
        });
        matches.dedup_by_key(|b| {
            let mut keys: Vec<_> = b.iter().collect();
            keys.sort_by_key(|k| k.0);
            format!("{:?}", keys)
        });

        for new_bind in matches {
            self.dfs_match(theorem, remaining.clone(), new_bind, flip_states.clone(), failed_paths, dep_mask, on_match);
        }
    }

    pub fn execute_constructions(
        &mut self,
        _theorem_name: &str, // 🌟 命名には親図形の実名を使うので、定理名はもう使わない(呼び出し側との互換のため残置)
        constructions: &[ConstructTemplate],
        bind: &mut Bind,
    ) -> bool {
        for constr in constructions {
            let mut parent_ids = Vec::new();
            for arg in &constr.args {
                if let Some(&id) = bind.get(arg) {
                    parent_ids.push(self.egraph.get_rep(id));
                } else {
                    return false;
                }
            }
            
            let def = match constr.def_type.as_str() {
                "LineThroughPoints" => Definition::new_line(parent_ids[0], parent_ids[1]),
                "DirectionOf" => Definition::DirectionOf(parent_ids[0]),
                "Midpoint" => {
                    let (a, b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::Midpoint(a, b)
                },
                "AnglePair" => Definition::AnglePair(parent_ids[0], parent_ids[1]),
                "Intersection" => {
                    let (l1, l2) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::Intersection(l1, l2)
                },
                "PerpendicularLine" => Definition::PerpendicularLine(parent_ids[0], parent_ids[1]),
                "TangentLine" => Definition::TangentLine(parent_ids[0], parent_ids[1]),
                "Circumcircle" => {
                    let mut arr = [parent_ids[0].0, parent_ids[1].0, parent_ids[2].0];
                    arr.sort_unstable();
                    Definition::Circumcircle(ClassId(arr[0]), ClassId(arr[1]), ClassId(arr[2]))
                },
                // 🌟 mmp_core/mod.rs::Definition::SecondIntersectionOfLineAndConic
                // のドキュメント参照。定理のconstructionsテンプレートから明示的に
                // (known_point, line, conic) → もう一方の交点、を作れるようにする。
                "SecondIntersectionOfLineAndConic" if parent_ids.len() == 3 =>
                    Definition::SecondIntersectionOfLineAndConic(parent_ids[0], parent_ids[1], parent_ids[2]),
                // 🌟 FIX: 不足していた作図定義を追加（これがないと return false で沈黙する）
                "LengthSq" => {
                    let (a, b) = if parent_ids[0].0 > parent_ids[1].0 { (parent_ids[1], parent_ids[0]) } else { (parent_ids[0], parent_ids[1]) };
                    Definition::LengthSq(a, b)
                },
                "ParallelLine" => Definition::ParallelLine(parent_ids[0], parent_ids[1]),
                // 🌟 CrossRatioのV4正規化(4元クライン群の畳み込み)は単純なソートより
                // 複雑なので、defined_by_valid_nodesと同じくmod.rs側のnormalize_definition
                // をそのまま呼ぶ(ロジックを1箇所に保つ)。
                "CrossRatio" => self.egraph.normalize_definition(
                    &Definition::CrossRatio(parent_ids[0], parent_ids[1], parent_ids[2], parent_ids[3])
                ),
                // 🌟 CrossRatioOfLines(線束の複比)もCrossRatioと同じV4正規化。
                "CrossRatioOfLines" => self.egraph.normalize_definition(
                    &Definition::CrossRatioOfLines(parent_ids[0], parent_ids[1], parent_ids[2], parent_ids[3])
                ),
                // 🌟 2つのScalarの積(順不同)。方冪の定理(PA・PB=PC・PD)のような
                // 「2辺の積」をconclusionsのIdenticalで比較できるようにする。
                "Product" => self.egraph.normalize_definition(
                    &Definition::Product(parent_ids[0], parent_ids[1])
                ),
                // 🌟 シュタイナーの定理の逆(射影版・円周角の定理の逆)が、
                // 複比が一致した6点のうち5点から二次曲線を構築するために使う。
                // Circumcircleと同じ「完全な順不同」なのでソートするだけ。
                "ConicThrough5Points" => {
                    let mut arr = [parent_ids[0].0, parent_ids[1].0, parent_ids[2].0, parent_ids[3].0, parent_ids[4].0];
                    arr.sort_unstable();
                    Definition::ConicThrough5Points(ClassId(arr[0]), ClassId(arr[1]), ClassId(arr[2]), ClassId(arr[3]), ClassId(arr[4]))
                }
                _ => return false,
            };

            // 🌟 FIX: 既に同じ定義のエンティティがキャッシュ（memo）に存在する場合は、
            // 新規作成せずに既存のIDを再利用して無限ループ・ゴミ生成を防ぐ
            let new_id = if let Some(&existing_id) = self.egraph.memo.get(&def) {
                self.egraph.get_rep(existing_id)
            } else {
                let entity_type = match constr.target_type.as_str() {
                    "Line" => EntityType::Line,
                    "Angle" => EntityType::Scalar,
                    "Circle" => EntityType::Conic,
                    "Scalar" => EntityType::Scalar, // 🌟 スカラー型の追加
                    "Conic" => EntityType::Conic,
                    // 🌟 EntityType::Direction撤廃(方向はL∞に接続された
                    // ただのPoint): "Point"はもちろん、旧"Direction"文字列も
                    // (theorems.rsを全て"Point"に置き換え済みだが)フォール
                    // バックとして自然にここに落ちる。
                    _ => EntityType::Point,
                };
                
                // 🐛 バグ修正: 以前はテンプレートの変数名(bind_to、例: "Ang_MH_CH")と
                // 定理名をそのまま繋げていたため、"Ang_MH_CH_直角三角形の斜辺の中線_(Auto)"
                // のように、実際にどの図形から作られたのか全く追跡できない名前になっていた。
                // match_defined_by の自動生成箇所と同じ規則で、実際に束縛された親図形の
                // 名前をそのまま繋げる(例: "AnglePair_H_C_(Auto)")ようにし、名前から
                // 構成を逆に辿れるようにする。
                let parent_names: Vec<String> = parent_ids.iter()
                    .map(|&id| self.egraph.entities[id.0].name.clone())
                    .collect();
                let prefix = if constr.def_type == "DirectionOf" { "Dir" } else { constr.def_type.as_str() };
                let name = format!("{}_{}_(Auto)", prefix, parent_names.join("_"));

                let id = self.egraph.create_entity(name, def.clone(), entity_type);
                self.egraph.apply_trivial_relations(id, &def);
                id
            };
            
            bind.insert(constr.bind_to.clone(), new_id);
        }
        true
    }

    /// 🌟 証明復元(explain)用: この定理が実際に使った前提事実だけを、
    /// bindを通じて具体的なClassIdに解決して集める。
    /// Python版はbind.values()を丸ごと前提として記録していたため、
    /// マッチの過程でたまたま一緒に束縛されていただけの無関係な図形まで
    /// 証明ツリーに混入していた(ユーザー指摘の「不要な定理が多く含まれる」原因)。
    /// ここではtheorem.patterns中のPattern::Fact節(実際に検証された前提)だけを
    /// 辿るので、そのような無関係な図形は含まれない。
    ///
    /// 🌟 "DefinedBy"前提は、fpd.target_type(例: "AnglePair"/"Midpoint")が
    /// 分かっている場合 "DefinedBy:AnglePair" のようにタグを付けて記録する。
    /// これはraw_proof::RawProofが「このDefinedBy前提はDefinition::AnglePairの
    /// どのインスタンスを指しているか」を、Definition単位の由来インデックスと
    /// 照合してピンポイントに特定するために必要な情報(単なる"DefinedBy"だけ
    /// では、AnglePair/Midpoint/LineThroughPointsなど複数の定義種別を
    /// 区別できない)。表示用のformat_justificationや他の消費側は文字列を
    /// そのまま前方一致/分割で扱うので、この変更で壊れることはない。
    fn compute_theorem_premises(theorem: &TheoremDef, bind: &Bind) -> Vec<(String, Vec<ClassId>)> {
        let mut premises = Vec::new();
        for pat in &theorem.patterns {
            if let Pattern::Fact(fpd) = pat {
                let resolved: Option<Vec<ClassId>> = fpd.args.iter().map(|a| bind.get(a).copied()).collect();
                if let Some(args) = resolved {
                    let fact_type = if fpd.fact_type == "DefinedBy" {
                        match &fpd.target_type {
                            Some(tt) => format!("DefinedBy:{}", tt),
                            None => fpd.fact_type.clone(),
                        }
                    } else {
                        fpd.fact_type.clone()
                    };
                    premises.push((fact_type, args));
                }
            }
        }
        premises
    }

    pub fn apply_conclusions(&mut self, theorem: &TheoremDef, bind: &Bind, flips: &FlipStates) -> (bool, Vec<Fact>) {
        let mut applied_anything = false;
        let mut new_facts = Vec::new();
        let theorem_name = theorem.name.as_str();
        let premises = Self::compute_theorem_premises(theorem, bind);

        for conc in &theorem.conclusions {
            match conc.fact_type.as_str() {
                "Identical" => {
                    if let (Some(&id1), Some(&id2)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1])) {

                        let r1 = self.egraph.get_rep(id1);
                        let r2 = self.egraph.get_rep(id2);
                        if r1 == r2 { continue; } // 既にマージ済みならスキップ

                        // 🌟 EntityType::Angle撤廃(is_already_proven側と同じ
                        // 理由。mmp_core/mod.rs::EntityTypeのドキュメント参照)
                        // により、型による絞り込みを外し常にf1==f2を確認する
                        // ようにした。FlipStatesは元々match_defined_by側で
                        // target_type=="AnglePair"の場合だけpopulateされる
                        // 型非依存の仕組みなので、角度以外のIdentical結論では
                        // f1・f2とも常にNone(→false)になり判定は変わらない。
                        let f1 = flips.get(&conc.args[0]).copied().unwrap_or(false);
                        let f2 = flips.get(&conc.args[1]).copied().unwrap_or(false);
                        if f1 != f2 { continue; } // 向きが違うならマージしない

                        let name1 = self.egraph.entities[r1.0].name.clone();
                        let name2 = self.egraph.entities[r2.0].name.clone();
                        let justification = crate::mmp_core::Justification::Theorem {
                            name: theorem_name.to_string(),
                            premises: premises.clone(),
                        };
                        if self.egraph.merge_entities_justified(r1, r2, justification) {
                            println!("  🟢 [マージ実行] {} ≡ {} (理由: {})", name1, name2, theorem_name);
                            // 🌟 マージされた代表元の熱を上げて今後のDFSで優先させる[cite: 5]
                            self.egraph.entities[r1.0].heat_bonus += 1.5;
                            applied_anything = true;
                        }
                    }
                }
                // 🌟 FIX: Connected によるE-Graphの物理リンク構築を追加
                // (Concyclic/Collinearを専用Factとして結論に持つのはやめ、
                // 「N点が同じ円/直線にConnectedである」という形に統一した)
                "Connected" => {
                    if let (Some(&child), Some(&parent)) = (bind.get(&conc.args[0]), bind.get(&conc.args[1])) {
                        let c_rep = self.egraph.get_rep(child);
                        let p_rep = self.egraph.get_rep(parent);
                        let justification = crate::mmp_core::Justification::Theorem {
                            name: theorem_name.to_string(),
                            premises: premises.clone(),
                        };
                        self.egraph.link_logical_incidence_justified(c_rep, p_rep, justification);
                        applied_anything = true;
                        println!("  🟢 [リンク構築] {} ∈ {} (理由: {})",
                            self.egraph.entities[c_rep.0].name, self.egraph.entities[p_rep.0].name, theorem_name);

                        // 🐛 FIX: 以前はここでe-graphへの物理リンクを張るだけで、
                        // Fact::Connected を一切生成・記録していなかった。そのため
                        // schedule_matcher_task によるシード付き再マッチングが
                        // 一度も起きず、この新しい接続に依存する他の定理(円周角の定理など)
                        // が「シードなしの全探索(schedule_full_sweep)頼み」になって
                        // 見逃されることがあった(miquelで実際に退行した)。
                        // Identical/他のFactと同様にFactとして記録し、FactProvenイベント
                        // 経由でシード付き再マッチングが起きるようにする。
                        let fact = Fact::Connected(c_rep, p_rep);
                        if !self.facts.contains(&fact) {
                            self.facts.push(fact.clone());
                            new_facts.push(fact);
                        }
                    }
                },
                _ => {}
            }
        }
        (applied_anything, new_facts)
    }

    fn get_fact_bindings(&self, theorem: &TheoremDef, fact: &Fact, fact_type: &str, args: &[String], current_bind: &Bind) -> Vec<Bind> {
        let (f_type, f_objs) = match fact {
            Fact::Identical(a, b) => ("Identical", vec![*a, *b]),
            Fact::Connected(c, p) => ("Connected", vec![*c, *p]),
            Fact::Parallel(a, b) => ("Parallel", vec![*a, *b]),
        };

        if f_type != fact_type || f_objs.len() != args.len() { return vec![]; }

        // 🌟 爆速化: 事実探索の段階でターゲット型と異なるエンティティを即座に破棄
        for (i, arg_name) in args.iter().enumerate() {
            if f_type == "Connected" {
                if let Some(expected_type) = theorem.entities.get(arg_name).copied() {
                    if self.egraph.entities[self.egraph.get_rep(f_objs[i]).0].entity_type != expected_type {
                        return vec![]; 
                    }
                }
            }
        }

        let is_unordered = f_type == "Identical";
        let perms = if is_unordered { get_permutations(&f_objs) } else { vec![f_objs.clone()] };

        let mut matches = Vec::new();
        for perm in perms {
            let mut next_bind = current_bind.clone();
            let mut conflict = false;
            for (i, arg_name) in args.iter().enumerate() {
                // 🌟 型チェック
                if let Some(expected_type) = theorem.entities.get(arg_name).copied() {
                    if self.egraph.entities[self.egraph.get_rep(perm[i]).0].entity_type != expected_type {
                        conflict = true; break;
                    }
                }
                if let Some(&existing) = next_bind.get(arg_name) {
                    if self.egraph.get_rep(existing) != self.egraph.get_rep(perm[i]) {
                        conflict = true; break;
                    }
                }
                next_bind.insert(arg_name.clone(), perm[i]);
            }
            if !conflict { matches.push(next_bind); }
        }
        matches
    }
}

pub struct BlackboardEngine {
    pub prover: ProverEngine,
    pub task_queue: BinaryHeap<MatchTask>,
    pub event_queue: VecDeque<Event>,
    // 🌟 UCB1バンディットの効果測定用のA/Bスイッチ。false にすると
    // schedule_full_sweep がシードなしタスクの優先度を常に0固定にする
    // (バンディット導入前の挙動に戻す)。既定は有効(true)。
    pub bandit_enabled: bool,
}

impl BlackboardEngine {
    pub fn new(prover: ProverEngine) -> Self {
        Self {
            prover,
            task_queue: BinaryHeap::new(),
            event_queue: VecDeque::new(),
            bandit_enabled: true,
        }
    }

    /// 🌟 eval.rs::log_conjecture_candidateが蓄積した「証明されていないが
    /// 数値的根拠のある予想」を処理する。実体はEGraph::process_pending_conjectures
    /// (mmp_core/eval.rs)に移した(MCTS(mcts.rs::run_step)がBlackboardEngineを
    /// 介さず、自分自身が発見した予想を同じrun_step呼び出しの中で直接
    /// 評価・反映できるようにするため)。ここは既存呼び出し元(main.rs)向けの
    /// 薄い委譲。
    pub fn process_pending_conjectures(&mut self, target: &Option<(String, Vec<ClassId>)>) -> usize {
        self.prover.egraph.process_pending_conjectures(target)
    }

    /// 🌟 ユーザー提案(「定理を無マージで動かし、conjectureのみでも定理を
    /// 適用させるモード」):予想(a≡b、まだ証明されていない数値的な偶然の
    /// 一致)を使い捨てのクローン上でのみ真だと仮定し、通常の定理探索
    /// エンジン(schedule_full_sweep + dfs_match、UCB1バンディットは無効化)を
    /// 限られた予算で走らせる。
    ///
    /// 既存のEGraph::estimate_conjecture_value(eval.rs)が合同閉包1回だけの
    /// 浅い見積もりに意図的に留めている(定理マッチングまで踏み込むと
    /// 組み合わせが指数的に増える恐れがあるため)のに対し、こちらは
    /// 「その仮定が実際に名前付き定理を連鎖的に発火させ、現実にはまだ
    /// 知られていない別の等式を導くか」を見るための、より深いプロービング。
    /// 現実のegraph(self.prover.egraph)は一切変更しない。
    ///
    /// 戻り値は「現実には(まだ)別々の代表元だが、この仮定の下での
    /// シミュレーションでは統合された」現実の代表元ペアの一覧――呼び出し側
    /// (discover.rs)がこれを新しい"条件付き"の予想としてconjecturesマップに
    /// 記録する想定(このメソッド自体は記録しない、純粋な問い合わせ)。
    /// 比較はreal_len未満(=シミュレーション内で新規に作られた補助構成では
    /// ない、現実にも存在する)代表元同士に限定する
    /// (EGraph::absorb_conjectures_fromと同じ理由)。
    pub fn probe_conjecture(&self, a: ClassId, b: ClassId, dfs_budget: usize, sweep_rounds: usize) -> Vec<(ClassId, ClassId)> {
        if self.prover.egraph.get_rep(a) == self.prover.egraph.get_rep(b) { return Vec::new(); }
        let real_len = self.prover.egraph.entities.len();

        let mut sim_prover = ProverEngine::new(self.prover.egraph.clone());
        sim_prover.theorems = self.prover.theorems.clone(); // Rc共有なのでコピーは軽い
        sim_prover.dfs_cap = dfs_budget as u64;
        let mut sim_engine = BlackboardEngine::new(sim_prover);
        sim_engine.bandit_enabled = false;

        if !sim_engine.prover.egraph.merge_entities_justified(a, b, crate::mmp_core::Justification::Trivial {
            reason: "仮説プロービング: 予想を一時的に真と仮定(discover.rs::probe_and_expand_conjectures)".to_string(),
        }) {
            return Vec::new();
        }
        sim_engine.prover.egraph.apply_congruence_closure();
        sim_engine.schedule_full_sweep();
        for _ in 0..sweep_rounds {
            if !sim_engine.run_step(dfs_budget) { break; }
        }

        // 現実に存在する代表元同士で、simでは統合されたが現実にはまだ
        // 別々、というペアを新しい条件付き結論として拾う。
        let mut discovered = Vec::new();
        let mut seen_reps: FxHashMap<ClassId, ClassId> = FxHashMap::default();
        for i in 0..real_len {
            let id = ClassId(i);
            if self.prover.egraph.get_rep(id) != id { continue; } // 現実側の代表元だけを見る(重複回避)
            let sim_rep = sim_engine.prover.egraph.get_rep(id);
            if let Some(&other_real_id) = seen_reps.get(&sim_rep) {
                discovered.push((other_real_id, id));
            } else {
                seen_reps.insert(sim_rep, id);
            }
        }
        discovered
    }

    pub fn schedule_full_sweep(&mut self) {
        // 🌟 ProverEngine::ProfileStatsのドキュメント参照: この関数自体が
        // 実際にどれだけの時間・頻度で呼ばれ、1回あたり何個の「空の
        // failed_pathsを持つシードなしタスク」を新規に作っているかを計測する。
        // 2度の撤回(DefinedBy遅延構築・スケジューラ精密化)がどちらも
        // 「この関数が重いはず」という推測止まりで終わった反省から、
        // 次に何か変える前にまずここを実測できるようにする。
        let sfs_start = std::time::Instant::now();
        self.prover.profile.sfs_calls += 1;

        // 🌟 FIX: シード注入済みのタスクは消さずに保持する!
        // 🐛 以前は「priority > 0」で判定していたが、UCB1バンディットの
        // 導入でシードなしタスクの優先度も +5 まで上がり得るようになったため、
        // priorityの値ではなく専用フラグ(is_seeded)で由来を判定する。
        let mut keep = Vec::new();
        for task in self.task_queue.drain() {
            if task.is_seeded { keep.push(task); }
        }
        self.task_queue = BinaryHeap::from(keep);

        // 🌟 UCB1バンディット: シードなし全探索タスクどうしの優先度を、
        // これまでの経験的な成功率(+探索ボーナス)で差別化する。
        // self.prover.theorems.iter() で theorems を借用したまま
        // self.prover.theorem_priority_bonus(&mut self.prover) は呼べない
        // (借用の競合)ため、先にインデックスごとの優先度だけを計算しておく。
        // bandit_enabled=false の場合は全定理を優先度0固定にし、導入前と
        // 同じ挙動に戻す(A/B比較用)。
        let theorem_count = self.prover.theorems.len();
        let priorities: Vec<i32> = if self.bandit_enabled {
            (0..theorem_count).map(|idx| self.prover.theorem_priority_bonus(idx)).collect()
        } else {
            vec![0; theorem_count]
        };

        // 🌟 型シグネチャ事前フィルタ(theorem_types_availableのドキュメント参照):
        // 借用チェッカの都合上(下のループはself.prover.theoremsを不変借用したまま
        // &mut self.proverを要求するtheorem_types_availableを呼べない)、
        // 先にインデックスごとの可否だけ計算しておく。
        let types_available: Vec<bool> = (0..theorem_count)
            .map(|idx| self.prover.theorem_types_available(idx))
            .collect();

        for (idx, theorem) in self.prover.theorems.iter().enumerate() {
            if !types_available[idx] { continue; }
            let mut initial_bind = Bind::default();
            initial_bind.insert("Ang90".to_string(), self.prover.egraph.ang90);
            initial_bind.insert("Ang0".to_string(), self.prover.egraph.ang0);

            self.task_queue.push(MatchTask {
                priority: priorities[idx],
                theorem_idx: idx,
                bind: initial_bind,
                flip_states: FlipStates::default(),
                remaining_patterns: Rc::new(theorem.patterns.clone()),
                is_seeded: false,
            });
            self.prover.profile.sfs_tasks_created += 1;
        }
        self.prover.profile.sfs_time += sfs_start.elapsed();
    }

    fn schedule_matcher_task(&mut self, fact: &Fact) {
        let (fact_type, fact_objs) = match fact {
            Fact::Identical(a, b) => ("Identical", vec![*a, *b]),
            Fact::Connected(c, p) => ("Connected", vec![*c, *p]),
            Fact::Parallel(a, b) => ("Parallel", vec![*a, *b]),
        };

        for (idx, theorem) in self.prover.theorems.iter().enumerate() {
            for pat in &theorem.patterns {
                if let Pattern::Fact(def) = pat {
                    if def.fact_type == fact_type && def.args.len() == fact_objs.len() {
                        
                        // 🌟 FIX: Python版の _evaluate_patterns_with_seed_gen を再現[cite: 6]
                        // 発見された事実のオブジェクトの順列を作り、変数を事前バインド（シード化）する
                        let perms = match fact_type {
                            "Connected" => vec![fact_objs.clone()], // 有向関係なので順列なし
                            _ => get_permutations(&fact_objs),      // Identical 等は全順列
                        };

                        for perm in perms {
                            let mut bind = Bind::default();
                            // 定数ノードの事前バインド
                            bind.insert("Ang90".to_string(), self.prover.egraph.ang90);
                            bind.insert("Ang0".to_string(), self.prover.egraph.ang0);

                            // 🌟 シードの注入
                            for (i, v_name) in def.args.iter().enumerate() {
                                bind.insert(v_name.clone(), perm[i]);
                            }

                            // シード済みリーチフォーマットとしてタスクを積む
                            self.task_queue.push(MatchTask {
                                priority: 10,
                                theorem_idx: idx,
                                bind,
                                flip_states: FlipStates::default(),
                                remaining_patterns: Rc::new(theorem.patterns.clone()),
                                is_seeded: true,
                            });
                        }
                    }
                }
            }
        }
    }

    pub fn emit(&mut self, event: Event) {
        self.event_queue.push_back(event);
    }

    pub fn run_step(&mut self, budget: usize) -> bool {
        let mut applied_anything = false;
        let mut calls = 0;

        while calls < budget {
            while let Some(event) = self.event_queue.pop_front() {
                match event {
                    Event::NodeMerged => {
                        if self.prover.egraph.apply_congruence_closure() {
                            applied_anything = true;
                            self.event_queue.push_back(Event::NodeMerged);
                        }
                    },
                    Event::FactProven(fact) => {
                        if !self.prover.facts.contains(&fact) {
                            self.prover.facts.push(fact.clone());
                            self.schedule_matcher_task(&fact);
                        }
                    }
                }
            }

            if let Some(mut task) = self.task_queue.pop() {
                calls += 1;
                self.prover.dfs_calls = 0;
                // 🌟 task はcap到達時に self.task_queue.push(task) で再キューされ
                // 得るため(move)、後段のバンディット記録で使うフィールドは
                // Copy型としてここで先に控えておく。
                let task_theorem_idx = task.theorem_idx;
                let task_is_seeded = task.is_seeded;
                // 🌟 theorems は Vec<Rc<TheoremDef>> なので、この clone() はもう
                // ディープコピーではなく参照カウントのインクリメントのみ(ポインタコピー相当)
                let theorem = self.prover.theorems[task.theorem_idx].clone();
                let mut new_binds = Vec::new();
                // 🌟 検証メモ: 当初は schedule_full_sweep() 由来のシードなしタスク
                // (priority<=0) だけ上限を 20,000 に下げる案を試したが、miquel の
                // 「有向角の加法性」「円周角の定理の逆」はまさにシードなし状態から
                // 20,000〜100,000回の間で成功しており、上限を下げるとリトライのたびに
                // failed_paths キャッシュが空の状態から探索をやり直すだけになって
                // かえって遅くなった(0.69s→1.15s)ため撤回した。
                // 上限自体は104行目のフィールド定義の通り常に100,000のまま。
                //
                // 🌟 ユーザー提案(「新規作図でfailed pathが破棄されるのは
                // ある程度どうしようもないが、接続の弱いfailed pathは型に
                // 関わらず保持できるはず」→続けて「タスクをまたいだグローバル
                // 化」)への対応。以前はfailed_pathsをMatchTask単位の寿命
                // (dfs_cap到達での再キュー間でしか持ち越せない)で持たせて
                // いたが、診断計測で判明した「dfs_matchの再訪問の38%はタスク
                // をまたいだもの」(UCB1がschedule_full_sweepのたびに同じ
                // 定理を新しいtask/新しいbindで何度も試す)を一切捕捉できて
                // いなかった。state_sigは元々bind内容だけで決まる(特定の
                // タスクインスタンスとは無関係な)ハッシュなので、
                // ProverEngine::global_failed_paths(theorem_idxごとの永続
                // マップ)へ昇格させ、このタスクの実行中だけ借用する
                // (std::mem::takeで一時的に取り出し、使い終わったら必ず
                // 書き戻す――dfs_matchが&mut selfを要求するため、self自身の
                // フィールドを借用しながら再帰呼び出しできない、という
                // 借用チェッカ上の制約を回避する常套手段)。
                self.prover.ensure_global_failed_paths();
                let mut failed_paths = std::mem::take(&mut self.prover.global_failed_paths[task.theorem_idx]);

                let mut dep_mask: u8 = 0;
                self.prover.dfs_match(
                    &theorem,
                    task.remaining_patterns.clone(), // Rc なのでポインタコピーのみ
                    task.bind.clone(),
                    task.flip_states.clone(),
                    &mut failed_paths,
                    &mut dep_mask,
                    &mut |bind, flips| {
                        new_binds.push((bind.clone(), flips.clone()));
                    }
                );
                // 🌟 借用したグローバルキャッシュを書き戻す。dfs_cap到達で
                // 再キューされるかどうかに関わらず、この定理への次のどの
                // タスク(全く別のbindでも)からも再利用できるよう常に戻す
                // (以前のタスク単位保存は再キュー時にしか書き戻さなかった
                // ため、cap到達に至らず自然にタスクが完了したケースでは
                // せっかく積んだfailed_pathsがそのまま捨てられていた)。
                self.prover.global_failed_paths[task.theorem_idx] = failed_paths;
                // 🌟 コスト考慮型バンディット報酬のために、このタスク1回が
                // 実際に消費したdfs_call数を控えておく(次のタスクの
                // self.prover.dfs_calls = 0 まではこの値のまま変わらない)。
                let dfs_calls_used = self.prover.dfs_calls;
                if task_is_seeded {
                    self.prover.profile.seeded_pops += 1;
                    self.prover.profile.seeded_dfs_calls += dfs_calls_used;
                } else {
                    self.prover.profile.unseeded_pops += 1;
                    self.prover.profile.unseeded_dfs_calls += dfs_calls_used;
                }

                // 🌟 スケジューリング工夫: DFSが上限(100,000)に張り付いた場合、
                // このタスクは重すぎるためペナルティを与えて後回しにする。
                //
                // 🐛 バグ修正: 以前はキューが空(＝他に実行できるタスクが無い)の場合でも
                // 無条件に再キューしていた。この場合 e-graph も bind も何一つ変化しないまま
                // 全く同じ 100,000 回の探索を優先度が尽きるまで(最大5回)繰り返すだけになり、
                // 実測で simson 問題では1つの定理(有向角の加法性)のリトライだけで
                // 5秒の予算のうち3秒以上を無駄にしていた。他に実行可能なタスクが残っている
                // 場合のみ再キューし、無い場合はその場で諦めてリカバリーフェーズに委ねる。
                if self.prover.dfs_calls >= self.prover.dfs_cap {
                    if !self.task_queue.is_empty() {
                        task.priority -= 5;
                        if task.priority >= -20 { // 諦める閾値
                            // 🌟 failed_pathsは既にglobal_failed_pathsへ書き戻し
                            // 済み(このタスク固有の状態としてではなく、この
                            // 定理全体で共有される状態として)なので、ここでは
                            // タスク自体(bind/remaining_patterns)を再キューする
                            // だけでよい。
                            self.task_queue.push(task);
                        }
                    }
                }

                // 🌟 UCB1バンディット: このタスク(1回のdfs_match呼び出し)が
                // 実際に何か結論を適用できたかどうかを、シードなしタスクに限って
                // theorem_statsに反映する。「試したが何も生まなかった」も
                // 立派な学習対象(失敗)である。
                let mut task_succeeded = false;

                for (mut bind, flips) in new_binds {
                    // 🌟 1. まず現在のE-Graphの状態で、この結論がすでに満たされているかチェックする
                    if self.prover.is_already_proven(&theorem.conclusions, &bind, &flips) {
                        continue;
                    }

                    // 🌟 2. 結論が満たされていない場合のみ、足りない図形を作図する
                    if self.prover.execute_constructions(&theorem.name, &theorem.constructions, &mut bind) {

                        // 🌟 3. 作図後、もう一度チェック。ここで真になるなら「作図しただけでマージ済み」なのでスキップ
                        if self.prover.is_already_proven(&theorem.conclusions, &bind, &flips) {
                            continue;
                        }

                        println!("  🎯 [リーチ通知] 定理「{}」の前提条件がすべて満たされました！", theorem.name);
                        for (var_name, class_id) in &bind {
                            if var_name.starts_with("__") { continue; }
                            let entity_name = self.prover.egraph.entities[self.prover.egraph.get_rep(*class_id).0].name.clone();
                            println!("      - 割り当て: {} = {}", var_name, entity_name);
                        }

                        let (applied, generated_facts) = self.prover.apply_conclusions(&theorem, &bind, &flips);
                        if applied {
                            applied_anything = true;
                            task_succeeded = true;
                            self.emit(Event::NodeMerged);
                            for f in generated_facts { self.emit(Event::FactProven(f)); }
                        }
                    }
                }

                if !task_is_seeded {
                    self.prover.record_theorem_attempt(task_theorem_idx, task_succeeded, dfs_calls_used);
                }
            } else { break; }
        }
        applied_anything
    }

    // 🌟 フェーズ1.5: 交点を持つ2直線のペアから有向角(AnglePair)を自動生成
    pub fn resolve_angle_demands(&mut self) -> bool {
        let mut applied = false;
        let mut angle_pairs_to_create = Vec::new();

        // 🌟 処理前にグラフを最新状態に正規化し、直線の重複を完全に消す
        self.prover.egraph.apply_congruence_closure();

        for i in 0..self.prover.egraph.entities.len() {
            let pt_id = ClassId(i);
            if self.prover.egraph.get_rep(pt_id) != pt_id { continue; }
            if self.prover.egraph.entities[i].entity_type != EntityType::Point { continue; }

            // 🐛 FIX: line_infinity自身は普通の「直線」として数えない。
            // EntityType::Direction撤廃(方向はL∞に接続されたただのPoint)以降、
            // ここでのptがDirectionだと、その定義上line_infinityに必ず
            // 接続されている(=lines_on_ptに常にline_infinityを含む)ため、
            // 「Directionの直線+line_infinity」というペアから
            // AnglePair(その方向, DirectionOf(line_infinity))という無意味な
            // 退化した有向角を自動生成してしまっていた
            // (miquel_quadrilateralで実際に観測: EntityType::Angle撤廃で
            // これがEntityType::Scalarに合流したことで、他の定理の自己束縛
            // 候補プールを無駄な退化角で汚染し証明を妨げるまでになった)。
            let mut lines_on_pt = Vec::new();
            for comp in &self.prover.egraph.entities[i].components {
                for &sub_id in &comp.subobjects {
                    let sub_rep = self.prover.egraph.get_rep(sub_id);
                    if sub_rep == self.prover.egraph.line_infinity { continue; }
                    if self.prover.egraph.entities[sub_rep.0].entity_type == EntityType::Line {
                        lines_on_pt.push(sub_rep);
                    }
                }
            }
            lines_on_pt.sort_unstable_by_key(|id| id.0);
            lines_on_pt.dedup();

            if lines_on_pt.len() >= 2 {
                for l1 in 0..lines_on_pt.len() {
                    for l2 in (l1 + 1)..lines_on_pt.len() {
                        let d1 = self.get_or_create_direction(lines_on_pt[l1]);
                        let d2 = self.get_or_create_direction(lines_on_pt[l2]);
                        
                        let r_d1 = self.prover.egraph.get_rep(d1);
                        let r_d2 = self.prover.egraph.get_rep(d2);

                        // 🌟 FIX: 方向が同じ(平行/同一)な直線のペアで0度角を生成しない
                        if r_d1 == r_d2 { continue; }

                        // 🌟 FIX: allow_flip があるため、ID順でソートして片方のみを生成（数を半分に！）
                        let (d_min, d_max) = if r_d1.0 < r_d2.0 { (r_d1, r_d2) } else { (r_d2, r_d1) };
                        angle_pairs_to_create.push((d_min, d_max));
                    }
                }
            }
        }

        angle_pairs_to_create.sort_unstable_by_key(|(d1, d2)| (d1.0, d2.0));
        angle_pairs_to_create.dedup();

        for (d1, d2) in angle_pairs_to_create {
            let def = Definition::AnglePair(d1, d2);
            if !self.prover.egraph.memo.contains_key(&def) {
                let name = format!("AnglePair_{}_{}_(Auto)", self.prover.egraph.entities[d1.0].name, self.prover.egraph.entities[d2.0].name);
                let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Scalar);
                
                // 🌟 FIX: Auto生成されたAngleの重要度を下げ、無駄なヒューリスティック探索を抑制
                self.prover.egraph.entities[new_id.0].base_importance = 0.2;
                
                self.prover.egraph.apply_trivial_relations(new_id, &def);
                applied = true;
            }
        }

        if applied {
            println!("  💡 [スマート補完] 交点を持つ意味のある有向角を自動生成しました");
            self.schedule_full_sweep();
        }
        applied
    }

    fn get_or_create_direction(&mut self, line_id: ClassId) -> ClassId {
        let def = Definition::DirectionOf(line_id);
        if let Some(&dir_id) = self.prover.egraph.memo.get(&def) {
            return self.prover.egraph.get_rep(dir_id);
        }
        let name = format!("Dir_{}_(Fallback)", self.prover.egraph.entities[line_id.0].name);
        let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Point);
        self.prover.egraph.apply_trivial_relations(new_id, &def);
        new_id
    }

    // 🌟 フェーズ2: 論理エンジンが欲しがっていた補助線(Demand)を引く
    //
    // 🌟 ユーザー提案: 「点の組A,Bについて、線分ABの次数がdeg(A)+deg(B)という
    // 素朴な上界に比べて退化して小さい組は、何らかの隠れた定理・偶然の一致が
    // 効いている兆候として『相性が良い』」への対応で、頻度ベースのscoreに
    // measure_line_affinity(A,B)の退化量(deg_a+deg_b - deg_line、0未満は0に
    // 切り詰め)を加点として合成し、頻度だけでは見えない「単純な組み合わせに
    // 見えて実は特別な関係にある」ペアも優先的に試せるようにする。
    pub fn resolve_demands(&mut self) -> bool {
        if self.prover.construction_demands.is_empty() { return false; }

        const AFFINITY_MAX_D: usize = 4;
        const AFFINITY_WEIGHT: f64 = 2.0;
        let mut demands: Vec<((ClassId, ClassId), f64, Option<(usize, usize, usize)>)> = self.prover.construction_demands.iter()
            .map(|(&(p1, p2), &score)| {
                let affinity = self.prover.egraph.measure_line_affinity(p1, p2, AFFINITY_MAX_D);
                (( p1, p2), score, affinity)
            })
            .collect();
        demands.sort_by(|a, b| {
            let priority = |&(_, score, aff): &((ClassId, ClassId), f64, Option<(usize, usize, usize)>)| -> f64 {
                let bonus = aff.map_or(0.0, |(da, db, dab)| {
                    (da as f64 + db as f64 - dab as f64).max(0.0)
                });
                score + AFFINITY_WEIGHT * bonus
            };
            priority(b).partial_cmp(&priority(a)).unwrap_or(std::cmp::Ordering::Equal)
                .then_with(|| (a.0).0.0.cmp(&(b.0).0.0))
                .then_with(|| (a.0).1.0.cmp(&(b.0).1.0))
        });

        let mut applied = false;
        let mut count = 0;

        for ((p1, p2), score, affinity) in demands.into_iter() {
            let def = Definition::new_line(p1, p2);
            if !self.prover.egraph.memo.contains_key(&def) {
                let name = format!("Line_{}_{}_(Demand)", self.prover.egraph.entities[p1.0].name, self.prover.egraph.entities[p2.0].name);
                match affinity {
                    Some((da, db, dab)) if da + db > dab => {
                        println!("  💡 [オンデマンド作図] 要請により {} を生成 (需要: {:.1}, 相性◎: 次数{}+{}→{})", name, score, da, db, dab);
                    }
                    _ => {
                        println!("  💡 [オンデマンド作図] 要請により {} を生成 (需要: {:.1})", name, score);
                    }
                }
                let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Line);

                // 🌟 FIX: Demand線の重要度を下げ、推論の主軸がブレるのを防ぐ
                self.prover.egraph.entities[new_id.0].base_importance = 0.5;

                self.prover.egraph.apply_trivial_relations(new_id, &def);
                applied = true;
                count += 1;
                if count >= 3 { break; }
            }
        }

        self.prover.construction_demands.clear();
        if applied {
            // 🌟 FIX: 作図直後に合同閉包を強制実行し、既存の直線と即座にマージさせる！
            self.prover.egraph.apply_congruence_closure();
            self.schedule_full_sweep();
        }
        applied
    }

    // 🌟 フェーズ2.9: 目標駆動のオンデマンド作図(最後の砦、MCTSに頼る直前)。
    //
    // 背景(HAGeo-409ベンチマークで判明): resolve_demands/resolve_point_demands/
    // resolve_angle_demandsはいずれも「ある定理のDFSが実際にその組み合わせを
    // 束縛しようとして初めて需要として記録される」という反応的な仕組みで
    // 統一されている。これは無関係な直線・点を無差別に作り続ける組み合わせ
    // 爆発を避けるための健全な設計だが、逆に言うと「証明したい目標
    // (target_fact)には出てくるのに、重要度が低くどの定理からも一度も
    // 束縛されない孤立点」には永遠に需要が発生しないという穴がある
    // (実例: bench_2005usamop3のQ。B1,C1,Pとは共円関係の探索が活発に
    // 進む一方、Qは他の3点への直線が一度も引かれずグラフから孤立したまま
    // 探索がStallしていた)。
    //
    // 目標の引数に現れる点同士は「最終的に何らかの関係を証明したい」という
    // 意味で構造的に重要なはずなので、他の需要駆動フェーズが尽きた場合に
    // 限り(MCTSのような無方向な探索に頼る前の最後の一手として)、まだ
    // 直線で結ばれていない目標点のペアに無条件で補助線を引いてみる。
    // 需要の頻度・次数による絞り込みが無い分、resolve_demandsより無防備な
    // 最終手段なので、他の全ての需要駆動フェーズが失敗した後にだけ呼ぶこと。
    pub fn resolve_target_demands(&mut self, target: &Option<(String, Vec<ClassId>)>) -> bool {
        let Some((_, target_args)) = target else { return false; };

        let mut points: Vec<ClassId> = target_args.iter()
            .map(|&id| self.prover.egraph.get_rep(id))
            .filter(|&id| self.prover.egraph.entities[id.0].entity_type == EntityType::Point)
            .collect();
        points.sort_unstable_by_key(|id| id.0);
        points.dedup();

        let mut applied = false;
        let mut count = 0;
        'outer: for i in 0..points.len() {
            for j in (i + 1)..points.len() {
                let (p1, p2) = (points[i], points[j]);
                let def = Definition::new_line(p1, p2);
                if self.prover.egraph.memo.contains_key(&def) { continue; }
                // 🐛 FIX: p1,p2が既に何らかの直線を共有しているなら、その直線を
                // 差し置いて別の新しいLineThroughPointsエンティティを作っては
                // いけない。理論上は「2点が決める直線」は1本しかないので数値的にも
                // 同一のはずだが、新しい直線を作るとapply_trivial_relationsが
                // p1,p2それぞれにこの新しい直線への接続をもう1本追加してしまい、
                // 「この点は複数の互いに矛盾しうる接続を持つ」と見なされて
                // (has_extraneous_incidence)数値サンプリングが特定の直線上に
                // 座標を固定できなくなる(assign_free_point_coordsが安全側に倒れて
                // 無制約の乱数を返す)。実際にminiquelで、既にLineBC上にある
                // C,DについてLine(C,D)を新規に作った結果、Dの数値サンプリングが
                // 壊れてLineBCとの合流はおろか無関係な円の合流まで数値的健全性
                // チェックに軒並み却下される、という副作用が実測で見つかった。
                // find_common_lineで「既に共有する直線があるか」を確認し、あれば
                // 何もしない(その直線は既に存在するので、そもそも需要ではない)。
                if self.prover.egraph.find_common_line(&[p1, p2]).is_some() { continue; }
                let name = format!("Line_{}_{}_(TargetDemand)", self.prover.egraph.entities[p1.0].name, self.prover.egraph.entities[p2.0].name);
                println!("  💡 [目標駆動オンデマンド作図] 証明目標に現れる点を結ぶ {} を生成", name);
                let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Line);
                // 🌟 他のDemand系と同様、新規図形の重要度は下げて推論の主軸がブレるのを防ぐ
                self.prover.egraph.entities[new_id.0].base_importance = 0.5;
                self.prover.egraph.apply_trivial_relations(new_id, &def);
                applied = true;
                count += 1;
                if count >= 3 { break 'outer; }
            }
        }

        if applied {
            self.prover.egraph.apply_congruence_closure();
            self.schedule_full_sweep();
        }
        applied
    }

    // 🌟 フェーズ2.5: 交点(Point)の需要を解消する。2種類の需要源を合流させる:
    //   (a) match_defined_by_fact由来のpoint_construction_demands――今のところ
    //       どの定理も"Intersection"をDefinedByパターンとして問い合わせて
    //       いないため実質発火しないが、将来そのような定理を追加した時のために
    //       残してある。
    //   (b) このメソッド自身が行う、垂線の足に対する能動的なヒューリスティック
    //       走査(resolve_angle_demandsと同じ設計思想): 既存のPerpendicularLine
    //       (L_base, P)それぞれについて、それ自身とL_baseの交点(=Pから
    //       L_baseへの垂線の足)がまだ図形として存在しなければ需要とみなす。
    //       これは「2直線の任意の組み合わせ」のような組み合わせ爆発ではなく、
    //       既存のPerpendicularLineの数(三角形なら高々3本)に比例するだけの
    //       安全なスキャンで、直感的にも「垂線を引いたなら、その足は普通
    //       興味の対象になる」という妥当な着眼点。
    //       ユーザー要望: orthocenter/orthocenter_altでE,Fのような補助点を
    //       手で問題文に書かなくても発見できるようにしたい、への対応。
    //
    // 🌟 安全策: resolve_demands/resolve_angle_demandsと同じく、DFSが完全に
    // Stallしたリカバリーフェーズでのみ呼ばれる。新規点の重要度は下げて
    // 推論の主軸がブレるのを防ぐ。
    pub fn resolve_point_demands(&mut self) -> bool {
        // (b) 垂線の足の能動的スキャン。既存のdemandに合流させる。
        for i in 0..self.prover.egraph.entities.len() {
            let id = ClassId(i);
            if self.prover.egraph.get_rep(id) != id { continue; }
            if self.prover.egraph.entities[i].entity_type != EntityType::Line { continue; }
            let bases: Vec<ClassId> = self.prover.egraph.entities[i].components.iter()
                .flat_map(|c| c.definitions.iter())
                .filter_map(|d| if let Definition::PerpendicularLine(base, _) = d { Some(*base) } else { None })
                .collect();
            for base in bases {
                let base_rep = self.prover.egraph.get_rep(base);
                if base_rep == id { continue; }
                let key = if id.0 < base_rep.0 { (id, base_rep) } else { (base_rep, id) };
                self.prover.point_construction_demands.entry(key).or_insert(0.0);
            }
        }

        if self.prover.point_construction_demands.is_empty() { return false; }

        // 🌟 MMPの次数(measure_intersection_degree_candidate)で候補を
        // ランク付けする(ユーザー指摘: 添付のMMP解説PDFの「次数」概念、
        // および旧Python版に既にあったnumerical_degree)。次数が低い
        // (=単純な)候補を優先し、異常に高い候補(DEGREE_CAP超)は最初から
        // 除外する。中点のような「構造的には複合に見えても実際は次数が
        // 上がらない」構成は自然に許容されつつ、無関係な直線同士の交点を
        // 無差別に取り続けるような構成は次数が積み上がるため自然に
        // 足切りされる(実測でこの2つが明確に区別できることを
        // test_numerical_degree_*系のテストで確認済み)。
        // 次数が測定不能(Noneを表す適切なmoverが見つからない等)な場合は
        // 安全側に倒し、除外せず「不明」として通す。
        const DEGREE_CAP: usize = 4;
        const MAX_D: usize = 6;
        let mut demands: Vec<((ClassId, ClassId), f64, Option<usize>)> = self.prover.point_construction_demands.iter()
            .map(|(&(l1, l2), &score)| {
                let deg = self.prover.egraph.measure_intersection_degree_candidate(l1, l2, MAX_D);
                (( l1, l2), score, deg)
            })
            .filter(|&(_, _, deg)| deg.map_or(true, |d| d <= DEGREE_CAP))
            .collect();
        demands.sort_by(|a, b| {
            let da = a.2.unwrap_or(usize::MAX);
            let db = b.2.unwrap_or(usize::MAX);
            da.cmp(&db)
                .then_with(|| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal))
                .then_with(|| (a.0).0.0.cmp(&(b.0).0.0))
                .then_with(|| (a.0).1.0.cmp(&(b.0).1.0))
        });

        let mut applied = false;
        let mut count = 0;

        for ((l1, l2), score, deg) in demands.into_iter() {
            // 🌟 需要記録時からさらにマージが進んでいる可能性があるため、
            // normalize_definitionで現在の代表元へ正規化してから照合する。
            let def = self.prover.egraph.normalize_definition(&Definition::Intersection(l1, l2));
            let (l1, l2) = match def { Definition::Intersection(a, b) => (a, b), _ => (l1, l2) };
            if l1 == l2 { continue; }
            if !self.prover.egraph.memo.contains_key(&def) {
                let name = format!("Pt_{}_{}_(Demand)",
                    self.prover.egraph.entities[l1.0].name, self.prover.egraph.entities[l2.0].name);
                let deg_str = deg.map(|d| d.to_string()).unwrap_or_else(|| "不明".to_string());
                println!("  💡 [オンデマンド作図] 要請により {} (交点、次数{})を生成 (需要: {:.1})", name, deg_str, score);
                let new_id = self.prover.egraph.create_entity(name, def.clone(), EntityType::Point);

                // 🌟 Demand点の重要度を下げ、推論の主軸がブレるのを防ぐ(Demand線と同じ配慮)
                self.prover.egraph.entities[new_id.0].base_importance = 0.5;

                self.prover.egraph.apply_trivial_relations(new_id, &def);
                applied = true;
                count += 1;
                // 🌟 実測に基づくFIX: 当初は上限4(三角形の垂線3本+余裕1)にしていたが、
                // orthocenter/orthocenter_altで実験したところ、3本の垂線の足を
                // 一度に全部作ってしまうと(円の候補が3通りに増える等)DFSの
                // 探索が拡散し、逆に目標へ到達しにくくなることが判明した。
                // 上限を2に下げる(=最初のスタックでは最も需要が高い2点だけを
                // 作る)ことで、orthocenter(対称形、垂線の足なし)が4.5秒、
                // orthocenter_alt(補助点E,Fなし)が2.5秒で解けるようになった
                // ――3本目が本当に必要なら、次にまたStallした時に改めて
                // 需要として再スキャンされるので、完全性は失われない。
                if count >= 2 { break; }
            }
        }

        self.prover.point_construction_demands.clear();
        if applied {
            self.prover.egraph.apply_congruence_closure();
            self.schedule_full_sweep();
        }
        applied
    }

    pub fn check_target_reached(&self) -> bool { false }
}
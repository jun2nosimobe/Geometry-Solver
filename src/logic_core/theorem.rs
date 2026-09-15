//! 🌟 定理の書き方そのもの(パターン・構成・結論の定義)と、その補助。
//!
//! ここにあるのはデータ構造と純粋な関数だけで、探索の状態は持たない。

use crate::mmp_core::{ClassId, EGraph, EntityType, Fact};
use rustc_hash::FxHashMap;
use std::cmp::Ordering;

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
pub(crate) fn collect_pattern_vars<'a>(pat: &'a Pattern, out: &mut Vec<&'a str>) {
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
pub(crate) fn has_paired_defined_by_fanout(theorem: &TheoremDef, v1: &str, v2: &str) -> bool {
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
pub(crate) fn required_hard_types(theorem: &TheoremDef) -> Vec<crate::mmp_core::EntityType> {
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
    // 🐛 FIX: HashSetの反復順はプロセスごとに変わるので、ここで並べ直す。
    // この結果は定理マッチングの事前チェックの順序に使われるため、
    // 揃えておかないと同じ問題でも実行のたびに探索順が変わる。
    let mut out: Vec<EntityType> = set.into_iter().collect();
    out.sort_by_key(|t| format!("{:?}", t));
    out
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
pub(crate) const ALL_ENTITY_TYPES: [crate::mmp_core::EntityType; 4] = [
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
pub(crate) fn snapshot_type_generations(egraph: &EGraph) -> [u64; 4] {
    std::array::from_fn(|i| egraph.type_generation.get(&ALL_ENTITY_TYPES[i]).copied().unwrap_or(0))
}

pub(crate) fn get_permutations(items: &[ClassId]) -> Vec<Vec<ClassId>> {
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
    // パターン側から埋まるが、今のマッチャーは読んでいない
    // (候補の絞り込みに使う余地を残してある)。
    #[allow(dead_code)]
    pub target_type: Option<String>,
    #[allow(dead_code)]
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
    pub(crate) fn ucb1_score(&self, total_attempts: u64, exploration_c: f64) -> f64 {
        if self.attempts == 0 { return f64::INFINITY; }
        let mean = self.total_reward / self.attempts as f64;
        let bonus = exploration_c * ((total_attempts.max(1) as f64).ln() / self.attempts as f64).sqrt();
        mean + bonus
    }
}

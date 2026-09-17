//! 定理の書き方そのもの(パターン・作図・結論)と、その静的な解析。
//!
//! ここにあるのはデータ構造と純粋な関数だけで、探索の状態は持たない。

use crate::mmp_core::{ClassId, DefKind, EGraph, EntityType};
use rustc_hash::FxHashMap;
use std::cmp::Ordering;

// bind は探索木の各ノードで複製されるので、構造共有する永続HashMapにする。
// ハッシャはシード固定のもの(RandomState だと反復順が実行ごとに変わり、
// 候補を試す順序=見つかる証明が再現しなくなる。FxHash は HAMT と相性が悪く遅い)。
type FixedHasher = std::hash::BuildHasherDefault<std::collections::hash_map::DefaultHasher>;
pub type Bind = im::HashMap<String, ClassId, FixedHasher>;
pub type FlipStates = im::HashMap<String, bool, FixedHasher>;

/// 定理ごとの失敗パスのキャッシュ。状態署名 → (依存した型のマスク, 記録時の型世代)。
pub type FailedPaths = rustc_hash::FxHashMap<u64, (u8, [u64; 4])>;

/// Identical(a, b) の両方が未束縛のとき、自己束縛の候補をどのプールから取るか。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelfBindPool {
    /// 宣言型の全代表元(Scalar なら角度以外)。
    Any,
    /// 角度(AnglePair 由来の Scalar)だけ。
    Angle,
    /// CrossRatioOfLines 由来の Scalar だけ。
    CrossRatioOfLines,
}

/// Connected の片側の変数に付ける絞り込み。点と二次曲線は型だけでは区別が付かないので
/// incidence で見分ける。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Refinement {
    /// 点なら有限点(L∞上にない)、二次曲線なら円でないもの。
    Default,
    /// L∞上の点(=方向)。
    Direction,
    /// 円周点 I, J を両方通る二次曲線(=円)。
    Circle,
}

/// DefinedBy(AnglePair) で有向角の向きをどう扱うか。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Flip {
    /// 格納された向きのまま読む。
    Fixed,
    /// 両方の向きを試す。
    Free,
    /// 両方の向きを試すが、同じグループのパターンとは向きをそろえる。
    Grouped(String),
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Identical { a: String, b: String, pool: SelfBindPool },
    Connected { child: String, parent: String, child_ref: Refinement, parent_ref: Refinement },
    /// parents から kind で作られた図形が result。
    DefinedBy { kind: DefKind, parents: Vec<String>, result: String, flip: Flip },
    Distinct(Vec<String>),
    /// 代表元IDの厳密な昇順。同じ候補プールから選ぶ変数の並べ替えを1通りに絞る。
    Order(Vec<String>),
    /// 代表元IDの非厳密な昇順("<=")。2組の役割を丸ごと入れ替えても同じ結論になる
    /// 対称性だけを間引く(等しい割り当ては残す)。
    OrderNonStrict(Vec<String>),
    Not(Box<Pattern>),
}

impl Pattern {
    /// 事実パターンの引数(DefinedBy は親の後に結果)。制約と Not は None。
    pub fn fact_args(&self) -> Option<Vec<&String>> {
        match self {
            Pattern::Identical { a, b, .. } => Some(vec![a, b]),
            Pattern::Connected { child, parent, .. } => Some(vec![child, parent]),
            Pattern::DefinedBy { parents, result, .. } => Some(parents.iter().chain(std::iter::once(result)).collect()),
            _ => None,
        }
    }

    /// 証明の記録に残す前提の種類名。raw_proof が "DefinedBy:<種類>" の形を読む。
    pub fn premise_label(&self) -> Option<String> {
        match self {
            Pattern::Identical { .. } => Some("Identical".to_string()),
            Pattern::Connected { .. } => Some("Connected".to_string()),
            Pattern::DefinedBy { kind, .. } => Some(format!("DefinedBy:{}", kind.name())),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Construction {
    pub kind: DefKind,
    pub args: Vec<String>,
    pub bind_to: String,
}

#[derive(Debug, Clone)]
pub enum Conclusion {
    Identical(String, String),
    Connected(String, String),
}

#[derive(Debug, Clone)]
pub struct TheoremDef {
    pub name: String,
    pub entities: FxHashMap<String, EntityType>,
    pub patterns: Vec<Pattern>,
    pub constructions: Vec<Construction>,
    pub conclusions: Vec<Conclusion>,
}

/// 前提(patterns)の中で実際に照合される変数名。作図・結論にしか出てこない変数は含まない。
pub(crate) fn collect_pattern_vars<'a>(pat: &'a Pattern, out: &mut Vec<&'a str>) {
    match pat {
        Pattern::Distinct(vars) | Pattern::Order(vars) | Pattern::OrderNonStrict(vars) => {
            out.extend(vars.iter().map(|v| v.as_str()));
        }
        Pattern::Not(inner) => collect_pattern_vars(inner, out),
        _ => out.extend(pat.fact_args().into_iter().flatten().map(|v| v.as_str())),
    }
}

/// Identical(v1, v2) の v1・v2 それぞれに、同じ種類の DefinedBy がぶら下がっているか。
/// そういう定理では自己束縛の候補数がそのまま下流の分岐係数になる。
pub(crate) fn has_paired_defined_by_fanout(theorem: &TheoremDef, v1: &str, v2: &str) -> bool {
    let mut kinds_for_v1 = rustc_hash::FxHashSet::default();
    let mut kinds_for_v2 = rustc_hash::FxHashSet::default();
    for p in &theorem.patterns {
        if let Pattern::DefinedBy { kind, result, .. } = p {
            if result == v1 { kinds_for_v1.insert(*kind); }
            if result == v2 { kinds_for_v2.insert(*kind); }
        }
    }
    kinds_for_v1.intersection(&kinds_for_v2).next().is_some()
}

/// 前提で照合される変数のうち、マッチ中にその場で作られない型(Scalar 以外)。
/// このどれかの実体が図に1つも無ければ、その定理は絶対にマッチしない。
pub(crate) fn required_hard_types(theorem: &TheoremDef) -> Vec<EntityType> {
    let mut names = Vec::new();
    for pat in &theorem.patterns {
        collect_pattern_vars(pat, &mut names);
    }
    let mut out: Vec<EntityType> = names.iter()
        .filter_map(|name| theorem.entities.get(*name).copied())
        .filter(|t| *t != EntityType::Scalar)
        .collect();
    // 事前チェックの順序が実行ごとに変わらないよう、決まった順に並べる。
    out.sort_by_key(|t| format!("{:?}", t));
    out.dedup();
    out
}

/// 失敗キャッシュが「どの型の候補プールを列挙したか」を表すビット。
pub(crate) fn entity_type_bit(t: EntityType) -> u8 {
    match t {
        EntityType::Point => 0b0001,
        EntityType::Line => 0b0010,
        EntityType::Scalar => 0b0100,
        EntityType::Conic => 0b1000,
    }
}
/// 依存先を型単位で特定できない経路が安全側に倒すときのマスク。
pub(crate) const ALL_TYPES_MASK: u8 = 0b1111;
/// entity_type_bit のビット順に並べた全型。
pub(crate) const ALL_ENTITY_TYPES: [EntityType; 4] = [
    EntityType::Point,
    EntityType::Line,
    EntityType::Scalar,
    EntityType::Conic,
];

/// ALL_ENTITY_TYPES 順の type_generation の現在値。
///
/// 失敗キャッシュの有効性はこの世代の比較だけで判定するので、e-graph の構造を書き換える
/// 操作は必ず create_entity / merge_entities / link_logical_incidence / insert_memo の
/// どれかを通して世代を進めること。通さないと、無効になった失敗を再利用して
/// 本来見つかるマッチを静かに逃す。
pub(crate) fn snapshot_type_generations(egraph: &EGraph) -> [u64; 4] {
    std::array::from_fn(|i| egraph.type_generation.get(&ALL_ENTITY_TYPES[i]).copied().unwrap_or(0))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    FactProven(crate::mmp_core::Fact),
    NodeMerged,
}

#[derive(Debug, Clone)]
pub struct MatchTask {
    pub priority: i32,
    pub theorem_idx: usize,
    pub bind: Bind,
    pub flip_states: FlipStates,
    /// 証明済みの事実で変数を固定して積んだタスクか(schedule_matcher_task)、
    /// 全変数未束縛の全探索か(schedule_full_sweep)。priority は実行中に減算されるので
    /// 由来はこのフラグで持つ。バンディットは全探索の成否だけを学習する。
    pub is_seeded: bool,
}

impl PartialEq for MatchTask { fn eq(&self, other: &Self) -> bool { self.priority == other.priority } }
impl Eq for MatchTask {}
impl PartialOrd for MatchTask { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) } }
impl Ord for MatchTask { fn cmp(&self, other: &Self) -> Ordering { self.priority.cmp(&other.priority) } }

/// 定理ごとの全探索タスクの実績(UCB1 バンディットと --stats 用)。
#[derive(Debug, Clone, Copy, Default)]
pub struct TheoremBanditStats {
    pub attempts: u64,
    pub total_reward: f64,
    /// dfs_cap に達した試行の回数。
    pub cap_hits: u64,
    pub total_dfs_calls: u64,
}

impl TheoremBanditStats {
    /// 経験的な平均報酬 + 探索ボーナス。未試行なら無限大(必ず一度は試す)。
    pub(crate) fn ucb1_score(&self, total_attempts: u64, exploration_c: f64) -> f64 {
        if self.attempts == 0 { return f64::INFINITY; }
        let mean = self.total_reward / self.attempts as f64;
        let bonus = exploration_c * ((total_attempts.max(1) as f64).ln() / self.attempts as f64).sqrt();
        mean + bonus
    }
}

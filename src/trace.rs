//! 🌟 探索の「効き」を実測するための診断(--trace)。
//!
//! これまでの計測フラグは、どちらも「何に時間を使ったか」しか答えられなかった:
//!   --profile  フェーズごとの壁時計時間の内訳
//!   --stats    定理ごとのUCB1統計。ただし is_seeded=false のタスクしか
//!              数えないので、実測で仕事量の大半を占めるシード済みタスクが
//!              まるごと視界の外にある(ProfileStats のドキュメント参照)。
//!
//! ここで足すのは「使った仕事のうち、どれが証明に残ったか」という別軸の問い。
//! 1回の発火(定理の結論を実際にe-graphへ適用できた瞬間)ごとに、そのときの
//! 優先度・シード由来か・累計仕事量を記録しておき、実行後に証明を根から
//! 辿って「実際に使われたマージ/接続」の集合を作り、両者を突き合わせる。
//!
//! 突き合わせは定理名ではなくマージそのもの(無向のスロット対)で行う。
//! 同じ定理が50回発火して1回だけ証明に残ることは普通にあるので、名前で
//! 結合すると「効いた仕事量」を大幅に過大評価してしまう。
//!
//! これで次の3つが実測で言えるようになる:
//!   ① 全仕事量のうち、証明に残る発火を生んだタスクが使ったのは何%か
//!      (小さいほど、探索の大半が捨て札になっている)
//!   ② 証明に効いた発火が、実行のどのあたりで・どの優先度で起きたか
//!      (前半に固まっていれば打ち切りの問題、散らばっていれば順序の問題)
//!   ③ 証明に登場した実体が、熱で並べたときに何位にいるか
//!      (heat_cap/fanout_heat_cap の外にいるなら、絞りすぎが真因)

use rustc_hash::{FxHashMap, FxHashSet};

use crate::mmp_core::{ClassId, EGraph, EntityOrigin, EntityType, Justification};

/// 1回の「発火」= 定理の結論を実際にe-graphへ適用できた瞬間の記録。
#[derive(Debug, Clone)]
pub struct Firing {
    pub theorem: String,
    /// この発火を生んだタスクの優先度(MatchTask::priority)。UCB1の
    /// theorem_priority_bonus とシード有無で決まる、まさに「発火の順番」を
    /// 決めている値そのもの。
    pub priority: i32,
    pub is_seeded: bool,
    /// この発火の時点での累計仕事量(ProverEngine::work_done)。
    pub work_at: u64,
    /// この発火を生んだタスク1回が消費した dfs_call 数。
    pub dfs_calls_used: u64,
    /// この発火を生んだタスクの通し番号。1回のタスクが複数の結論を適用して
    /// 複数の発火になることがあるので、仕事量を足し合わせるときは必ずこれで
    /// 重複を落とす(落とさないと同じタスクの dfs_call を何度も数えてしまい、
    /// 全体を超える割合が出る)。
    pub task_seq: u64,
    /// この発火が作ったマージ(無向のスロット対)。証明との突き合わせの鍵。
    pub merges: Vec<(usize, usize)>,
    /// この発火が張った接続(無向のスロット対)。
    pub incidences: Vec<(usize, usize)>,
}

/// 発火ログ本体。ProverEngine::trace が Some のときだけ積まれる
/// (既定は None なので、診断を使わない実行には一切のコストが無い)。
#[derive(Debug, Default)]
pub struct TraceLog {
    pub firings: Vec<Firing>,
    /// いま処理中のタスクの(優先度, シード由来か)。run_step がタスクを
    /// pop するたびに書き換え、apply_conclusions が発火を記録するときに読む。
    /// 発火の記録側(prover)と、優先度を知っている側(blackboard)が別関数に
    /// 分かれているため、この1段の受け渡しが要る。
    pub current: (i32, bool),
    /// タスクの通し番号。run_step がタスクを pop するたびに1つ進める。
    pub task_seq: u64,
}

impl TraceLog {
    /// apply_conclusions から呼ぶ。1回の apply_conclusions 呼び出しが
    /// 複数の結論を適用することがあるので、まとめて1発火として記録する。
    pub fn record(&mut self, theorem: &str, work_at: u64, dfs_calls_used: u64,
                  merges: Vec<(usize, usize)>, incidences: Vec<(usize, usize)>) {
        if merges.is_empty() && incidences.is_empty() { return; }
        self.firings.push(Firing {
            theorem: theorem.to_string(),
            priority: self.current.0,
            is_seeded: self.current.1,
            work_at,
            dfs_calls_used,
            task_seq: self.task_seq,
            merges,
            incidences,
        });
    }
}

/// 無向のスロット対。マージ辺は「吸収された側のスロット番号」で一意に
/// 決まるので、順序を落とした対も同じく一意(explain_identical は読みやすさの
/// ために b 側の経路の from/to を入れ替えて返すため、順序に依存できない)。
fn key(a: ClassId, b: ClassId) -> (usize, usize) {
    if a.0 <= b.0 { (a.0, b.0) } else { (b.0, a.0) }
}

/// 証明を根から辿って集めた「実際に使われたもの」。
#[derive(Default)]
pub struct ProofSupport {
    pub merges: FxHashSet<(usize, usize)>,
    pub incidences: FxHashSet<(usize, usize)>,
    /// 証明に登場した実体の代表元。熱の順位を見るのに使う。
    pub entities: FxHashSet<usize>,
    pub theorems: Vec<String>,
    /// 由来を追い切れずに止まった箇所の数。ここが多いと、以下の集計は
    /// 「証明に効いた分」を過小評価している可能性がある。
    pub unresolved: usize,
    /// 証明に使われた根拠の種類ごとの件数(定理/合同閉包/一意性/自明/前提)。
    /// 「この証明は何でできているか」が分かると、名前付き定理が1つも
    /// 出てこない証明(作図と局所伝播だけで閉じている)を見分けられる。
    pub kinds: Vec<(&'static str, usize)>,
    /// 目標そのものが成立していたか。作図の定義だけで閉じる証明では
    /// merges/incidences がどちらも空になり得るので、「集合が空かどうか」では
    /// 到達判定にならない(実際 Concyclic の外接円はこの形になる)。
    pub reached: bool,
}

const GOAL_IDENTICAL: u8 = 0;
const GOAL_INCIDENCE: u8 = 1;
/// 🌟 「この実体が今の姿になるまでに、誰がここへ合流してきたか」を辿る目標。
/// 前提が Identical(X, X) や DefinedBy の形だと explain_identical は空を返し、
/// 一見すると自明な基底事実に見えるが、実際にはその合流こそが定理の仕事で
/// あることが多い(raw_proof.rs::build_result_ancestry_step と同じ話)。
const GOAL_ANCESTRY: u8 = 2;

/// 目標の事実から出発して、証明に実際に使われたマージ・接続・実体を集める。
///
/// EGraph::explain_identical / find_incidence_justification が返す
/// Justification を辿るだけの素直な探索で、raw_proof::verify_identical が
/// 出力テキストに対して行っているのと同じことを、生きたe-graphに対して行う。
pub fn collect_proof_support(eg: &EGraph, target: &(String, Vec<ClassId>),
                             follow_ancestry: bool) -> ProofSupport {
    let mut sup = ProofSupport::default();
    // 「誰がこの実体へ合流してきたか」の逆引き。proof_edges は吸収された側の
    // スロット番号を鍵にしているので、生き残った側からは引けない。
    let mut reverse: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
    if follow_ancestry {
        for (&absorbed, edge) in eg.proof_edges.iter() {
            reverse.entry(edge.to.0).or_default().push(absorbed);
        }
        for v in reverse.values_mut() { v.sort_unstable(); }
    }
    let mut names: FxHashSet<String> = FxHashSet::default();
    let mut kinds: FxHashMap<&'static str, usize> = FxHashMap::default();
    let mut seen: FxHashSet<(u8, usize, usize)> = FxHashSet::default();
    let mut work: Vec<(u8, ClassId, ClassId)> = Vec::new();

    let (fact_type, args) = target;
    match fact_type.as_str() {
        // 🌟 Concyclic は「N点が同じ円に乗っている」= 共通の円への接続N本。
        // proof.rs::generate_proof と同じく、まず共通の円を特定してから
        // 各点の接続の由来を辿る(ここを Identical と取り違えると、実際には
        // 別物である最初の2点を同一視しようとして証明が1件も見つからない)。
        "Concyclic" => {
            if let Some(circle) = eg.find_shared_circle(args) {
                sup.reached = true;
                sup.entities.insert(eg.get_rep(circle).0);
                for &p in args { work.push((GOAL_INCIDENCE, p, circle)); }
            }
        }
        "Connected" if args.len() >= 2 => {
            sup.reached = eg.is_connected(eg.get_rep(args[0]), eg.get_rep(args[1]));
            work.push((GOAL_INCIDENCE, args[0], args[1]));
        }
        _ if args.len() >= 2 => {
            sup.reached = eg.get_rep(args[0]) == eg.get_rep(args[1]);
            work.push((GOAL_IDENTICAL, args[0], args[1]));
        }
        _ => {}
    }

    // 安全弁: 証明の森は有限だが、接続の橋渡しで往復する可能性があるので
    // 上限を切っておく(診断なので、打ち切っても実害は集計の過小評価だけ)。
    let mut guard = 0usize;
    while let Some((kind, a, b)) = work.pop() {
        guard += 1;
        if guard > 500_000 { break; }
        let (ra, rb) = (eg.get_rep(a).0, eg.get_rep(b).0);
        let canon = if ra <= rb { (kind, ra, rb) } else { (kind, rb, ra) };
        if !seen.insert(canon) { continue; }
        sup.entities.insert(ra);
        sup.entities.insert(rb);

        if kind == GOAL_ANCESTRY {
            // 前向き: この実体が吸収されて root に向かう道。
            let mut cur = ra;
            let mut hops = 0;
            while let Some(edge) = eg.proof_edges.get(&cur) {
                hops += 1;
                if hops > 500 { break; }
                sup.merges.insert(key(ClassId(cur), edge.to));
                expand(eg, &edge.justification, ClassId(cur), edge.to,
                       &mut work, &mut names, &mut sup.unresolved, &mut kinds, follow_ancestry);
                cur = edge.to.0;
            }
            // 逆向き: 誰がこの実体へ合流してきたか。代表元はそもそも
            // proof_edges の鍵にならないので、こちらを見ないと何も出てこない。
            for &src in reverse.get(&ra).into_iter().flatten() {
                if let Some(edge) = eg.proof_edges.get(&src) {
                    sup.merges.insert(key(ClassId(src), edge.to));
                    expand(eg, &edge.justification, ClassId(src), edge.to,
                           &mut work, &mut names, &mut sup.unresolved, &mut kinds, follow_ancestry);
                }
            }
        } else if kind == GOAL_IDENTICAL {
            let edges = eg.explain_identical(a, b);
            if edges.is_empty() {
                // 同じ実体そのもの(説明すべきことが無い)なら正常。
                // 別の同値類のままなら、証明が繋がっていない。
                if ra != rb { sup.unresolved += 1; }
                continue;
            }
            for edge in edges {
                sup.merges.insert(key(edge.from, edge.to));
                sup.entities.insert(eg.get_rep(edge.from).0);
                sup.entities.insert(eg.get_rep(edge.to).0);
                expand(eg, &edge.justification, edge.from, edge.to,
                       &mut work, &mut names, &mut sup.unresolved, &mut kinds, follow_ancestry);
            }
        } else {
            match eg.find_incidence_justification(a, b) {
                Some((orig_p, orig_c, just)) => {
                    sup.incidences.insert(key(orig_p, orig_c));
                    // 記録時と違う実体経由で同じ代表元に来ている場合、その
                    // 橋渡し(a≡orig_p, b≡orig_c)も証明の一部。
                    work.push((GOAL_IDENTICAL, a, orig_p));
                    work.push((GOAL_IDENTICAL, b, orig_c));
                    expand(eg, &just, orig_p, orig_c, &mut work, &mut names, &mut sup.unresolved, &mut kinds, follow_ancestry);
                }
                // 🌟 provenance が無い接続は「作図そのものから従う」ものが
                // ほとんど(Intersection(l1,l2) で作った点は定義上 l1・l2 に
                // 乗っているし、LineThroughPoints(A,B) は定義上 A・B を通る)。
                // これは証明の穴ではなく前提なので、unresolved には数えない。
                // ただし「定義に書かれている親」と「いま接続している実体」が
                // 別物で、後から合流して同じ同値類になっただけのことがある。
                // その合流の理由まで辿らないと、点の一意性で閉じる証明が
                // 丸ごと空に見える(structural_incidence のドキュメント参照)。
                None => match structural_incidence(eg, a, b) {
                    Some(bridges) => {
                        for (p, q) in bridges { work.push((GOAL_IDENTICAL, p, q)); }
                    }
                    None => sup.unresolved += 1,
                },
            }
        }
    }

    let mut v: Vec<String> = names.into_iter().collect();
    v.sort();
    sup.theorems = v;
    sup.kinds = { let mut k: Vec<_> = kinds.into_iter().collect(); k.sort_by(|a, b| b.1.cmp(&a.1)); k };
    sup
}

/// 「x が y に乗っている」ことが、どちらかの作図の定義そのものから従うか。
///
/// 🐛 ユーザー指摘への対応: 以前はここで真偽だけを返し、真なら「前提だから
/// 追う必要なし」と打ち切っていた。しかし親との一致を見ているのは代表元
/// どうし(get_rep)なので、「定義に書かれている親そのもの」ではなく
/// 「定義に書かれている親に後から合流してきた実体」で一致していることが
/// 多い。その合流こそが定理の仕事なのに、丸ごと見落としていた
/// (orthocenter が「証明に効いた発火0件」に見えていた原因)。
///
/// そこで、一致した親(定義に書かれている側)と相手を返し、呼び出し側が
/// 「その2つがなぜ同じ同値類にいるのか」を改めて辿れるようにする。
/// 同じスロットそのものだった場合は explain_identical が空を返すだけなので、
/// 呼び出し側は何も特別扱いしなくてよい。
fn structural_incidence(eg: &EGraph, x: ClassId, y: ClassId) -> Option<Vec<(ClassId, ClassId)>> {
    let (rx, ry) = (eg.get_rep(x), eg.get_rep(y));
    let mut bridges: Vec<(ClassId, ClassId)> = Vec::new();
    let mut found = false;
    // 接続は代表元の subobjects に記録されるが、定義を持っているのは
    // その同値類に吸収された側であることもあるので、クラス全体を見る。
    for i in 0..eg.entities.len() {
        let owner = ClassId(i);
        let owner_rep = eg.get_rep(owner);
        let other_rep = if owner_rep == rx { ry } else if owner_rep == ry { rx } else { continue };
        // owner が x 側なら相手は y、y 側なら相手は x。
        let (other, same_side) = if owner_rep == rx { (y, x) } else { (x, y) };
        for p in eg.entities[i].original_definition.get_parents() {
            if eg.get_rep(p) != other_rep { continue; }
            found = true;
            // ① 相手の側の橋渡し: 定義に書かれている親 p と、いま問われている実体。
            if p != other { bridges.push((p, other)); }
            // ② 器の側の橋渡し: 定義を持っている実体 owner と、いま問われている実体。
            //    orthocenter はここが本体だった――Line_A_H_AltB_AltC は定義上
            //    H_AltB_AltC を通るが、目標の接続先はそれと合流した別の直線で、
            //    その合流(同位角による平行判定 → 直線の一意性)こそが垂心定理。
            //    ①だけ返して打ち切ると、この連鎖が丸ごと証明から消える。
            if owner != same_side { bridges.push((owner, same_side)); }
            break;
        }
    }
    if found { Some(bridges) } else { None }
}

/// 1つの Justification から、さらに遡るべき部分目標を積む。
fn expand(eg: &EGraph, j: &Justification, from: ClassId, to: ClassId,
          work: &mut Vec<(u8, ClassId, ClassId)>, names: &mut FxHashSet<String>,
          unresolved: &mut usize, kinds: &mut FxHashMap<&'static str, usize>,
          follow_ancestry: bool) {
    let kind = match j {
        Justification::Theorem { .. } => "名前付き定理",
        Justification::Congruence { .. } => "合同閉包",
        Justification::LineUniqueness { .. } => "直線の一意性",
        Justification::ConicUniqueness { .. } => "円錐曲線の一意性",
        Justification::PointUniqueness { .. } => "交点の一意性",
        Justification::Trivial { .. } => "定義から自明",
        Justification::Given => "問題の前提",
    };
    *kinds.entry(kind).or_insert(0) += 1;
    match j {
        Justification::Theorem { name, premises } => {
            names.insert(name.clone());
            for (ft, args) in premises {
                if args.is_empty() { continue; }
                match ft.as_str() {
                    "Identical" if args.len() >= 2 => {
                        work.push((GOAL_IDENTICAL, args[0], args[1]));
                        // 🌟 args[0] と args[1] が既に同じ実体だと explain_identical は
                        // 空を返し、追跡がここで止まる。しかしその実体がその姿に
                        // なったのは他の実体が合流してきたからで、多くの場合それこそが
                        // 定理の仕事(orthocenter の「同位角による平行判定」の前提が
                        // まさにこれ)。合流履歴まで辿る設定なら、そちらへ回す。
                        if follow_ancestry {
                            work.push((GOAL_ANCESTRY, args[0], args[0]));
                            work.push((GOAL_ANCESTRY, args[1], args[1]));
                        }
                    }
                    "Connected" if args.len() >= 2 => work.push((GOAL_INCIDENCE, args[0], args[1])),
                    // DefinedBy(親…, 結果)は「結果はこの定義で作られている」
                    // という構造的な前提で、遡るべき等式そのものは含まない。
                    // ただし結果の実体の合流履歴は上と同じ理由で意味を持つ。
                    _ => {
                        if follow_ancestry {
                            for &a in args { work.push((GOAL_ANCESTRY, a, a)); }
                        }
                    }
                }
            }
        }
        Justification::Congruence { .. } => {
            // 合同閉包 f(a)=f(b) if a=b。どの引数が等しかったのかは
            // Justification には残っていないが、両辺の original_definition
            // から機械的に復元できる(同じ構築子・同じ引数個数のはず)。
            // 引数は normalize_definition でソートされていることがあるので、
            // まず「既に同値なもの」同士を取り除いてから残りを順に対応づける。
            let pa = eg.entities[from.0].original_definition.get_parents();
            let pb = eg.entities[to.0].original_definition.get_parents();
            if pa.len() != pb.len() || pa.is_empty() {
                *unresolved += 1;
                return;
            }
            let mut left: Vec<ClassId> = Vec::new();
            let mut right: Vec<ClassId> = pb.clone();
            for &x in &pa {
                match right.iter().position(|&y| eg.get_rep(y) == eg.get_rep(x)) {
                    Some(i) => { right.remove(i); }
                    None => left.push(x),
                }
            }
            for (x, y) in left.into_iter().zip(right.into_iter()) {
                work.push((GOAL_IDENTICAL, x, y));
            }
        }
        Justification::LineUniqueness { shared_points }
        | Justification::ConicUniqueness { shared_points } => {
            for &p in shared_points {
                work.push((GOAL_INCIDENCE, p, from));
                work.push((GOAL_INCIDENCE, p, to));
            }
        }
        Justification::PointUniqueness { via_lines } => {
            for &l in &[via_lines.0, via_lines.1] {
                work.push((GOAL_INCIDENCE, from, l));
                work.push((GOAL_INCIDENCE, to, l));
            }
        }
        // Given / Trivial は仮定・定義から機械的に従うもので、遡る先が無い。
        Justification::Given | Justification::Trivial { .. } => {}
    }
}

/// 発火ログ1件が証明に残ったか。
fn on_proof_path(f: &Firing, sup: &ProofSupport) -> bool {
    f.merges.iter().any(|m| sup.merges.contains(m))
        || f.incidences.iter().any(|i| sup.incidences.contains(i))
}

struct Row { fires: u64, useful: u64, anc_useful: u64, work: u64, useful_work: u64, pri_sum: i64, seeded: u64 }


/// 🌟 「その場で作った図形は、本当に使われているのか」の集計(--origins)。
///
/// 動機(ユーザー要望): オンデマンド作図(resolve_*_demands)と、定理の
/// マッチングが DefinedBy パターンを満たすためにその場で作る図形は、
/// どちらも「行き詰まったら図を増やす」という賭けをしている。作った数は
/// ログに出ていたが、作ったものが実際に証明へ効いたかは一度も測れていな
/// かった。
///
/// 数え方で気を付けたのは2点:
///
/// - 直接作ったものと、その作図に付随して apply_trivial_relations が芋づる式に
///   作ったもの(方向・長さ・自動生成の直線)を分ける。補助線を1本引くと
///   何個も派生するので、混ぜると「作った数」が実態の何倍にも見える。
/// - 「証明に登場した」は代表元ではなくスロット単位で数える。代表元で数えると、
///   たまたま同じ同値類へ合流しただけの無関係な補助図形まで「証明に登場した」に
///   なってしまう(合流させること自体が目的の補助図形では、これは深刻な
///   過大評価になる)。collect_proof_support の merges/incidences は生の
///   スロット対で記録されているので、そのまま使える。
pub fn report_origins(eg: &EGraph, target: &Option<(String, Vec<ClassId>)>, problem: &str) {
    // --- 証明に実際に登場したスロット ---
    let mut in_proof: FxHashSet<usize> = FxHashSet::default();
    // 証明の手順そのもの(マージ・接続)に端点として登場したスロットだけ。
    // in_proof はこれを親方向へ閉じたものなので、両方出さないと
    // 「本当に推論に使われた」のか「ただの材料」なのかが区別できない。
    let mut in_steps: FxHashSet<usize> = FxHashSet::default();
    let mut reached = false;
    if let Some(t) = target {
        let sup = collect_proof_support(eg, t, true);
        reached = sup.reached;
        for &(a, b) in sup.merges.iter().chain(sup.incidences.iter()) {
            in_proof.insert(a);
            in_proof.insert(b);
            in_steps.insert(a);
            in_steps.insert(b);
        }
        for &id in &t.1 { in_proof.insert(id.0); }
        // 証明のステップが乗っている作図そのもの(親)も「使われた」に数える。
        // 「Pt_l1_l2 を作ったから l1∩l2 の接続が言えた」という筋を、材料側の
        // 直線まで含めて拾うため。
        let mut stack: Vec<usize> = in_proof.iter().copied().collect();
        let mut guard = 0usize;
        while let Some(i) = stack.pop() {
            guard += 1;
            if guard > 200_000 { break; }
            if i >= eg.entities.len() { continue; }
            for p in eg.entities[i].original_definition.get_parents() {
                if in_proof.insert(p.0) { stack.push(p.0); }
            }
        }
    }

    // --- マージの履歴に一度でも現れたスロット(吸収された側・吸収した側の両方) ---
    // このエンジンの進捗は全てマージか接続なので、一度もマージに関与しなかった
    // 図形は「作っただけで何も生まなかった」と言い切れる。
    let mut merged: FxHashSet<usize> = FxHashSet::default();
    for (&absorbed, edge) in eg.proof_edges.iter() {
        merged.insert(absorbed);
        merged.insert(edge.to.0);
    }

    println!("\n=== 🧱 作図の出どころ別の効き (--origins) ===");
    println!("  目標: {}", if target.is_none() { "なし(自由探索)" }
        else if reached { "到達" } else { "未到達(「証明に登場」列は参考値)" });
    println!("  {:<16} {:>6} {:>6} | {:>10} {:>6} | {:>12} {:>12} {:>6}",
        "出どころ", "直接", "付随", "マージ関与", "割合", "証明の手順", "証明の材料", "割合");

    let mut total_in_proof = 0usize;
    for &o in EntityOrigin::ALL {
        let mut direct = 0usize;
        let mut cascade = 0usize;
        let mut m = 0usize;
        let mut p = 0usize;
        let mut st = 0usize;
        for (i, e) in eg.entities.iter().enumerate() {
            if e.origin != o { continue; }
            if e.origin_cascade { cascade += 1; } else { direct += 1; }
            if merged.contains(&i) { m += 1; }
            if in_proof.contains(&i) { p += 1; }
            if in_steps.contains(&i) { st += 1; }
        }
        let n = direct + cascade;
        if n == 0 { continue; }
        total_in_proof += p;
        println!("  {:<16} {:>6} {:>6} | {:>10} {:>5.0}% | {:>12} {:>12} {:>5.0}%",
            o.label(), direct, cascade,
            m, 100.0 * m as f64 / n as f64,
            st, p, 100.0 * p as f64 / n as f64);
        // 掠えで集計するための機械可読な行(シェルから拾う)。
        println!("ORIGINS	{}	{:?}	{}	{}	{}	{}	{}	{}",
            problem, o, direct, cascade, m, st, p, reached);
    }

    // 出どころ × 定義の種類の内訳。DefinedBy 生成や角の需要は1問で数百個
    // 作るので、「どの種類を作りすぎているのか」まで割らないと、次に何を
    // 絞ればよいかが決められない。
    let mut kinds: std::collections::BTreeMap<(EntityOrigin, &'static str), (usize, usize, usize)> =
        std::collections::BTreeMap::new();
    for (i, e) in eg.entities.iter().enumerate() {
        if e.origin == EntityOrigin::Given || e.origin_cascade { continue; }
        let k = kinds.entry((e.origin, e.original_definition.get_type_name())).or_insert((0, 0, 0));
        k.0 += 1;
        if merged.contains(&i) { k.1 += 1; }
        if in_steps.contains(&i) { k.2 += 1; }
    }
    if !kinds.is_empty() {
        println!("  -- 直接作ったものの種類別 (作った / マージ関与 / 証明の手順) --");
        for (&(o, ty), &(n, m, st)) in &kinds {
            println!("    {:<14} {:<26} {:>5} {:>5} {:>5}", o.label(), ty, n, m, st);
            println!("ORIGINKIND\t{}\t{:?}\t{}\t{}\t{}\t{}\t{}", problem, o, ty, n, m, st, reached);
        }
    }

    // 証明に登場した「その場で作った図形」を実名で挙げる。数字だけだと
    // 「何が効いたのか」が分からず、次に何を強化すべきか判断できない。
    if reached && total_in_proof > 0 {
        let mut named: Vec<&str> = eg.entities.iter().enumerate()
            .filter(|(i, e)| e.origin != EntityOrigin::Given && !e.origin_cascade && in_proof.contains(i))
            .map(|(_, e)| e.original_name.as_str())
            .collect();
        named.sort_unstable();
        named.dedup();
        if named.is_empty() {
            println!("  証明に効いた「その場の作図」: なし(問題文の図形だけで閉じている)");
        } else {
            println!("  証明に効いた「その場の作図」({}件): {}", named.len(),
                named.iter().take(12).cloned().collect::<Vec<_>>().join(", "));
        }
    }
    println!("=============================\n");
}

pub fn report(eg: &EGraph, log: &TraceLog, target: &Option<(String, Vec<ClassId>)>,
              total_work: u64, heat_cap: usize, fanout_heat_cap: usize) {
    println!("\n=== 🔬 発火と証明への寄与 (--trace) ===");
    if log.firings.is_empty() {
        println!("  発火が1件もありませんでした。");
        println!("=============================\n");
        return;
    }

    // 🌟 2通りで集める。
    //   厳密: 証明の説明経路に直接現れたマージ/接続だけ(下界)。
    //   合流込み: 前提が「既に同じ実体」だったときに、その実体へ誰が合流して
    //             きたかまで辿ったもの(上界)。raw_proof.rs が同じ近似を
    //             使っており、この特定の前提と無関係な合流が混ざり得る。
    // orthocenter のように、証明の本体が「前提の実体が既に合流済みである
    // こと」そのものに隠れている問題があるので、片方だけでは判断を誤る。
    let sup = match target {
        Some(t) => collect_proof_support(eg, t, false),
        None => ProofSupport::default(),
    };
    let sup_anc = match target {
        Some(t) => collect_proof_support(eg, t, true),
        None => ProofSupport::default(),
    };
    let have_proof = sup.reached;

    // --- ① 定理ごとの発火と、そのうち証明に残った数 -------------------
    // 🌟 仕事量は必ずタスク単位で数える。1回のタスクが複数の結論を適用して
    // 複数の発火になることがあり、発火ごとに dfs_calls_used を足すと同じ
    // タスクの仕事を何度も数えてしまう(実測で全体の182%という値が出た)。
    let mut counted_task: FxHashSet<u64> = FxHashSet::default();
    let mut useful_tasks: FxHashSet<u64> = FxHashSet::default();
    let mut per: FxHashMap<&str, Row> = FxHashMap::default();
    let (mut total_useful, mut useful_work, mut fired_work) = (0u64, 0u64, 0u64);
    let mut anc_useful = 0u64;
    let mut anc_work_tasks: FxHashSet<u64> = FxHashSet::default();
    let mut anc_work = 0u64;
    for f in &log.firings {
        let good = have_proof && on_proof_path(f, &sup);
        if have_proof && on_proof_path(f, &sup_anc) {
            anc_useful += 1;
            if anc_work_tasks.insert(f.task_seq) { anc_work += f.dfs_calls_used; }
        }
        let first_of_task = counted_task.insert(f.task_seq);
        let r = per.entry(f.theorem.as_str())
            .or_insert(Row { fires: 0, useful: 0, anc_useful: 0, work: 0, useful_work: 0, pri_sum: 0, seeded: 0 });
        r.fires += 1;
        if have_proof && on_proof_path(f, &sup_anc) { r.anc_useful += 1; }
        r.pri_sum += f.priority as i64;
        if f.is_seeded { r.seeded += 1; }
        if first_of_task {
            r.work += f.dfs_calls_used;
            fired_work += f.dfs_calls_used;
        }
        if good {
            r.useful += 1;
            total_useful += 1;
            if useful_tasks.insert(f.task_seq) {
                r.useful_work += f.dfs_calls_used;
                useful_work += f.dfs_calls_used;
            }
        }
    }

    let pct = |x: u64, y: u64| -> f64 { if y > 0 { 100.0 * x as f64 / y as f64 } else { 0.0 } };
    println!("  発火 {}件 / 仕事量 {} ステップ", log.firings.len(), total_work);
    if have_proof {
        println!("  うち証明に残った発火 : {}件 ({:.1}%) / 合流履歴まで含めると {}件 ({:.1}%)",
            total_useful, pct(total_useful, log.firings.len() as u64),
            anc_useful, pct(anc_useful, log.firings.len() as u64));
        println!("  証明に残った発火を生んだタスクの仕事量 : {} ({:.2}% of 全体) / 合流履歴まで {} ({:.2}%)",
            useful_work, pct(useful_work, total_work), anc_work, pct(anc_work, total_work));
        println!("  発火したタスク全体の仕事量             : {} ({:.2}% of 全体)", fired_work, pct(fired_work, total_work));
        println!("    -> 残りの {:.2}% は、一度も結論を適用できなかったタスクが使った分。",
            100.0 - pct(fired_work, total_work));
        println!("  証明に使われたマージ {}件 / 接続 {}件 / 実体 {}個 / 定理 {}種",
            sup.merges.len(), sup.incidences.len(), sup.entities.len(), sup.theorems.len());
        println!("  合流履歴まで含めると  マージ {}件 / 接続 {}件 / 実体 {}個 / 定理 {}種",
            sup_anc.merges.len(), sup_anc.incidences.len(), sup_anc.entities.len(), sup_anc.theorems.len());
        if !sup_anc.theorems.is_empty() {
            println!("  合流履歴まで含めた定理 : {}", sup_anc.theorems.join(", "));
        }
        if !sup.kinds.is_empty() {
            let parts: Vec<String> = sup.kinds.iter().map(|(k, n)| format!("{} {}件", k, n)).collect();
            println!("  証明の根拠の内訳 : {}", parts.join(" / "));
        }
        if sup.unresolved > 0 {
            println!("  ⚠️ 由来を辿り切れなかった箇所が {}件あります(以下の集計は過小評価の可能性)。", sup.unresolved);
        }
    } else {
        println!("  (目標に到達していないため、証明との突き合わせはできません。発火の内訳だけ表示します。)");
    }

    let mut rows: Vec<(&str, &Row)> = per.iter().map(|(k, v)| (*k, v)).collect();
    rows.sort_by(|a, b| (b.1.useful, b.1.anc_useful, b.1.fires).cmp(&(a.1.useful, a.1.anc_useful, a.1.fires)));
    println!("\n  --- 定理ごとの発火(証明に残った数の多い順、上位20件) ---");
    println!("  {:>6} {:>6} {:>8} {:>10} {:>10} {:>8} {:>6}  定理", "発火", "有効", "合流込", "仕事量", "有効分", "平均優先", "シード");
    for (name, r) in rows.iter().take(20) {
        println!("  {:>6} {:>6} {:>8} {:>10} {:>10} {:>+8.1} {:>5.0}%  {}",
            r.fires, r.useful, r.anc_useful, r.work, r.useful_work,
            r.pri_sum as f64 / r.fires as f64,
            100.0 * r.seeded as f64 / r.fires as f64,
            name);
    }
    if rows.len() > 20 { println!("  ... 他 {}種", rows.len() - 20); }

    // --- ② 証明に効いた発火が、実行のどのあたりで起きたか ---------------
    if have_proof {
        println!("\n  --- 証明に効いた発火の時点(発火順) ---");
        let mut shown = 0;
        let mut first_pos = 100.0f64;
        let mut last_pos = 0.0f64;
        for (i, f) in log.firings.iter().enumerate() {
            if !on_proof_path(f, &sup) { continue; }
            last_pos = pct(f.work_at, total_work);
            if shown == 0 { first_pos = last_pos; }
            if shown < 25 {
                println!("    発火#{:<4} 仕事量 {:>9} ({:>5.1}%) 優先度{:>+3} {} : {}",
                    i + 1, f.work_at, last_pos, f.priority,
                    if f.is_seeded { "シード" } else { "全探索" }, f.theorem);
            }
            shown += 1;
        }
        if shown > 25 { println!("    ... 他 {}件", shown - 25); }
        if shown > 0 {
            println!("    -> 証明に効いた発火は全仕事量の {:.1}% 〜 {:.1}% の区間にある。", first_pos, last_pos);
            if last_pos < 60.0 {
                println!("       残り {:.1}% は証明が出揃った後の探索。打ち切り/目標検知の側に伸びしろがある。", 100.0 - last_pos);
            } else if first_pos > 60.0 {
                println!("       必要な発火が終盤に偏っている。それまでの {:.1}% は、証明に要る定理が選ばれないまま使われた分。順序付け(優先度/シード)に伸びしろがある。", first_pos);
            } else {
                println!("       実行全体に散らばっている。順序付けより、連鎖そのものの長さが支配的。");
            }
        }
    }

    // --- ③ ヒューリスティックのパラメータが実際どうなっているか ---------
    println!("\n  --- 証明に登場した実体のヒューリスティック値 ---");
    if !have_proof {
        println!("  (証明が無いので比較できません。)");
        println!("=============================\n");
        return;
    }

    // heat_cap による絞り込みは「同じ型の中で heat() の降順に並べて上位N件」
    // という形(cost.rs の heat_capped_* / matcher.rs の自己束縛ソート)なので、
    // 順位も同じ土俵、すなわち型ごと・heat()降順で数える。
    // 熱には2つの式がある(GeoEntity::heat / heat_with_degree)。cap の
    // 絞り込みは次数抜きの heat() を使っているので、両方の順位を
    // 並べて「どちらで並べる方が証明に要る実体を上に持ち上げるか」を
    // その場で見比べられるようにする。
    // 🌟 ユーザー指摘「次数は低いほどうれしいから熱から次数を引くべきでは」
    // への対応。ここで言う次数は uses.len()(参照数。heat_with_degree が
    // 足している方)ではなく、動点法の代数的な次数(EGraph::cached_degree)。
    // 低次数ほど単純で扱いやすいので、符号は負で入るのが自然なはず
    // ――それを順位で確かめられるよう、3つの並べ方を同じ土俵で比べる。
    const DEGREE_MAX_D: usize = 6;
    const DEGREE_WEIGHT: f64 = 0.5;
    let score_of = |i: usize, mode: u8| -> f64 {
        match mode {
            1 => eg.entities[i].heat_with_degree(),
            2 => eg.entities[i].heat()
                 - DEGREE_WEIGHT * eg.cached_degree(ClassId(i), DEGREE_MAX_D).unwrap_or(0) as f64,
            // 熱を全く動かさず、同点のときだけ低次数を先にする辞書式。
            // 熱の刻みは 1.5 単位、次数は高々 DEGREE_MAX_D なので、
            // 熱を1000倍しておけば次数が熱の順序を覆すことはあり得ない。
            3 => eg.entities[i].heat() * 1000.0
                 - eg.cached_degree(ClassId(i), DEGREE_MAX_D).unwrap_or(0) as f64,
            // 逆向きの同点処理(高次数を先に)。低次数優先が効くのかどうかを
            // 片側だけ見ても判断できないので、必ず両方を並べて出す。
            4 => eg.entities[i].heat() * 1000.0
                 + eg.cached_degree(ClassId(i), DEGREE_MAX_D).unwrap_or(0) as f64,
            _ => eg.entities[i].heat(),
        }
    };
    let rank_of = |ty: EntityType, mode: u8| -> (usize, Vec<usize>) {
        let mut pool: Vec<(usize, f64)> = (0..eg.entities.len())
            .filter(|&i| eg.get_rep(ClassId(i)).0 == i)
            .filter(|&i| eg.entities[i].entity_type == ty && eg.entities[i].is_active())
            .map(|i| (i, score_of(i, mode)))
            .collect();
        pool.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        let n = pool.len();
        let ranks = pool.iter().enumerate()
            .filter(|(_, (i, _))| sup.entities.contains(i))
            .map(|(r, _)| r + 1)
            .collect();
        (n, ranks)
    };
    let types = [EntityType::Point, EntityType::Line, EntityType::Scalar, EntityType::Conic];
    let mut sums = [0usize; 5];
    let mut over_fan_counts = [0usize; 5];
    let mut n_ranked = 0usize;
    for ty in types {
        let (n, ranks) = rank_of(ty, 0);
        if n == 0 { continue; }
        if ranks.is_empty() {
            println!("  {:?}: 全{}個中、証明に登場したものは無し", ty, n);
            continue;
        }
        let (_, ranks_uses) = rank_of(ty, 1);
        let (_, ranks_deg) = rank_of(ty, 2);
        let (_, ranks_tie) = rank_of(ty, 3);
        let (_, ranks_tie_hi) = rank_of(ty, 4);
        let over_heat = ranks.iter().filter(|&&r| r > heat_cap).count();
        let shown: Vec<String> = ranks.iter().take(20)
            .map(|&r| if r > heat_cap { format!("{}*", r) } else { r.to_string() })
            .collect();
        println!("  {:?}: 全{}個中{}個が証明に登場。heat()の順位 = {}{}",
            ty, n, ranks.len(), shown.join(", "),
            if ranks.len() > 20 { ", ..." } else { "" });
        println!("        heat_cap={} の外 : {}個", heat_cap, over_heat);
        for (m, rs) in [&ranks, &ranks_uses, &ranks_deg, &ranks_tie, &ranks_tie_hi].iter().enumerate() {
            sums[m] += rs.iter().sum::<usize>();
            over_fan_counts[m] += rs.iter().filter(|&&r| r > fanout_heat_cap).count();
        }
        n_ranked += ranks.len();
    }
    if n_ranked > 0 {
        let avg = |m: usize| sums[m] as f64 / n_ranked as f64;
        println!("  証明に要る実体の平均順位(小さいほど良い並べ方):");
        println!("    heat()                   = {:>5.1} / fanout_heat_cap={} の外 {}個", avg(0), fanout_heat_cap, over_fan_counts[0]);
        println!("    heat() + 参照数*0.5      = {:>5.1} / fanout_heat_cap={} の外 {}個", avg(1), fanout_heat_cap, over_fan_counts[1]);
        println!("    heat() - 代数的次数*{:.1}  = {:>5.1} / fanout_heat_cap={} の外 {}個", DEGREE_WEIGHT, avg(2), fanout_heat_cap, over_fan_counts[2]);
        println!("    heat()→同点なら低次数   = {:>5.1} / fanout_heat_cap={} の外 {}個", avg(3), fanout_heat_cap, over_fan_counts[3]);
        println!("    heat()→同点なら高次数   = {:>5.1} / fanout_heat_cap={} の外 {}個", avg(4), fanout_heat_cap, over_fan_counts[4]);
        let best = (0..5).min_by_key(|&m| sums[m]).unwrap_or(0);
        println!("    -> この問題で最も上に持ち上げるのは {}",
            ["heat()", "heat() + 参照数", "heat() - 代数的次数", "heat()→同点なら低次数", "heat()→同点なら高次数"][best]);
    }

    // 熱・参照数・退化関係の生の値も、証明に登場したものと全体とで比べる。
    let stat = |pick: &dyn Fn(usize) -> bool| -> (f64, f64, f64, f64, usize) {
        let (mut n, mut heat, mut uses, mut degen) = (0usize, 0.0f64, 0.0f64, 0usize);
        let (mut deg_sum, mut deg_n) = (0usize, 0usize);
        for i in 0..eg.entities.len() {
            if eg.get_rep(ClassId(i)).0 != i { continue; }
            if !eg.entities[i].is_active() { continue; }
            if !pick(i) { continue; }
            n += 1;
            heat += eg.entities[i].heat();
            uses += eg.entities[i].uses.len() as f64;
            if let Some(d) = eg.cached_degree(ClassId(i), DEGREE_MAX_D) { deg_sum += d; deg_n += 1; }
            if let Some(rel) = &eg.degeneration_groups {
                degen += rel.members_of(ClassId(i)).len();
            }
        }
        if n == 0 { return (0.0, 0.0, 0.0, 0.0, 0); }
        let deg_avg = if deg_n > 0 { deg_sum as f64 / deg_n as f64 } else { 0.0 };
        (heat / n as f64, uses / n as f64, deg_avg, degen as f64 / n as f64, n)
    };
    let (h_all, u_all, g_all, d_all, n_all) = stat(&|_| true);
    let (h_pr, u_pr, g_pr, d_pr, n_pr) = stat(&|i| sup.entities.contains(&i));
    println!("\n  {:<12} {:>6} {:>8} {:>10} {:>12} {:>14}", "", "実体数", "平均熱", "平均参照数", "平均代数的次数", "平均退化関係数");
    println!("  {:<12} {:>6} {:>8.2} {:>10.2} {:>12.2} {:>14.2}", "全体", n_all, h_all, u_all, g_all, d_all);
    println!("  {:<12} {:>6} {:>8.2} {:>10.2} {:>12.2} {:>14.2}", "証明に登場", n_pr, h_pr, u_pr, g_pr, d_pr);
    if eg.degeneration_groups.is_none() {
        println!("  (退化関係は未計算です。--degen-heat を付けると計算されます。)");
    }
    if h_pr > h_all * 1.2 {
        println!("  -> 熱は効いている(証明に要る実体の方が明確に熱い)。");
    } else if h_pr < h_all {
        println!("  -> ⚠️ 証明に要る実体の方が平均的に冷たい。熱は今の形では効いていない。");
    } else {
        println!("  -> 熱の差は小さい。今の熱の式では証明に要る実体をほとんど区別できていない。");
    }
    println!("=============================\n");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mmp_core::Definition;

    /// 🌟 突き合わせの核: 証明を根から辿って「実際に使われたマージ」を
    /// 集められること、そしてそこに使われていない発火を取り違えないこと。
    /// この2つが崩れると --trace の数字は全部意味を失う。
    #[test]
    fn proof_support_finds_the_merge_that_the_target_actually_used() {
        let mut eg = EGraph::new();
        let a = eg.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let b = eg.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let c = eg.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
        let d = eg.create_entity("D".into(), Definition::FreePoint, EntityType::Point);

        // 目標に使うマージ(定理X)と、使わないマージ(定理Y)を1つずつ作る。
        eg.merge_entities_justified(a, b, Justification::Theorem {
            name: "定理X".into(), premises: Vec::new() });
        eg.merge_entities_justified(c, d, Justification::Theorem {
            name: "定理Y".into(), premises: Vec::new() });

        let sup = collect_proof_support(&eg, &("Identical".to_string(), vec![a, b]), false);
        assert_eq!(sup.theorems, vec!["定理X".to_string()],
            "目標A≡Bの証明に使われたのは定理Xだけのはず");

        let used = Firing {
            theorem: "定理X".into(), priority: 0, is_seeded: false, work_at: 0,
            dfs_calls_used: 1, task_seq: 1,
            merges: vec![key(a, b)], incidences: Vec::new(),
        };
        let unused = Firing {
            theorem: "定理Y".into(), priority: 0, is_seeded: false, work_at: 0,
            dfs_calls_used: 1, task_seq: 2,
            merges: vec![key(c, d)], incidences: Vec::new(),
        };
        assert!(on_proof_path(&used, &sup));
        assert!(!on_proof_path(&unused, &sup),
            "同じ実行の中の無関係なマージを証明に数えてはいけない");
    }

    /// 🌟 作図の定義そのものから従う接続(Intersectionで作った点が、その2直線に
    /// 乗っていること)は前提であって、定理が証明したものではない。ここを
    /// 「由来不明」と数えると、点の一意性で閉じる証明が丸ごと追えなくなる。
    #[test]
    fn incidences_implied_by_the_construction_are_treated_as_premises() {
        let mut eg = EGraph::new();
        let a = eg.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let b = eg.create_entity("B".into(), Definition::FreePoint, EntityType::Point);
        let l = eg.create_entity("L".into(), Definition::new_line(a, b), EntityType::Line);
        assert!(structural_incidence(&eg, a, l).is_some(), "直線L=AB は定義上Aを通る");
        assert!(structural_incidence(&eg, b, a).is_none(), "自由点どうしに構造的な接続は無い");

        // 🌟 「定義に書かれている親」ではなく「そこへ後から合流した実体」で
        // 接続が成立している場合、その合流を橋渡しとして返すこと。
        // これを返さないと、合流を生んだ定理の発火が証明から漏れる。
        let c = eg.create_entity("C".into(), Definition::FreePoint, EntityType::Point);
        eg.merge_entities_justified(a, c, Justification::Theorem {
            name: "点の橋渡しの定理".into(), premises: Vec::new() });
        let bridges = structural_incidence(&eg, c, l).expect("Cはaと同値なのでL上にある");
        assert!(bridges.iter().any(|&(p, q)| eg.get_rep(p) == eg.get_rep(a) && eg.get_rep(q) == eg.get_rep(c)),
            "点の側の橋渡し(定義に書かれた親 A と、問われている C)が要る");
    }

    /// 🌟 orthocenter の検証で判明した取りこぼしの回帰テスト。点が乗っている
    /// のは「定義上その点を通る直線」ではなく、それと後から合流した別の直線。
    /// 器の側の合流を返さないと、合流を生んだ定理が証明から丸ごと消える。
    #[test]
    fn the_container_side_merge_is_also_part_of_the_proof() {
        let mut eg = EGraph::new();
        let a = eg.create_entity("A".into(), Definition::FreePoint, EntityType::Point);
        let h = eg.create_entity("H".into(), Definition::FreePoint, EntityType::Point);
        let p = eg.create_entity("P".into(), Definition::FreePoint, EntityType::Point);
        // L1 は定義上 H を通る。L2 は通らない。
        let l1 = eg.create_entity("L1".into(), Definition::new_line(a, h), EntityType::Line);
        let l2 = eg.create_entity("L2".into(), Definition::new_line(a, p), EntityType::Line);
        eg.merge_entities_justified(l1, l2, Justification::Theorem {
            name: "直線の橋渡しの定理".into(), premises: Vec::new() });

        let bridges = structural_incidence(&eg, h, l2).expect("HはL1上にあり、L1はL2と同値");
        assert!(bridges.iter().any(|&(x, y)| {
                let (rx, ry) = (eg.get_rep(x), eg.get_rep(y));
                rx == ry && (x == l1 || y == l1) && (x == l2 || y == l2)
            }),
            "器の側の橋渡し(L1 と L2 の合流)が返らないと、その合流を生んだ定理が追えない");
    }
}

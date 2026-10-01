//! 🌟 代数的な追跡(AR、`--ar`): 複比と有向角の等式を、形式的な対数の線形代数でまとめて閉じる。
//!
//! 同じ直線の上の2点 X, Y の「差」を形式的な記号 s(X,Y) とすると(s(Y,X) = −s(X,Y))、評価器の複比
//! (A,B;C,D) = τ_C/τ_D は s(A,C)·s(D,B) / (s(C,B)·s(A,D)) と書ける(基準点 R を取った行列式 [XYR] が実際の値)。
//! 有向角は虚円点との複比 (I,J;D1,D2)、線束の複比は方向の点の複比なので、どれも無限遠直線を含む直線の上の
//! 点の複比として同じ形に載る。形式的な対数を取ると、複比の積・商の関係は記号の整数係数の和になる。
//! 数値の対数は計算しない(離散対数は要らない)。
//!
//! 係数は ℤ で持つ: 有向角は mod π なので、2θ₁ = 2θ₂ から θ₁ = θ₂ は出ない(割り算をすると健全でない)。
//! 向きの入れ替え(−1)・直角(−1)・虚円点で出る ±i は、ねじれの座標 T(4倍すると0)で持つ ― ℤⁿ ⊕ ℤ/4。
//! 等式の集合を整数の格子(エルミート標準形)に積み、各同値類の記号の式を正準な剰余に還元して、剰余が同じ
//! 同値類どうしを併合する。証明の前提には、その差を消すのに使った等式(同値類の中の2つの定義の一致)を記録する。
//!
//! 各定義を記号の式に写したら、固定座標でその式の値(行列式の積)と定義の値が一致することを確かめ、一致した
//! ものだけを使う(向きの約束の取り違えや、共点でない4直線の線束の複比などを弾く)。値の定まらない記号
//! (重なった2点の差)を含む定義も使わない(非退化条件)。

use std::collections::BTreeMap;
use std::ops::Bound::{Excluded, Unbounded};

use rustc_hash::FxHashMap;

use super::BlackboardEngine;
use crate::mmp_core::{ClassId, Definition, EGraph, EntityOrigin, EntityType, Justification};
use crate::mmp_math::ModInt;

/// 行演算を仕事量に数えるときの割り算(ar_round のコメント参照)。
const AR_OPS_PER_WORK: u64 = 4;
/// 1回の追跡で相似・対応する点に使う行演算の上限(超えたらそこで足すのをやめる。決定的)。図が大きいと行が長くなり、
/// 相似の組の等式を入れるだけで1回に数十秒かかった(hageo:2020RMMSLG3 で 600万回・40秒)。
const AR_ROUND_OPS_CAP: u64 = 400_000;

/// ねじれの座標(4倍すると0)。列の中で最後に来るよう最大値にする。
const T: u32 = u32::MAX;

type SVec = BTreeMap<u32, i64>;

fn add_scaled(v: &mut SVec, r: &SVec, k: i64) -> Option<()> {
    if k == 0 { return Some(()); }
    for (&c, &x) in r {
        let e = v.entry(c).or_insert(0);
        *e = e.checked_add(x.checked_mul(k)?)?;
        if *e == 0 { v.remove(&c); }
    }
    Some(())
}

fn scaled(v: &SVec, k: i64) -> Option<SVec> {
    let mut out = SVec::new();
    for (&c, &x) in v { let y = x.checked_mul(k)?; if y != 0 { out.insert(c, y); } }
    Some(out)
}

fn union(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() || j < b.len() {
        let x = match (a.get(i), b.get(j)) {
            (Some(&x), Some(&y)) if x == y => { i += 1; j += 1; x }
            (Some(&x), Some(&y)) if x < y => { i += 1; x }
            (Some(_), Some(&y)) => { j += 1; y }
            (Some(&x), None) => { i += 1; x }
            (None, Some(&y)) => { j += 1; y }
            (None, None) => unreachable!(),
        };
        out.push(x);
    }
    out
}

/// 拡張ユークリッド: (g, x, y) で x·a + y·b = g > 0。
fn egcd(a: i64, b: i64) -> (i64, i64, i64) {
    let (mut r0, mut r1, mut s0, mut s1, mut t0, mut t1) = (a, b, 1i64, 0i64, 0i64, 1i64);
    while r1 != 0 {
        let q = r0.div_euclid(r1);
        (r0, r1) = (r1, r0 - q * r1);
        (s0, s1) = (s1, s0 - q * s1);
        (t0, t1) = (t1, t0 - q * t1);
    }
    if r0 < 0 { (-r0, -s0, -t0) } else { (r0, s0, t0) }
}

/// 整数の格子(行はエルミート標準形の階段、主成分は正)。各行は、どの等式から作ったか(出どころ)を持つ。
#[derive(Default, Clone)]
struct Lattice {
    rows: BTreeMap<u32, (SVec, Vec<u32>)>,
    /// 行の組み合わせの回数(仕事量に数える)。
    ops: u64,
}

impl Lattice {
    fn insert(&mut self, mut v: SVec, mut src: Vec<u32>) -> Option<()> {
        loop {
            let Some((&c, &b)) = v.iter().next() else { return Some(()) };
            let Some((row, rsrc)) = self.rows.get(&c).cloned() else {
                if b < 0 { v = scaled(&v, -1)?; }
                self.rows.insert(c, (v, src));
                return Some(());
            };
            self.ops += 1;
            let a = row[&c];
            if b % a == 0 {
                add_scaled(&mut v, &row, -(b / a))?;
                src = union(&src, &rsrc);
            } else {
                let (g, x, y) = egcd(a, b);
                let mut new_row = scaled(&row, x)?;
                add_scaled(&mut new_row, &v, y)?;
                let mut rest = scaled(&v, a / g)?;
                add_scaled(&mut rest, &row, -(b / g))?;
                let both = union(&src, &rsrc);
                self.rows.insert(c, (new_row, both.clone()));
                v = rest;
                src = both;
            }
        }
    }

    /// 正準な剰余(主成分の列を 0 ≤ v[c] < 主成分 に揃える)と、使った行の出どころ。
    fn reduce(&mut self, v: &SVec) -> Option<(SVec, Vec<u32>)> {
        let mut v = v.clone();
        let mut src: Vec<u32> = Vec::new();
        let mut from: Option<u32> = None;
        loop {
            let next = match from { None => v.iter().next(), Some(c) => v.range((Excluded(c), Unbounded)).next() }
                .map(|(&c, &x)| (c, x));
            let Some((c, x)) = next else { break };
            if let Some((row, rsrc)) = self.rows.get(&c) {
                let q = x.div_euclid(row[&c]);
                if q != 0 {
                    self.ops += 1;
                    add_scaled(&mut v, row, -q)?;
                    src = union(&src, rsrc);
                }
            }
            from = Some(c);
        }
        Some((v, src))
    }

    /// reduce と同じ剰余を、記号1つずつの剰余(cache に溜める)の和をもう一度簡約して求める。格子を変えない間に
    /// 同じ記号を含む式をたくさん簡約するとき用。出どころは返さない(記号ごとの出どころの和は大きすぎて証明が膨らむ)
    /// ので、使うと決めた式だけ reduce で出どころを取り直す。
    fn reduce_cached(&mut self, v: &SVec, cache: &mut FxHashMap<u32, SVec>) -> Option<SVec> {
        let mut acc = SVec::new();
        for (&c, &x) in v {
            if !cache.contains_key(&c) {
                let (r, _) = self.reduce(&SVec::from([(c, 1)]))?;
                cache.insert(c, r);
            }
            add_scaled(&mut acc, &cache[&c], x)?;
        }
        Some(self.reduce(&acc)?.0)
    }

    /// 2つの格子が同じか: 主成分の列と値が同じで、self の行が全て other で 0 に還元される(指数が 1 になる)。
    fn same_span(&self, other: &mut Lattice) -> Option<bool> {
        if self.rows.len() != other.rows.len() || self.rows.iter().zip(other.rows.iter()).any(|((c, (r, _)), (d, (q, _)))| c != d || r[c] != q[d]) {
            return Some(false);
        }
        for (row, _) in self.rows.values() {
            if !other.reduce(row)?.0.is_empty() { return Some(false); }
        }
        Some(true)
    }
}

/// 記号の番号の端(実体・等方線束の要素)が指す実体。
fn entity_of(x: usize) -> ClassId {
    if x >= ISO_I_BASE { ClassId(x - ISO_I_BASE) } else if x >= ISO_J_BASE { ClassId(x - ISO_J_BASE) } else { ClassId(x) }
}

/// 相似 σ(番号 id、opposite は裏返し)で (A,B) が (A2,B2) に移るという2つの等式:
/// s(JA2,JB2) − s(JA,JB) − log a = 0 と、I の線束での同じ式(裏返しは I と J を入れ替える)。
fn sim_relations(atoms: &mut Atoms, a: ClassId, b: ClassId, a2: ClassId, b2: ClassId, opposite: bool, id: usize) -> Vec<SVec> {
    let maps: [(u8, fn(ClassId) -> usize, fn(ClassId) -> usize); 2] = if opposite {
        [(SIM_J, iso_i, iso_j), (SIM_I, iso_j, iso_i)]
    } else {
        [(SIM_J, iso_j, iso_j), (SIM_I, iso_i, iso_i)]
    };
    let mut out = Vec::new();
    for (kind, src_iso, dst_iso) in maps {
        let mut v = SVec::new();
        let ok = atoms.add(&mut v, dst_iso(a2), dst_iso(b2), 1).and_then(|_| atoms.add(&mut v, src_iso(a), src_iso(b), -1))
            .and_then(|_| atoms.add_fresh(&mut v, (kind, id, 0, 0), -1));
        if ok.is_some() { out.push(v); }
    }
    out
}

/// AR の規則の一覧(Atlas §07 の「代数的な追跡の規則」の元。`geom_solver theorem-atlas` が書き出す)。
/// kind は「等式」(図の状況から格子に関係式を足す)・「検出」(格子で式が 0 に還元されたら e-graph に結論を入れる)・
/// 「検出→等式」(検出してから関係式を足す、線形でない一歩を含むもの)。規則を足したらここにも足す。
pub(crate) struct ArRule {
    pub kind: &'static str,
    pub name: &'static str,
    pub situation: &'static str,
    pub relation: &'static str,
    pub ledger: &'static str,
}

pub(crate) const AR_RULES: &[ArRule] = &[
    ArRule { kind: "等式", name: "定義の翻訳(有向角・複比)",
        situation: "同値類にある AnglePair(D1,D2)・CrossRatio(A,B,C,D)・CrossRatioOfLines の定義(固定座標で写像を確かめたもの)",
        relation: "(A,B;C,D) = s(A,C) + s(D,B) − s(C,B) − s(A,D)、有向角は虚円点との複比 (I,J;D1,D2)。同じ同値類の2つの定義の式は等しい", ledger: "82" },
    ArRule { kind: "等式", name: "定義の翻訳(長さ)",
        situation: "同値類にある LengthSq(X,Y)・Product(a,b) の定義",
        relation: "LengthSq(X,Y) = s(JX,JY) + s(IX,IY)(虚円点 J・I からの線束の要素の差)、積は和", ledger: "85" },
    ArRule { kind: "等式", name: "中点・調和共役の比",
        situation: "Midpoint(A,B) = M(A,B,M を通る直線がある)、HarmonicConjugateOf(A,B,C) = D",
        relation: "(A,B;M,∞) = −1、s(A,B) = s(A,M) + log 2、(A,B;C,D) = −1", ledger: "82・84" },
    ArRule { kind: "等式", name: "アフィンの等式",
        situation: "直線 L の上の2点 X, Y",
        relation: "s(X,∞_L) = s(Y,∞_L)(z = 1 の座標で無限遠点までの差が一定。無限遠点との複比が本物の比になる)", ledger: "84" },
    ArRule { kind: "等式", name: "地図の等式(直線と等方線束)",
        situation: "直線 m の上の2点 X, Y",
        relation: "s(JX,JY) − s(X,Y) = κ_J(m)、κ_J(m) − κ_I(m) = β(m の方向) + 定数(直線の上の比と方向の角をつなぐ)", ledger: "85" },
    ArRule { kind: "等式", name: "二次曲線(シュタイナー・円周角・接弦)",
        situation: "二次曲線 C の上の点 P と、C の上の点 X への直線 PX(X = P なら接線)。円では I・J も C の点として入れる(P から I への方向は I)",
        relation: "s(d_X,d_Y) = s_C(X,Y) + μ_P(X) + μ_P(Y) + κ_P(線束は曲線の媒介変数の一次分数変換)。円は I・J を動かさないのでこの対応が定数倍になり、β(PX) = θ_C(P) + θ_C(X) + c_C・接線 β = 2θ_C(P) + c_C(円周角の定理・接弦定理)の形になる。θ_C(X) = s_C(I,X) − s_C(X,J) + ℓ_C でつなぐ。円の上の2点を通る直線が図に無い弦は、線分の向きで dir(PX) − c_0 = θ_C(P) + θ_C(X) + c_C", ledger: "83・91・93" },
    ArRule { kind: "等式", name: "射影(中心からの射影)",
        situation: "中心 O と、O を通らない直線 L1, L2。O を通る直線 m ごとの対応 m∩L1 ↦ m∩L2 と、動かない L1∩L2。有限の O では L2 = 無限遠直線(X ↦ 直線 OX の方向)、無限遠の O(方向 D の平行線の族)では L1, L2 は有限の直線",
        relation: "s(X2,Y2) − s(X1,Y1) = μ(X1) + μ(Y1) + κ(射影は一次分数変換)。O が無限遠なら ∞_L1 ↦ ∞_L2 でアフィンなので μ は一定で、比が一定になる(平行 ⇒ 比、三角形の比の定理)", ledger: "83・84・89" },
    ArRule { kind: "等式", name: "メネラウスの定理",
        situation: "3辺が図にある三角形 ABC と、辺(の直線)BC・CA・AB を D・E・F で切る直線(1つは無限遠点でもよい ― 辺に平行な横断線。固定座標で積が −1)",
        relation: "s(A,F) − s(F,B) + s(B,D) − s(D,C) + s(C,E) − s(E,A) = 2T(向きつきの比の積 = −1)。D が無限遠点ならアフィンの等式で BD/DC = −1 になり、平行線と比の定理になる", ledger: "88・90" },
    ArRule { kind: "等式", name: "チェバの定理",
        situation: "3辺が図にある三角形 ABC と、1点 O で交わる直線 AD・BE・CF(O や D・E・F の1つは無限遠点でもよい ― 平行な3本・辺に平行な直線。固定座標で積が 1)",
        relation: "s(A,F) − s(F,B) + s(B,D) − s(D,C) + s(C,E) − s(E,A) = 0(比の積 = 1)", ledger: "88・90" },
    ArRule { kind: "検出→等式", name: "相似(AA・二辺夾角・三辺)",
        situation: "3辺が図にある2つの三角形で、2つの頂点の有向角の剰余が一致(AA)、角とそれを挟む2辺の長さの2乗の比が一致(二辺夾角)、2つの長さの2乗の比が一致(三辺)。裏返しは角の符号を変える。二辺夾角・三辺は向き(半直線の向き・裏返しか)を格子では決められないので固定座標の標本で選ぶ(作図は有理的なので図全体で1つに決まる)。同じ3点の置換(二等辺三角形の裏返し)も使う",
        relation: "対応する各辺で s(JX′,JY′) = s(JX,JY) + log a、I の線束でも同じ(裏返しは I と J を入れ替える)。三角形が閉じる条件が足し算なので、検出の一歩だけ線形でない", ledger: "85・90" },
    ArRule { kind: "検出→等式", name: "相似で対応する点",
        situation: "相似な三角形の辺 XY の上の点 P と対応する辺の上の点 P′ で、σ(X) = X′ からの2つの等式が格子で言える(同じ直線の上では内分比が等しいこと)",
        relation: "P′ = σ(P) として、頂点・他の対応点との組で相似の等式を足す(図の上で同じ点の組は使わない)", ledger: "85" },
    ArRule { kind: "検出→等式", name: "鏡映",
        situation: "直線 m に関する鏡映で A ↦ B と言える組(AB ⊥ m で、AB の中点が m の上にあるか m の上の点 P で PA = PB、または m の上の2点で等距離。候補は固定座標で選ぶ)",
        relation: "m の上の点(動かない)と A ↔ B の対応で、裏返しの相似と同じ等式 s(JX′,JY′) = s(IX,IY) + κ_J、s(IX′,IY′) = s(JX,JY) + κ_I と κ_J + κ_I = 0(等長)。垂直二等分線の上の点の等距離・二等辺三角形の底角", ledger: "89" },
    ArRule { kind: "検出→等式", name: "中心の分かった円",
        situation: "点 O から等距離と格子で言える点 P(候補は固定座標で選ぶ)。O が AB の中点で ∠APB が直角の点も含める。円の実体に3点以上が乗っていればその円",
        relation: "s(JO,JP) = θ(P) + c_J、s(IO,IP) = −θ(P) + c_I(θ は弦の等式と同じ円の記号)と c_C − c_J + c_I + c_0 = 2T。実体の無い円には弦の等式も足す。中心角・斜辺の中線・二等辺三角形の底角・半径と接線の直交", ledger: "89" },
    ArRule { kind: "検出", name: "垂直二等分線の逆",
        situation: "鏡映の軸 m(図の直線)で A ↔ B と言えていて、図の点 P で |PA|² = |PB|² が格子で言える(固定座標で P ∈ m が真の候補だけ)",
        relation: "P を m に接続する", ledger: "90" },
    ArRule { kind: "検出", name: "中心から等距離 ⇒ 円の上",
        situation: "中心 O の分かった円 C(の実体)と、図の点 P で |OP|² が半径の2乗と格子で等しい(固定座標で P ∈ C が真の候補だけ)",
        relation: "P を C に接続する", ledger: "90" },
    ArRule { kind: "検出", name: "同値類の併合",
        situation: "2つの同値類の式の正準な剰余が一致",
        relation: "2つの同値類をマージする(理由: 代数的な追跡(複比・有向角の線形関係))", ledger: "82" },
    ArRule { kind: "検出", name: "平行(方向の併合)",
        situation: "(I,J;D1,D2) の式が 0 に還元される",
        relation: "方向 D1 と D2 をマージする(平行)", ledger: "82" },
    ArRule { kind: "検出", name: "比 ⇒ 平行",
        situation: "2直線を切る2本の横断線で、交点からの比(または既に平行な横断線を基準にした比)の式が一致",
        relation: "2本の横断線の方向をマージする(中点連結定理はこの特別な場合)", ledger: "84" },
    ArRule { kind: "検出", name: "シュタイナーの逆",
        situation: "二次曲線 C の上の5点 P, P′, A, B, D と C の外の点 Z で、(PA,PB;PD,PZ) と (P′A,P′B;P′D,P′Z) の式の差が 0 に還元される(固定座標で Z ∈ C が真の候補だけ)",
        relation: "Z を C に接続する", ledger: "91" },
    ArRule { kind: "検出", name: "円周角の逆",
        situation: "円 C の外の点 Z から C の上の2点 A, B への線分の向きの差 dir(ZA) − dir(ZB)(直線があれば β の差)が θ_C(A) − θ_C(B) に還元される(候補は固定座標で C に乗る点)",
        relation: "Z を C に接続する", ledger: "83・93" },
    ArRule { kind: "検出", name: "図に無い円の円周角の逆",
        situation: "固定座標で同じ円に乗る4点以上の組で3点が乗る円が図に無く、4点 A, B, C, Z の共円を表す3通りの角の等式(2本の弦への分け方)のどれかが格子で言える",
        relation: "外接円 ABC を作って Z を接続する(言えなかった組には、4点のうち直線の無い組に直線を引く)", ledger: "93" },
    ArRule { kind: "検出", name: "メネラウスの逆",
        situation: "三角形の2辺の上の点(1つは無限遠点でもよい)を通る直線 t があり、3つ目の辺の上の点 E で比の積の式が −1 に還元される(固定座標で E ∈ t が真の候補だけ)",
        relation: "E を t に接続する(共線)", ledger: "88" },
    ArRule { kind: "検出", name: "チェバの逆",
        situation: "直線 AD・BE が O で交わり(平行なら無限遠点)、AB の上の F で比の積の式が 1 に還元される(固定座標で F ∈ CO が真の候補だけ)",
        relation: "F を直線 CO に接続する(共点)", ledger: "88" },
];

/// 前回の追跡で規則(鏡映・中心の分かった円・相似・メネラウス)を足した後の状態。規則が読むのは格子(剰余は格子だけで
/// 決まる)と図の構造だけなので、図の構造の指紋と土台の格子が同じなら、規則を回し直しても同じ等式しか出ない。
pub(crate) struct ArCache {
    fingerprint: u64,
    base: Lattice,
    after_rules: ArState,
    length_links: Vec<(ClassId, ClassId, Vec<u32>, &'static str)>,
}

/// 三角形の枠(1回の追跡で1度だけ作る): 有限の点、2点を通る直線(図にあるもの)、3辺が図にある三角形、直線ごとの点。
struct Frame {
    points: Vec<ClassId>,
    edge: FxHashMap<(usize, usize), ClassId>,
    tris: Vec<[ClassId; 3]>,
    on_line: FxHashMap<usize, Vec<ClassId>>,
    /// 点ごとに、それを通る直線(図にあるもの)。
    lines_at: FxHashMap<usize, Vec<ClassId>>,
}

impl Frame {
    fn line_of(&self, a: ClassId, b: ClassId) -> Option<ClassId> { self.edge.get(&(a.0.min(b.0), a.0.max(b.0))).copied() }
    fn on(&self, l: ClassId) -> &[ClassId] { self.on_line.get(&l.0).map(|v| v.as_slice()).unwrap_or(&[]) }
}

/// 1回の追跡の状態: 記号の表・格子・等式の出どころと、既に入れた等式。
#[derive(Clone)]
struct ArState {
    atoms: Atoms,
    lattice: Lattice,
    premises_of: Vec<Vec<(String, Vec<ClassId>)>>,
    /// 既に格子に入れた等式(式そのもの)。同じ等式を2度入れない。
    seen: rustc_hash::FxHashSet<Vec<(u32, i64)>>,
    /// この行演算の数を超えたら、相似・対応する点を足すのをやめる。
    ops_cap: u64,
    /// 各等式の式(GS_DEBUG_AR_REL のときだけ持つ。調査用)。
    rels_dbg: Vec<SVec>,
    /// 相似な三角形の組ごとの、相似の定数の記号の番号。
    sim_ids: FxHashMap<([usize; 3], [usize; 3], bool), usize>,
    /// 2つの実体が固定座標で区別できるか(記号 s(X,Y) が意味を持つか)の判定の使い回し。
    distinct: FxHashMap<(usize, usize), bool>,
}

impl ArState {
    fn new() -> Option<Self> {
        let mut st = ArState { atoms: Atoms::default(), lattice: Lattice::default(), premises_of: Vec::new(),
            seen: Default::default(), sim_ids: FxHashMap::default(), distinct: FxHashMap::default(), rels_dbg: Vec::new(), ops_cap: u64::MAX };
        st.lattice.insert(SVec::from([(T, 4)]), Vec::new())?;
        Some(st)
    }

    /// 格子に入れない前提だけの記録(検出の結論の出どころに、接続・方向などの前提を足すため)。番号を返す。
    fn note(&mut self, premises: Vec<(String, Vec<ClassId>)>) -> u32 {
        self.premises_of.push(premises);
        (self.premises_of.len() - 1) as u32
    }

    /// 等式を(まだ入れていなければ)格子に入れる。extra は、この等式を出すのに使った既存の等式(出どころ)。
    /// 入れたら Some(true)、既にあれば Some(false)、係数があふれたら None。
    fn insert(&mut self, eg: &EGraph, rel: SVec, premises: Vec<(String, Vec<ClassId>)>, extra: &[u32]) -> Option<bool> {
        if rel.is_empty() { return Some(false); }
        // 2点の差の記号は、2点が実際に別の点でないと意味を持たない(長さ 0 の差の対数)。まだマージされていないだけで
        // 図の上では同じ点(例: centroid で別々に作った2つの重心)の記号を含む等式は、格子に矛盾(2 = −1 など)を持ち込む。
        for &c in rel.keys() {
            let Some(&(x, y)) = self.atoms.pair_of.get(&c) else { continue };
            if is_virtual(x) || is_virtual(y) { continue; }
            let (ex, ey) = (entity_of(x), entity_of(y));
            if ex == ey { continue; }
            let key = (ex.0.min(ey.0), ex.0.max(ey.0));
            let ok = *self.distinct.entry(key).or_insert_with(|| eg.fixed_equal(ex, ey) == Some(Some(false)));
            if !ok { return Some(false); }
        }
        let key: Vec<(u32, i64)> = rel.iter().map(|(&c, &x)| (c, x)).collect();
        if !self.seen.insert(key) { return Some(false); }
        let id = self.premises_of.len() as u32;
        if std::env::var("GS_DEBUG_AR_REL").is_ok() || std::env::var("GS_DEBUG_AR_RAW").is_ok() { while self.rels_dbg.len() < self.premises_of.len() { self.rels_dbg.push(SVec::new()); } self.rels_dbg.push(rel.clone()); }
        self.premises_of.push(premises);
        self.lattice.insert(rel, union(&[id], extra))?;
        Some(true)
    }
}

/// 記号の番号。s(X,Y)(順序のない点の組ごと)と、等式を作るときに導入する新しい記号(円の点の記号など)。
#[derive(Default, Clone)]
struct Atoms {
    ids: FxHashMap<(usize, usize), u32>,
    /// ids の逆引き(記号の番号 → 点の組)。
    pair_of: FxHashMap<u32, (usize, usize)>,
    fresh: FxHashMap<(u8, usize, usize, usize), u32>,
    next: u32,
}

/// 点の組の記号の番号は NAMED_BASE から上(等方線束の記号はさらに 1 << 29 から上)、新しい記号は NAMED_BASE の下に置く。
/// 格子は小さい番号の列から主成分にするので、新しい記号(存在するだけの補助の量)が先に消去され、点の組の記号だけの行が
/// 短く保たれる。
const NAMED_BASE: u32 = 1 << 30;

/// 新しい記号の種類。
const THETA: u8 = 0;       // 円 C の上の点 P の記号 θ_C(P)(弦 PX の方向の記号 = θ_C(P) + θ_C(X) + c_C)
const CIRCLE_C: u8 = 1;    // 円 C の定数 c_C
const PROJ_MU: u8 = 2;     // 中心 O から直線 L への射影の、点 X の倍率 μ_{O,L}(X)
const PROJ_K: u8 = 3;      // その定数 κ_{O,L}
const CONIC_S: u8 = 4;     // 二次曲線 C の媒介変数の差 s_C(X,Y)(向きのある組)
const STEINER_MU: u8 = 5;  // 二次曲線 C の頂点 P からの線束の、点 X の倍率
const STEINER_K: u8 = 6;   // その定数
const PARALLEL_K: u8 = 7;
const LOG_PRIME: u8 = 8;
const CHART_J: u8 = 9;     // 直線 m の上の点の差と、J の等方線束の差のずれ(m ごとの定数)
const CHART_I: u8 = 10;    // 同じく I の等方線束
const CHART_0: u8 = 11;    // 等方線束のずれの差と方向の角の記号のずれ(全体で1つ)
const SIM_J: u8 = 12;      // 相似ごとの定数(J の線束の上の拡大・回転、複素数 a の対数)
const CONIC_LINK: u8 = 16; // 円周角の記号 θ とシュタイナーの記号をつなぐ円ごとの定数 ℓ_C
const CENTER_J: u8 = 14;   // 中心の分かった円の定数 c_J(s(JO,JP) = θ(P) + c_J)
const CENTER_I: u8 = 15;   // 同じく c_I(s(IO,IP) = −θ(P) + c_I)
const SIM_I: u8 = 13;      // 同じく I の線束(共役 ā)   // 素数 p の形式的な対数 log p(有理数の比の定数。足し算の関係から来る比を積の世界に持ち込む)  // 方向 D に沿った直線 L1 から L2 への射影(アフィン)の拡大率 κ_{D,L1,L2}

/// 等方線束の要素(点 X を通る J 方向・I 方向の等方直線 JX・IX)の番号。実体の番号・仮の無限遠点と重ならない範囲に置く。
/// JX と JY は J で交わるので、その差の記号 s(JX,JY) は J の線束の上の差(複素座標の差 z_X − z_Y)。
const ISO_J_BASE: usize = 1 << 40;
const ISO_I_BASE: usize = 1 << 41;
fn iso_j(x: ClassId) -> usize { ISO_J_BASE + x.0 }
fn iso_i(x: ClassId) -> usize { ISO_I_BASE + x.0 }
fn is_entity(id: usize) -> bool { id < ISO_J_BASE }

/// 直線の無限遠点の仮の番号(方向の点がまだ図に無い直線用)。実体の番号とは重ならない大きい側に置く。
const VIRTUAL_BASE: usize = usize::MAX / 2;
fn virtual_infinity(line: ClassId) -> usize { usize::MAX - line.0 }
fn is_virtual(id: usize) -> bool { id >= VIRTUAL_BASE }

impl Atoms {
    /// s(X,Y) を v に sign 倍で足す。X > Y なら向きを入れ替えてねじれ 2(= −1)を足す。重なった2点なら None。
    fn add(&mut self, v: &mut SVec, x: usize, y: usize, sign: i64) -> Option<()> {
        if x == y { return None; }
        let (key, flipped) = if x < y { ((x, y), false) } else { ((y, x), true) };
        let id = match self.ids.get(&key) { Some(&id) => id, None => {
            // 等方線束の記号(複素座標の差)は後ろに置く(先に消去すると行が長くなった)。
            let iso = key.0 >= ISO_J_BASE && !is_virtual(key.0);
            let id = NAMED_BASE + (u32::from(iso) << 29) + self.next; self.next += 1; self.ids.insert(key, id); self.pair_of.insert(id, key); id } };
        add_scaled(v, &SVec::from([(id, 1)]), sign)?;
        if flipped { add_scaled(v, &SVec::from([(T, 2)]), sign)?; }
        Some(())
    }

    /// 新しい記号を v に sign 倍で足す。
    fn add_fresh(&mut self, v: &mut SVec, key: (u8, usize, usize, usize), sign: i64) -> Option<()> {
        let id = match self.fresh.get(&key) { Some(&id) => id, None => { let id = NAMED_BASE - 1 - self.next; self.next += 1; self.fresh.insert(key, id); id } };
        add_scaled(v, &SVec::from([(id, 1)]), sign)
    }

    /// 向きのある差の新しい記号(s_C(Y,X) = s_C(X,Y) + ねじれ 2)。
    fn add_fresh_diff(&mut self, v: &mut SVec, kind: u8, owner: usize, x: usize, y: usize, sign: i64) -> Option<()> {
        if x == y { return None; }
        let (a, b, flipped) = if x < y { (x, y, false) } else { (y, x, true) };
        self.add_fresh(v, (kind, owner, a, b), sign)?;
        if flipped { add_scaled(v, &SVec::from([(T, 2)]), sign)?; }
        Some(())
    }

    /// 方向 D の角の記号 β(D) = s(I,D) − s(D,J)(有向角 (I,J;D1,D2) = β(D1) − β(D2))。
    fn add_beta(&mut self, v: &mut SVec, i: usize, j: usize, d: usize, sign: i64) -> Option<()> {
        self.add(v, i, d, sign)?;
        self.add(v, d, j, -sign)
    }

    /// 長さの2乗 |XY|² = s(JX,JY) + s(IX,IY)。
    fn add_len(&mut self, v: &mut SVec, x: ClassId, y: ClassId, sign: i64) -> Option<()> {
        self.add(v, iso_j(x), iso_j(y), sign)?;
        self.add(v, iso_i(x), iso_i(y), sign)
    }

    /// 線分 XY の向き(z の差と z̄ の差の比)s(JX,JY) − s(IX,IY)。直線 XY が図にあれば β(XY) + c_0(地図の等式)。
    fn add_dir(&mut self, v: &mut SVec, x: ClassId, y: ClassId, sign: i64) -> Option<()> {
        self.add(v, iso_j(x), iso_j(y), sign)?;
        self.add(v, iso_i(x), iso_i(y), -sign)
    }
}

/// 固定座標の直線の係数を、最初の 0 でない係数で割って比べられる形にする。
fn line_key(v: &[ModInt]) -> Option<[i64; 3]> {
    if v.len() < 3 { return None; }
    let piv = v[..3].iter().find(|x| x.0 != 0).copied()?;
    Some([(v[0] / piv).0, (v[1] / piv).0, (v[2] / piv).0])
}

/// 鏡映の相似の定数の番号(相似の番号と重ならない範囲)と、仮の円の番号。
const REFLECT_BASE: usize = 1 << 42;
const VIRTUAL_CIRCLE_BASE: usize = 1 << 43;

impl BlackboardEngine {
    /// 方向の点(無限遠直線の上の点)の代表元。直線の方向がまだ図に無ければ None。
    fn ar_direction(&self, line: ClassId) -> Option<ClassId> {
        let eg = &self.prover.egraph;
        eg.memo.get(&eg.normalize_definition(&Definition::DirectionOf(eg.get_rep(line)))).map(|&d| eg.get_rep(d))
    }

    /// 定義が表す複比の4点 (A,B;C,D)(代表元)。
    fn ar_cross_ratio_points(&self, def: &Definition) -> Option<[usize; 4]> {
        let eg = &self.prover.egraph;
        let r = |x: ClassId| eg.get_rep(x).0;
        match *def {
            Definition::AnglePair(d1, d2) => Some([r(eg.circ_i), r(eg.circ_j), r(d1), r(d2)]),
            Definition::CrossRatio(a, b, c, d) => Some([r(a), r(b), r(c), r(d)]),
            Definition::CrossRatioOfLines(a, b, c, d) =>
                Some([self.ar_direction(a)?.0, self.ar_direction(b)?.0, self.ar_direction(c)?.0, self.ar_direction(d)?.0]),
            _ => None,
        }
    }

    /// 点(仮の無限遠点を含む)の固定座標での値。直線 (a,b,c) の無限遠点は (b,−a,0)。
    fn ar_point_value(&self, id: usize, k: usize) -> Option<Vec<ModInt>> {
        let eg = &self.prover.egraph;
        if !is_entity(id) && !is_virtual(id) { return None; }
        if is_virtual(id) {
            let l = eg.class_value(ClassId(usize::MAX - id), k)?;
            return (l.len() >= 3).then(|| vec![l[1], -l[0], ModInt::new(0)]);
        }
        eg.class_value(ClassId(id), k)
    }

    /// 記号の式 s(A,C)·s(D,B) / (s(C,B)·s(A,D)) の固定座標での値(基準点 R の行列式 [XYR])。どれかの差が 0 なら None。
    fn ar_formula_value(&self, pts: [usize; 4], k: usize) -> Option<ModInt> {
        let p: Vec<Vec<ModInt>> = pts.iter().map(|&x| self.ar_point_value(x, k)).collect::<Option<_>>()?;
        // 基準点は一般の位置の定数(どの直線にも乗らない)。
        let rr = [ModInt::new(314_159 + 17 * k as i64), ModInt::new(271_828 + 29 * k as i64), ModInt::new(1)];
        let det = |x: &[ModInt], y: &[ModInt]| x[0] * (y[1] * rr[2] - y[2] * rr[1]) - x[1] * (y[0] * rr[2] - y[2] * rr[0]) + x[2] * (y[0] * rr[1] - y[1] * rr[0]);
        let num = det(&p[0], &p[2]) * det(&p[3], &p[1]);
        let den = det(&p[2], &p[1]) * det(&p[0], &p[3]);
        (num.0 != 0 && den.0 != 0).then(|| num / den)
    }

    /// 定義の値が記号の式の値と一致するか(全標本)。
    fn ar_verify(&self, def: &Definition, pts: [usize; 4]) -> bool {
        let eg = &self.prover.egraph;
        (0..eg.fixed_samples()).all(|k| {
            let val = eg.fixed_def_value(def, k).and_then(|v| v.first().copied());
            matches!((val, self.ar_formula_value(pts, k)), (Some(v), Some(f)) if v.0 == f.0)
        })
    }

    /// 記号の式の値が定数 c か(全標本)。
    fn ar_verify_const(&self, pts: [usize; 4], c: ModInt) -> bool {
        (0..self.prover.egraph.fixed_samples()).all(|k| matches!(self.ar_formula_value(pts, k), Some(f) if f.0 == c.0))
    }

    /// 定義から従う「比」の等式(無限遠点との複比が −1): 中点 (A,B;M,∞) = −1、調和共役 (A,B;C,D) = −1。
    /// 返り値は (4点, 前提)。
    fn ar_ratio_facts(&self) -> Vec<([usize; 4], (String, Vec<ClassId>))> {
        let eg = &self.prover.egraph;
        let mut out = Vec::new();
        for i in 0..eg.entities.len() {
            let rep = ClassId(i);
            if eg.get_rep(rep) != rep || eg.entities[i].entity_type != EntityType::Point { continue; }
            let defs = eg.entities[i].components.first().map(|c| c.definitions.clone()).unwrap_or_default();
            for def in &defs {
                let ent = eg.memo.get(&eg.normalize_definition(def)).copied().unwrap_or(rep);
                match *def {
                    Definition::Midpoint(a, b) => {
                        let (a, b) = (eg.get_rep(a), eg.get_rep(b));
                        let Some(line) = eg.find_common_line(&[a, b, rep]) else { continue };
                        let inf = self.ar_direction(line).map(|d| d.0).unwrap_or_else(|| virtual_infinity(line));
                        out.push(([a.0, b.0, rep.0, inf], ("DefinedBy:Midpoint".to_string(), vec![a, b, ent])));
                    }
                    Definition::HarmonicConjugateOf(a, b, c) => {
                        let (a, b, c) = (eg.get_rep(a), eg.get_rep(b), eg.get_rep(c));
                        out.push(([a.0, b.0, c.0, rep.0], ("DefinedBy:HarmonicConjugateOf".to_string(), vec![a, b, c, ent])));
                    }
                    _ => {}
                }
            }
        }
        out
    }

    /// 1回の追跡: 等式を格子に積み、剰余が同じ同値類を併合する。併合した数を返す。
    fn ar_round(&mut self) -> usize {
        // 格子は毎回作り直す(来歴 #85: 呼び出しをまたいで積むと、古い代表元の記号の行が溜まって遅くなり、
        // 行の出どころが合併を重ねて太り、証明が数十倍に膨らんだ)。
        let fp = self.ar_fingerprint();
        let Some(mut st) = ArState::new() else { return 0 };
        // 記号の番号をそろえる(前回の状態を使い回すとき、今回の式を同じ番号で読む)。
        if let Some(c) = self.ar_cache.as_ref().filter(|c| c.fingerprint == fp) { st.atoms = c.after_rules.atoms.clone(); }
        let merged = self.ar_round_with(&mut st, fp);
        // 行演算4回で仕事量1と数える: 44問と HAGeo の実測で、dfs_match 1回(合同閉包・結論の適用を含む)が約 7.7µs、
        // 行演算1回が約 2.0µs(来歴 #94。#91 では行が長く 2回で1、それ以前は 16回で1)。
        self.prover.egraph.spiral_prop_work += st.lattice.ops / AR_OPS_PER_WORK;
        self.ar_ops += st.lattice.ops;
        self.ar_rounds += 1;
        merged.unwrap_or(0)
    }

    /// 規則が読む図の構造の指紋: 有効な点・直線・二次曲線の代表元、直線・二次曲線に乗る点、直線の方向、円の中心の定義
    /// (接続・定義が増えても、これらが変わらなければ規則の結果は同じ)。
    fn ar_fingerprint(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let eg = &self.prover.egraph;
        let mut h = rustc_hash::FxHasher::default();
        for i in 0..eg.entities.len() {
            let (c, e) = (ClassId(i), &eg.entities[i]);
            if eg.get_rep(c) != c || !e.is_active() { continue; }
            match e.entity_type {
                EntityType::Point => i.hash(&mut h),
                EntityType::Line | EntityType::Conic => {
                    i.hash(&mut h);
                    let Some(comp) = e.components.first() else { continue };
                    let mut pts: Vec<usize> = comp.subobjects.iter().map(|&x| eg.get_rep(x))
                        .filter(|&x| eg.entities[x.0].entity_type == EntityType::Point && eg.entities[x.0].is_active()).map(|x| x.0).collect();
                    pts.sort_unstable();
                    pts.dedup();
                    pts.hash(&mut h);
                    if e.entity_type == EntityType::Line {
                        self.ar_direction(c).map(|d| d.0).hash(&mut h);
                    } else {
                        comp.definitions.iter().find_map(|d| match *d {
                            Definition::CircleCenterPoint(o, p) => Some((eg.get_rep(o).0, eg.get_rep(p).0)), _ => None }).hash(&mut h);
                    }
                }
                _ => {}
            }
        }
        h.finish()
    }

    fn ar_round_with(&mut self, st: &mut ArState, fp: u64) -> Option<usize> {
        let (t0, ops0) = (std::time::Instant::now(), st.lattice.ops);
        let eg = &self.prover.egraph;
        let mut atoms = std::mem::take(&mut st.atoms);
        // 同値類ごとの (記号の式, その式を持つ実体)。
        let mut classes: Vec<(ClassId, Vec<(SVec, Vec<(String, Vec<ClassId>)>)>)> = Vec::new();
        let (mut dbg_degen, mut dbg_unverified, mut dbg_ratio) = (0usize, 0usize, 0usize);
        let (ang90, ang0) = (eg.get_rep(eg.ang90), eg.get_rep(eg.ang0));
        for i in 0..eg.entities.len() {
            let rep = ClassId(i);
            if eg.get_rep(rep) != rep || eg.entities[i].entity_type != EntityType::Scalar { continue; }
            // 各式の前提: その定義がこの同値類にある(記録した実体の番号が、その時点で別の類にいることがあるので、
            // 「どの実体か」ではなく「この類にこの定義がある」として記録する)。
            let mut vs: Vec<(SVec, Vec<(String, Vec<ClassId>)>)> = Vec::new();
            if rep == ang90 { vs.push((SVec::from([(T, 2)]), vec![("Identical".to_string(), vec![eg.ang90, rep])])); }
            if rep == ang0 { vs.push((SVec::new(), vec![("Identical".to_string(), vec![eg.ang0, rep])])); }
            let defs = eg.entities[i].components.first().map(|c| c.definitions.clone()).unwrap_or_default();
            for def in &defs {
                // 長さ: LengthSq(X,Y) = (z_X − z_Y)(z̄_X − z̄_Y) = s(JX,JY) + s(IX,IY)。積は和。
                if let Some((v, mut extra)) = self.ar_length_vector(def, &mut atoms) {
                    extra.push(Self::defined_by_premise(def, rep));
                    vs.push((v, extra));
                    continue;
                }
                let Some(pts) = self.ar_cross_ratio_points(def) else { continue };
                let mut v = SVec::new();
                let [a, b, c, d] = pts;
                let ok = atoms.add(&mut v, a, c, 1).and_then(|_| atoms.add(&mut v, d, b, 1))
                    .and_then(|_| atoms.add(&mut v, c, b, -1)).and_then(|_| atoms.add(&mut v, a, d, -1));
                if ok.is_none() { dbg_degen += 1; continue; }
                if !self.ar_verify(def, pts) { dbg_unverified += 1; continue; }
                vs.push((v, vec![Self::defined_by_premise(def, rep)]));
            }
            if !vs.is_empty() { classes.push((rep, vs)); }
        }

        st.atoms = atoms;
        // 等式(同値類の中の2つの式の差)。ねじれの関係 4T = 0 は状態を作るときに入れてある。
        for (_, vs) in &classes {
            for (v, prem) in &vs[1..] {
                let mut rel = v.clone();
                if add_scaled(&mut rel, &vs[0].0, -1).is_none() { continue; }
                st.insert(&self.prover.egraph, rel, [prem.clone(), vs[0].1.clone()].concat(), &[])?;
            }
        }
        // 定義から従う比の等式(無限遠点との複比が −1)。
        let minus_one = ModInt::new(-1);
        for (pts, premise) in self.ar_ratio_facts() {
            let [a, b, c, d] = pts;
            let mut rel = SVec::new();
            let ok = st.atoms.add(&mut rel, a, c, 1).and_then(|_| st.atoms.add(&mut rel, d, b, 1))
                .and_then(|_| st.atoms.add(&mut rel, c, b, -1)).and_then(|_| st.atoms.add(&mut rel, a, d, -1))
                .and_then(|_| add_scaled(&mut rel, &SVec::from([(T, 2)]), -1));
            if ok.is_none() || !self.ar_verify_const(pts, minus_one) { continue; }
            if st.insert(&self.prover.egraph, rel, vec![premise], &[])? { dbg_ratio += 1; }
        }

        // 定理の代わりに等式を作る(円・透視射影・二次曲線の射影対応)。
        let mut gen_count = 0usize;
        for (rel, premises) in self.ar_generated_relations(&mut st.atoms) {
            if st.insert(&self.prover.egraph, rel, premises, &[])? { gen_count += 1; }
        }
        let (t1, ops1) = (std::time::Instant::now(), st.lattice.ops);
        st.ops_cap = st.lattice.ops + AR_ROUND_OPS_CAP;
        // 図の構造と土台の格子が前回と同じなら、規則を足した後の状態を使い回す(今回の記号の表は前回の上に足したもの)。
        let mut cached = self.ar_cache.take().filter(|c| c.fingerprint == fp);
        let reuse = match cached.as_mut() {
            Some(c) => {
                let before = c.base.ops;
                let same = c.base.same_span(&mut st.lattice)?;
                st.lattice.ops += c.base.ops - before;
                same
            }
            None => false,
        };
        if std::env::var("GS_DEBUG_AR").is_ok() { println!("  AR_CACHE fp_match={} same_span={} rows={}", cached.is_some(), reuse, st.lattice.rows.len()); }
        let base_snapshot = if reuse { None } else { Some(st.lattice.clone()) };
        if let (true, Some(c)) = (reuse, cached.as_ref()) {
            let (atoms, ops) = (std::mem::take(&mut st.atoms), st.lattice.ops);
            let left = c.after_rules.ops_cap.saturating_sub(c.after_rules.lattice.ops);
            *st = c.after_rules.clone();
            st.atoms = atoms;
            st.lattice.ops = ops;
            st.ops_cap = ops + left;
        }
        let dbg = std::env::var("GS_DEBUG_AR").is_ok();
        let mut stage = (std::time::Instant::now(), st.lattice.ops);
        let mut lap = |name: &str, st: &ArState| {
            if dbg { println!("  AR_STAGE {:<14} {:>10.3?} {:>9} ops", name, stage.0.elapsed(), st.lattice.ops - stage.1); }
            stage = (std::time::Instant::now(), st.lattice.ops);
        };
        let frame = self.ar_frame();
        lap("frame", st);
        // 鏡映・中心の分かった円の逆(長さが等しい ⇒ 垂直二等分線・円の上)の結論。後で他の検出と一緒に接続する。
        let mut length_links: Vec<(ClassId, ClassId, Vec<u32>, &'static str)> = Vec::new();
        let mut sims = 0;
        if let (true, Some(c)) = (reuse, cached.as_ref()) {
            length_links = c.length_links.clone();
            self.ar_reused += 1;
            if dbg { println!("  AR_STAGE reused"); }
        } else {
            let xy = self.ar_frame_xy(&frame);
            // GS_AR_OFF=reflect,circle で規則を外す(測定用)。
            let off = std::env::var("GS_AR_OFF").unwrap_or_default();
            let refl = if off.contains("reflect") { 0 } else { self.ar_reflections(st, &frame, &xy, &mut length_links)? };
            lap("reflections", st);
            let circ = if off.contains("circle") { 0 } else { self.ar_centered_circles(st, &frame, &xy, &mut length_links)? };
            lap("circles", st);
            if std::env::var("GS_DEBUG_AR").is_ok() { println!("  AR_DEBUG reflections={} centered_circles={}", refl, circ); }
            sims = self.ar_similarity(st, &frame)?;
            lap("similarity", st);
            self.ar_menelaus_ceva_relations(st, &frame)?;
            lap("menelaus", st);
            self.ar_similar += sims as u64;
        }
        cached = match base_snapshot {
            Some(base) => Some(ArCache { fingerprint: fp, base, after_rules: st.clone(), length_links: length_links.clone() }),
            None => cached,
        };
        self.ar_cache = cached;
        let (t2, ops2) = (std::time::Instant::now(), st.lattice.ops);
        if std::env::var("GS_DEBUG_AR").is_ok() {
            println!("  AR_DEBUG generated={} similar_pairs={} insert {:?}/{} ops, similarity {:?}/{} ops", gen_count, sims,
                t1 - t0, ops1 - ops0, t2 - t1, ops2 - ops1);
            let mapped: usize = classes.iter().map(|(_, v)| v.len()).sum();
            println!("  AR_DEBUG classes={} mapped={} degen={} unverified={} ratio_facts={} relations={} rows={} atoms={}",
                classes.len(), mapped, dbg_degen, dbg_unverified, dbg_ratio, st.premises_of.len(), st.lattice.rows.len(), st.atoms.ids.len());
        }
        // 剰余が同じ同値類を探す。ここから先は格子を変えないので、記号ごとの剰余を使い回す。
        let mut rc: FxHashMap<u32, SVec> = FxHashMap::default();
        let mut by_key: FxHashMap<Vec<(u32, i64)>, usize> = FxHashMap::default();
        let mut merges: Vec<(ClassId, ClassId, Vec<u32>)> = Vec::new();
        for (idx, (rep, vs)) in classes.iter().enumerate() {
            let Some(r) = st.lattice.reduce_cached(&vs[0].0, &mut rc) else { continue };
            let key: Vec<(u32, i64)> = r.into_iter().collect();
            match by_key.get(&key) {
                None => { by_key.insert(key, idx); }
                Some(&first) => {
                    let mut diff = vs[0].0.clone();
                    if add_scaled(&mut diff, &classes[first].1[0].0, -1).is_none() { continue; }
                    let Some((_, src)) = st.lattice.reduce(&diff) else { continue };
                    merges.push((classes[first].0, *rep, src));
                }
            }
        }
        // 方向どうしの一致: (I,J;D1,D2) の式が 0 に還元されるなら D1 = D2(平行)。等式に出てくる方向だけを見る。
        let eg = &self.prover.egraph;
        let (ci, cj) = (eg.get_rep(eg.circ_i), eg.get_rep(eg.circ_j));
        let mut dirs: Vec<ClassId> = st.atoms.ids.keys()
            .flat_map(|&(x, y)| [x, y]).filter(|&x| is_entity(x)).map(ClassId)
            .filter(|&d| d != ci && d != cj && eg.get_rep(d) == d && eg.entities[d.0].entity_type == EntityType::Point
                && eg.is_connected(d, eg.line_infinity))
            .collect();
        dirs.sort_by_key(|d| d.0);
        dirs.dedup();
        let zero = st.lattice.reduce(&SVec::new()).map(|r| r.0);
        let mut dir_merges: Vec<(ClassId, ClassId, Vec<u32>)> = Vec::new();
        for i in 0..dirs.len() {
            for j in (i + 1)..dirs.len() {
                let (d1, d2) = (dirs[i], dirs[j]);
                let mut v = SVec::new();
                let ok = st.atoms.add(&mut v, ci.0, d1.0, 1).and_then(|_| st.atoms.add(&mut v, d2.0, cj.0, 1))
                    .and_then(|_| st.atoms.add(&mut v, d1.0, cj.0, -1)).and_then(|_| st.atoms.add(&mut v, ci.0, d2.0, -1));
                if ok.is_none() { continue; }
                if st.lattice.reduce_cached(&v, &mut rc).as_ref() != zero.as_ref() { continue; }
                let Some((_, src)) = st.lattice.reduce(&v) else { continue };
                if std::env::var("GS_DEBUG_AR_RAW").is_ok() {
                    let eg = &self.prover.egraph;
                    println!("AR_RAW target {} {} : {}", eg.entities[d1.0].name, eg.entities[d2.0].name,
                        v.iter().map(|(c, x)| format!("{}:{}", c, x)).collect::<Vec<_>>().join(" "));
                    for &i in &src {
                        let r = st.rels_dbg.get(i as usize).cloned().unwrap_or_default();
                        println!("AR_RAW rel {} : {}", i, r.iter().map(|(c, x)| format!("{}:{}", c, x)).collect::<Vec<_>>().join(" "));
                    }
                }
                dir_merges.push((d1, d2, src));
            }
        }
        let mut links: Vec<(ClassId, ClassId, Vec<u32>, &str)> = self.ar_detect_concyclic(&mut st.atoms, &mut st.lattice, &mut rc, zero.as_ref())
            .into_iter().map(|(z, c, src)| (z, c, src, "代数的な追跡(円周角の逆)")).collect();
        links.extend(self.ar_detect_menelaus_ceva(st, &frame, &mut rc));
        links.extend(self.ar_detect_conic_converse(st, &mut rc));
        links.extend(length_links);
        let (virtual_concyclic, wanted_lines) = if std::env::var("GS_AR_OFF").unwrap_or_default().contains("vconcyclic") { (Vec::new(), Vec::new()) }
            else { self.ar_detect_virtual_concyclic(st, &frame, &mut rc) };
        let parallels = self.ar_detect_parallel(&mut st.atoms, &mut st.lattice, &mut rc, zero.as_ref());
        if std::env::var("GS_DEBUG_AR").is_ok() {
            println!("  AR_DEBUG detect {:?}/{} ops", t2.elapsed(), st.lattice.ops - ops2);
        }
        merges.extend(dir_merges);
        merges.extend(parallels);

        let mut merged = 0;
        for (a, b, src) in merges {
            if std::env::var("GS_DEBUG_AR_RAW").is_ok() {
                for &i in &src {
                    let r = st.rels_dbg.get(i as usize).cloned().unwrap_or_default();
                    println!("AR_RAW rel {} : {}", i, r.iter().map(|(c, x)| format!("{}:{}", c, x)).collect::<Vec<_>>().join(" "));
                }
                println!("AR_RAW end");
            }
            if std::env::var("GS_DEBUG_AR_REL").is_ok() && self.prover.egraph.get_rep(a) != self.prover.egraph.get_rep(b) {
                let eg = &self.prover.egraph;
                println!("  AR_REL merge {} ≡ {} uses {} relations:", eg.entities[eg.get_rep(a).0].name, eg.entities[eg.get_rep(b).0].name, src.len());
                for &i in &src {
                    let v = st.rels_dbg.get(i as usize).cloned().unwrap_or_default();
                    println!("    [{}] {}", i, self.ar_describe(&st.atoms, &v));
                }
            }
            let eg = &mut self.prover.egraph;
            if eg.get_rep(a) == eg.get_rep(b) { continue; }
            if eg.merge_checks && eg.fixed_equal(a, b) == Some(Some(false)) {
                self.ar_rejected += 1;
                continue;
            }
            let premises: Vec<(String, Vec<ClassId>)> = src.iter()
                .flat_map(|&i| st.premises_of[i as usize].clone()).collect();
            let (na, nb) = (eg.entities[eg.get_rep(a).0].name.clone(), eg.entities[eg.get_rep(b).0].name.clone());
            if std::env::var("GS_DEBUG_AR").is_ok() { println!("  AR_DEBUG merge src={} premises={}", src.len(), premises.len()); }
            let justification = Justification::Theorem { name: "代数的な追跡(複比・有向角の線形関係)".to_string(), premises };
            if eg.merge_entities_justified(a, b, justification) {
                println!("  🧮 [代数的な追跡] {} ≡ {}", na, nb);
                merged += 1;
            }
        }
        // 円周角の逆・メネラウスの逆・チェバの逆(検出): 点を円・直線に接続する。
        for (z, c, src, name) in links {
            let eg = &mut self.prover.egraph;
            let (z, c) = (eg.get_rep(z), eg.get_rep(c));
            if eg.is_connected(z, c) { continue; }
            if eg.merge_checks && eg.numeric_incidence_check(z, c, 2) == Some(false) { self.ar_rejected += 1; continue; }
            let premises: Vec<(String, Vec<ClassId>)> = src.iter().flat_map(|&i| st.premises_of[i as usize].clone()).collect();
            let (nz, nc) = (eg.entities[z.0].name.clone(), eg.entities[c.0].name.clone());
            eg.link_logical_incidence_justified(z, c, Justification::Theorem { name: name.to_string(), premises });
            println!("  🧮 [代数的な追跡] {} ∈ {}", nz, nc);
            merged += 1;
        }
        // 図に無い円の円周角の逆: 3点の外接円を作り、乗ると分かった点を接続する。
        for ([a, b, c], z, src) in virtual_concyclic {
            let eg = &self.prover.egraph;
            let (a, b, c, z) = (eg.get_rep(a), eg.get_rep(b), eg.get_rep(c), eg.get_rep(z));
            let name = format!("Circ_{}_{}_{}_(AR)", eg.entities[a.0].name, eg.entities[b.0].name, eg.entities[c.0].name);
            let Some(circle) = self.add_aux(name, Definition::Circumcircle(a, b, c), EntityType::Conic, EntityOrigin::Construct, None) else { continue };
            let eg = &mut self.prover.egraph;
            let circle = eg.get_rep(circle);
            if eg.is_connected(z, circle) { continue; }
            if eg.merge_checks && eg.numeric_incidence_check(z, circle, 2) == Some(false) { self.ar_rejected += 1; continue; }
            let premises: Vec<(String, Vec<ClassId>)> = src.iter().flat_map(|&i| st.premises_of[i as usize].clone()).collect();
            let (nz, nc) = (eg.entities[z.0].name.clone(), eg.entities[circle.0].name.clone());
            eg.link_logical_incidence_justified(z, circle, Justification::Theorem { name: "代数的な追跡(円周角の逆)".to_string(), premises });
            println!("  🧮 [代数的な追跡] {} ∈ {}", nz, nc);
            merged += 1;
        }
        // 共円と言えなかった組の直線を引く(次の追跡で、その直線の上の比・平行・相似が格子に載る)。
        for (x, y) in wanted_lines {
            let eg = &self.prover.egraph;
            let (x, y) = (eg.get_rep(x), eg.get_rep(y));
            let def = Definition::new_line(x, y);
            if x == y || eg.live_memo(&eg.normalize_definition(&def)) || !self.ar_lines_through(x, y).is_empty() { continue; }
            let name = format!("Line_{}_{}_(AR)", eg.entities[x.0].name, eg.entities[y.0].name);
            if self.add_aux(name, def, EntityType::Line, EntityOrigin::LineDemand, Some(0.5)).is_some() { merged += 1; }
        }
        Some(merged)
    }

    /// 記号の式を読める形にする(調査用)。
    fn ar_describe(&self, atoms: &Atoms, v: &SVec) -> String {
        let eg = &self.prover.egraph;
        let nm = |x: usize| -> String {
            if is_virtual(x) { return format!("∞[{}]", eg.entities[usize::MAX - x].name); }
            let pre = if x >= ISO_I_BASE { "I" } else if x >= ISO_J_BASE { "J" } else { "" };
            format!("{}{}", pre, eg.entities[entity_of(x).0].name.chars().take(40).collect::<String>())
        };
        let mut rev: FxHashMap<u32, String> = FxHashMap::default();
        for (&(a, b), &id) in &atoms.ids { rev.insert(id, format!("s({},{})", nm(a), nm(b))); }
        for (&(k, o, x, y), &id) in &atoms.fresh { rev.insert(id, format!("f{}[{},{},{}]", k, o % 100000, x % 100000, y % 100000)); }
        v.iter().map(|(&c, &x)| if c == T { format!("{:+}T", x) } else { format!("{:+}·{}", x, rev.get(&c).cloned().unwrap_or(format!("#{}", c))) }).collect::<Vec<_>>().join(" ")
    }

    /// 直線の方向の点(無ければ直線ごとの仮の無限遠点)。
    fn ar_dir_or_virtual(&self, line: ClassId) -> usize {
        self.ar_direction(line).map(|d| d.0).unwrap_or_else(|| virtual_infinity(line))
    }

    /// 有限の点として扱ってよいか: 無限遠直線に乗っておらず、固定座標でも無限遠にない(平行な2直線の「交点」のような、
    /// まだ方向と同一視されていない無限遠点を有限の点として扱うと、偽の等式が出る)。
    fn ar_finite(&self, p: ClassId) -> bool {
        let eg = &self.prover.egraph;
        !eg.is_connected(p, eg.get_rep(eg.line_infinity))
            && !(0..eg.fixed_samples()).any(|k| eg.class_value(p, k).is_some_and(|v| v.len() >= 3 && v[2].0 == 0))
    }

    /// 有限の点の代表元のうち、曲線 c に乗っているもの(図の上でも乗っていて、互いに相異なるもの)。
    fn ar_points_on(&self, c: ClassId) -> Vec<ClassId> {
        let eg = &self.prover.egraph;
        let mut out: Vec<ClassId> = eg.entities[c.0].components.first().map(|comp| comp.subobjects.iter().map(|&s| eg.get_rep(s))
            .filter(|&s| eg.entities[s.0].entity_type == EntityType::Point && self.ar_finite(s)).collect()).unwrap_or_default();
        out.sort_by_key(|x| x.0);
        out.dedup();
        out.retain(|&p| eg.fixed_incidence(p, c, eg.entities[c.0].entity_type) == Some(Some(true)));
        let mut distinct: Vec<ClassId> = Vec::new();
        for p in out { if distinct.iter().all(|&q| eg.fixed_equal(p, q) == Some(Some(false))) { distinct.push(p); } }
        distinct
    }

    /// 直線の代表元のうち、点 a と b を両方通るもの。
    fn ar_lines_through(&self, a: ClassId, b: ClassId) -> Vec<ClassId> {
        let eg = &self.prover.egraph;
        let mut out: Vec<ClassId> = eg.entities[a.0].components.first().map(|comp| comp.subobjects.iter().map(|&s| eg.get_rep(s))
            .filter(|&s| eg.entities[s.0].entity_type == EntityType::Line && s != eg.get_rep(eg.line_infinity) && eg.is_connected(b, s)).collect()).unwrap_or_default();
        out.sort_by_key(|x| x.0);
        out.dedup();
        out
    }

    /// 円か(虚円点 I, J を通る二次曲線)。
    fn ar_is_circle(&self, c: ClassId) -> bool {
        let eg = &self.prover.egraph;
        eg.is_connected(c, eg.get_rep(eg.circ_i)) && eg.is_connected(c, eg.get_rep(eg.circ_j))
    }

    /// 定理の代わりに作る等式と、その前提。
    /// - 円: 弦 PX の方向の記号 β = θ_C(P) + θ_C(X) + c_C、接線 β = 2θ_C(P) + c_C(円周角の定理・接弦定理)。
    ///   単位円の複素座標で、弦 PX の方向の等角座標は −p·x、接線は −p² になる(2点の積に分かれる)ことによる。
    /// - 透視射影: 中心 O から直線 L への射影は一次分数変換なので、方向の差 = 点の差 + 各点の倍率 + 定数
    ///   (点→線束・線束→点の透視射影不変性)。
    /// - 円以外の二次曲線: 頂点 P からの線束も二次曲線の媒介変数の一次分数変換なので、同じ形(シュタイナーの定理)。
    fn ar_generated_relations(&self, atoms: &mut Atoms) -> Vec<(SVec, Vec<(String, Vec<ClassId>)>)> {
        let eg = &self.prover.egraph;
        let (ci, cj) = (eg.get_rep(eg.circ_i).0, eg.get_rep(eg.circ_j).0);
        let linf = eg.get_rep(eg.line_infinity);
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        let mut out = Vec::new();
        let conics: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&c| eg.get_rep(c) == c && eg.entities[c.0].entity_type == EntityType::Conic && eg.entities[c.0].is_active()).collect();
        let lines: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&l| eg.get_rep(l) == l && l != linf && eg.entities[l.0].entity_type == EntityType::Line && eg.entities[l.0].is_active()).collect();
        let tangent_of = |l: ClassId| -> Option<(ClassId, ClassId)> {
            eg.entities[l.0].components.first()?.definitions.iter().find_map(|d| match *d {
                Definition::TangentLine(c, p) => Some((eg.get_rep(c), eg.get_rep(p))), _ => None })
        };

        for &c in &conics {
            let pts = self.ar_points_on(c);
            if pts.len() < 2 { continue; }
            if self.ar_is_circle(c) {
                // 弦
                for i in 0..pts.len() {
                    for j in (i + 1)..pts.len() {
                        let (p, x) = (pts[i], pts[j]);
                        let chords = self.ar_lines_through(p, x);
                        for &l in &chords {
                            let d = self.ar_dir_or_virtual(l);
                            let mut v = SVec::new();
                            let ok = atoms.add_beta(&mut v, ci, cj, d, 1)
                                .and_then(|_| atoms.add_fresh(&mut v, (THETA, c.0, p.0, 0), -1))
                                .and_then(|_| atoms.add_fresh(&mut v, (THETA, c.0, x.0, 0), -1))
                                .and_then(|_| atoms.add_fresh(&mut v, (CIRCLE_C, c.0, 0, 0), -1));
                            if ok.is_some() { out.push((v, vec![conn(p, c), conn(x, c), conn(p, l), conn(x, l)])); }
                        }
                        // 直線の無い弦: 線分の向き s(JP,JX) − s(IP,IX) は、直線があればその β + c_0(地図の等式)なので、同じ形で書く。
                        if chords.is_empty() {
                            let mut v = SVec::new();
                            let ok = atoms.add_dir(&mut v, p, x, 1)
                                .and_then(|_| atoms.add_fresh(&mut v, (CHART_0, 0, 0, 0), -1))
                                .and_then(|_| atoms.add_fresh(&mut v, (THETA, c.0, p.0, 0), -1))
                                .and_then(|_| atoms.add_fresh(&mut v, (THETA, c.0, x.0, 0), -1))
                                .and_then(|_| atoms.add_fresh(&mut v, (CIRCLE_C, c.0, 0, 0), -1));
                            if ok.is_some() { out.push((v, vec![conn(p, c), conn(x, c)])); }
                        }
                    }
                }
                // 接線
                for &l in &lines {
                    let Some((tc, tp)) = tangent_of(l) else { continue };
                    if tc != c || !pts.contains(&tp) { continue; }
                    let d = self.ar_dir_or_virtual(l);
                    let mut v = SVec::new();
                    let ok = atoms.add_beta(&mut v, ci, cj, d, 1)
                        .and_then(|_| atoms.add_fresh(&mut v, (THETA, c.0, tp.0, 0), -2))
                        .and_then(|_| atoms.add_fresh(&mut v, (CIRCLE_C, c.0, 0, 0), -1));
                    if ok.is_some() { out.push((v, vec![conn(tp, c), ("DefinedBy:TangentLine".to_string(), vec![c, tp, l])])); }
                }
                // 円周角の記号 θ とシュタイナーの記号(二次曲線の媒介変数の差 s_C)をつなぐ: 円は I・J を通る二次曲線で、頂点から
                // I・J への直線の方向は I・J そのものなので、線束と円の対応は I・J を動かさない。(I,J;d_X,d_Y) = (I,J;X,Y)_C から
                // θ(X) = s_C(I,X) − s_C(X,J) + ℓ_C(円ごとの定数)。
                if pts.len() >= 3 && !std::env::var("GS_AR_OFF").unwrap_or_default().contains("conicunify") {
                    for &x in &pts {
                        let mut v = SVec::new();
                        let ok = atoms.add_fresh(&mut v, (THETA, c.0, x.0, 0), 1)
                            .and_then(|_| atoms.add_fresh_diff(&mut v, CONIC_S, c.0, ci, x.0, -1))
                            .and_then(|_| atoms.add_fresh_diff(&mut v, CONIC_S, c.0, x.0, cj, 1))
                            .and_then(|_| atoms.add_fresh(&mut v, (CONIC_LINK, c.0, 0, 0), -1));
                        if ok.is_some() { out.push((v, vec![conn(x, c)])); }
                    }
                }
            }
            // シュタイナー: 二次曲線の点 P からの線束は、二次曲線の媒介変数の一次分数変換(接線は X = P の方向)。円では I・J も
            // 曲線の点として入れる(P から I への方向は I)。円周角の形は、I・J を動かさないのでこの対応が定数倍になった特別な場合。
            let circle = self.ar_is_circle(c);
            let unify = circle && !std::env::var("GS_AR_OFF").unwrap_or_default().contains("conicunify");
            if (unify && pts.len() >= 2) || (!circle && pts.len() >= 4) {
                for &p in &pts {
                    let mut rays: Vec<(usize, usize, Vec<(String, Vec<ClassId>)>)> = Vec::new();
                    for &x in &pts {
                        if x == p { continue; }
                        if let Some(l) = self.ar_lines_through(p, x).first().copied() {
                            rays.push((x.0, self.ar_dir_or_virtual(l), vec![conn(p, c), conn(x, c), conn(p, l), conn(x, l)]));
                        }
                    }
                    for &l in &lines {
                        if let Some((tc, tp)) = tangent_of(l) && tc == c && tp == p {
                            rays.push((p.0, self.ar_dir_or_virtual(l), vec![conn(p, c), ("DefinedBy:TangentLine".to_string(), vec![c, p, l])]));
                        }
                    }
                    if unify {
                        for iso in [ci, cj] { rays.push((iso, iso, vec![conn(p, c), conn(ClassId(iso), c)])); }
                    }
                    if rays.len() < 4 { continue; }
                    for a in 0..rays.len() {
                        for b in (a + 1)..rays.len() {
                            let (x, dx, px) = &rays[a];
                            let (y, dy, py) = &rays[b];
                            let mut v = SVec::new();
                            let ok = atoms.add(&mut v, *dx, *dy, 1)
                                .and_then(|_| atoms.add_fresh_diff(&mut v, CONIC_S, c.0, *x, *y, -1))
                                .and_then(|_| atoms.add_fresh(&mut v, (STEINER_MU, c.0, p.0, *x), -1))
                                .and_then(|_| atoms.add_fresh(&mut v, (STEINER_MU, c.0, p.0, *y), -1))
                                .and_then(|_| atoms.add_fresh(&mut v, (STEINER_K, c.0, p.0, 0), -1));
                            if ok.is_some() { out.push((v, [px.clone(), py.clone()].concat())); }
                        }
                    }
                }
            }
        }

        // 等方線束と直線のつながり: J から直線 m への射影は m の無限遠点を無限遠直線に移すので、J の線束の差と m の上の差の
        // ずれは m ごとの定数(s(JX,JY) = s(X,Y) + κ_J(m))。I も同じ。ずれの差は m の方向の角の記号と全体の定数だけずれる
        // (z の差と z̄ の差の比が方向の等角座標)。
        for &m in &lines {
            let pts = self.ar_points_on(m);
            if pts.len() < 2 { continue; }
            for a in 0..pts.len() {
                for b in (a + 1)..pts.len() {
                    let (x, y) = (pts[a], pts[b]);
                    for (kind, iso) in [(CHART_J, iso_j as fn(ClassId) -> usize), (CHART_I, iso_i as fn(ClassId) -> usize)] {
                        let mut v = SVec::new();
                        let ok = atoms.add(&mut v, iso(x), iso(y), 1).and_then(|_| atoms.add(&mut v, x.0, y.0, -1))
                            .and_then(|_| atoms.add_fresh(&mut v, (kind, m.0, 0, 0), -1));
                        if ok.is_some() { out.push((v, vec![conn(x, m), conn(y, m)])); }
                    }
                }
            }
            let d = self.ar_dir_or_virtual(m);
            let mut v = SVec::new();
            let ok = atoms.add_fresh(&mut v, (CHART_J, m.0, 0, 0), 1).and_then(|_| atoms.add_fresh(&mut v, (CHART_I, m.0, 0, 0), -1))
                .and_then(|_| atoms.add_beta(&mut v, ci, cj, d, -1)).and_then(|_| atoms.add_fresh(&mut v, (CHART_0, 0, 0, 0), -1));
            if ok.is_some() { out.push((v, vec![conn(pts[0], m), conn(pts[1], m)])); }
        }

        // アフィンの等式: 同じ直線の上では、無限遠点までの差 s(X,∞_L) が一定(z=1 の座標で [X ∞ R] が X によらない)。
        // これで無限遠点との複比が本物の比になる(中点 (A,B;M,∞) = −1 から AM = MB)。座標の取り方によらない量
        // (複比・方向)の併合にしか使わないので健全。
        let mut on_line: FxHashMap<usize, Vec<ClassId>> = FxHashMap::default();
        for &l in &lines {
            let pts = self.ar_points_on(l);
            if pts.len() >= 2 {
                let inf = self.ar_dir_or_virtual(l);
                for &x in &pts[1..] {
                    let mut v = SVec::new();
                    let ok = atoms.add(&mut v, x.0, inf, 1).and_then(|_| atoms.add(&mut v, pts[0].0, inf, -1));
                    if ok.is_some() { out.push((v, vec![conn(pts[0], l), conn(x, l)])); }
                }
            }
            on_line.insert(l.0, pts);
        }

        // 中点の比(足し算の関係 A − B = 2(M − B) から来る、定数 2 の比): s(A,B) = s(A,M) + log 2、s(B,A) = s(B,M) + log 2。
        // 無限遠点との複比 −1 は「AM = MB」しか言わず、「BA = 2·BM」は足し算からしか出ないので、ここで定義から入れる。
        for i in 0..eg.entities.len() {
            let m = ClassId(i);
            if eg.get_rep(m) != m || eg.entities[i].entity_type != EntityType::Point { continue; }
            let defs = eg.entities[i].components.first().map(|c| c.definitions.clone()).unwrap_or_default();
            for def in &defs {
                let Definition::Midpoint(a, b) = *def else { continue };
                let (a, b) = (eg.get_rep(a), eg.get_rep(b));
                if a == b || a == m || b == m { continue; }
                let ent = eg.memo.get(&eg.normalize_definition(def)).copied().unwrap_or(m);
                let premise = vec![("DefinedBy:Midpoint".to_string(), vec![a, b, ent])];
                for (x, y) in [(a, b), (b, a)] {
                    let mut v = SVec::new();
                    let ok = atoms.add(&mut v, x.0, y.0, 1).and_then(|_| atoms.add(&mut v, x.0, m.0, -1))
                        .and_then(|_| atoms.add_fresh(&mut v, (LOG_PRIME, 2, 0, 0), -1));
                    if ok.is_some() { out.push((v, premise.clone())); }
                }
            }
        }

        self.ar_projection_relations(atoms, &lines, &on_line, &mut out);
        out
    }

    /// 射影: 中心 O から直線 L1 を直線 L2 に写す対応(O を通る直線 m ごとに m∩L1 ↦ m∩L2、L1∩L2 は動かない)は
    /// 一次分数変換なので、対応する2組について s(X2,Y2) − s(X1,Y1) = μ(X1) + μ(Y1) + κ(μ は点ごとの倍率)。
    /// - 有限の中心: L2 を無限遠直線に取る(X2 は直線 OX の方向の点。∞_L は動かない)。L2 が有限の直線の場合は、
    ///   2本の L からの対応を格子の中で合成すれば出る。
    /// - 無限遠の中心(方向 D の平行線の族): ∞_L1 ↦ ∞_L2 なので対応はアフィンで、有限の点の μ は一定(κ に入れる)。
    ///   族の1本である無限遠直線の対応 (∞_L1, ∞_L2) は、新しい記号 μ(∞) が増えるだけで何も足さないので入れない。
    /// 一次分数変換は3組の対応で決まるので、等式が意味を持つのは対応が4組以上(アフィンなら3組以上)あるときだけ。
    fn ar_projection_relations(&self, atoms: &mut Atoms, lines: &[ClassId], on_line: &FxHashMap<usize, Vec<ClassId>>,
        out: &mut Vec<(SVec, Vec<(String, Vec<ClassId>)>)>) {
        let eg = &self.prover.egraph;
        let linf = eg.get_rep(eg.line_infinity);
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        type Corr = (usize, usize, Vec<(String, Vec<ClassId>)>);
        let mut emit = |atoms: &mut Atoms, corr: &[Corr], mu: Option<(usize, usize)>, k: (u8, usize, usize, usize), shared: &[(String, Vec<ClassId>)]| {
            for a in 0..corr.len() {
                for b in (a + 1)..corr.len() {
                    let ((x1, x2, pa), (y1, y2, pb)) = (&corr[a], &corr[b]);
                    let mut v = SVec::new();
                    let mut ok = atoms.add(&mut v, *x2, *y2, 1).and_then(|_| atoms.add(&mut v, *x1, *y1, -1))
                        .and_then(|_| atoms.add_fresh(&mut v, k, -1));
                    if let Some((o, l)) = mu {
                        ok = ok.and_then(|_| atoms.add_fresh(&mut v, (PROJ_MU, o, l, *x1), -1))
                            .and_then(|_| atoms.add_fresh(&mut v, (PROJ_MU, o, l, *y1), -1));
                    }
                    if ok.is_some() { out.push((v, [pa.clone(), pb.clone(), shared.to_vec()].concat())); }
                }
            }
        };
        // 有限の中心 O、L2 = 無限遠直線。
        let points: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&o| eg.get_rep(o) == o && eg.entities[o.0].entity_type == EntityType::Point && eg.entities[o.0].is_active()
                && self.ar_finite(o)).collect();
        for &o in &points {
            let through_o: Vec<ClassId> = eg.entities[o.0].components.first().map(|comp| comp.subobjects.iter().map(|&s| eg.get_rep(s))
                .filter(|&s| s != linf && eg.entities[s.0].entity_type == EntityType::Line).collect()).unwrap_or_default();
            if through_o.len() < 3 { continue; }
            for &l in lines {
                if eg.is_connected(o, l) || eg.fixed_incidence(o, l, EntityType::Line) != Some(Some(false)) { continue; }
                let on_l = &on_line[&l.0];
                let mut corr: Vec<Corr> = Vec::new();
                for &m in &through_o {
                    // m と L の交点のうち図にある有限の点。
                    let Some(&x) = on_l.iter().find(|&&x| x != o && eg.is_connected(x, m)) else { continue };
                    if corr.iter().any(|c| c.0 == x.0) { continue; }
                    corr.push((x.0, self.ar_dir_or_virtual(m), vec![conn(o, m), conn(x, m), conn(x, l)]));
                }
                if corr.len() < 3 { continue; }
                // L と無限遠直線の交点 ∞_L は動かない。
                let inf = self.ar_dir_or_virtual(l);
                let prem = if is_virtual(inf) { Vec::new() } else { vec![("DefinedBy:DirectionOf".to_string(), vec![l, ClassId(inf)])] };
                corr.push((inf, inf, prem));
                emit(atoms, &corr, Some((o.0, l.0)), (PROJ_K, o.0, l.0, 0), &[]);
            }
        }
        // 無限遠の中心(平行線の族)。
        for (d, fam, l1, l2, corr) in self.ar_parallel_correspondences(lines, on_line) {
            if corr.len() < 3 { continue; }
            let corr: Vec<Corr> = corr.into_iter().map(|(x1, x2, p)| (x1.0, x2.0, p)).collect();
            emit(atoms, &corr, None, (PARALLEL_K, d, l1.0, l2.0), &fam);
        }
    }

    /// 方向 D の平行線の族が2直線 L1 < L2 を切る点の対応 (X1 ∈ L1, X2 ∈ L2)。2直線が交わる点は自分自身に対応する。
    /// 返り値は (D, 族全体の前提(今は空), L1, L2, [(X1, X2, 前提)])。対応が2つ以上あるものだけ。
    #[allow(clippy::type_complexity)]
    fn ar_parallel_correspondences(&self, lines: &[ClassId], on_line: &FxHashMap<usize, Vec<ClassId>>)
        -> Vec<(usize, Vec<(String, Vec<ClassId>)>, ClassId, ClassId, Vec<(ClassId, ClassId, Vec<(String, Vec<ClassId>)>)>)> {
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        let mut families: FxHashMap<usize, Vec<ClassId>> = FxHashMap::default();
        for &m in lines {
            if let Some(d) = self.ar_direction(m) { families.entry(d.0).or_default().push(m); }
        }
        let mut out = Vec::new();
        let mut dirs: Vec<usize> = families.keys().copied().collect();
        dirs.sort();
        for d in dirs {
            let fam = &families[&d];
            if fam.is_empty() { continue; }
            for i in 0..lines.len() {
                for j in (i + 1)..lines.len() {
                    let (l1, l2) = (lines[i], lines[j]);
                    if fam.contains(&l1) || fam.contains(&l2) { continue; }
                    let (p1, p2) = (&on_line[&l1.0], &on_line[&l2.0]);
                    let mut corr: Vec<(ClassId, ClassId, Vec<(String, Vec<ClassId>)>)> = Vec::new();
                    // 2直線の交点
                    if let Some(&a) = p1.iter().find(|a| p2.contains(a)) { corr.push((a, a, vec![conn(a, l1), conn(a, l2)])); }
                    for &m in fam {
                        let on_m = &on_line[&m.0];
                        let x1 = p1.iter().find(|x| on_m.contains(x));
                        let x2 = p2.iter().find(|x| on_m.contains(x));
                        if let (Some(&x1), Some(&x2)) = (x1, x2) {
                            if x1 == x2 || corr.iter().any(|c| c.0 == x1 || c.1 == x2) { continue; }
                            corr.push((x1, x2, vec![conn(x1, l1), conn(x1, m), conn(x2, l2), conn(x2, m),
                                ("DefinedBy:DirectionOf".to_string(), vec![m, ClassId(d)])]));
                        }
                    }
                    if corr.len() >= 2 { out.push((d, Vec::new(), l1, l2, corr)); }
                }
            }
        }
        out
    }

    /// 比 ⇒ 平行(検出)。2直線 L1, L2 を切る横断線 m_i(L1 と X1_i、L2 と X2_i で交わる)について:
    /// - L1, L2 が点 A で交わるなら、AX2_i / AX1_i の比が2本で一致すれば m_i ∥ m_j(中点連結定理はこの特別な場合)。
    /// - 既に平行な m_i ∥ m_j があり、第3の m_k で X1_i X1_k / X1_i X1_j と X2_i X2_k / X2_i X2_j が一致すれば m_k ∥ m_i。
    /// 返り値は併合する方向の組と、使った等式。
    fn ar_detect_parallel(&self, atoms: &mut Atoms, lattice: &mut Lattice, rc: &mut FxHashMap<u32, SVec>, zero: Option<&SVec>) -> Vec<(ClassId, ClassId, Vec<u32>)> {
        let eg = &self.prover.egraph;
        let linf = eg.get_rep(eg.line_infinity);
        let mut out = Vec::new();
        let Some(zero) = zero else { return out };
        let lines: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&l| eg.get_rep(l) == l && l != linf && eg.entities[l.0].entity_type == EntityType::Line && eg.entities[l.0].is_active()).collect();
        let on_line: FxHashMap<usize, Vec<ClassId>> = lines.iter().map(|&l| (l.0, self.ar_points_on(l))).collect();
        for i in 0..lines.len() {
            for j in (i + 1)..lines.len() {
                let (l1, l2) = (lines[i], lines[j]);
                let (p1, p2) = (&on_line[&l1.0], &on_line[&l2.0]);
                if p1.len() < 2 || p2.len() < 2 { continue; }
                let shared = p1.iter().find(|a| p2.contains(a)).copied();
                // 横断線: L1, L2 以外の直線で、L1 と L2 のそれぞれと図にある点で交わるもの(交点は共有点以外)。
                let mut trans: Vec<(ClassId, ClassId, ClassId, ClassId)> = Vec::new(); // (m, X1, X2, dir)
                for &m in &lines {
                    if m == l1 || m == l2 { continue; }
                    let on_m = &on_line[&m.0];
                    let x1 = p1.iter().find(|x| on_m.contains(x) && Some(**x) != shared);
                    let x2 = p2.iter().find(|x| on_m.contains(x) && Some(**x) != shared);
                    let (Some(&x1), Some(&x2)) = (x1, x2) else { continue };
                    if x1 == x2 { continue; }
                    let Some(d) = self.ar_direction(m) else { continue };
                    trans.push((m, x1, x2, d));
                }
                if trans.len() < 2 { continue; }
                for a in 0..trans.len() {
                    for b in (a + 1)..trans.len() {
                        let (ma, xa1, xa2, da) = trans[a];
                        let (mb, xb1, xb2, db) = trans[b];
                        if da == db || ma == mb { continue; }
                        let mut v = SVec::new();
                        let ok = if let Some(o) = shared {
                            // s(A,Xa2) − s(A,Xa1) − s(A,Xb2) + s(A,Xb1) ≡ 0
                            atoms.add(&mut v, o.0, xa2.0, 1).and_then(|_| atoms.add(&mut v, o.0, xa1.0, -1))
                                .and_then(|_| atoms.add(&mut v, o.0, xb2.0, -1)).and_then(|_| atoms.add(&mut v, o.0, xb1.0, 1))
                        } else {
                            // 既に平行な横断線 m_c ∥ m_a を基準に、m_b が同じ比で切るか。
                            let Some(&(_, xc1, xc2, _)) = trans.iter().find(|t| t.3 == da && t.0 != ma) else { continue };
                            atoms.add(&mut v, xc2.0, xa2.0, 1).and_then(|_| atoms.add(&mut v, xc1.0, xa1.0, -1))
                                .and_then(|_| atoms.add(&mut v, xc2.0, xb2.0, -1)).and_then(|_| atoms.add(&mut v, xc1.0, xb1.0, 1))
                        };
                        if ok.is_none() { continue; }
                        if lattice.reduce_cached(&v, rc).as_ref() != Some(zero) { continue; }
                        let Some((_, src)) = lattice.reduce(&v) else { continue };
                        if std::env::var("GS_DEBUG_AR_RAW").is_ok() {
                            println!("AR_RAW target {} {} : {}", eg.entities[da.0].name, eg.entities[db.0].name,
                                v.iter().map(|(c, x)| format!("{}:{}", c, x)).collect::<Vec<_>>().join(" "));
                        }
                        out.push((da, db, src));
                    }
                }
            }
        }
        out
    }

    /// 長さの記号の式: LengthSq(X,Y) = s(JX,JY) + s(IX,IY)、Product(a,b) は a と b の(LengthSq の)式の和。
    /// 「定義 def が同値類 rep にある」という前提(DefinedBy:型(引数…, rep))。監査は、その定義を元々持っていた実体と、
    /// 引数・rep への合流まで辿る。
    fn defined_by_premise(def: &Definition, rep: ClassId) -> (String, Vec<ClassId>) {
        let mut args = def.get_parents();
        args.push(rep);
        (format!("DefinedBy:{}", def.get_type_name()), args)
    }

    fn ar_length_vector(&self, def: &Definition, atoms: &mut Atoms) -> Option<(SVec, Vec<(String, Vec<ClassId>)>)> {
        let eg = &self.prover.egraph;
        let len = |d: &Definition, atoms: &mut Atoms| -> Option<SVec> {
            let Definition::LengthSq(x, y) = *d else { return None };
            let (x, y) = (eg.get_rep(x), eg.get_rep(y));
            if x == y || eg.is_connected(x, eg.line_infinity) || eg.is_connected(y, eg.line_infinity) { return None; }
            let mut v = SVec::new();
            atoms.add(&mut v, iso_j(x), iso_j(y), 1)?;
            atoms.add(&mut v, iso_i(x), iso_i(y), 1)?;
            Some(v)
        };
        match def {
            Definition::LengthSq(..) => Some((len(def, atoms)?, Vec::new())),
            Definition::Product(a, b) => {
                let first_len = |c: ClassId| eg.entities[eg.get_rep(c).0].components.first()
                    .and_then(|comp| comp.definitions.iter().find(|d| matches!(d, Definition::LengthSq(..))).cloned());
                let (da, db) = (first_len(*a)?, first_len(*b)?);
                let mut v = len(&da, atoms)?;
                add_scaled(&mut v, &len(&db, atoms)?, 1)?;
                // 積の値は、それぞれの因子の同値類にある長さの定義で決まる(その定義がその類にあることも前提)。
                Some((v, vec![Self::defined_by_premise(&da, eg.get_rep(*a)), Self::defined_by_premise(&db, eg.get_rep(*b))]))
            }
            _ => None,
        }
    }

    /// 相似の検出(AA)と結論。3辺が図にある三角形の、2つの頂点の有向角の記号の正準な剰余を鍵にして、同じ鍵の三角形どうしを
    /// 同じ向きの相似、符号を変えた鍵と一致するものを裏返しの相似とする。
    /// 同じ向きの相似は I と J を動かさない射影変換なので、J の線束の上では拡大・回転(複素数 a 倍)になる:
    /// 対応する各辺 (X,Y) について s(JX′,JY′) = s(JX,JY) + log a、I の線束で s(IX′,IY′) = s(IX,IY) + log ā。
    /// 裏返しは I と J を入れ替える。仮定の角から結論を出すのは線形でない(三角形が閉じる条件が足し算)ので、ここで検出して等式を足す。
    /// 返り値は足した相似の組の数。
    /// 三角形の枠を作る(相似・メネラウス・チェバが共有する)。
    fn ar_frame(&self) -> Frame {
        const MAX_TRIANGLES: usize = 3000;
        let eg = &self.prover.egraph;
        let points: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&o| eg.get_rep(o) == o && eg.entities[o.0].entity_type == EntityType::Point && eg.entities[o.0].is_active()
                && self.ar_finite(o)).collect();
        // 辺: 2点を通る直線が図にある組。
        let mut edge: FxHashMap<(usize, usize), ClassId> = FxHashMap::default();
        let mut nbr: FxHashMap<usize, Vec<ClassId>> = FxHashMap::default();
        let mut lines_at: FxHashMap<usize, Vec<ClassId>> = FxHashMap::default();
        for i in 0..points.len() {
            for j in (i + 1)..points.len() {
                let (a, b) = (points[i], points[j]);
                if let Some(&l) = self.ar_lines_through(a, b).first() {
                    edge.insert((a.0, b.0), l);
                    nbr.entry(a.0).or_default().push(b);
                    nbr.entry(b.0).or_default().push(a);
                    for x in [a, b] { let v = lines_at.entry(x.0).or_default(); if !v.contains(&l) { v.push(l); } }
                }
            }
        }
        let mut on_line: FxHashMap<usize, Vec<ClassId>> = FxHashMap::default();
        for &l in edge.values() { on_line.entry(l.0).or_insert_with(|| self.ar_points_on(l)); }
        let mut frame = Frame { points, edge, tris: Vec::new(), on_line, lines_at };
        let mut tris: Vec<[ClassId; 3]> = Vec::new();
        'outer: for &a in &frame.points {
            let Some(na) = nbr.get(&a.0) else { continue };
            for &b in na {
                if b.0 <= a.0 { continue; }
                for &c in na {
                    if c.0 <= b.0 || frame.line_of(b, c).is_none() { continue; }
                    let (lab, lbc, lca) = (frame.line_of(a, b).unwrap(), frame.line_of(b, c).unwrap(), frame.line_of(c, a).unwrap());
                    if lab == lbc || lbc == lca || lca == lab { continue; }
                    if eg.fixed_collinear(&[a, b, c]) != Some(Some(false)) { continue; }
                    tris.push([a, b, c]);
                    if tris.len() >= MAX_TRIANGLES { break 'outer; }
                }
            }
        }
        frame.tris = tris;
        frame
    }

    fn ar_similarity(&self, st: &mut ArState, frame: &Frame) -> Option<usize> {
        const MAX_PAIRS: usize = 400;
        let t_sim = std::time::Instant::now();
        let eg = &self.prover.egraph;
        let (ci, cj) = (eg.get_rep(eg.circ_i).0, eg.get_rep(eg.circ_j).0);
        let (points, tris) = (&frame.points, &frame.tris);
        let line_of = |a: ClassId, b: ClassId| frame.line_of(a, b);
        // 順序つきの三角形 (P,Q,R) の鍵 = (P での角, Q での角) の剰余。角は2方向だけで決まるので、方向の β の剰余と
        // 角の剰余(と符号を変えた剰余)を方向の組ごとに1度だけ求める(剰余は線形なので、剰余の差をもう一度簡約すればよい)。
        // 出どころは、相似の組として使うと決めたものだけ、角の式を直接簡約して取り直す。
        let mut beta_cache: FxHashMap<usize, Option<SVec>> = FxHashMap::default();
        let mut angle_cache: FxHashMap<(usize, usize), Option<(SVec, SVec)>> = FxHashMap::default();
        let mut angle = |st: &mut ArState, p: ClassId, q: ClassId, r: ClassId| -> Option<(SVec, SVec)> {
            let (dpq, dpr) = (self.ar_dir_or_virtual(line_of(p, q)?), self.ar_dir_or_virtual(line_of(p, r)?));
            if let Some(a) = angle_cache.get(&(dpq, dpr)) { return a.clone(); }
            let mut beta = |st: &mut ArState, d: usize| -> Option<SVec> {
                if let Some(b) = beta_cache.get(&d) { return b.clone(); }
                let mut v = SVec::new();
                let b = st.atoms.add_beta(&mut v, ci, cj, d, 1).and_then(|_| st.lattice.reduce(&v)).map(|r| r.0);
                beta_cache.insert(d, b.clone());
                b
            };
            let a = (|| {
                let mut v = beta(st, dpq)?;
                add_scaled(&mut v, &beta(st, dpr)?, -1)?;
                let (k, _) = st.lattice.reduce(&v)?;
                let (m, _) = st.lattice.reduce(&scaled(&k, -1)?)?;
                Some((k, m))
            })();
            angle_cache.insert((dpq, dpr), a.clone());
            a
        };
        // 三角形 (P,Q,R) の P と Q の角の式を直接簡約したときの出どころ。
        let exact_src = |st: &mut ArState, t: &[ClassId; 3]| -> Option<Vec<u32>> {
            let mut src = Vec::new();
            for (p, q, r) in [(t[0], t[1], t[2]), (t[1], t[2], t[0])] {
                let mut v = SVec::new();
                st.atoms.add_beta(&mut v, ci, cj, self.ar_dir_or_virtual(line_of(p, q)?), 1)?;
                st.atoms.add_beta(&mut v, ci, cj, self.ar_dir_or_virtual(line_of(p, r)?), -1)?;
                src = union(&src, &st.lattice.reduce(&v)?.1);
            }
            Some(src)
        };
        type Key = (Vec<(u32, i64)>, Vec<(u32, i64)>);
        let mut by_key: FxHashMap<Key, Vec<[ClassId; 3]>> = FxHashMap::default();
        let mut entries: Vec<([ClassId; 3], Key, Key)> = Vec::new();
        for t in tris {
            for [p, q, r] in [[t[0], t[1], t[2]], [t[0], t[2], t[1]], [t[1], t[0], t[2]], [t[1], t[2], t[0]], [t[2], t[0], t[1]], [t[2], t[1], t[0]]] {
                let (Some((kp, mp)), Some((kq, mq))) = (angle(st, p, q, r), angle(st, q, r, p)) else { continue };
                let key: Key = (kp.into_iter().collect(), kq.into_iter().collect());
                let mirror: Key = (mp.into_iter().collect(), mq.into_iter().collect());
                by_key.entry(key.clone()).or_default().push([p, q, r]);
                entries.push(([p, q, r], key, mirror));
            }
        }
        let sorted_set = |t: &[ClassId; 3]| { let mut v = t.map(|x| x.0); v.sort(); v };
        let mut done: rustc_hash::FxHashSet<([usize; 3], [usize; 3], bool)> = rustc_hash::FxHashSet::default();
        let mut pairs = 0usize;
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        // 見つけた相似の組 (t, u, 裏返しか, 番号)。後で対応する点を探す。
        let mut found: Vec<([ClassId; 3], [ClassId; 3], bool, usize)> = Vec::new();
        'scan: for (t, key, mirror) in &entries {
            for (opposite, k) in [(false, key), (true, mirror)] {
                let Some(others) = by_key.get(k) else { continue };
                for u in others {
                    let (sa, sb) = (sorted_set(t), sorted_set(u));
                    if sa == sb || sa > sb || !done.insert((sa, sb, opposite)) { continue; }
                    if pairs >= MAX_PAIRS || st.lattice.ops > st.ops_cap { break 'scan; }
                    let next = st.sim_ids.len();
                    let id = *st.sim_ids.entry((sa, sb, opposite)).or_insert(next);
                    let mut prem: Vec<(String, Vec<ClassId>)> = Vec::new();
                    for (x, y) in [(0, 1), (0, 2), (1, 2)] {
                        for tr in [t, u] {
                            if let Some(l) = line_of(tr[x], tr[y]) { prem.push(conn(tr[x], l)); prem.push(conn(tr[y], l)); }
                        }
                    }
                    let (Some(ts), Some(us)) = (exact_src(st, t), exact_src(st, u)) else { continue };
                    let key_src = union(&ts, &us);
                    let mut added = false;
                    for (x, y) in [(0, 1), (0, 2), (1, 2)] {
                        for v in sim_relations(&mut st.atoms, t[x], t[y], u[x], u[y], opposite, id) {
                            if st.insert(&self.prover.egraph, v, prem.clone(), &key_src)? { added = true; }
                        }
                    }
                    if added { pairs += 1; }
                    if std::env::var("GS_DEBUG_AR").is_ok() {
                        let nm = |c: ClassId| eg.entities[c.0].name.clone();
                        println!("  AR_DEBUG sim [{} {} {}] ~ [{} {} {}] opp={}", nm(t[0]), nm(t[1]), nm(t[2]), nm(u[0]), nm(u[1]), nm(u[2]), opposite);
                    }
                    found.push((*t, *u, opposite, id));
                }
            }
        }
        // 二辺夾角(SAS)と三辺(SSS)の相似。長さの2乗の比は s(J..) + s(I..) の差で格子に載るので、(P での角, |PQ|²/|PR|²) と
        // (|PQ|²/|PR|², |QR|²/|QP|²) の剰余を鍵にする。有向角(mod π)と長さの比だけでは「半直線が逆向き」と区別できず
        // (格子では J の線束の比の2倍までしか言えない)、三辺は同じ向きと裏返しのどちらもあり得る。作図は全て有理的なので、
        // どちらになるかは図全体で1つに決まる(2通りの積が恒等的に 0 なら片方が恒等的に 0)。固定座標の標本で向きを選ぶ。
        let dbg = std::env::var("GS_DEBUG_AR").is_ok();
        if dbg { println!("  AR_STAGE   sim-AA         {:?} tris={} pairs={} {} ops", t_sim.elapsed(), tris.len(), pairs, st.lattice.ops); }
        let t_sas = std::time::Instant::now();
        if pairs < MAX_PAIRS && st.lattice.ops <= st.ops_cap && !std::env::var("GS_AR_OFF").unwrap_or_default().contains("sas") {
            let samples = eg.fixed_samples();
            let i_unit: Vec<Option<ModInt>> = (0..samples).map(|k| eg.class_value(eg.circ_i, k)
                .filter(|v| v.len() >= 2 && v[0].0 != 0).map(|v| v[1] / v[0])).collect();
            let zval = |p: ClassId, k: usize, conj: bool| -> Option<ModInt> {
                let v = eg.class_value(p, k)?;
                if v.len() < 3 || v[2].0 == 0 { return None; }
                let (x, y, i) = (v[0] / v[2], v[1] / v[2], i_unit[k]?);
                Some(if conj { x - i * y } else { x + i * y })
            };
            // t_i ↦ u_i が同じ向き(裏返しなら共役を取った)相似か: (t1 − t0)/(t2 − t0) = (u1 − u0)/(u2 − u0)。
            let similar_numerically = |t: &[ClassId; 3], u: &[ClassId; 3], opposite: bool| -> bool {
                (0..samples).all(|k| (|| {
                    let a: Vec<ModInt> = t.iter().map(|&p| zval(p, k, false)).collect::<Option<_>>()?;
                    let b: Vec<ModInt> = u.iter().map(|&p| zval(p, k, opposite)).collect::<Option<_>>()?;
                    if (a[1] - a[0]).0 == 0 || (a[2] - a[0]).0 == 0 { return None; }
                    Some(((a[1] - a[0]) * (b[2] - b[0])).0 == ((a[2] - a[0]) * (b[1] - b[0])).0)
                })().unwrap_or(false))
            };
            fn len_vec(st: &mut ArState, p: ClassId, q: ClassId, r: ClassId) -> Option<SVec> {
                let mut v = SVec::new();
                st.atoms.add_len(&mut v, p, q, 1)?;
                st.atoms.add_len(&mut v, p, r, -1)?;
                Some(v)
            }
            let mut len_cache: FxHashMap<(usize, usize), Option<SVec>> = FxHashMap::default();
            let mut len_res = |st: &mut ArState, p: ClassId, q: ClassId| -> Option<SVec> {
                let key = (p.0.min(q.0), p.0.max(q.0));
                if let Some(v) = len_cache.get(&key) { return v.clone(); }
                let mut v = SVec::new();
                let r = st.atoms.add_len(&mut v, p, q, 1).and_then(|_| st.lattice.reduce(&v)).map(|r| r.0);
                len_cache.insert(key, r.clone());
                r
            };
            let mut ratio = |st: &mut ArState, p: ClassId, q: ClassId, r: ClassId| -> Option<Vec<(u32, i64)>> {
                let mut v = len_res(st, p, q)?;
                add_scaled(&mut v, &len_res(st, p, r)?, -1)?;
                Some(st.lattice.reduce(&v)?.0.into_iter().collect())
            };
            type K2 = (Vec<(u32, i64)>, Vec<(u32, i64)>);
            let mut by_sas: FxHashMap<K2, Vec<[ClassId; 3]>> = FxHashMap::default();
            let mut by_sss: FxHashMap<K2, Vec<[ClassId; 3]>> = FxHashMap::default();
            let mut sas_entries: Vec<([ClassId; 3], K2, K2)> = Vec::new();
            'keys: for t in tris {
                for [p, q, r] in [[t[0], t[1], t[2]], [t[0], t[2], t[1]], [t[1], t[0], t[2]], [t[1], t[2], t[0]], [t[2], t[0], t[1]], [t[2], t[1], t[0]]] {
                    if st.lattice.ops > st.ops_cap { break 'keys; }
                    let (Some(rp), Some(rq)) = (ratio(st, p, q, r), ratio(st, q, r, p)) else { continue };
                    by_sss.entry((rp.clone(), rq)).or_default().push([p, q, r]);
                    let Some((kp, mp)) = angle(st, p, q, r) else { continue };
                    let key: K2 = (kp.into_iter().collect(), rp.clone());
                    let mirror: K2 = (mp.into_iter().collect(), rp);
                    by_sas.entry(key.clone()).or_default().push([p, q, r]);
                    sas_entries.push(([p, q, r], key, mirror));
                }
            }
            // 候補 (t, u, 裏返しか, 三辺か)。同じ3点どうし(二等辺三角形の裏返しなど)も、対応が恒等でなければ使う。
            // 出どころ(簡約のやり直し)は重いので、既に見つけた組を除いた後で求める。
            let mut cands: Vec<([ClassId; 3], [ClassId; 3], bool, bool)> = Vec::new();
            let ratio_src = |st: &mut ArState, t: &[ClassId; 3], u: &[ClassId; 3], which: &[(usize, usize, usize)]| -> Option<Vec<u32>> {
                let mut src = Vec::new();
                for &(x, y, z) in which {
                    let mut v = len_vec(st, t[x], t[y], t[z])?;
                    add_scaled(&mut v, &len_vec(st, u[x], u[y], u[z])?, -1)?;
                    src = union(&src, &st.lattice.reduce(&v)?.1);
                }
                Some(src)
            };
            for (t, key, mirror) in &sas_entries {
                for (opposite, k) in [(false, key), (true, mirror)] {
                    let Some(others) = by_sas.get(k) else { continue };
                    for u in others {
                        if st.lattice.ops > st.ops_cap { break; }
                        if u == t || !similar_numerically(t, u, opposite) { continue; }
                        cands.push((*t, *u, opposite, false));
                    }
                }
            }
            for group in by_sss.values() {
                for x in 0..group.len() {
                    for y in (x + 1)..group.len() {
                        if st.lattice.ops > st.ops_cap { break; }
                        let (t, u) = (&group[x], &group[y]);
                        let Some(opposite) = [false, true].into_iter().find(|&o| similar_numerically(t, u, o)) else { continue };
                        cands.push((*t, *u, opposite, true));
                    }
                }
            }
            let mut self_done: rustc_hash::FxHashSet<(Vec<(usize, usize)>, bool)> = rustc_hash::FxHashSet::default();
            for (t, u, opposite, sss) in cands {
                if pairs >= MAX_PAIRS || st.lattice.ops > st.ops_cap { break; }
                let (sa, sb) = (sorted_set(&t), sorted_set(&u));
                // 同じ3点の組の中の対応(置換)ごとに別の相似。恒等な対応は除く。
                let mut perm: Vec<(usize, usize)> = (0..3).map(|i| (t[i].0, u[i].0)).collect();
                perm.sort_unstable();
                let pair_key = if sa < sb { (sa, sb, opposite) } else { (sb, sa, opposite) };
                if sa == sb {
                    if perm.iter().all(|(a, b)| a == b) || self_done.contains(&(perm.clone(), opposite)) { continue; }
                } else if done.contains(&pair_key) { continue; }
                // 鍵の出どころ: 辺の比(三辺なら2つ)と、二辺夾角なら角の等式(裏返しは符号を変えて)。
                let key_src = if sss { ratio_src(st, &t, &u, &[(0, 1, 2), (1, 2, 0)]) } else { (|| {
                    let rs = ratio_src(st, &t, &u, &[(0, 1, 2)])?;
                    let (lt1, lt2, lu1, lu2) = (line_of(t[0], t[1])?, line_of(t[0], t[2])?, line_of(u[0], u[1])?, line_of(u[0], u[2])?);
                    let sign = if opposite { -1 } else { 1 };
                    let mut v = SVec::new();
                    st.atoms.add_beta(&mut v, ci, cj, self.ar_dir_or_virtual(lt1), 1)?;
                    st.atoms.add_beta(&mut v, ci, cj, self.ar_dir_or_virtual(lt2), -1)?;
                    st.atoms.add_beta(&mut v, ci, cj, self.ar_dir_or_virtual(lu1), -sign)?;
                    st.atoms.add_beta(&mut v, ci, cj, self.ar_dir_or_virtual(lu2), sign)?;
                    Some(union(&rs, &st.lattice.reduce(&v)?.1))
                })() };
                let Some(key_src) = key_src else { continue };
                let id_key = if sa == sb {
                    self_done.insert((perm.clone(), opposite));
                    let mut ub = [0usize; 3];
                    for (i, (_, b)) in perm.iter().enumerate() { ub[i] = *b; }
                    (sa, ub, opposite)
                } else {
                    done.insert(pair_key);
                    pair_key
                };
                let next = st.sim_ids.len();
                let id = *st.sim_ids.entry(id_key).or_insert(next);
                let mut prem: Vec<(String, Vec<ClassId>)> = Vec::new();
                for (x, y) in [(0, 1), (0, 2), (1, 2)] {
                    for tr in [&t, &u] {
                        if let Some(l) = line_of(tr[x], tr[y]) { prem.push(conn(tr[x], l)); prem.push(conn(tr[y], l)); }
                    }
                }
                let mut added = false;
                for (x, y) in [(0, 1), (0, 2), (1, 2)] {
                    for v in sim_relations(&mut st.atoms, t[x], t[y], u[x], u[y], opposite, id) {
                        if st.insert(&self.prover.egraph, v, prem.clone(), &key_src)? { added = true; }
                    }
                }
                if added { pairs += 1; }
                if std::env::var("GS_DEBUG_AR").is_ok() {
                    let nm = |c: ClassId| eg.entities[c.0].name.clone();
                    println!("  AR_DEBUG sim(SAS/SSS) [{} {} {}] ~ [{} {} {}] opp={}", nm(t[0]), nm(t[1]), nm(t[2]), nm(u[0]), nm(u[1]), nm(u[2]), opposite);
                }
                if sa != sb { found.push((t, u, opposite, id)); }
            }
        }
        if dbg { println!("  AR_STAGE   sim-SAS/SSS    {:?} pairs={} {} ops", t_sas.elapsed(), pairs, st.lattice.ops); }
        let t = std::time::Instant::now();
        let ncorr = self.ar_sim_correspondences(st, &found, &line_of, points)?;
        if dbg { println!("  AR_STAGE   sim-corr       {:?} corr={} {} ops", t.elapsed(), ncorr, st.lattice.ops); }
        Some(pairs)
    }

    /// 相似で対応する点: 相似 σ: t → u の辺 XY の上の点 P と、対応する辺 X'Y' の上の点 P' について、
    /// σ(X) = X' からの2つの等式(s(JX',JP') − s(JX,JP) = log a と I の線束の同じ式)が格子で言えるなら P' = σ(P)
    /// (同じ直線の上では、これは内分比 XP/XY = X'P'/X'Y' が言えることと同じ)。
    /// 対応が分かった点は、三角形の頂点と既に分かった対応点の全てとの組で σ の等式を足す。返り値は見つけた対応の数。
    /// 固定座標の複素座標 z = x + iy(conj なら x − iy。i は有限体の −1 の平方根)。
    fn ar_zval(&self, p: ClassId, k: usize, conj: bool) -> Option<ModInt> {
        let eg = &self.prover.egraph;
        let iv = eg.class_value(eg.circ_i, k).filter(|v| v.len() >= 2 && v[0].0 != 0).map(|v| v[1] / v[0])?;
        let v = eg.class_value(p, k)?;
        if v.len() < 3 || v[2].0 == 0 { return None; }
        let (x, y) = (v[0] / v[2], v[1] / v[2]);
        Some(if conj { x - iv * y } else { x + iv * y })
    }

    /// 固定座標で、t_i ↦ u_i が同じ向き(opposite なら裏返し)の相似か: (t2 − t0)/(t1 − t0) = (u2 − u0)/(u1 − u0)。
    fn ar_maps_numerically(&self, t: [ClassId; 3], u: [ClassId; 3], opposite: bool) -> bool {
        (0..self.prover.egraph.fixed_samples()).all(|k| (|| {
            let a: Vec<ModInt> = t.iter().map(|&p| self.ar_zval(p, k, false)).collect::<Option<_>>()?;
            let b: Vec<ModInt> = u.iter().map(|&p| self.ar_zval(p, k, opposite)).collect::<Option<_>>()?;
            if (a[1] - a[0]).0 == 0 || (b[1] - b[0]).0 == 0 { return None; }
            Some(((a[2] - a[0]) * (b[1] - b[0])).0 == ((b[2] - b[0]) * (a[1] - a[0])).0)
        })().unwrap_or(false))
    }

    fn ar_sim_correspondences(&self, st: &mut ArState, found: &[([ClassId; 3], [ClassId; 3], bool, usize)],
        line_of: &dyn Fn(ClassId, ClassId) -> Option<ClassId>, points: &[ClassId]) -> Option<usize> {
        const MAX_CANDIDATES: usize = 20000;
        let is_point: rustc_hash::FxHashSet<usize> = points.iter().map(|p| p.0).collect();
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        let eg = &self.prover.egraph;
        let zero = st.lattice.reduce(&SVec::new())?.0;
        let mut tried = 0usize;
        let mut count = 0usize;
        for &(t, u, opposite, id) in found {
            // 対応の分かった点の組 (P, P', その前提, 使った等式)。三角形の頂点から始める。
            let mut pts: Vec<(ClassId, ClassId)> = (0..3).map(|i| (t[i], u[i])).collect();
            for (x, y) in [(0, 1), (0, 2), (1, 2)] {
                let (Some(l), Some(l2)) = (line_of(t[x], t[y]), line_of(u[x], u[y])) else { continue };
                let on_l: Vec<ClassId> = self.ar_points_on(l).into_iter().filter(|p| is_point.contains(&p.0) && !t.contains(p)).collect();
                let on_l2: Vec<ClassId> = self.ar_points_on(l2).into_iter().filter(|p| is_point.contains(&p.0) && !u.contains(p)).collect();
                for &p in &on_l {
                    for &p2 in &on_l2 {
                        if pts.iter().any(|&(a, b)| a == p || b == p2) { continue; }
                        // 候補は固定座標で絞る: 相似を当てはめて P が P′ に移るものだけを格子で確かめる(格子の簡約は重い)。
                        if !self.ar_maps_numerically([t[x], t[y], p], [u[x], u[y], p2], opposite) { continue; }
                        tried += 1;
                        if tried > MAX_CANDIDATES || st.lattice.ops > st.ops_cap { return Some(count); }
                        let rels = sim_relations(&mut st.atoms, t[x], p, u[x], p2, opposite, id);
                        if rels.len() < 2 { continue; }
                        let mut src = Vec::new();
                        let mut ok = true;
                        for v in &rels {
                            match st.lattice.reduce(v) {
                                Some((r, s)) if r == zero => src = union(&src, &s),
                                _ => { ok = false; break; }
                            }
                        }
                        if !ok { continue; }
                        let prem = vec![conn(p, l), conn(p2, l2)];
                        for &(a, a2) in &pts {
                            // 図の上で同じ点の組(相似の中心とまだマージされていない点など)の等式は、記号が打ち消し合って
                            // 「log a = 0」のような偽の等式になる(centroid で 2 = −1 が出た)。
                            if a == t[x] || eg.fixed_equal(a, p) != Some(Some(false)) || eg.fixed_equal(a2, p2) != Some(Some(false)) { continue; }
                            for v in sim_relations(&mut st.atoms, a, p, a2, p2, opposite, id) {
                                st.insert(&self.prover.egraph, v, prem.clone(), &src)?;
                            }
                        }
                        if std::env::var("GS_DEBUG_AR").is_ok() {
                            let nm = |c: ClassId| self.prover.egraph.entities[c.0].name.clone();
                            println!("  AR_DEBUG corr [{} {} {}] -> [{} {} {}] opp={} : {} -> {}", nm(t[0]), nm(t[1]), nm(t[2]), nm(u[0]), nm(u[1]), nm(u[2]), opposite, nm(p), nm(p2));
                        }
                        pts.push((p, p2));
                        count += 1;
                        break;
                    }
                }
            }
        }
        Some(count)
    }

    /// 枠の点の固定座標 (x, y)(標本ごと)。
    fn ar_frame_xy(&self, frame: &Frame) -> Vec<Option<Vec<(ModInt, ModInt)>>> {
        let eg = &self.prover.egraph;
        frame.points.iter().map(|&p| (0..eg.fixed_samples()).map(|k| {
            let v = eg.class_value(p, k)?;
            (v.len() >= 3 && v[2].0 != 0).then(|| (v[0] / v[2], v[1] / v[2]))
        }).collect()).collect()
    }

    /// 式 v が格子で 0 に還元されれば、使った等式。
    fn ar_proves(st: &mut ArState, v: &SVec, zero: &SVec) -> Option<Vec<u32>> {
        let (r, src) = st.lattice.reduce(v)?;
        (&r == zero).then_some(src)
    }

    /// 鏡映(検出 → 等式)。直線 m に関する鏡映 σ は I と J を入れ替える等長変換なので、対応する2組 (X,Y) ↦ (X′,Y′) に
    /// ついて s(JX′,JY′) = s(IX,IY) + κ_J、s(IX′,IY′) = s(JX,JY) + κ_I(裏返しの相似と同じ形)で、κ_J + κ_I = 0。
    /// 対応は m の上の点(動かない)と、σ(A) = B と言えた組の両向き。σ(A) = B と言える条件(格子と図で):
    /// AB ⊥ m で、AB の中点(図にある)が m の上にあるか m の上の点 P で PA = PB、または m の上の2点 P, Q で PA = PB・QA = QB。
    /// 候補は固定座標で選ぶ(AB の垂直二等分線の値が図の直線 m の値と一致する組)。返り値は鏡映の数。
    fn ar_reflections(&self, st: &mut ArState, frame: &Frame, xy: &[Option<Vec<(ModInt, ModInt)>>],
        links: &mut Vec<(ClassId, ClassId, Vec<u32>, &'static str)>) -> Option<usize> {
        const MAX_CORR: usize = 12;
        let eg = &self.prover.egraph;
        let linf = eg.get_rep(eg.line_infinity);
        let (ci, cj) = (eg.get_rep(eg.circ_i).0, eg.get_rep(eg.circ_j).0);
        let samples = eg.fixed_samples();
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        let mut line_by_key: FxHashMap<Vec<[i64; 3]>, ClassId> = FxHashMap::default();
        for l in (0..eg.entities.len()).map(ClassId) {
            if eg.get_rep(l) != l || l == linf || eg.entities[l.0].entity_type != EntityType::Line || !eg.entities[l.0].is_active() { continue; }
            let Some(key) = (0..samples).map(|k| eg.class_value(l, k).and_then(|v| line_key(&v))).collect::<Option<Vec<_>>>() else { continue };
            line_by_key.entry(key).or_insert(l);
        }
        let half = ModInt::new(1) / ModInt::new(2);
        let mut cand: BTreeMap<usize, Vec<(ClassId, ClassId)>> = BTreeMap::new();
        for i in 0..frame.points.len() {
            let Some(pa) = &xy[i] else { continue };
            for j in (i + 1)..frame.points.len() {
                let Some(pb) = &xy[j] else { continue };
                let key: Option<Vec<[i64; 3]>> = (0..samples).map(|k| {
                    let ((ax, ay), (bx, by)) = (pa[k], pb[k]);
                    let (u, v) = (bx - ax, by - ay);
                    // 等方な AB(u² + v² = 0)には垂直二等分線が無い。
                    if (u * u + v * v).0 == 0 { return None; }
                    line_key(&[u, v, -(bx * bx + by * by - ax * ax - ay * ay) * half])
                }).collect();
                let Some(key) = key else { continue };
                if let Some(&m) = line_by_key.get(&key) { cand.entry(m.0).or_default().push((frame.points[i], frame.points[j])); }
            }
        }
        let zero = st.lattice.reduce(&SVec::new())?.0;
        // 軸ごとの (動かない点, その前提, σ(A) = B と言えた組)。
        type Proven = Vec<(ClassId, ClassId, Vec<u32>, Vec<(String, Vec<ClassId>)>)>;
        let mut groups: BTreeMap<usize, (Vec<ClassId>, Vec<(String, Vec<ClassId>)>, Proven)> = BTreeMap::new();
        let off_num = std::env::var("GS_AR_OFF").unwrap_or_default().contains("numrefl");
        for (m, pairs) in cand {
            if off_num { break; }
            let m = ClassId(m);
            let on_m = self.ar_points_on(m);
            let dm = self.ar_dir_or_virtual(m);
            let mut proven: Proven = Vec::new();
            for (a, b) in pairs {
                // AB ⊥ m: 線分 AB の向き − (β(m) + c_0) = 2T。
                let mut v = SVec::new();
                let perp = st.atoms.add_dir(&mut v, a, b, 1).and_then(|_| st.atoms.add_beta(&mut v, ci, cj, dm, -1))
                    .and_then(|_| st.atoms.add_fresh(&mut v, (CHART_0, 0, 0, 0), -1))
                    .and_then(|_| add_scaled(&mut v, &SVec::from([(T, 2)]), -1))
                    .and_then(|_| Self::ar_proves(st, &v, &zero));
                let mut eqs: Vec<(ClassId, Vec<u32>)> = Vec::new();
                for &p in &on_m {
                    let mut v = SVec::new();
                    if st.atoms.add_len(&mut v, p, a, 1).and_then(|_| st.atoms.add_len(&mut v, p, b, -1)).is_none() { continue; }
                    if let Some(s) = Self::ar_proves(st, &v, &zero) { eqs.push((p, s)); if eqs.len() >= 2 { break; } }
                }
                let mid = eg.memo.get(&eg.normalize_definition(&Definition::Midpoint(a, b))).map(|&x| eg.get_rep(x))
                    .filter(|&x| eg.is_connected(x, m));
                let found = match (&perp, mid, eqs.as_slice()) {
                    (Some(ps), Some(x), _) => Some((ps.clone(), vec![Self::defined_by_premise(&Definition::Midpoint(a, b), x), conn(x, m)])),
                    (Some(ps), None, [(p, s), ..]) => Some((union(ps, s), vec![conn(*p, m)])),
                    (None, _, [(p, s), (q, t), ..]) => Some((union(s, t), vec![conn(*p, m), conn(*q, m)])),
                    _ => None,
                };
                if let Some((src, prem)) = found { proven.push((a, b, src, prem)); }
            }
            if proven.is_empty() { continue; }
            let fixed_prem: Vec<(String, Vec<ClassId>)> = on_m.iter().map(|&p| conn(p, m)).collect();
            groups.insert(m.0, (on_m, fixed_prem, proven));
        }
        // 円の外の点 A から引いた2本の接線(接点 T1, T2): 直線 AO(O は円の中心)に関する鏡映で T1 ↔ T2(接線の長さが等しい)。
        // 直線 AO が図に無くても、動かない点 A, O と組 T1 ↔ T2 だけで等式が作れる。
        let mut virt = 0usize;
        let off = std::env::var("GS_AR_OFF").unwrap_or_default();
        for (c, o, cdef) in if off.contains("tangent") { Vec::new() } else { self.ar_known_centers() } {
            let tangents: Vec<(ClassId, ClassId)> = (0..eg.entities.len()).map(ClassId)
                .filter(|&l| eg.get_rep(l) == l && eg.entities[l.0].entity_type == EntityType::Line && eg.entities[l.0].is_active())
                .filter_map(|l| eg.entities[l.0].components.first()?.definitions.iter().find_map(|d| match *d {
                    Definition::TangentLine(cc, t) if eg.get_rep(cc) == c => Some((l, eg.get_rep(t))), _ => None }))
                .collect();
            for i in 0..tangents.len() {
                for j in (i + 1)..tangents.len() {
                    let ((l1, t1), (l2, t2)) = (tangents[i], tangents[j]);
                    if t1 == t2 || eg.fixed_equal(t1, t2) != Some(Some(false)) { continue; }
                    let Some(a) = self.ar_points_on(l1).into_iter().find(|&a| eg.is_connected(a, l2)) else { continue };
                    if a == o || eg.fixed_equal(a, o) != Some(Some(false)) { continue; }
                    let prem = vec![Self::defined_by_premise(&Definition::TangentLine(c, t1), l1), Self::defined_by_premise(&Definition::TangentLine(c, t2), l2),
                        conn(a, l1), conn(a, l2), cdef.clone()];
                    let key = match self.ar_lines_through(a, o).first() {
                        Some(&m) => {
                            groups.entry(m.0).or_insert_with(|| { let on = self.ar_points_on(m); let pr = on.iter().map(|&p| conn(p, m)).collect(); (on, pr, Vec::new()) });
                            m.0
                        }
                        None => { virt += 1; groups.insert(usize::MAX / 8 + virt, (vec![a, o], Vec::new(), Vec::new())); usize::MAX / 8 + virt }
                    };
                    groups.get_mut(&key)?.2.push((t1, t2, Vec::new(), prem));
                }
            }
        }
        let mut count = 0usize;
        for (key, (fixed, fixed_prem, proven)) in groups {
            if proven.is_empty() { continue; }
            let mut corr: Vec<(ClassId, ClassId)> = Vec::new();
            let mut prem: Vec<(String, Vec<ClassId>)> = Vec::new();
            let mut src: Vec<u32> = Vec::new();
            for (k, &p) in fixed.iter().enumerate().take(MAX_CORR / 2) { corr.push((p, p)); if let Some(pr) = fixed_prem.get(k) { prem.push(pr.clone()); } }
            for (a, b, s, pr) in proven {
                if corr.len() + 2 > MAX_CORR { break; }
                corr.push((a, b));
                corr.push((b, a));
                src = union(&src, &s);
                prem.extend(pr);
            }
            let id = REFLECT_BASE + key;
            let mut v = SVec::new();
            st.atoms.add_fresh(&mut v, (SIM_J, id, 0, 0), 1)?;
            st.atoms.add_fresh(&mut v, (SIM_I, id, 0, 0), 1)?;
            st.insert(eg, v, prem.clone(), &src)?;
            for x in 0..corr.len() {
                for y in (x + 1)..corr.len() {
                    let ((p, p2), (q, q2)) = (corr[x], corr[y]);
                    if p == q || p2 == q2 { continue; }
                    for v in sim_relations(&mut st.atoms, p, q, p2, q2, true, id) { st.insert(eg, v, prem.clone(), &src)?; }
                }
            }
            // 逆: 軸 m が図の直線なら、A ↔ B の両端から格子で等距離な図の点を m に乗せる(垂直二等分線の逆)。
            if key < usize::MAX / 8 && let Some(&(a, b)) = corr.iter().find(|(p, q)| p != q) {
                let m = ClassId(key);
                let zero = st.lattice.reduce(&SVec::new())?.0;
                for &p in &frame.points {
                    if p == a || p == b || eg.is_connected(p, m) || eg.fixed_incidence(p, m, EntityType::Line) != Some(Some(true)) { continue; }
                    let mut v = SVec::new();
                    if st.atoms.add_len(&mut v, p, a, 1).and_then(|_| st.atoms.add_len(&mut v, p, b, -1)).is_none() { continue; }
                    let Some(s2) = Self::ar_proves(st, &v, &zero) else { continue };
                    let n = st.note(prem.clone());
                    links.push((p, m, union(&union(&src, &s2), &[n]), "代数的な追跡(垂直二等分線の逆)"));
                }
            }
            if std::env::var("GS_DEBUG_AR").is_ok() {
                let nm = |c: ClassId| eg.entities[c.0].name.clone();
                let axis = if key < usize::MAX / 8 { nm(ClassId(key)) } else { "(仮の軸)".to_string() };
                println!("  AR_DEBUG reflect {} : {}", axis, corr.iter().map(|&(a, b)| format!("{}->{}", nm(a), nm(b))).collect::<Vec<_>>().join(" "));
            }
            count += 1;
        }
        Some(count)
    }

    /// 定義で中心が分かっている円(中心と1点で決まる円): (円, 中心, 前提)。
    fn ar_known_centers(&self) -> Vec<(ClassId, ClassId, (String, Vec<ClassId>))> {
        let eg = &self.prover.egraph;
        let mut out = Vec::new();
        for c in (0..eg.entities.len()).map(ClassId) {
            if eg.get_rep(c) != c || eg.entities[c.0].entity_type != EntityType::Conic || !eg.entities[c.0].is_active() { continue; }
            let Some(comp) = eg.entities[c.0].components.first() else { continue };
            if let Some((o, p)) = comp.definitions.iter().find_map(|d| match *d { Definition::CircleCenterPoint(o, p) => Some((o, p)), _ => None }) {
                let (o, p) = (eg.get_rep(o), eg.get_rep(p));
                if eg.is_connected(o, eg.line_infinity) { continue; }
                out.push((c, o, Self::defined_by_premise(&Definition::CircleCenterPoint(o, p), c)));
            }
        }
        out
    }

    /// 中心の分かった円(検出 → 等式)。点 O から等距離の点(格子で |OP|² が等しい)は中心 O の円に乗る。円を単位円の
    /// 媒介変数 t で書くと z_P − z_O = r·t_P、z̄_P − z̄_O = r/t_P なので、θ(P) = log t_P として
    /// s(JO,JP) = θ(P) + c_J、s(IO,IP) = −θ(P) + c_I(どちらも線形。2 で割らずに長さと角がつながる)。弦の等式
    /// β(PX) = θ(P) + θ(X) + c_C と同じ θ を使うので c_C − c_J + c_I + c_0 = 2T も入れる(c_0 は地図の等式の定数)。
    /// ここから中心角・斜辺の中線・二等辺三角形の底角・半径と接線の直交が出る。
    /// 円の実体に3点以上が乗っていればその円の θ を使って円の上の他の点にも等式を足し、無ければ仮の円を置いて図にある弦の
    /// 等式も足す。O が AB の中点で ∠APB が直角と格子で言える点 P も同じ円に乗せる(直径の上の円周角の逆)。
    /// 候補は固定座標で選ぶ(O からの距離の2乗が等しい点)。返り値は円の数。
    fn ar_centered_circles(&self, st: &mut ArState, frame: &Frame, xy: &[Option<Vec<(ModInt, ModInt)>>],
        links: &mut Vec<(ClassId, ClassId, Vec<u32>, &'static str)>) -> Option<usize> {
        const MAX_CIRCLES: usize = 200;
        const MAX_MEMBERS: usize = 16;
        let eg = &self.prover.egraph;
        let samples = eg.fixed_samples();
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        let circles: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&c| eg.get_rep(c) == c && eg.entities[c.0].entity_type == EntityType::Conic && eg.entities[c.0].is_active() && self.ar_is_circle(c)).collect();
        let zero = st.lattice.reduce(&SVec::new())?.0;
        let len_diff = |st: &mut ArState, o: ClassId, p: ClassId, q: ClassId| -> Option<SVec> {
            let mut v = SVec::new();
            st.atoms.add_len(&mut v, o, p, 1)?;
            st.atoms.add_len(&mut v, o, q, -1)?;
            Some(v)
        };
        let mut count = 0usize;
        // 定義で中心が分かっている円(中心と1点で決まる円)。
        let mut structural: Vec<(ClassId, ClassId)> = Vec::new();
        let off_struct = std::env::var("GS_AR_OFF").unwrap_or_default().contains("structcircle");
        for &c in &circles {
            if off_struct { break; }
            let defs = eg.entities[c.0].components.first().map(|comp| comp.definitions.clone()).unwrap_or_default();
            for d in &defs {
                let Definition::CircleCenterPoint(o, p) = *d else { continue };
                let o = eg.get_rep(o);
                if eg.is_connected(o, eg.line_infinity) || structural.iter().any(|x| x.0 == c) { continue; }
                let cl: Vec<(ClassId, Vec<u32>, Vec<(String, Vec<ClassId>)>)> = self.ar_points_on(c).into_iter().filter(|&q| q != o)
                    .take(MAX_MEMBERS).map(|q| (q, Vec::new(), vec![conn(q, c)])).collect();
                if cl.is_empty() { continue; }
                let cprem = vec![Self::defined_by_premise(&Definition::CircleCenterPoint(o, eg.get_rep(p)), c)];
                self.ar_emit_circle(st, frame, o, c.0, Some(c), &cl, &cprem, &[], links)?;
                structural.push((c, o));
                count += 1;
            }
        }
        // 図の上で同じ位置の別の実体(まだ合流していない同じ点)は1つだけ使う。同じ点を2つの円の点として持つと、その2点を
        // 「通る」直線(どれでもよい)を弦とみなした偽の等式が入る(中心 A の円の点 I と EF の中点で、半径 AI を弦とした)。
        let dup: Vec<bool> = (0..frame.points.len()).map(|j| xy[j].as_ref().is_some_and(|pj| (0..j).any(|i| xy[i].as_ref() == Some(pj)))).collect();
        for (i, &o) in frame.points.iter().enumerate() {
            if dup[i] { continue; }
            let Some(po) = &xy[i] else { continue };
            let mut groups: BTreeMap<Vec<i64>, Vec<ClassId>> = BTreeMap::new();
            for (j, &p) in frame.points.iter().enumerate() {
                if j == i || dup[j] { continue; }
                let Some(pp) = &xy[j] else { continue };
                let key: Vec<i64> = (0..samples).map(|k| { let (dx, dy) = (pp[k].0 - po[k].0, pp[k].1 - po[k].1); (dx * dx + dy * dy).0 }).collect();
                if key.contains(&0) { continue; }
                groups.entry(key).or_default().push(p);
            }
            let mids: Vec<(ClassId, ClassId)> = eg.entities[o.0].components.first().map(|c| c.definitions.iter().filter_map(|d| match *d {
                Definition::Midpoint(a, b) => Some((eg.get_rep(a), eg.get_rep(b))), _ => None }).collect()).unwrap_or_default();
            for g in groups.into_values() {
                if g.len() < 2 { continue; }
                // 格子で |OP|² が等しい類に分ける。各点は (点, 使った等式, 前提)。類の最初の点が半径を決める。
                let mut classes: Vec<Vec<(ClassId, Vec<u32>, Vec<(String, Vec<ClassId>)>)>> = Vec::new();
                for &p in &g {
                    let mut placed = false;
                    for cl in classes.iter_mut() {
                        let Some(v) = len_diff(st, o, p, cl[0].0) else { continue };
                        if let Some(s) = Self::ar_proves(st, &v, &zero) { cl.push((p, s, Vec::new())); placed = true; break; }
                    }
                    if !placed { classes.push(vec![(p, Vec::new(), Vec::new())]); }
                }
                // 直径の上の直角: O = AB の中点で A, B が同じ類にあれば、∠APB が直角の点 P を足す。
                let off_rj = std::env::var("GS_AR_OFF").unwrap_or_default().contains("rightjoin");
                for &(a, b) in if off_rj { &[][..] } else { &mids[..] } {
                    let Some(k) = classes.iter().position(|cl| cl.iter().any(|m| m.0 == a) && cl.iter().any(|m| m.0 == b)) else { continue };
                    let base = classes[k].iter().find(|m| m.0 == a).map(|m| m.1.clone()).unwrap_or_default();
                    for kk in 0..classes.len() {
                        if kk == k { continue; }
                        for idx in 0..classes[kk].len() {
                            let p = classes[kk][idx].0;
                            let mut v = SVec::new();
                            let ok = st.atoms.add_dir(&mut v, p, a, 1).and_then(|_| st.atoms.add_dir(&mut v, p, b, -1))
                                .and_then(|_| add_scaled(&mut v, &SVec::from([(T, 2)]), -1));
                            if ok.is_none() { continue; }
                            let Some(s) = Self::ar_proves(st, &v, &zero) else { continue };
                            let prem = vec![Self::defined_by_premise(&Definition::Midpoint(a, b), o)];
                            classes[k].push((p, union(&s, &base), prem));
                        }
                    }
                    let moved: Vec<ClassId> = classes[k].iter().map(|m| m.0).collect();
                    for (kk, cl) in classes.iter_mut().enumerate() { if kk != k { cl.retain(|m| !moved.contains(&m.0)); } }
                }
                for mut cl in classes {
                    if cl.len() < 2 || count >= MAX_CIRCLES { continue; }
                    cl.truncate(MAX_MEMBERS);
                    // 円の実体に3点以上が乗っていれば、O はその円の中心。
                    let entity = circles.iter().copied().find(|&c| cl.iter().filter(|m| eg.is_connected(m.0, c)).count() >= 3);
                    if let Some(c) = entity && structural.contains(&(c, o)) { continue; }
                    if entity.is_some() && std::env::var("GS_AR_OFF").unwrap_or_default().contains("ecircle") { continue; }
                    let (key, cprem, csrc) = match entity {
                        Some(c) => {
                            let on: Vec<&(ClassId, Vec<u32>, Vec<(String, Vec<ClassId>)>)> = cl.iter().filter(|m| eg.is_connected(m.0, c)).take(3).collect();
                            let mut src = Vec::new();
                            let mut prem = Vec::new();
                            for m in on { src = union(&src, &m.1); prem.extend(m.2.clone()); prem.push(conn(m.0, c)); }
                            (c.0, prem, src)
                        }
                        None => {
                            if std::env::var("GS_AR_OFF").unwrap_or_default().contains("vcircle") { continue; }
                            let has_chord = (0..cl.len()).any(|x| ((x + 1)..cl.len()).any(|y| frame.line_of(cl[x].0, cl[y].0).is_some()));
                            if cl.len() < 3 && !has_chord { continue; }
                            (VIRTUAL_CIRCLE_BASE + count, Vec::new(), Vec::new())
                        }
                    };
                    if let Some(c) = entity {
                        for q in self.ar_points_on(c) {
                            if q == o || cl.iter().any(|m| m.0 == q) || cl.len() >= MAX_MEMBERS { continue; }
                            cl.push((q, Vec::new(), vec![conn(q, c)]));
                        }
                    }
                    self.ar_emit_circle(st, frame, o, key, entity, &cl, &cprem, &csrc, links)?;
                    count += 1;
                }
            }
        }
        Some(count)
    }

    /// 中心 O の円(key は円の実体か仮の円の番号)の等式を入れる。cl は (点, 使った等式, 前提)、cprem・csrc は円全体の前提。
    #[allow(clippy::too_many_arguments)]
    fn ar_emit_circle(&self, st: &mut ArState, frame: &Frame, o: ClassId, key: usize, entity: Option<ClassId>,
        cl: &[(ClassId, Vec<u32>, Vec<(String, Vec<ClassId>)>)], cprem: &[(String, Vec<ClassId>)], csrc: &[u32],
        links: &mut Vec<(ClassId, ClassId, Vec<u32>, &'static str)>) -> Option<()> {
        let eg = &self.prover.egraph;
        let (ci, cj) = (eg.get_rep(eg.circ_i).0, eg.get_rep(eg.circ_j).0);
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        let mut v = SVec::new();
        st.atoms.add_fresh(&mut v, (CIRCLE_C, key, 0, 0), 1)?;
        st.atoms.add_fresh(&mut v, (CENTER_J, key, 0, 0), -1)?;
        st.atoms.add_fresh(&mut v, (CENTER_I, key, 0, 0), 1)?;
        st.atoms.add_fresh(&mut v, (CHART_0, 0, 0, 0), 1)?;
        add_scaled(&mut v, &SVec::from([(T, 2)]), -1)?;
        if !std::env::var("GS_AR_OFF").unwrap_or_default().contains("v3") { st.insert(eg, v, Vec::new(), &[])?; }
        let off_cr = std::env::var("GS_AR_OFF").unwrap_or_default().contains("centerrel");
        for (p, s, pr) in if off_cr { &[][..] } else { cl } {
            let (prem, src) = ([cprem.to_vec(), pr.clone()].concat(), union(csrc, s));
            for (iso, kind, sign) in [(iso_j as fn(ClassId) -> usize, CENTER_J, -1), (iso_i as fn(ClassId) -> usize, CENTER_I, 1)] {
                let mut v = SVec::new();
                if st.atoms.add(&mut v, iso(o), iso(*p), 1).and_then(|_| st.atoms.add_fresh(&mut v, (THETA, key, p.0, 0), sign))
                    .and_then(|_| st.atoms.add_fresh(&mut v, (kind, key, 0, 0), -1)).is_none() { continue; }
                st.insert(eg, v, prem.clone(), &src)?;
            }
        }
        // 仮の円の弦。
        if entity.is_none() && !std::env::var("GS_AR_OFF").unwrap_or_default().contains("vchord") {
            for x in 0..cl.len() {
                for y in (x + 1)..cl.len() {
                    let ((p, sp, pp), (q, sq, pq)) = (&cl[x], &cl[y]);
                    let Some(l) = frame.line_of(*p, *q) else { continue };
                    let mut v = SVec::new();
                    let ok = st.atoms.add_beta(&mut v, ci, cj, self.ar_dir_or_virtual(l), 1)
                        .and_then(|_| st.atoms.add_fresh(&mut v, (THETA, key, p.0, 0), -1))
                        .and_then(|_| st.atoms.add_fresh(&mut v, (THETA, key, q.0, 0), -1))
                        .and_then(|_| st.atoms.add_fresh(&mut v, (CIRCLE_C, key, 0, 0), -1));
                    if ok.is_none() { continue; }
                    let prem = [pp.clone(), pq.clone(), vec![conn(*p, l), conn(*q, l)]].concat();
                    st.insert(eg, v, prem, &union(sp, sq))?;
                }
            }
        }
        if std::env::var("GS_DEBUG_AR").is_ok() {
            let nm = |c: ClassId| eg.entities[c.0].name.clone();
            println!("  AR_DEBUG circle key={} center={} {} : {}", key % 100000, nm(o), entity.map(nm).unwrap_or_else(|| "(仮)".into()),
                cl.iter().map(|m| nm(m.0)).collect::<Vec<_>>().join(" "));
        }
        // 逆: 円の実体があれば、図の点のうち中心からの距離が半径と格子で等しい点をその円に乗せる(中心の分かった円の逆)。
        if let (Some(c), Some(first)) = (entity, cl.first()) {
            let zero = st.lattice.reduce(&SVec::new())?.0;
            for &p in &frame.points {
                if p == o || eg.is_connected(p, c) || eg.fixed_incidence(p, c, EntityType::Conic) != Some(Some(true)) { continue; }
                let mut v = SVec::new();
                if st.atoms.add_len(&mut v, o, p, 1).and_then(|_| st.atoms.add_len(&mut v, o, first.0, -1)).is_none() { continue; }
                let Some(s2) = Self::ar_proves(st, &v, &zero) else { continue };
                let n = st.note([cprem.to_vec(), first.2.clone()].concat());
                links.push((p, c, union(&union(&union(csrc, &first.1), &s2), &[n]), "代数的な追跡(中心から等距離 ⇒ 円の上)"));
            }
        }
        Some(())
    }

    /// 三角形 ABC と、辺(の直線)BC・CA・AB の上の点 D・E・F の比の積 (AF/FB)(BD/DC)(CE/EA)(向きつき)の記号の式。
    /// menelaus なら積が −1(D・E・F が共線、メネラウスの定理)、そうでなければ 1(AD・BE・CF が1点で交わる、チェバの定理)を
    /// 引いた形にする(0 になれば成り立つ)。同じ直線の上の差の比なので、直線ごとの定数は打ち消し合う。
    /// D・E・F は無限遠点(辺の方向の点)でもよい: アフィンの等式で s(B,∞) = s(C,∞) なので、BD/DC の形式的な比は −1 になり、
    /// 横断線が辺に平行な場合(平行線と比)・チェバの直線が辺に平行な場合もそのまま同じ式になる。
    fn menelaus_vec(atoms: &mut Atoms, t: [ClassId; 3], d: usize, e: usize, f: usize, menelaus: bool) -> Option<SVec> {
        let [a, b, c] = t.map(|x| x.0);
        let mut v = SVec::new();
        atoms.add(&mut v, a, f, 1)?;
        atoms.add(&mut v, f, b, -1)?;
        atoms.add(&mut v, b, d, 1)?;
        atoms.add(&mut v, d, c, -1)?;
        atoms.add(&mut v, c, e, 1)?;
        atoms.add(&mut v, e, a, -1)?;
        if menelaus { add_scaled(&mut v, &SVec::from([(T, 2)]), -1)?; }
        Some(v)
    }

    /// 同じ比の積の固定座標での値(全標本で c なら真)。有限の点は z = 1 に揃え、無限遠点はそのまま使う(分子と分母に1回ずつ
    /// 出るので尺度は打ち消し合う。アフィンの等式の値の割り当てと同じ)。
    fn ratio_product_is(&self, t: [ClassId; 3], d: usize, e: usize, f: usize, c: ModInt) -> bool {
        let eg = &self.prover.egraph;
        (0..eg.fixed_samples()).all(|k| {
            let Some(p) = [t[0].0, t[1].0, t[2].0, d, e, f].iter().map(|&x| self.ar_point_value(x, k).filter(|v| v.len() >= 3)
                .map(|v| if v[2].0 != 0 { [v[0] / v[2], v[1] / v[2], ModInt::new(1)] } else { [v[0], v[1], v[2]] }))
                .collect::<Option<Vec<_>>>() else { return false };
            let rr = [ModInt::new(314_159 + 17 * k as i64), ModInt::new(271_828 + 29 * k as i64), ModInt::new(1)];
            let det = |x: &[ModInt; 3], y: &[ModInt; 3]| x[0] * (y[1] * rr[2] - y[2] * rr[1]) - x[1] * (y[0] * rr[2] - y[2] * rr[0]) + x[2] * (y[0] * rr[1] - y[1] * rr[0]);
            let (a, b, cc, dd, ee, ff) = (&p[0], &p[1], &p[2], &p[3], &p[4], &p[5]);
            let num = det(a, ff) * det(b, dd) * det(cc, ee);
            let den = det(ff, b) * det(dd, cc) * det(ee, a);
            den.0 != 0 && (num / den).0 == c.0
        })
    }

    /// 辺の直線 side(端点 x, y)と直線 t の交点: 図にある有限の点(端点以外)か、平行なら方向の点(無限遠点)。前提つき。
    fn ar_meet(&self, frame: &Frame, side: ClassId, x: ClassId, y: ClassId, t: ClassId) -> Option<(usize, Vec<(String, Vec<ClassId>)>)> {
        if side == t { return None; }
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        if let Some(&p) = frame.on(side).iter().find(|&&p| p != x && p != y && frame.on(t).contains(&p)) {
            return Some((p.0, vec![conn(p, side), conn(p, t)]));
        }
        let (ds, dt) = (self.ar_direction(side)?, self.ar_direction(t)?);
        (ds == dt).then(|| (ds.0, vec![Self::direction_premise(side, ds), Self::direction_premise(t, dt)]))
    }

    fn direction_premise(l: ClassId, d: ClassId) -> (String, Vec<ClassId>) { ("DefinedBy:DirectionOf".to_string(), vec![l, d]) }

    /// 点 p を通り q を通る図の直線(q が方向の点なら、p を通ってその方向を持つ直線)。
    fn ar_lines_joining(&self, frame: &Frame, p: ClassId, q: usize) -> Vec<(ClassId, Vec<(String, Vec<ClassId>)>)> {
        let eg = &self.prover.egraph;
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        let qc = ClassId(q);
        if !eg.is_connected(qc, eg.line_infinity) {
            return frame.line_of(p, qc).map(|l| vec![(l, vec![conn(p, l), conn(qc, l)])]).unwrap_or_default();
        }
        frame.lines_at.get(&p.0).map(|v| v.iter().copied().filter(|&l| self.ar_direction(l) == Some(qc))
            .map(|l| (l, vec![conn(p, l), Self::direction_premise(l, qc)])).collect()).unwrap_or_default()
    }

    /// 2直線 l1, l2 の交点: 図にある有限の点(除く点以外)か、平行なら方向の点。
    fn ar_common(&self, frame: &Frame, l1: ClassId, l2: ClassId, except: &[ClassId]) -> Option<(usize, Vec<(String, Vec<ClassId>)>)> {
        if l1 == l2 { return None; }
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        if let Some(&o) = frame.on(l1).iter().find(|&&p| !except.contains(&p) && frame.on(l2).contains(&p)) {
            return Some((o.0, vec![conn(o, l1), conn(o, l2)]));
        }
        let (d1, d2) = (self.ar_direction(l1)?, self.ar_direction(l2)?);
        (d1 == d2).then(|| (d1.0, vec![Self::direction_premise(l1, d1), Self::direction_premise(l2, d2)]))
    }

    fn ar_is_infinite(&self, id: usize) -> bool {
        let eg = &self.prover.egraph;
        is_virtual(id) || (is_entity(id) && eg.is_connected(ClassId(id), eg.line_infinity))
    }

    /// 三角形の枠の上で、メネラウスの定理(横断線 D・E・F)とチェバの定理(1点 O で交わる3本の直線)の等式を入れる。
    /// 無限遠点(辺に平行な横断線・平行な3本の直線)も含める。数値で積が −1・1 であることも確かめる(退化した配置を避ける)。
    fn ar_menelaus_ceva_relations(&self, st: &mut ArState, frame: &Frame) -> Option<()> {
        const MAX_RELATIONS: usize = 4000;
        let eg = &self.prover.egraph;
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        let mut done: rustc_hash::FxHashSet<Vec<usize>> = rustc_hash::FxHashSet::default();
        let mut count = 0usize;
        let lines_at = |p: ClassId| frame.lines_at.get(&p.0).map(|v| v.as_slice()).unwrap_or(&[]);
        for &t in &frame.tris {
            let [a, b, c] = t;
            let (Some(lab), Some(lbc), Some(lca)) = (frame.line_of(a, b), frame.line_of(b, c), frame.line_of(c, a)) else { continue };
            let sides = [lab, lbc, lca];
            let base = vec![conn(a, lab), conn(b, lab), conn(b, lbc), conn(c, lbc), conn(c, lca), conn(a, lca)];
            let mut sorted = t.map(|x| x.0);
            sorted.sort_unstable();
            // メネラウス: 辺の上の有限の点を通る直線 tl が3辺(の直線)と交わる点(平行なら無限遠点、高々1つ)。
            let mut cands: Vec<ClassId> = Vec::new();
            for (l, x, y) in [(lab, a, b), (lbc, b, c), (lca, c, a)] {
                for &p in frame.on(l) {
                    if p == x || p == y { continue; }
                    for &tl in lines_at(p) { if !sides.contains(&tl) && !cands.contains(&tl) { cands.push(tl); } }
                }
            }
            for tl in cands {
                let (Some((d, pd)), Some((e, pe)), Some((f, pf))) = (self.ar_meet(frame, lbc, b, c, tl), self.ar_meet(frame, lca, c, a, tl), self.ar_meet(frame, lab, a, b, tl)) else { continue };
                if [d, e, f].iter().filter(|&&x| self.ar_is_infinite(x)).count() > 1 { continue; }
                if !done.insert(vec![0, sorted[0], sorted[1], sorted[2], tl.0]) || !self.ratio_product_is(t, d, e, f, ModInt::new(-1)) { continue; }
                let Some(v) = Self::menelaus_vec(&mut st.atoms, t, d, e, f, true) else { continue };
                if st.insert(eg, v, [base.clone(), pd, pe, pf].concat(), &[])? { count += 1; }
                if count >= MAX_RELATIONS { return Some(()); }
            }
            // チェバ: A・B を通る直線 la・lb の交点 O(平行なら無限遠点)と、C と O を通る直線 lc。
            for &la in lines_at(a) {
                if sides.contains(&la) { continue; }
                let Some((d, pd)) = self.ar_meet(frame, lbc, b, c, la) else { continue };
                for &lb in lines_at(b) {
                    if sides.contains(&lb) { continue; }
                    let Some((e, pe)) = self.ar_meet(frame, lca, c, a, lb) else { continue };
                    let Some((o, po)) = self.ar_common(frame, la, lb, &[a, b]) else { continue };
                    for (lc, pc) in self.ar_lines_joining(frame, c, o) {
                        if sides.contains(&lc) { continue; }
                        let Some((f, pf)) = self.ar_meet(frame, lab, a, b, lc) else { continue };
                        if [d, e, f, o].iter().filter(|&&x| self.ar_is_infinite(x)).count() > 1 { continue; }
                        if !done.insert(vec![1, sorted[0], sorted[1], sorted[2], o]) || !self.ratio_product_is(t, d, e, f, ModInt::new(1)) { continue; }
                        let Some(v) = Self::menelaus_vec(&mut st.atoms, t, d, e, f, false) else { continue };
                        if st.insert(eg, v, [base.clone(), pd.clone(), pe.clone(), pf, po.clone(), pc].concat(), &[])? { count += 1; }
                        if count >= MAX_RELATIONS { return Some(()); }
                    }
                }
            }
        }
        Some(())
    }

    /// メネラウスの逆・チェバの逆(検出)。固定座標で「その点がその直線に乗る」が真の候補だけを、格子で確かめる:
    /// - メネラウスの逆: AB の上の F と BC の上の D(どちらかは無限遠点でもよい)を通る直線 t があり、CA の上の E で比の積が −1 に
    ///   還元されれば E ∈ t。
    /// - チェバの逆: A・B を通る直線が O(無限遠点でもよい)で交わり、AB の上の F で積が 1 に還元されれば F ∈ CO(CO が図にあれば)。
    /// 返り値は (点, 直線, 使った等式, 理由の名前)。等式以外の前提(接続・方向)は st.note で等式の出どころに入れる。
    fn ar_detect_menelaus_ceva(&self, st: &mut ArState, frame: &Frame, rc: &mut FxHashMap<u32, SVec>) -> Vec<(ClassId, ClassId, Vec<u32>, &'static str)> {
        let eg = &self.prover.egraph;
        let mut out = Vec::new();
        let Some((zero, _)) = st.lattice.reduce(&SVec::new()) else { return out };
        let mut done: rustc_hash::FxHashSet<(usize, usize)> = rustc_hash::FxHashSet::default();
        let numeric_on = |p: ClassId, l: ClassId| eg.fixed_incidence(p, l, EntityType::Line) == Some(Some(true)) && !eg.is_connected(p, l);
        let lines_at = |p: ClassId| frame.lines_at.get(&p.0).map(|v| v.as_slice()).unwrap_or(&[]);
        for &t in &frame.tris {
            for rot in 0..3 {
                let [a, b, c] = [t[rot], t[(rot + 1) % 3], t[(rot + 2) % 3]];
                let (Some(lab), Some(lbc), Some(lca)) = (frame.line_of(a, b), frame.line_of(b, c), frame.line_of(c, a)) else { continue };
                let sides = [lab, lbc, lca];
                // 辺の上の点(端点以外の有限の点と、辺の方向の点)。
                let inner = |l: ClassId, x: ClassId, y: ClassId| -> Vec<usize> {
                    let mut v: Vec<usize> = frame.on(l).iter().copied().filter(|&p| p != x && p != y).map(|p| p.0).collect();
                    if let Some(d) = self.ar_direction(l) { v.push(d.0); }
                    v
                };
                // メネラウスの逆
                for f in inner(lab, a, b) {
                    for d in inner(lbc, b, c) {
                        if self.ar_is_infinite(f) && self.ar_is_infinite(d) { continue; }
                        let (fin, other) = if self.ar_is_infinite(f) { (ClassId(d), f) } else { (ClassId(f), d) };
                        for (tl, pt) in self.ar_lines_joining(frame, fin, other) {
                            if sides.contains(&tl) { continue; }
                            for &e in frame.on(lca) {
                                if e == c || e == a || !numeric_on(e, tl) || !done.insert((e.0, tl.0)) { continue; }
                                let Some(v) = Self::menelaus_vec(&mut st.atoms, [a, b, c], d, e.0, f, true) else { continue };
                                if st.lattice.reduce_cached(&v, rc).as_ref() != Some(&zero) { continue; }
                                let Some((_, src)) = st.lattice.reduce(&v) else { continue };
                                let mut prem = pt.clone();
                                for (p, l) in [(f, lab), (d, lbc)] {
                                    if self.ar_is_infinite(p) { prem.push(Self::direction_premise(l, ClassId(p))); } else { prem.push(("Connected".to_string(), vec![ClassId(p), l])); }
                                }
                                let n = st.note(prem);
                                out.push((e, tl, union(&src, &[n]), "代数的な追跡(メネラウスの逆)"));
                            }
                        }
                    }
                }
                // チェバの逆
                for &la in lines_at(a) {
                    if sides.contains(&la) { continue; }
                    let Some((d, pd)) = self.ar_meet(frame, lbc, b, c, la) else { continue };
                    for &lb in lines_at(b) {
                        if sides.contains(&lb) { continue; }
                        let Some((e, pe)) = self.ar_meet(frame, lca, c, a, lb) else { continue };
                        let Some((o, po)) = self.ar_common(frame, la, lb, &[a, b]) else { continue };
                        for (lc, pc) in self.ar_lines_joining(frame, c, o) {
                            if sides.contains(&lc) { continue; }
                            for &f in frame.on(lab) {
                                if f == a || f == b || !numeric_on(f, lc) || !done.insert((f.0, lc.0)) { continue; }
                                let Some(v) = Self::menelaus_vec(&mut st.atoms, [a, b, c], d, e, f.0, false) else { continue };
                                if st.lattice.reduce_cached(&v, rc).as_ref() != Some(&zero) { continue; }
                                let Some((_, src)) = st.lattice.reduce(&v) else { continue };
                                let n = st.note([pd.clone(), pe.clone(), po.clone(), pc.clone()].concat());
                                out.push((f, lc, union(&src, &[n]), "代数的な追跡(チェバの逆)"));
                            }
                        }
                    }
                }
            }
        }
        out
    }

    /// シュタイナーの逆(検出): 二次曲線 C の上の2点 P, P′ と、C の上の3点 A, B, D(5点は相異なる)について、C の外の点 Z への
    /// 線束の複比 (PA,PB;PD,PZ) と (P′A,P′B;P′D,P′Z) が格子で等しければ Z ∈ C(5点を通る二次曲線は1つで、複比が等しい点の
    /// 軌跡はその曲線)。候補は固定座標で C に乗っている点だけ。返り値は (点, 曲線, 使った等式(前提の記録を含む), 理由の名前)。
    fn ar_detect_conic_converse(&self, st: &mut ArState, rc: &mut FxHashMap<u32, SVec>) -> Vec<(ClassId, ClassId, Vec<u32>, &'static str)> {
        const MAX_TRIES: usize = 4000;
        let eg = &self.prover.egraph;
        let conn = |a: ClassId, b: ClassId| ("Connected".to_string(), vec![a, b]);
        let mut out = Vec::new();
        let Some((zero, _)) = st.lattice.reduce(&SVec::new()) else { return out };
        let points: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&o| eg.get_rep(o) == o && eg.entities[o.0].entity_type == EntityType::Point && eg.entities[o.0].is_active()
                && self.ar_finite(o)).collect();
        let mut tries = 0usize;
        for c in (0..eg.entities.len()).map(ClassId) {
            if eg.get_rep(c) != c || eg.entities[c.0].entity_type != EntityType::Conic || !eg.entities[c.0].is_active() { continue; }
            let pts = self.ar_points_on(c);
            if pts.len() < 5 { continue; }
            for &z in &points {
                if eg.is_connected(z, c) || eg.fixed_incidence(z, c, EntityType::Conic) != Some(Some(true)) { continue; }
                if pts.iter().any(|&q| eg.fixed_equal(q, z) != Some(Some(false))) { continue; }
                // 頂点ごとの (曲線の点 → その直線の方向) の表(Z への直線があるものだけ)。
                let mut fans: Vec<(ClassId, usize, FxHashMap<usize, (usize, ClassId)>)> = Vec::new();
                for &p in &pts {
                    let Some(&lz) = self.ar_lines_through(p, z).first() else { continue };
                    let mut fan: FxHashMap<usize, (usize, ClassId)> = FxHashMap::default();
                    for &x in &pts {
                        if x == p { continue; }
                        if let Some(&l) = self.ar_lines_through(p, x).first() { fan.insert(x.0, (self.ar_dir_or_virtual(l), l)); }
                    }
                    fans.push((p, self.ar_dir_or_virtual(lz), fan));
                    let _ = lz;
                }
                'pairs: for i in 0..fans.len() {
                    for j in (i + 1)..fans.len() {
                        let (p, dzp, fp) = &fans[i];
                        let (q, dzq, fq) = &fans[j];
                        let common: Vec<usize> = pts.iter().map(|x| x.0).filter(|x| *x != p.0 && *x != q.0 && fp.contains_key(x) && fq.contains_key(x)).take(3).collect();
                        if common.len() < 3 { continue; }
                        tries += 1;
                        if tries > MAX_TRIES { return out; }
                        let [a, b, d] = [common[0], common[1], common[2]];
                        let mut v = SVec::new();
                        let ok = (|| {
                            for (sign, f, dz) in [(1i64, fp, *dzp), (-1, fq, *dzq)] {
                                let (da, db, dd) = (f[&a].0, f[&b].0, f[&d].0);
                                st.atoms.add(&mut v, da, dd, sign)?;
                                st.atoms.add(&mut v, dz, db, sign)?;
                                st.atoms.add(&mut v, dd, db, -sign)?;
                                st.atoms.add(&mut v, da, dz, -sign)?;
                            }
                            Some(())
                        })();
                        if ok.is_none() || st.lattice.reduce_cached(&v, rc).as_ref() != Some(&zero) { continue; }
                        let Some((_, src)) = st.lattice.reduce(&v) else { continue };
                        let mut prem = vec![conn(*p, c), conn(*q, c)];
                        for x in [a, b, d] {
                            prem.push(conn(ClassId(x), c));
                            for (vtx, f) in [(*p, fp), (*q, fq)] { let l = f[&x].1; prem.push(conn(vtx, l)); prem.push(conn(ClassId(x), l)); }
                        }
                        for vtx in [*p, *q] { if let Some(&l) = self.ar_lines_through(vtx, z).first() { prem.push(conn(vtx, l)); prem.push(conn(z, l)); } }
                        let n = st.note(prem);
                        out.push((z, c, union(&src, &[n]), "代数的な追跡(シュタイナーの逆)"));
                        break 'pairs;
                    }
                }
            }
        }
        out
    }

    /// 円周角の逆(検出): 円 C の外の点 Z から、C の上の2点 A, B への線分の向きの差 dir(ZA) − dir(ZB)(直線があれば β の差)が
    /// θ_C(A) − θ_C(B) に還元されるなら、Z は C の上にある。候補は固定座標で C に乗る点だけ。返り値は (Z, C, 使った等式)。
    fn ar_detect_concyclic(&self, atoms: &mut Atoms, lattice: &mut Lattice, rc: &mut FxHashMap<u32, SVec>, zero: Option<&SVec>) -> Vec<(ClassId, ClassId, Vec<u32>)> {
        let eg = &self.prover.egraph;
        let mut out = Vec::new();
        let Some(zero) = zero else { return out };
        let conics: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&c| eg.get_rep(c) == c && eg.entities[c.0].entity_type == EntityType::Conic && eg.entities[c.0].is_active()).collect();
        let points: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&o| eg.get_rep(o) == o && eg.entities[o.0].entity_type == EntityType::Point && eg.entities[o.0].is_active()
                && self.ar_finite(o)).collect();
        for &c in &conics {
            if !self.ar_is_circle(c) { continue; }
            let on_c = self.ar_points_on(c);
            if on_c.len() < 3 { continue; }
            // 円の点の記号が格子に出ている(弦の等式がある)点だけを使う。
            let with_theta: Vec<ClassId> = on_c.into_iter().filter(|p| atoms.fresh.contains_key(&(THETA, c.0, p.0, 0))).collect();
            if with_theta.len() < 2 { continue; }
            for &z in &points {
                if eg.is_connected(z, c) || with_theta.contains(&z) { continue; }
                if eg.fixed_incidence(z, c, EntityType::Conic) != Some(Some(true)) { continue; }
                // 格子が知っているのはどれかの弦を見込む角なので、円の点の組を順に試す。
                let cand: Vec<ClassId> = with_theta.iter().copied().filter(|&a| eg.fixed_equal(z, a) == Some(Some(false))).take(8).collect();
                'pairs: for i in 0..cand.len() {
                    for j in (i + 1)..cand.len() {
                        let (a, b) = (cand[i], cand[j]);
                        let mut v = SVec::new();
                        let ok = atoms.add_dir(&mut v, z, a, 1).and_then(|_| atoms.add_dir(&mut v, z, b, -1))
                            .and_then(|_| atoms.add_fresh(&mut v, (THETA, c.0, a.0, 0), -1))
                            .and_then(|_| atoms.add_fresh(&mut v, (THETA, c.0, b.0, 0), 1));
                        if ok.is_none() { continue; }
                        if lattice.reduce_cached(&v, rc).as_ref() != Some(zero) { continue; }
                        let Some((_, src)) = lattice.reduce(&v) else { continue };
                        out.push((z, c, src));
                        break 'pairs;
                    }
                }
            }
        }
        out
    }

    /// 図に無い円の円周角の逆(検出): 固定座標で同じ円に乗る4点以上の組で、3点が乗る円の実体が無いものについて、
    /// 最初の3点 A, B, C と他の点 Z で ∠(ZA,ZB) = ∠(CA,CB)(線分の向きの差)が格子で言えるなら、Z は円 ABC の上にある。
    /// 円は後で作る。候補は固定座標で選ぶ(証明は格子)。返り値は ([A,B,C], Z, 使った等式) と、言えなかった組で引きたい直線
    /// (4点のうち直線の無い組。中点連結の平行などは直線が図にあって初めて格子に載るので、円周角の逆の定理が需要で引いていた直線を
    /// 代わりに引く)。
    #[allow(clippy::type_complexity)]
    fn ar_detect_virtual_concyclic(&self, st: &mut ArState, frame: &Frame, rc: &mut FxHashMap<u32, SVec>)
        -> (Vec<([ClassId; 3], ClassId, Vec<u32>)>, Vec<(ClassId, ClassId)>) {
        const MAX_POINTS: usize = 120;
        const MAX_SETS: usize = 60;
        const MAX_LINES: usize = 6;
        let eg = &self.prover.egraph;
        let mut out = Vec::new();
        let mut wanted: Vec<(ClassId, ClassId)> = Vec::new();
        let Some((zero, _)) = st.lattice.reduce(&SVec::new()) else { return (out, wanted) };
        let mut pts: Vec<(ClassId, (ModInt, ModInt))> = Vec::new();
        for &p in &frame.points {
            let Some(v) = eg.class_value(p, 0) else { continue };
            if v.len() < 3 || v[2].0 == 0 { continue; }
            let xy = (v[0] / v[2], v[1] / v[2]);
            if pts.iter().any(|(_, q)| q.0.0 == xy.0.0 && q.1.0 == xy.1.0) { continue; }
            pts.push((p, xy));
            if pts.len() >= MAX_POINTS { break; }
        }
        // 3点ごとの円の鍵(中心と半径の2乗)で、同じ円に乗る点の組を集める。
        let two = ModInt::new(2);
        let mut sets: FxHashMap<(i64, i64, i64), Vec<usize>> = FxHashMap::default();
        let n = pts.len();
        for i in 0..n {
            for j in (i + 1)..n {
                for k in (j + 1)..n {
                    let ((ax, ay), (bx, by), (cx, cy)) = (pts[i].1, pts[j].1, pts[k].1);
                    let d = two * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by));
                    if d.0 == 0 { continue; }
                    let (a2, b2, c2) = (ax * ax + ay * ay, bx * bx + by * by, cx * cx + cy * cy);
                    let ux = (a2 * (by - cy) + b2 * (cy - ay) + c2 * (ay - by)) / d;
                    let uy = (a2 * (cx - bx) + b2 * (ax - cx) + c2 * (bx - ax)) / d;
                    let r2 = (ax - ux) * (ax - ux) + (ay - uy) * (ay - uy);
                    let e = sets.entry((ux.0 as i64, uy.0 as i64, r2.0 as i64)).or_default();
                    for x in [i, j, k] { if !e.contains(&x) { e.push(x); } }
                }
            }
        }
        let mut groups: Vec<Vec<usize>> = sets.into_values().filter(|g| g.len() >= 4).map(|mut g| { g.sort_unstable(); g }).collect();
        // 点の多い組から(4点の組は補助作図の点どうしの偶然の共円が多く、上限で大事な組が切られる)。
        groups.sort_by(|x, y| y.len().cmp(&x.len()).then_with(|| x.cmp(y)));
        let circles: Vec<ClassId> = (0..eg.entities.len()).map(ClassId)
            .filter(|&c| eg.get_rep(c) == c && eg.entities[c.0].entity_type == EntityType::Conic && eg.entities[c.0].is_active() && self.ar_is_circle(c)).collect();
        for g in groups.into_iter().take(MAX_SETS) {
            if st.lattice.ops > st.ops_cap { break; }
            let members: Vec<ClassId> = g.iter().map(|&i| pts[i].0).collect();
            // 3点以上が乗る円の実体があれば、既存の円の円周角の逆に任せる。
            if circles.iter().any(|&c| members.iter().filter(|&&m| eg.is_connected(m, c)).count() >= 3) { continue; }
            let (a, b, c) = (members[0], members[1], members[2]);
            // 4点の共円は、2本の弦への分け方ごとの3通りの角の等式のどれでも言える(互いに線形には導けない)ので、3通りとも試す。
            for &z in members[3..].iter().take(8) {
                let before = out.len();
                for (x, y, u) in [(a, b, c), (a, c, b), (b, c, a)] {
                    let mut v = SVec::new();
                    let ok = st.atoms.add_dir(&mut v, z, x, 1).and_then(|_| st.atoms.add_dir(&mut v, z, y, -1))
                        .and_then(|_| st.atoms.add_dir(&mut v, u, x, -1)).and_then(|_| st.atoms.add_dir(&mut v, u, y, 1));
                    if ok.is_none() { continue; }
                    if st.lattice.reduce_cached(&v, rc).as_ref() != Some(&zero) { continue; }
                    let Some((_, src)) = st.lattice.reduce(&v) else { continue };
                    out.push(([a, b, c], z, src));
                    break;
                }
                if out.len() == before && wanted.len() < MAX_LINES {
                    for (x, y) in [(z, a), (z, b), (z, c), (a, b), (a, c), (b, c)] {
                        if wanted.len() < MAX_LINES && frame.line_of(x, y).is_none() && !wanted.contains(&(x, y)) { wanted.push((x, y)); }
                    }
                }
            }
        }
        (out, wanted)
    }

    /// 手が止まったときに呼ぶ。併合が無くなるまで(最大数回)追跡し、何か併合したら定理を全部試し直させる。
    pub fn run_ar(&mut self) -> bool {
        if !self.prover.egraph.fixed_active() { return false; }
        let t_ar = std::time::Instant::now();
        let mut total = 0;
        for _ in 0..4 {
            // 予算を使い切ったら、続けて回さない(手詰まり1回の中で予算を大きく超えないように)。
            if self.work_limit > 0 && self.prover.work_done() >= self.work_limit { break; }
            let n = self.ar_round();
            if n == 0 { break; }
            total += n;
            self.prover.egraph.apply_congruence_closure();
        }
        self.ar_merged += total as u64;
        self.prover.profile.ar_time += t_ar.elapsed();
        if total > 0 { self.schedule_full_sweep(); }
        total > 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sv(xs: &[(u32, i64)]) -> SVec { xs.iter().copied().collect() }
    fn same(l: &mut Lattice, a: &SVec, b: &SVec) -> bool { l.reduce(a).unwrap().0 == l.reduce(b).unwrap().0 }

    /// x − y = 0 を積めば x と y は同じ剰余になる。
    #[test]
    fn a_relation_makes_both_sides_equal() {
        let mut l = Lattice::default();
        l.insert(sv(&[(0, 1), (1, -1)]), vec![0]).unwrap();
        assert!(same(&mut l, &sv(&[(0, 1)]), &sv(&[(1, 1)])));
        assert!(!same(&mut l, &sv(&[(0, 1)]), &sv(&[(2, 1)])));
    }

    /// ℤ の上なので 2x = 2y から x = y は出ない(有向角 mod π で 2θ₁ = 2θ₂ ⇏ θ₁ = θ₂)。
    #[test]
    fn no_division_by_two() {
        let mut l = Lattice::default();
        l.insert(sv(&[(0, 2), (1, -2)]), vec![0]).unwrap();
        assert!(!same(&mut l, &sv(&[(0, 1)]), &sv(&[(1, 1)])));
        assert!(same(&mut l, &sv(&[(0, 2)]), &sv(&[(1, 2)])));
    }

    /// ねじれ: 4T = 0 と x = y + 2T(x = −y)から、2x = 2y と x ≠ y が出る。
    #[test]
    fn torsion_mod_four() {
        let mut l = Lattice::default();
        l.insert(sv(&[(T, 4)]), vec![]).unwrap();
        l.insert(sv(&[(0, 1), (1, -1), (T, -2)]), vec![0]).unwrap();
        assert!(same(&mut l, &sv(&[(0, 1)]), &sv(&[(1, 1), (T, 2)])));
        assert!(same(&mut l, &sv(&[(0, 2)]), &sv(&[(1, 2)])));
        assert!(!same(&mut l, &sv(&[(0, 1)]), &sv(&[(1, 1)])));
        assert!(same(&mut l, &sv(&[(T, 6)]), &sv(&[(T, 2)])));
    }

    /// 主成分が割り切れない行どうしは拡張ユークリッドで置き換える(格子は変わらない)。
    #[test]
    fn gcd_combination_keeps_the_lattice() {
        let mut l = Lattice::default();
        // 2x − 3y と 3x − 5y が張る格子は、行列式が −1 なので x と y を両方含む(x = y = 0)。
        l.insert(sv(&[(0, 2), (1, -3)]), vec![0]).unwrap();
        l.insert(sv(&[(0, 3), (1, -5)]), vec![1]).unwrap();
        assert!(same(&mut l, &sv(&[(0, 1)]), &SVec::new()));
        assert!(same(&mut l, &sv(&[(1, 1)]), &SVec::new()));
        let (_, src) = l.reduce(&sv(&[(0, 1)])).unwrap();
        assert_eq!(src, vec![0, 1]);
    }

    /// 記号ごとの剰余を足して簡約し直しても、まとめて簡約したのと同じ剰余になる(ねじれ・割り切れない主成分を含めて)。
    #[test]
    fn cached_reduction_matches_direct() {
        let mut l = Lattice::default();
        l.insert(sv(&[(T, 4)]), vec![]).unwrap();
        l.insert(sv(&[(0, 3), (2, -1), (T, 1)]), vec![0]).unwrap();
        l.insert(sv(&[(1, 2), (3, 5)]), vec![1]).unwrap();
        l.insert(sv(&[(2, 4), (3, -2), (T, 2)]), vec![2]).unwrap();
        let mut cache = FxHashMap::default();
        for v in [sv(&[(0, 5), (1, -3), (3, 7)]), sv(&[(0, -2), (2, 9), (T, 3)]), sv(&[(1, 4), (2, -4), (3, 2)]), SVec::new()] {
            assert_eq!(l.reduce(&v).unwrap().0, l.reduce_cached(&v, &mut cache).unwrap());
        }
    }
}

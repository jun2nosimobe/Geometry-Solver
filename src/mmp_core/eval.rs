//! 🌟 数値評価環境(MMPテスト用)と、それを土台にした健全性チェック。
//! ここでの数値計算はあくまでテスト・事後検証のためのものであり、
//! メインの証明導出(合同閉包・定理適用)は一切これに依存しない。

use std::collections::HashSet;
use rustc_hash::FxHashMap;
use crate::mmp_math::ModInt;
use crate::mmp_calculators;
use super::{ClassId, ConjectureEntry, ConjectureValue, Definition, EntityType, EGraph, Justification};

impl EGraph {
    /// 🌟 数値評価環境 (MMPテスト用)
    pub fn evaluate_node(
        &self,
        node_id: ClassId,
        vars: &FxHashMap<String, ModInt>,
        cache: &mut FxHashMap<usize, Vec<ModInt>>,
    ) -> Option<Vec<ModInt>> {
        let mut in_progress = HashSet::new();
        self.evaluate_node_inner(node_id, vars, cache, &mut in_progress)
    }

    /// 🌟 evaluate_node の実体。PerpDirectionOf/HarmonicConjugateOfのように、
    /// マージによって「互いを参照し合う定義」が同じコンポーネントに同居する
    /// ことがある(例: D=Harm(A,B,C) と C=Harm(A,B,D) が対合として互いに
    /// マージされる)。素朴に再帰するとどちらの定義から計算しても計算不能な
    /// 組み合わせで無限再帰(スタックオーバーフロー)に陥るため、
    /// 計算中のIDへの再突入を in_progress で検出し、その場合はその定義を
    /// 諦めて(Noneを返して)コンポーネント内の他の定義を試す。
    fn evaluate_node_inner(
        &self,
        node_id: ClassId,
        vars: &FxHashMap<String, ModInt>,
        cache: &mut FxHashMap<usize, Vec<ModInt>>,
        in_progress: &mut HashSet<usize>,
    ) -> Option<Vec<ModInt>> {
        let rep_id = self.get_rep(node_id);
        if let Some(val) = cache.get(&rep_id.0) {
            return Some(val.clone());
        }
        if !in_progress.insert(rep_id.0) {
            return None;
        }

        let name = self.entities[rep_id.0].name.clone();
        let definitions = match self.entities[rep_id.0].components.first() {
            Some(c) => c.definitions.clone(),
            None => { in_progress.remove(&rep_id.0); return None; }
        };

        // 🌟 マージ後は1つのコンポーネントに複数の定義が同居し得るので、
        // 計算可能なものが見つかるまで順に試す(以前は.first()決め打ちで、
        // たまたま循環参照側が先頭に来ると即失敗していた)。
        let mut result = None;
        for def in &definitions {
            if let Some(v) = self.evaluate_definition(def, &name, vars, cache, in_progress) {
                result = Some(v);
                break;
            }
        }

        in_progress.remove(&rep_id.0);
        if let Some(ref v) = result {
            cache.insert(rep_id.0, v.clone());
        }
        result
    }

    fn evaluate_definition(
        &self,
        def: &Definition,
        name: &str,
        vars: &FxHashMap<String, ModInt>,
        cache: &mut FxHashMap<usize, Vec<ModInt>>,
        in_progress: &mut HashSet<usize>,
    ) -> Option<Vec<ModInt>> {
        match def {
            Definition::FreePoint | Definition::GivenPoint => {
                let x = vars.get(&format!("{}_x", name)).copied().unwrap_or(ModInt::new(0));
                let y = vars.get(&format!("{}_y", name)).copied().unwrap_or(ModInt::new(0));
                Some(vec![x, y, ModInt::new(1)])
            }
            Definition::Midpoint(p1, p2) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_midpoint(&v1, &v2))
            }
            Definition::LineThroughPoints(p1, p2) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                // 🐛 FIX: calc_line_through_pointsは2点の座標が数値的に一致した場合
                // (退化)にvec![]を返す。以前はここでSome(vec![])として素通りさせて
                // しまい、この空Vecが後続のIntersection計算等でcross_productに
                // 渡されてindex out of bounds panicを起こしていた(orthocenter --mctsで
                // 実際に発生)。to_optionで確実にNone(計算不能)に変換する。
                let result = mmp_calculators::calc_line_through_points(&v1, &v2);
                if result.is_empty() {
                    // 🔮 CONJECTURE: 無作為な座標(独立一様分布, 法998244353)で
                    // p1とp2が偶然一致する確率は約10億分の1で、単発でも観測されたなら
                    // ほぼ確実に偶然ではない(Schwartz-Zippel補題の逆読み)。まだ記号的
                    // には別物として扱われている2点が、実は常に同一なのではないか、
                    // という「証明はできていないが数値的根拠のある予想」として
                    // 目立つ形でログに残す(数値サニティチェックの土台として黙って
                    // Noneに変換するだけでは、この情報がそのまま捨てられてしまう)。
                    self.log_conjecture_candidate(*p1, *p2, "2点が同一点である");
                }
                Self::to_option(result)
            }
            Definition::Intersection(l1, l2) => {
                let v1 = self.evaluate_node_inner(*l1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*l2, vars, cache, in_progress)?;
                let result = mmp_calculators::calc_intersection(&v1, &v2);
                if result.is_empty() || result.iter().all(|x| x.0 == 0) {
                    // 🔮 CONJECTURE: 2直線の交点が定義不能([0,0,0])になるのは、
                    // 2直線が数値的に同一直線である場合だけ(平行なだけの別直線は
                    // 無限遠点で交わる、通常の交点として well-defined)。上と同じ理由で
                    // 「実はl1とl2は同一直線なのでは」という予想として記録する。
                    self.log_conjecture_candidate(*l1, *l2, "2直線が同一直線である");
                }
                Self::to_option(result)
            }
            Definition::DirectionOf(l) => {
                let v = self.evaluate_node_inner(*l, vars, cache, in_progress)?;
                if v.len() >= 3 {
                    // 直線 ax + by + c = 0 の方向ベクトルは (b, -a)。
                    // 🐛 FIX: 以前は2要素[dx,dy]のまま返していたが、これだと
                    // 「無限遠直線との交点」として計算される3要素の同次座標
                    // (Intersection(Line_infinity, l) = cross_product([0,0,1], v))
                    // と要素数が食い違い、数値サニティチェック(numeric_plausibility_check)
                    // が両者を「別の値」と誤判定してしまう(この2つは設計上、
                    // 常に同じ点=方向を表すべきもの)。z成分0を付けた3要素の
                    // 同次座標として統一する。
                    // 🐛 FIX: lが無限遠直線[0,0,c]だと(v[0]=v[1]=0のため)
                    // 結果が[0,0,0]という「方向として定義不能」な退化値になる。
                    // to_optionで全成分ゼロもNoneとして弾く。
                    Self::to_option(mmp_calculators::normalize(&[v[1], -v[0], ModInt::new(0)]))
                } else {
                    None
                }
            }
            // 🌟 ユーザー提案「有向角を複比として扱う」への対応。
            // D1,D2は既にDirectionOf/PerpDirectionOf経由で無限遠直線上の点
            // (x,y,0)として評価されるので、同じく無限遠直線上の固定点である
            // 円周点I,Jと合わせて4点(I,J,D1,D2)は常に共線 ―― 通常の
            // CrossRatio(4点が共線な直線上の点)と全く同じcalc_cross_ratioの
            // 式でそのまま複比 (I,J;D1,D2) が計算できる(「円も係数を射影空間の
            // 点だと思えばOK」「線束も点とみなせる」と同じ発想を、方向にも
            // 適用しただけ)。I,Jを基準(A,B)側に固定して測る(D1,D2を「動く」
            // C,D側に置く)ことで、D1を基準としたτ_D2/τ_D1というMöbius変換上の
            // 比になり、既存の「有向角の加法性」「有向角の交替律」定理
            // (AnglePairの値をIdenticalで比較するだけの純粋に構造的な定理)が
            // 求める代数法則(τ_a/τ_b * τ_b/τ_c = τ_a/τ_c、および
            // a/b=c/d ⟹ a/c=b/d)をそのまま満たす。したがって定理・パターン
            // 側は一切変更せずに、この評価式の変更だけで「有向角=複比」化が
            // 完了する。
            Definition::AnglePair(d1, d2) => {
                let v1 = self.evaluate_node_inner(*d1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*d2, vars, cache, in_progress)?;
                let vi = self.evaluate_node_inner(self.circ_i, vars, cache, in_progress)?;
                let vj = self.evaluate_node_inner(self.circ_j, vars, cache, in_progress)?;
                mmp_calculators::calc_cross_ratio(&vi, &vj, &v1, &v2)
                    .map(|k| vec![k, ModInt::new(1), ModInt::new(1)])
            }
            Definition::LengthSq(p1, p2) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                // 🐛 FIX: calc_squared_distanceは同次座標のz成分が0(無限遠点)だと
                // 内部の除算(ModInt::inv())でpanicしていたため、Option<ModInt>を
                // 返す実装に変更済み(mmp_calculators.rs参照)。ここではmapで
                // Vec<ModInt>形式に包み直すだけ。
                mmp_calculators::calc_squared_distance(&v1, &v2)
                    .map(|d| vec![d, ModInt::new(1), ModInt::new(1)])
            }
            Definition::PerpendicularLine(l, p) => {
                let vl = self.evaluate_node_inner(*l, vars, cache, in_progress)?;
                let vp = self.evaluate_node_inner(*p, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_perpendicular(&vl, &vp))
            }
            // 🌟 以前は未実装で、ParallelLine型のエンティティ(まだ他の定義と
            // マージされていないもの)を数値サニティチェック(numeric_plausibility_check)
            // で評価できず、健全性チェックが素通りしてしまう抜け穴になっていた。
            Definition::ParallelLine(l, p) => {
                let vl = self.evaluate_node_inner(*l, vars, cache, in_progress)?;
                let vp = self.evaluate_node_inner(*p, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_parallel(&vl, &vp))
            }
            // 🌟 同上の理由でPerpDirectionOfも実装する。方向ベクトル(dx,dy)を
            // 90度回転させるだけ((dx,dy) -> (-dy,dx))。
            Definition::PerpDirectionOf(d) => {
                let v = self.evaluate_node_inner(*d, vars, cache, in_progress)?;
                if v.len() >= 2 {
                    // DirectionOfと同じ理由でz成分0を付けた3要素の同次座標に統一する。
                    // (同じくv=[0,0,...]由来の全ゼロ退化値をto_optionで弾く)
                    Self::to_option(mmp_calculators::normalize(&[-v[1], v[0], ModInt::new(0)]))
                } else {
                    None
                }
            }
            // 🌟 ユーザー提案(射影幾何への移植: circle型を完全にconic型にする):
            // 円は古典的に「円周点(circular points at infinity) I,J を通る
            // 二次曲線」として特徴づけられる。この事実をそのまま実装にし、
            // 外接円の作図をcalc_circumcircle(円専用の3点公式)ではなく
            // 「3点+I+Jを通る二次曲線」(calc_conic_through_5_points、
            // シュタイナーの定理の接線版と全く同じ計算)として行う。
            // これにより外接円もEntityType::Conic(6係数[A,B,C,D,E,F])として
            // 一様に扱えるようになり(apply_trivial_relationsでI,Jへの
            // incidenceを張ることで「I,Jを通る=円である」ことを構造的にも
            // 表現する)、円専用のEntityType::Conicという型タグが不要になる。
            Definition::Circumcircle(p1, p2, p3) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                let v3 = self.evaluate_node_inner(*p3, vars, cache, in_progress)?;
                let vi = self.evaluate_node_inner(self.circ_i, vars, cache, in_progress)?;
                let vj = self.evaluate_node_inner(self.circ_j, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_conic_through_5_points(&[v1, v2, v3, vi, vj]))
            }
            Definition::TangentLine(c, p) => {
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                let vp = self.evaluate_node_inner(*p, vars, cache, in_progress)?;
                // 🌟 射影幾何への移植(接弦定理→シュタイナーの定理の接線版):
                // TangentLineの第1引数はCircle(4係数[A,D,E,F])だけでなく
                // 一般のConic(6係数[A,B,C,D,E,F]、calc_conic_through_5_points参照)
                // にもなり得るようにした。円と二次曲線は係数ベクトルの長さが
                // 4/6で必ず異なる(円は「4点目の生成元」を要求しないので同じ
                // Definitionを共有していても混同しない)ため、長さで振り分ける。
                let result = if vc.len() >= 6 {
                    mmp_calculators::calc_tangent_to_conic(&vc, &vp)
                } else {
                    mmp_calculators::calc_tangent_line(&vc, &vp)
                };
                Self::to_option(result)
            }
            // 🌟 mmp_core/mod.rs::Definition::SecondIntersectionOfLineAndConic
            // のドキュメント参照。既知の交点p、直線l、二次曲線cから、
            // もう一方の交点を斉次座標のまま(割り算無しで)直接求める。
            Definition::SecondIntersectionOfLineAndConic(p, l, c) => {
                let vp = self.evaluate_node_inner(*p, vars, cache, in_progress)?;
                let vl = self.evaluate_node_inner(*l, vars, cache, in_progress)?;
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_second_intersection_of_line_and_conic(&vp, &vl, &vc))
            }
            Definition::HarmonicConjugateOf(a, b, c) => {
                let va = self.evaluate_node_inner(*a, vars, cache, in_progress)?;
                let vb = self.evaluate_node_inner(*b, vars, cache, in_progress)?;
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_harmonic_conjugate(&va, &vb, &vc))
            }
            // 🌟 複比(A,B;C,D)はPoint型ではなくScalar型の値(A,B,C,Dが直線上に
            // ある前提でのτ_D/τ_C)なので、点のような同次座標[x,y,z]ではなく
            // LengthSqと同じ「値, 1, 1」の3要素形式で返す(numeric_values_proportional
            // が単純な値比較として扱えるようにするための既存の慣習)。
            Definition::CrossRatio(a, b, c, d) => {
                let va = self.evaluate_node_inner(*a, vars, cache, in_progress)?;
                let vb = self.evaluate_node_inner(*b, vars, cache, in_progress)?;
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                let vd = self.evaluate_node_inner(*d, vars, cache, in_progress)?;
                mmp_calculators::calc_cross_ratio(&va, &vb, &vc, &vd)
                    .map(|k| vec![k, ModInt::new(1), ModInt::new(1)])
            }
            // 🌟 4本の共点直線がなす線束の複比。直線の同次係数(a,b,c)を
            // 射影平面の"点"とみなせば(ユーザー指摘:「円も係数を射影空間の
            // 点だと思えばOK」と同じ発想)、4直線が共点(=双対平面上で係数が
            // 共線)であるときのCrossRatioOfLinesは、通常のCrossRatio(4点が
            // 共線)と全く同じcalc_cross_ratioの式でそのまま計算できる。
            Definition::CrossRatioOfLines(a, b, c, d) => {
                let va = self.evaluate_node_inner(*a, vars, cache, in_progress)?;
                let vb = self.evaluate_node_inner(*b, vars, cache, in_progress)?;
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                let vd = self.evaluate_node_inner(*d, vars, cache, in_progress)?;
                mmp_calculators::calc_cross_ratio(&va, &vb, &vc, &vd)
                    .map(|k| vec![k, ModInt::new(1), ModInt::new(1)])
            }
            // 🌟 円周点I,Jのような「常にこの値」の定数。varsの内容に関わらず
            // 埋め込まれたModIntをそのまま返す。
            Definition::ConstantHomogeneous(a, b, c) => Some(vec![*a, *b, *c]),
            // 🌟 5点を通る一般二次曲線の係数[A,B,C,D,E,F]。calc_circumcircleの
            // 一般化(calc_conic_through_5_pointsのコメント参照)。
            Definition::ConicThrough5Points(p1, p2, p3, p4, p5) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                let v3 = self.evaluate_node_inner(*p3, vars, cache, in_progress)?;
                let v4 = self.evaluate_node_inner(*p4, vars, cache, in_progress)?;
                let v5 = self.evaluate_node_inner(*p5, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_conic_through_5_points(&[v1, v2, v3, v4, v5]))
            }
            // 🌟 2つのScalarの積。LengthSq等と同じ「値,1,1」の3要素形式で
            // 評価する(numeric_values_proportionalが単純な値比較として扱える)。
            Definition::Product(a, b) => {
                let va = self.evaluate_node_inner(*a, vars, cache, in_progress)?;
                let vb = self.evaluate_node_inner(*b, vars, cache, in_progress)?;
                if va.is_empty() || vb.is_empty() { return None; }
                Some(vec![va[0] * vb[0], ModInt::new(1), ModInt::new(1)])
            }
        }
    }

    /// 🌟 calc_*系のヘルパーが退化した入力(座標が数値的に一致した2点、
    /// 平行な2直線等)に対して返す空Vecを、evaluate_definition全体で一貫して
    /// 「計算不能」(None)に変換する。これが無いと、空Vecがあたかも妥当な値
    /// であるかのようにSome(vec![])として上流(呼び出し元のevaluate_node_inner
    /// のキャッシュ・そのまた呼び出し元)に伝播してしまい、後続の計算
    /// (cross_product等の固定インデックスアクセス)でindex out of bounds
    /// panicを起こす(orthocenter --mctsで実際に発生した既知のバグ。
    /// mmp_calculators.rs側でもcross_product/calc_squared_distance/
    /// calc_tangent_line自体に長さ・ゼロ除算ガードを追加したが、それとは
    /// 独立に、ここでも「空=計算不能」という変換を一箇所に集約しておく)。
    ///
    /// 🐛 FIX: 長さが正しくても全成分が0の同次座標(例: cross_productが
    /// 「数値的に同一な2直線」の交点を求めようとした時に返す[0,0,0])は、
    /// 射影平面上の点として定義不能(P^2の点は少なくとも1成分が非ゼロで
    /// なければならない)なのに、以前は「空ではない」という理由だけで
    /// Some([0,0,0])として素通りしていた。normalize()は全ゼロ入力を
    /// そのまま(全ゼロのまま)返す実装なので、cross_product/normalizeの
    /// 長さガードだけではこのケースを検出できない。ここで全ゼロも
    /// 明示的にNoneとして弾く(orthocenter --mctsの問題設定自体に退化の
    /// 原因があるわけではなく、MCTSが生成する補助構成が、探索中はまだ
    /// 記号的にマージされていない2つの直線/点をたまたま同じ数値サンプルで
    /// 数値的に一致させてしまうケースがこれに当たる)。
    fn to_option(v: Vec<ModInt>) -> Option<Vec<ModInt>> {
        if v.is_empty() || v.iter().all(|x| x.0 == 0) { None } else { Some(v) }
    }

    /// 🔮 CONJECTURE: 記号的にはまだ別物として扱われている2つの図形a, bが、
    /// 独立にランダムサンプリングした座標の下で数値的に一致してしまった
    /// (LineThroughPointsの2点が同一点になった/Intersectionの2直線が
    /// 同一直線になった)ことを目立つ形でログに残す。
    ///
    /// 独立一様分布(法998244353)からサンプリングした2つの値が偶然一致する
    /// 確率は約10億分の1なので、単発の観測でもほぼ確実に偶然ではなく、
    /// a と b の間に(まだ証明されていない)何らかの構造的な同一性が
    /// 実在することを強く示唆する(Schwartz-Zippel補題の逆読み)。
    /// これは証明ではなく、あくまで「調べる価値の高い予想」の提示に過ぎない
    /// ―― 経路によっては数値的に偶然近い値になるだけの見せかけの一致も
    /// 理論上あり得るため、実際に証明したい場合は改めてtrials回数を
    /// 増やした再現確認や、記号的な証明の探索が必要になる。
    // 🌟 pub(crate)化: 数値評価が独立に見つけた偶然の一致だけでなく、
    // logic_core.rs側の「仮説駆動の定理プロービング」(BlackboardEngine::
    // probe_conjecture)が見つけた"条件付きの"発見も、同じconjectures
    // マップ・同じ重複排除ロジックに乗せたい(2種類の発見経路を別々の
    // 仕組みで管理すると、process_pending_conjectures側の評価・報告が
    // 二重化してしまう)ため、クレート内限定で公開する。
    pub(crate) fn log_conjecture_candidate(&self, a: ClassId, b: ClassId, hypothesis: &str) {
        let rep_a = self.get_rep(a);
        let rep_b = self.get_rep(b);
        if rep_a == rep_b { return; } // 既に記号的に証明済みなら予想ではない
        let key = if rep_a.0 < rep_b.0 { (rep_a.0, rep_b.0) } else { (rep_b.0, rep_a.0) };

        // 🌟 同じペアは観測のたびに(場合によっては数百回)何度も検出される
        // (orthocenter --mctsの実測で1回の実行あたり最大2000回超)。コンソールを
        // 埋め尽くさないよう、ログ出力は初回だけにし、以降はconjecturesマップの
        // occurrencesカウンタを静かに増やすだけにする(BlackboardEngine側の
        // process_pending_conjecturesが、蓄積されたこの情報を後でまとめて処理する)。
        //
        // 🐛 FIX: union-find(get_rep)は経路圧縮やマージにより、同じ「論理的な
        // 実体」(例: H_AltA_AltBという交点)の代表元ClassIdが実行時間の経過で
        // 変わり得る。以前は単純にrep_a.0/rep_b.0そのものをキーにしていたため、
        // 代表元が変わるたびに全く同じ論理的関係が新しいキーとして再登録され、
        // 実測でorthocenterの中心的な予想(H_AltA_AltB≡H_AltB_AltC)が
        // "1つの関係"ではなく約800個の別々のエントリとして蓄積されてしまう
        // 深刻な重複が発生していた。ここで、既存キーをCURRENT get_repで
        // 再解決した結果が今回のキーと一致するものが無いか線形探索し、
        // 見つかればそのエントリを現在のキーへ付け替えて更新する
        // (マップは論理的に別個な関係の数だけ、通常は数十件以内に収まるので、
        // この線形探索のコストは無視できる)。
        let mut map = self.conjectures.borrow_mut();
        let canonical_existing = map.keys().copied().find(|&(ka, kb)| {
            let (ra, rb) = (self.get_rep(ClassId(ka)), self.get_rep(ClassId(kb)));
            let (ra, rb) = if ra.0 < rb.0 { (ra.0, rb.0) } else { (rb.0, ra.0) };
            (ra, rb) == key
        });
        let is_first = match canonical_existing {
            Some(old_key) => {
                if old_key != key {
                    if let Some(entry) = map.remove(&old_key) { map.insert(key, entry); }
                }
                if let Some(entry) = map.get_mut(&key) { entry.occurrences += 1; }
                false
            }
            None => {
                map.insert(key, ConjectureEntry {
                    hypothesis: hypothesis.to_string(),
                    occurrences: 1,
                    tested: false,
                });
                true
            }
        };
        drop(map);

        if is_first {
            let name_a = &self.entities[rep_a.0].name;
            let name_b = &self.entities[rep_b.0].name;
            println!(
                "  🔮 [予想候補] {} と {} は独立な乱数サンプルで数値的に一致しました(仮説: {})。\
                 まだ証明はされていませんが、偶然の確率は約10億分の1なので実在する関係の可能性が高いです。",
                name_a, name_b, hypothesis
            );
        }
    }

    /// 🌟 予想(a≡b)を実際に真だと仮定した場合、合同閉包だけでどれだけの
    /// 追加的な帰結(マージ)が即座に得られるかを、使い捨てのクローン上で
    /// 見積もる。証明の健全性には一切影響しない(現実のegraphは一切変更
    /// しない)、あくまで探索の優先度付け(heat_bonus)のためのヒューリスティックな
    /// 価値推定であり、これ自体が新しい事実を証明するわけではない。
    ///
    /// 🌟 組み合わせ爆発対策: 意図的に定理マッチング(dfs_match)までは行わず、
    /// 合同閉包(apply_congruence_closure、直線/点の一意性の局所伝播)だけに
    /// 留める。定理マッチングまで踏み込み、その結論をさらに新しい予想として
    /// 連鎖的に評価し始めると、組み合わせが指数的に増える恐れがある。
    /// まず最も安価でよく効く一段階の構造的伝播だけで価値を見積もり、
    /// 効果が薄ければそれ以上深追いしない設計にすることで、1つの予想を
    /// 評価するコストを「クローン1回+合同閉包1回」に固定している。
    pub fn estimate_conjecture_value(&self, a: ClassId, b: ClassId, target: &Option<(String, Vec<ClassId>)>) -> ConjectureValue {
        let mut sim = self.clone();
        let classes_before = sim.count_active_classes();
        sim.merge_entities_justified(a, b, Justification::Trivial {
            reason: "予想(数値的根拠のみ、未証明)を価値評価のため一時的に仮定".to_string(),
        });
        sim.apply_congruence_closure();
        let classes_after = sim.count_active_classes();
        let additional_merges = classes_before.saturating_sub(classes_after);

        let target_reached = match target {
            Some((ftype, targets)) if ftype == "Identical" && targets.len() == 2 => {
                sim.get_rep(targets[0]) == sim.get_rep(targets[1])
            }
            Some((ftype, targets)) if ftype == "Concyclic" => {
                let reps: Vec<ClassId> = targets.iter().map(|&t| sim.get_rep(t)).collect();
                sim.points_share_a_circle(&reps)
            }
            _ => false,
        };

        ConjectureValue { additional_merges, target_reached }
    }

    /// 🌟 使い捨てクローン(MCTSのsim_egraph等)側で検出された予想候補を、
    /// 実際の(現実の)EGraphの予想マップへ合流させる。
    ///
    /// 🐛 背景: EGraph全体をクローンするとconjectures(RefCell)の中身も
    /// そのまま複製されるが、これは複製先(独立したRefCell)であり、複製元とは
    /// 一切共有されない。MCTSは1シミュレーションごとに使い捨てのsim_egraphを
    /// 作り、その中でapply_congruence_closureを回すため、log_conjecture_candidate
    /// がそこで検出した予想はシミュレーション終了時にsim_egraphごと丸ごと
    /// 破棄され、現実のegraph側には一切反映されないまま失われていた
    /// (実測: 1回の実行で"初回検出"ログが900件超出ても、実際に現実の
    /// マップに記録され後続処理されたのはそのうち1件だけ、という深刻な
    /// 取りこぼしが起きていた)。
    ///
    /// ここでは、クローン側で新しく作られた実体(=現実のegraphにはまだ
    /// 存在しないClassId、シミュレーション内でしか意味を持たない補助構成)を
    /// 参照する予想は除外し、両方の実体が現実のegraphにも実在するものだけを
    /// 合流させる(存在しない実体へのheat_bonusフィードバックは意味を
    /// 持たないため)。合流時は現実のegraph側の"今の"代表元で正規化し直す
    /// (log_conjecture_candidateの重複排除ロジックと同じ理由)。
    pub fn absorb_conjectures_from(&self, other: &EGraph) {
        let real_len = self.entities.len();
        let incoming: Vec<((usize, usize), ConjectureEntry)> = {
            let other_map = other.conjectures.borrow();
            other_map.iter()
                .filter(|&(&(a, b), _)| a < real_len && b < real_len)
                .map(|(&k, v)| (k, v.clone()))
                .collect()
        };
        if incoming.is_empty() { return; }

        let mut map = self.conjectures.borrow_mut();
        for ((a, b), entry) in incoming {
            let (ra, rb) = (self.get_rep(ClassId(a)), self.get_rep(ClassId(b)));
            if ra == rb { continue; } // 現実のegraph側では既に証明済み
            let key = if ra.0 < rb.0 { (ra.0, rb.0) } else { (rb.0, ra.0) };
            match map.get_mut(&key) {
                Some(existing) => existing.occurrences += entry.occurrences,
                None => { map.insert(key, entry); }
            }
        }
    }

    /// 🌟 log_conjecture_candidateが蓄積した「証明されていないが数値的根拠の
    /// ある予想」を処理する。まだ評価していない予想それぞれについて
    /// estimate_conjecture_valueで(使い捨てクローン上で)価値を見積もり、
    /// 一定以上の価値があれば、その予想が指す2つの実体のheat_bonusを引き上げて
    /// 以後のDFS/MCTS探索がそちらを優先的に調べるよう仕向ける。現実のegraphの
    /// 証明状態(union-find/memo/facts)は一切変更しない、あくまで優先度付けの
    /// ヒント。
    ///
    /// 🌟 元々BlackboardEngine側にあったが、MCTS(mcts.rs::run_step)からも
    /// 自分自身が発見した予想を同じrun_step呼び出しの中で即座に評価・反映
    /// (以後の同じ呼び出し内のシミュレーションのentity_weightに直結)したく
    /// なったため、BlackboardEngineを介さずEGraph単体で完結するようここに
    /// 移した。BlackboardEngine::process_pending_conjecturesは薄い委譲に
    /// なっている。
    ///
    /// 🌟 組み合わせ爆発対策:
    /// 1. 予想ごとの評価はestimate_conjecture_value側で合同閉包1回だけの
    ///    浅い見積もりに固定し、定理マッチングや「予想の予想」への再帰的な
    ///    連鎖は一切行わない。
    /// 2. 同じ(a,b)ペアは(何度観測されても)ConjectureEntry.testedにより
    ///    一度しか評価しない。
    /// 3. 呼び出し1回あたりに新規評価する予想の数をMAX_PER_CALLで絞り、
    ///    大量の予想が一度に湧いても評価コストが1呼び出しに集中しないように
    ///    分散させる(mainループの毎イテレーション、及びMCTSの各run_step内で
    ///    複数回呼ばれる想定)。
    pub fn process_pending_conjectures(&mut self, target: &Option<(String, Vec<ClassId>)>) -> usize {
        const MAX_PER_CALL: usize = 3;
        const MERGE_THRESHOLD: usize = 3;
        const HEAT_BOOST: f64 = 2.0;
        const HEAT_BOOST_TARGET: f64 = 10.0;

        let pending: Vec<(usize, usize, String, u32)> = {
            let map = self.conjectures.borrow();
            map.iter()
                .filter(|(_, e)| !e.tested)
                .take(MAX_PER_CALL)
                .map(|(&(a, b), e)| (a, b, e.hypothesis.clone(), e.occurrences))
                .collect()
        };
        if pending.is_empty() { return 0; }

        for (a_idx, b_idx, hypothesis, occurrences) in &pending {
            let (a, b) = (ClassId(*a_idx), ClassId(*b_idx));
            let name_a = self.entities[*a_idx].name.clone();
            let name_b = self.entities[*b_idx].name.clone();

            println!("  🔍 [予想の検証開始] {} ≡ {} (仮説: {}, これまでに{}回観測) を一時的に仮定して検証します。\
                以下は使い捨ての複製上での仮想的な帰結であり、実際の証明状態には反映されません:",
                name_a, name_b, hypothesis, occurrences);
            let value = self.estimate_conjecture_value(a, b, target);
            println!("  🔍 [予想の検証終了] 合同閉包だけで{}件の追加的な帰結{}",
                value.additional_merges, if value.target_reached { "、さらに証明目標にも到達" } else { "" });

            if let Some(entry) = self.conjectures.borrow_mut().get_mut(&(*a_idx, *b_idx)) {
                entry.tested = true;
            }

            if value.target_reached {
                // 🌟 "🎯"は既存のリーチ通知(健全に完全マッチした定理の通知)で使われて
                // いるため紛らわしい。こちらは未証明の仮定に基づく評価なので"🏆"を使う。
                println!("  🏆 [予想の評価] {} ≡ {} を仮定するだけで証明目標に到達しました！この2点への注目度を大きく引き上げます。", name_a, name_b);
                self.entities[*a_idx].heat_bonus += HEAT_BOOST_TARGET;
                self.entities[*b_idx].heat_bonus += HEAT_BOOST_TARGET;
            } else if value.additional_merges >= MERGE_THRESHOLD {
                println!("  📈 [予想の評価] {} ≡ {} は仮定するだけで{}件の追加的な帰結を生むため、この2点への注目度を引き上げます。",
                    name_a, name_b, value.additional_merges);
                self.entities[*a_idx].heat_bonus += HEAT_BOOST;
                self.entities[*b_idx].heat_bonus += HEAT_BOOST;
            }
        }
        pending.len()
    }

    /// 🌟 同次座標(2要素または3要素)としての比例判定。normalize()の正規化
    /// 方式が定義の種類によって異なる(FreePointは[x,y,1]のまま、他の多くは
    /// 「最初の非ゼロ成分を1にする」方式)ため、単純な要素比較ではなく
    /// 外積(クロス積)がゼロかどうかで比較する(mmp_tester.rsのverify_identicalと
    /// 同じロジック。EGraphからmmp_tester.rsに依存させたくないのでここに複製する)。
    fn numeric_values_proportional(v1: &[ModInt], v2: &[ModInt]) -> bool {
        if v1.len() != v2.len() || v1.is_empty() { return false; }
        if v1.len() == 3 {
            let z1 = v1[0] * v2[1] - v1[1] * v2[0];
            let z2 = v1[1] * v2[2] - v1[2] * v2[1];
            let z3 = v1[2] * v2[0] - v1[0] * v2[2];
            return z1.0 == 0 && z2.0 == 0 && z3.0 == 0;
        }
        if v1.len() == 2 {
            let cross = v1[0] * v2[1] - v1[1] * v2[0];
            return cross.0 == 0;
        }
        v1.iter().zip(v2.iter()).all(|(a, b)| a.0 == b.0)
    }

    /// 🌟 健全性の穴を塞ぐための数値的裏付けチェック。
    ///
    /// propagate_line_uniqueness / propagate_point_uniqueness の
    /// 「十分な数の接続関係を共有していれば同一とみなす」ショートカットは、
    /// 手作りの定理適用や素直な作図からしか合流が起きない前提では
    /// ほぼ常に正しいが、MCTSのような無方向な探索が持ち込む偶然の一致が
    /// 重なると、本来別々であるべき直線・点を誤って同一視してしまうことが
    /// 実際にあった(orthocenter問題で"垂線 ≡ 辺"のような偽の等式が生成され、
    /// 三角形が1本の直線に潰れる退化が発生した)。
    ///
    /// マージを確定する前に、FreePointにランダムな座標を割り当てた具体例で
    /// 両者が本当に等しい値になるかを検算し(Schwartz-Zippel的な考え方)、
    /// 明確に矛盾するならSome(false)を返して却下する。有向角(Ang90など)の
    /// ように座標を持たない記号的な定義しか無く判定不能な場合はNoneを返し、
    /// 呼び出し側は(従来通り)構造的な証明をそのまま信用してよい。
    ///
    /// これは証明の主経路に座標計算を持ち込むものではなく、あくまで
    /// 「安すぎて信用しすぎていたショートカットに対する事後検証」であり、
    /// このチェック自体が新しい事実を証明するわけではない。
    /// 🌟 直線/円curveへのpointの接続(incidence)が、curve自身の定義から
    /// 自然に(座標的に矛盾なく)従うものかどうかを判定する。
    /// 例: Line_AB=LineThroughPoints(A,B) に対する A の接続は、AがLine_ABの
    /// 定義の親そのものなので「自然」(常に座標的に正しい)。一方、
    /// Line_CAD=LineThroughPoints(C,A) に対する D の接続(miquel.rs等の
    /// 「DはこのCircle上にある」のような直接のlink_logical_incidence)は、
    /// Dがその定義の親に含まれないので「自然ではない」(座標的な裏付けがない、
    /// 構造だけの前提)。
    fn is_natural_incidence(&self, point: ClassId, curve: ClassId) -> bool {
        let point_rep = self.get_rep(point);
        let curve_rep = self.get_rep(curve);
        let curve_defs = match self.entities[curve_rep.0].components.first() {
            Some(c) => c.definitions.clone(),
            None => return false,
        };
        // 🐛 FIX (HAGeo-409ベンチマークで判明、propagate_circle_uniquenessの
        // 導入で顕在化): 以前はcurve_defsの「いずれか」の定義でpointが親なら
        // 自然な接続とみなしていた。しかしpropagate_line_uniqueness/
        // propagate_circle_uniquenessが「異なる点ペア(3点組)から作られた
        // 同じ直線(円)」を正しく統合すると、その直線(円)のdefinitionsは
        // 両方の点ペア(3点組)のUNIONになる――例えばLineThroughPoints(A,B)
        // と後から合流したLineThroughPoints(A,F)が両方残る。ここで「いずれか」
        // 判定をすると、Fは「line_ab上にある」という証明された(が本質的には
        // A,Bという真の生成点に対しては従属した)事実によってではなく、
        // 「LineThroughPoints(A,F)というdefinitionの親だから自然」という
        // 理由でnatural=trueになってしまい、以後Fの数値サンプリングが
        // 「line_ab上にある」という制約を無視した完全な乱数になる
        // (実測: miquelでこれが原因でLineAB自身とその需要駆動の複製が
        // 誤って「別の直線」と判定され、本来解けていた証明が解けなくなった)。
        // 対策として、curve_defsの中から常に同じ1つ(canonical_shape_definition、
        // 親のClassIdが辞書順最小のもの)だけを「真の自由な生成点の定義」として
        // 採用する。後から合流した(=canonicalではない)definitionの親は、
        // 直線/円が確かに通ることが証明された点ではあっても、それ自体は
        // 従属点として引き続き制約付きサンプリング(sample_point_on_constraint)
        // の対象にする――これは不健全化ではなく、むしろより正確な扱いになる
        // (F自身の座標はどのみちline_ab上に拘束されるべきものなので)。
        match Self::canonical_shape_definition(&curve_defs) {
            Some(def) => def.get_parents().iter().any(|&p| self.get_rep(p) == point_rep),
            None => false,
        }
    }

    /// 🌟 is_natural_incidenceのための決定論的な選択: 複数のdefinitionsが
    /// 合流して溜まっている場合でも、常に同じ1つ(親のClassId列が辞書順
    /// 最小のもの)を選ぶことで、「この直線/円の真の自由な生成点は誰か」を
    /// 一意に固定する(選び方が実行のたびにブレると、is_natural_incidenceの
    /// 判定結果ひいては数値サンプリングの安定性がブレてしまうため)。
    /// DirectionOf等の1引数のdefinitionは対象外(生成点のペア/組ではないため)。
    fn canonical_shape_definition(defs: &[Definition]) -> Option<&Definition> {
        defs.iter()
            .filter(|d| d.get_parents().len() >= 2)
            .min_by_key(|d| d.get_parents().iter().map(|p| p.0).collect::<Vec<_>>())
    }

    /// 🌟 このFreePointが、自身の座標では裏付けられない接続(incidence)を
    /// 1つでも持っているか(=numeric_plausibility_checkがこの点に依存する
    /// 数値評価を信用してよいか)を判定する。
    fn has_extraneous_incidence(&self, free_point: ClassId) -> bool {
        let rep = self.get_rep(free_point);
        let comp = match self.entities[rep.0].components.first() {
            Some(c) => c,
            None => return false,
        };
        comp.subobjects.iter()
            .map(|&s| self.get_rep(s))
            .filter(|&s| matches!(self.entities[s.0].entity_type, EntityType::Line | EntityType::Conic))
            .any(|curve| !self.is_natural_incidence(rep, curve))
    }

    /// 🌟 has_extraneous_incidenceが真だったFreePointについて、その前提の
    /// 相手となる直線/円を1つ選ぶ(自身の定義からは自然に従わない、
    /// link_logical_incidenceだけに由来する接続のうち最初に見つかったもの)。
    /// 1点が複数の構造的前提を同時に持つ場合、ここでは最初の1つしか満たさない
    /// (全部を同時に満たす座標は一般には存在しないので、これは近似的な
    /// 対処にとどまる)。
    fn find_incidence_constraint(&self, free_point: ClassId) -> Option<ClassId> {
        let rep = self.get_rep(free_point);
        let comp = self.entities[rep.0].components.first()?;
        comp.subobjects.iter()
            .map(|&s| self.get_rep(s))
            .find(|&s| matches!(self.entities[s.0].entity_type, EntityType::Line | EntityType::Conic)
                && !self.is_natural_incidence(rep, s))
    }

    /// 🌟 idの祖先(FreePoint)がすべてvarsに座標を持っているか。
    /// evaluate_node/evaluate_definitionはFreePointの座標がvarsに無くても
    /// (0,0)にフォールバックして黙って計算を続けてしまう(既存の呼び出しは
    /// 必ず全自由点の座標を事前に埋めてから呼ぶ前提のため、これが問題に
    /// ならなかった)。ここでの用途では「まだ座標が決まっていない自由点に
    /// 依存する評価」を(0,0)で誤魔化さず確実に弾く必要があるため、
    /// evaluate_nodeを呼ぶ前に明示的にチェックする。
    fn free_point_ancestors_ready(&self, id: ClassId, vars: &FxHashMap<String, ModInt>) -> bool {
        let mut visited = HashSet::new();
        let mut ancestors = Vec::new();
        self.collect_free_point_ancestors(id, &mut visited, &mut ancestors);
        ancestors.iter().all(|&fp| vars.contains_key(&format!("{}_x", self.entities[fp.0].name)))
    }

    /// 🌟 直線の係数(a,b,c: a*x+b*y+c=0)を満たすランダムな点(x,y)を1つ選ぶ。
    fn sample_point_on_line_coeffs(a: ModInt, b: ModInt, c: ModInt) -> Option<(ModInt, ModInt)> {
        if b.0 != 0 {
            let x = ModInt::new(rand::random::<i64>());
            let y = -(a * x + c) / b;
            Some((x, y))
        } else if a.0 != 0 {
            let y = ModInt::new(rand::random::<i64>());
            let x = -c / a;
            Some((x, y))
        } else {
            None // 縮退した直線(0=0)。理論上起こらないはずだが安全側に倒す
        }
    }

    /// 🌟 直線lineの上にあるランダムな点を1つサンプリングする。
    /// lineが依存する自由点の座標がまだ決まっていなければNone(呼び出し側で
    /// 後の反復に回してもらう)。
    fn sample_point_on_line(&self, line: ClassId, vars: &FxHashMap<String, ModInt>, cache: &mut FxHashMap<usize, Vec<ModInt>>) -> Option<(ModInt, ModInt)> {
        if !self.free_point_ancestors_ready(line, vars) { return None; }
        let coeffs = self.evaluate_node(line, vars, cache)?;
        if coeffs.len() < 3 { return None; }
        Self::sample_point_on_line_coeffs(coeffs[0], coeffs[1], coeffs[2])
    }

    /// 🌟 EntityType::Circle撤廃(円もConic)により、以前ここにあった
    /// circle_definition_known_point/sample_point_on_circle(4係数専用、
    /// Vietaの公式)は不要になり削除した。円もConicThrough5Pointsと全く同じ
    /// 経路(conic_definition_known_point/sample_point_on_conic、6係数)で
    /// サンプリングされる――円は実質的に「実点3つ+I+Jという5点」なので、
    /// 同じVietaの理屈がそのまま平方根なしに使える(削除の前提となった
    /// 旧コメントが指摘していたcalc_circumcircleの係数並び順の食い違いも、
    /// Circumcircleの評価自体をcalc_conic_through_5_points経由に統一した
    /// ことで解消済み)。
    ///
    /// 🌟 Circumcircle/ConicThrough5Pointsの定義から、その二次曲線に
    /// (定義上)乗っていることが保証されている点を1つ返す。Circumcircleの
    /// 3生成元はどれも本物の(L∞上ではない)点なので先頭でよいが、
    /// ConicThrough5Pointsの5生成元は(将来的にI,Jを直接生成元に含む
    /// 二次曲線が構築される可能性に備えて)L∞上の点(=無限遠点、z=0で
    /// Vietaのサンプリングに使えない)を避けて最初の"普通の"点を選ぶ。
    fn conic_definition_known_point(&self, conic: ClassId) -> Option<ClassId> {
        let rep = self.get_rep(conic);
        let comp = self.entities[rep.0].components.first()?;
        comp.definitions.iter().find_map(|def| {
            match def {
                Definition::Circumcircle(p1, _, _) => Some(*p1),
                Definition::ConicThrough5Points(p1, p2, p3, p4, p5) => {
                    [*p1, *p2, *p3, *p4, *p5].into_iter()
                        .find(|&p| !self.is_connected(p, self.line_infinity))
                }
                _ => None,
            }
        })
    }

    /// 🌟 二次曲線conicの上にあるランダムな点を1つサンプリングする。
    /// sample_point_on_circleの一般化: 二次曲線の方程式
    /// A x²+B xy+C y²+D x+E y+F=0 に、既に乗っていると分かっている点
    /// known_point=(x1,y1)を通るランダムな直線(x1+t dx, y1+t dy)を代入すると、
    /// tの2次方程式 α t²+β t+γ=0 のうちγ(定数項)はknown_pointが解であることから
    /// 恒等的に0になるので、t(αt+β)=0 の非自明な解 t=-β/α が(円の場合と全く
    /// 同じVietaの理屈で)平方根なしに直接求まる。
    fn sample_point_on_conic(&self, conic: ClassId, vars: &FxHashMap<String, ModInt>, cache: &mut FxHashMap<usize, Vec<ModInt>>) -> Option<(ModInt, ModInt)> {
        if !self.free_point_ancestors_ready(conic, vars) { return None; }
        let coeffs = self.evaluate_node(conic, vars, cache)?;
        if coeffs.len() < 6 { return None; }
        let (a, b, c, d, e) = (coeffs[0], coeffs[1], coeffs[2], coeffs[3], coeffs[4]);

        let known_point = self.conic_definition_known_point(conic)?;
        // known_pointはconicの生成元自身なので、free_point_ancestors_ready(conic, ..)が
        // 真であれば必ずその祖先もvarsに揃っている(部分集合関係)。
        let kp = self.evaluate_node(known_point, vars, cache)?;
        if kp.len() < 3 || kp[2].0 == 0 { return None; }
        let (x1, y1) = (kp[0] / kp[2], kp[1] / kp[2]);

        let two = ModInt::new(2);
        for _ in 0..8 {
            let dx = ModInt::new(rand::random::<i64>());
            let dy = ModInt::new(rand::random::<i64>());
            let alpha = a * dx * dx + b * dx * dy + c * dy * dy;
            if alpha.0 == 0 { continue; } // 縮退方向(漸近方向、理論上ごく低確率)。引き直す
            let beta = two * a * x1 * dx + b * (x1 * dy + y1 * dx) + two * c * y1 * dy + d * dx + e * dy;
            let t = -(beta / alpha);
            return Some((x1 + t * dx, y1 + t * dy));
        }
        None
    }

    /// 🌟 has_extraneous_incidence(fp)が真の自由点について、乗っていると
    /// 分かっている直線/円/二次曲線の上に乗るランダムな座標をサンプリングする。
    ///
    /// 🐛 FIX (HAGeo-409ベンチマークで判明): 以前はfind_incidence_constraint
    /// (複数の「構造的前提」のうち最初の1つだけを返す)が選んだ制約だけを
    /// 満たす座標を割り当てていた。1点が2本以上の直線に乗っていること
    /// (例: 「Fはline_ab上」という前提に加え、後からpropagate_line_uniqueness/
    /// propagate_circle_uniquenessの需要駆動作図が「Fはline_bf上」という
    /// 別の前提を追加した場合)が構造的には両立するはずの状況でも、
    /// 最初に見つかった1本だけを満たす座標では、選ばれなかった側の直線とは
    /// 数値的に食い違ってしまい、本来正しいはずの合流をnumeric_plausibility_checkが
    /// 誤って却下する(実測: miquelでLine_B_F_(Demand)とLineAB自体が
    /// 誤って「別の直線」と判定された)。乗っている直線が2本以上あって
    /// どちらも(依存する自由点の座標が既に揃っていて)評価可能なら、
    /// 1本だけ選ぶのではなくその2本の交点を計算することで、両方の前提を
    /// 同時に満たす一意な座標が求まる(2直線の交点は常に一意なので、
    /// 3本以上あっても最初の2本だけで位置は確定し、残りは自動的に
    /// 満たされているはずの構造的主張と整合する)。
    fn sample_point_on_constraint(&self, fp: ClassId, vars: &FxHashMap<String, ModInt>, cache: &mut FxHashMap<usize, Vec<ModInt>>) -> Option<(ModInt, ModInt)> {
        let rep = self.get_rep(fp);
        let ready_lines: Vec<ClassId> = self.find_extraneous_incidences(rep).into_iter()
            .filter(|&c| self.entities[c.0].entity_type == EntityType::Line && self.free_point_ancestors_ready(c, vars))
            .collect();
        if ready_lines.len() >= 2 {
            let v1 = self.evaluate_node(ready_lines[0], vars, cache)?;
            let v2 = self.evaluate_node(ready_lines[1], vars, cache)?;
            let inter = mmp_calculators::calc_intersection(&v1, &v2);
            if inter.len() < 3 || inter[2].0 == 0 { return None; } // 平行(無限遠)や退化は諦める
            return Some((inter[0] / inter[2], inter[1] / inter[2]));
        }

        let curve = self.find_incidence_constraint(rep)?;
        match self.entities[curve.0].entity_type {
            EntityType::Line => self.sample_point_on_line(curve, vars, cache),
            // 🌟 EntityType::Circle撤廃(円もConic)により、sample_point_on_circle
            // (4係数専用)への分岐は不要になった。全てsample_point_on_conic
            // (6係数、円は3実点+I+Jの5点として自動的に含まれる)に一本化する。
            EntityType::Conic => self.sample_point_on_conic(curve, vars, cache),
            _ => None,
        }
    }

    /// 🌟 find_incidence_constraintの「複数版」: has_extraneous_incidenceが
    /// 真となる原因になっている(=自身の定義からは自然に従わない)接続を
    /// 全て列挙する。sample_point_on_constraintが「2本以上の直線に同時に
    /// 乗っている」ケースを検出するために使う。
    fn find_extraneous_incidences(&self, free_point: ClassId) -> Vec<ClassId> {
        let rep = self.get_rep(free_point);
        let comp = match self.entities[rep.0].components.first() {
            Some(c) => c,
            None => return Vec::new(),
        };
        comp.subobjects.iter()
            .map(|&s| self.get_rep(s))
            .filter(|&s| matches!(self.entities[s.0].entity_type, EntityType::Line | EntityType::Conic)
                && !self.is_natural_incidence(rep, s))
            .collect()
    }

    /// 🌟 numeric_plausibility_check用に、祖先の自由点それぞれへ座標を割り当てる。
    /// 構造的前提を持たない自由点には単純な乱数座標を、持つ自由点にはその前提
    /// (直線/円の上にあること)を実際に満たす座標を割り当てる。前提を満たす
    /// 座標は、前提の相手(直線/円)が依存する自由点の座標が先に決まっている
    /// 必要があるため、複数パスで「計算できるものから確定させる」不動点反復を
    /// 行う。全ての制約点を解決できればtrue、対応できない構造的前提や
    /// 循環依存が残ればfalseを返す(呼び出し側は判定不能(None)に倒すこと)。
    fn assign_free_point_coords(&self, ancestors: &[ClassId], vars: &mut FxHashMap<String, ModInt>) -> bool {
        let mut pending: Vec<ClassId> = Vec::new();
        for &fp in ancestors {
            if self.has_extraneous_incidence(fp) {
                pending.push(fp);
            } else {
                let name = self.entities[fp.0].name.clone();
                vars.insert(format!("{}_x", name), ModInt::new(rand::random::<i64>()));
                vars.insert(format!("{}_y", name), ModInt::new(rand::random::<i64>()));
            }
        }

        let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
        loop {
            if pending.is_empty() { return true; }
            let mut progressed = false;
            let mut still_pending = Vec::new();
            for fp in pending.drain(..) {
                match self.sample_point_on_constraint(fp, vars, &mut cache) {
                    Some((x, y)) => {
                        let name = self.entities[fp.0].name.clone();
                        vars.insert(format!("{}_x", name), x);
                        vars.insert(format!("{}_y", name), y);
                        progressed = true;
                    }
                    None => still_pending.push(fp),
                }
            }
            pending = still_pending;
            if !progressed { return false; }
        }
    }

    /// 🌟 idの祖先(Definitionの親を再帰的に辿った先)にあるFreePointを全て集める。
    /// 定数(GivenPoint)はそこで打ち切る(座標を持たないので祖先探索の対象外)。
    /// マージ後は1つのエンティティが複数のDefinitionを持ち得るので、
    /// 「安全側」に倒して全てのDefinitionの親を辿る(いずれか1つでも構造的にしか
    /// 保証されていないFreePointに触れたら、そちら経由の値かもしれないとみなし
    /// 用心する)。
    fn collect_free_point_ancestors(&self, id: ClassId, visited: &mut HashSet<usize>, out: &mut Vec<ClassId>) {
        let rep = self.get_rep(id);
        if !visited.insert(rep.0) { return; }
        let defs = match self.entities[rep.0].components.first() {
            Some(c) => c.definitions.clone(),
            None => return,
        };
        for def in &defs {
            match def {
                Definition::FreePoint => out.push(rep),
                Definition::GivenPoint => {} // Ang90/Ang0/Line_infinity等の定数。座標を持たないので対象外
                _ => {
                    for p in def.get_parents() {
                        self.collect_free_point_ancestors(p, visited, out);
                    }
                }
            }
        }
    }

    /// 🌟 congruence.rs の propagate_line_uniqueness / propagate_point_uniqueness
    /// から、マージを確定する前のゲートとして呼ばれる(crate内の他モジュールから
    /// 呼べるようpub(crate)にしてある)。
    pub(crate) fn numeric_plausibility_check(&self, a: ClassId, b: ClassId, trials: usize) -> Option<bool> {
        // 🐛 FIX: このプロジェクトの問題設定は、しばしば「PはこのCircleに乗っている」
        // 「D,A,Cはこの順に一直線上」のような前提を、実際の座標制約としてではなく
        // link_logical_incidenceによる純粋に構造的な事実として直接与える
        // (simson.rs, miquel.rs, two_circles_reim.rs、あるいはMCTSの調和共役点の
        // 補助点P,Q等)。これは代数計算を避けるという設計方針そのものであり
        // 正しい設計だが、そのようなFreePointに完全に無作為な座標を割り当てると、
        // 本来満たすべき構造的な前提を満たさない具体例になってしまい、この
        // 健全性チェックが正しいマージまで誤って却下してしまう
        // (miquel/two_circles_reimで実際に発生した)。
        // 以前はここでNone(判定不能)を返して検証そのものを諦めていたが、
        // 現在はassign_free_point_coordsが、構造的前提を持つ自由点には
        // その前提(直線/円の上にあること)を実際に満たす座標をサンプリングする
        // (sample_point_on_line/sample_point_on_circle)。前提を満たす座標を
        // 組み立てられなかった場合(未対応の前提や循環依存)だけ、従来通り
        // Noneに倒す。
        let mut visited = HashSet::new();
        let mut ancestors = Vec::new();
        self.collect_free_point_ancestors(a, &mut visited, &mut ancestors);
        self.collect_free_point_ancestors(b, &mut visited, &mut ancestors);
        if ancestors.is_empty() { return None; }

        for _ in 0..trials {
            let mut vars: FxHashMap<String, ModInt> = FxHashMap::default();
            if !self.assign_free_point_coords(&ancestors, &mut vars) { return None; }

            let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
            match (self.evaluate_node(a, &vars, &mut cache), self.evaluate_node(b, &vars, &mut cache)) {
                (Some(va), Some(vb)) => {
                    if !Self::numeric_values_proportional(&va, &vb) { return Some(false); }
                }
                _ => return None,
            }
        }
        Some(true)
    }

    /// 🌟 Method of Moving Points(動点法)の「次数」を、実際に1つの自由点を
    /// 動かして数値的に測定する。以前のPython版にあったnumerical_degree/
    /// get_numerical_degreeに相当する機能で、mmp_math.rsには既に移植されて
    /// いた(matrix_rank_mod/get_numerical_degree)が、これまでどこからも
    /// 呼ばれていなかった(ユーザーが添付したMMP解説PDFの指摘で判明)。
    ///
    /// naive_degree的な「親の次数の単純和」という構造的な上界と違い、これは
    /// 実際にmover(祖先の自由点のうち1つ)を直線に沿って動かして複数の
    /// パラメータ値でサンプリングし、有限体上のランク判定(get_numerical_degree)
    /// で座標が実際に満たす有理関数の次数を検出する。これにより、
    /// Midpoint(中点)のような「構造的には2つの入力の合成に見えても、実際
    /// には次数が上がらない」操作を正しく低次数と判定できる一方、無関係な
    /// 2直線を繰り返し交差させるような操作は素直に次数が積み上がっていく
    /// ため、「次数が低い補助点を優先し、異常に高い補助点は避ける」という
    /// 判定に使える。
    ///
    /// mover(前提を持たない自由点祖先)が見つからない、あるいはいずれかの
    /// サンプルで評価不能(退化)だった場合はNone(次数不明)を返す――
    /// 呼び出し側は安全側に倒し、次数による足切りをしない扱いにすること。
    pub fn measure_numerical_degree(&self, entity: ClassId, max_d: usize) -> Option<usize> {
        let mut visited = HashSet::new();
        let mut ancestors = Vec::new();
        self.collect_free_point_ancestors(entity, &mut visited, &mut ancestors);
        if ancestors.is_empty() { return Some(0); } // 自由点に一切依存しない(定数)ので次数0

        let (mover, base_vars) = self.setup_mover_and_base_vars(&ancestors)?;
        let mover_name = self.entities[mover.0].name.clone();

        let k = 2 * max_d + 2;
        let (x0, y0, dx, dy) = Self::random_mover_line();
        let mut t_vals = Vec::with_capacity(k);
        let mut x_vals = Vec::with_capacity(k);
        let mut y_vals = Vec::with_capacity(k);
        for i in 1..=k {
            let t = ModInt::new(i as i64);
            let mut vars = base_vars.clone();
            vars.insert(format!("{}_x", mover_name), x0 + t * dx);
            vars.insert(format!("{}_y", mover_name), y0 + t * dy);
            let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
            let v = self.evaluate_node(entity, &vars, &mut cache)?;
            if v.len() < 3 || v[2].0 == 0 { return None; }
            t_vals.push(t);
            x_vals.push(v[0] / v[2]);
            y_vals.push(v[1] / v[2]);
        }
        let dxd = crate::mmp_math::get_numerical_degree(&t_vals, &x_vals, max_d);
        let dyd = crate::mmp_math::get_numerical_degree(&t_vals, &y_vals, max_d);
        Some(dxd.max(dyd))
    }

    /// 🌟 measure_numerical_degreeのメモ化版。ユーザー要望: 「複比の透視射影
    /// 不変性のように関連するオブジェクトが非常に多い定理を、次数を
    /// ヒューリスティックに使って最適な順序でマッチングしたい」への対応で、
    /// logic_core.rs::match_defined_by_fact が「候補が多いDefinedByパターンの
    /// マッチ候補を、次数の低い(単純な)ものから先に試す」ために呼ぶ。
    /// 定理マッチングは同じエンティティに対して何度も呼ばれ得るホットパスなので、
    /// 一度測定した代表元についてはGeoEntity::degree_cacheに結果を記憶し、以後は
    /// 再測定しない(measure_numerical_degree自体は複数回のevaluate_node呼び出しと
    /// 有限体上のランク判定を伴うため、無条件に呼び続けると探索そのものより
    /// 重くなりかねない)。キャッシュは(ユーザー指摘によりheat_bonus/uses等と
    /// 同じ場所に置くよう変更した)代表元自身のGeoEntity::degree_cacheに持たせる
    /// ――もし後からその代表元がさらに別のクラスへ吸収されても、古いスロットの
    /// キャッシュ値がどこかから誤って読まれることはない(get_repは常に現在の
    /// 代表元を指すインデックスへ解決するため)。
    pub fn cached_degree(&self, id: ClassId, max_d: usize) -> Option<usize> {
        let rep = self.get_rep(id);
        if let Some(cached) = self.entities[rep.0].degree_cache.get() {
            return cached;
        }
        let deg = self.measure_numerical_degree(rep, max_d);
        self.entities[rep.0].degree_cache.set(Some(deg));
        deg
    }

    /// 🌟 measure_numerical_degreeの「まだエンティティとして存在しない候補」版。
    /// resolve_point_demandsのような「実際に作る前に有望さを判定したい」
    /// 場面向けに、2直線l1, l2の交点をentityとして作らずに次数だけ測定する。
    pub fn measure_intersection_degree_candidate(&self, l1: ClassId, l2: ClassId, max_d: usize) -> Option<usize> {
        let mut visited = HashSet::new();
        let mut ancestors = Vec::new();
        self.collect_free_point_ancestors(l1, &mut visited, &mut ancestors);
        self.collect_free_point_ancestors(l2, &mut visited, &mut ancestors);
        if ancestors.is_empty() { return Some(0); }

        let (mover, base_vars) = self.setup_mover_and_base_vars(&ancestors)?;
        let mover_name = self.entities[mover.0].name.clone();

        let k = 2 * max_d + 2;
        let (x0, y0, dx, dy) = Self::random_mover_line();
        let mut t_vals = Vec::with_capacity(k);
        let mut x_vals = Vec::with_capacity(k);
        let mut y_vals = Vec::with_capacity(k);
        for i in 1..=k {
            let t = ModInt::new(i as i64);
            let mut vars = base_vars.clone();
            vars.insert(format!("{}_x", mover_name), x0 + t * dx);
            vars.insert(format!("{}_y", mover_name), y0 + t * dy);
            let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
            let v1 = self.evaluate_node(l1, &vars, &mut cache)?;
            let v2 = self.evaluate_node(l2, &vars, &mut cache)?;
            let p = mmp_calculators::calc_intersection(&v1, &v2);
            if p.len() < 3 || p.iter().all(|x| x.0 == 0) { return None; }
            t_vals.push(t);
            x_vals.push(p[0] / p[2]);
            y_vals.push(p[1] / p[2]);
        }
        let dxd = crate::mmp_math::get_numerical_degree(&t_vals, &x_vals, max_d);
        let dyd = crate::mmp_math::get_numerical_degree(&t_vals, &y_vals, max_d);
        Some(dxd.max(dyd))
    }

    /// 🌟 ある同次座標ベクトルの時系列サンプル(t_valsに対応する各tでの値)から
    /// 次数を測る共通処理。ユーザー指摘:「円も係数を射影空間の点だと思えば
    /// OK」への対応で、成分数を2D点/直線の3に固定していた旧実装を一般化した。
    /// 同次座標なので絶対スケールに意味は無く、比だけが意味を持つ――
    /// 最後の成分を基準に他の全成分を割った値それぞれの次数を測り、その
    /// 最大値を返す(3成分の点(x,y,1)/直線(a,b,c)なら常にindex 2で割って
    /// いた旧実装と完全に後方互換。円の係数(A,D,E,F)のような4成分でも
    /// そのまま同じ枠組みで動く)。基準成分がいずれかのサンプルで0になって
    /// いたら(退化)測定不能としてNoneを返す。
    fn degree_of_homogeneous_samples(t_vals: &[ModInt], samples: &[Vec<ModInt>], max_d: usize) -> Option<usize> {
        let n = samples.first()?.len();
        if n < 2 { return None; }
        let norm_idx = n - 1;
        if samples.iter().any(|s| s.len() != n || s[norm_idx].0 == 0) { return None; }
        let mut max_deg = 0;
        for i in 0..norm_idx {
            let ratios: Vec<ModInt> = samples.iter().map(|s| s[i] / s[norm_idx]).collect();
            max_deg = max_deg.max(crate::mmp_math::get_numerical_degree(t_vals, &ratios, max_d));
        }
        Some(max_deg)
    }

    /// 🌟 ユーザー提案: 「点の組A,Bについて、線分ABの次数がdeg(A)+deg(B)という
    /// 素朴な上界に比べて退化して小さい組は、何らかの隠れた定理・偶然の一致が
    /// 効いている兆候として『相性が良い』とみなせるのではないか」「多点での
    /// 評価を導入する」への対応。parents(2点でも3点でも4点でも良い)それぞれの
    /// 次数と、combineで組み合わせた結果(任意の成分数の同次座標ベクトル)の
    /// 次数を、同じmover・同じ他の自由点座標を使う1回の一貫したサンプリング
    /// パスで測定する。combineが返すベクトルは(円の係数(A,D,E,F)のような
    /// 4成分でも)degree_of_homogeneous_samplesにそのまま渡せる「射影空間の点」
    /// として扱う。
    ///
    /// 🌟 なぜ一貫した測定が必要か: measure_numerical_degreeをparentsの数だけ
    /// バラバラに呼ぶと、それぞれが(祖先集合が異なれば)別のmoverを選んだり、
    /// 「他の」自由点に別々の乱数座標を割り当てたりし得るため、次数どうしを
    /// 単純に比較することに意味がなくなる(比較したいのは「同じ1つの動きに
    /// 対して、各parentがどれだけ複雑に動くか・組み合わせ結果がどれだけ
    /// 複雑に動くか」という相対関係であり、測定条件を揃える必要がある)。
    pub fn measure_group_degrees(
        &self,
        parents: &[ClassId],
        combine: impl Fn(&[Vec<ModInt>]) -> Vec<ModInt>,
        max_d: usize,
    ) -> Option<(Vec<usize>, usize)> {
        let mut visited = HashSet::new();
        let mut ancestors = Vec::new();
        for &p in parents {
            self.collect_free_point_ancestors(p, &mut visited, &mut ancestors);
        }
        if ancestors.is_empty() { return Some((vec![0; parents.len()], 0)); }

        let (mover, base_vars) = self.setup_mover_and_base_vars(&ancestors)?;
        let mover_name = self.entities[mover.0].name.clone();

        let k = 2 * max_d + 2;
        let (x0, y0, dx, dy) = Self::random_mover_line();
        let mut t_vals = Vec::with_capacity(k);
        let mut parent_samples: Vec<Vec<Vec<ModInt>>> = vec![Vec::with_capacity(k); parents.len()];
        let mut combined_samples: Vec<Vec<ModInt>> = Vec::with_capacity(k);
        for i in 1..=k {
            let t = ModInt::new(i as i64);
            let mut vars = base_vars.clone();
            vars.insert(format!("{}_x", mover_name), x0 + t * dx);
            vars.insert(format!("{}_y", mover_name), y0 + t * dy);
            let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
            let mut vals = Vec::with_capacity(parents.len());
            for &p in parents {
                vals.push(self.evaluate_node(p, &vars, &mut cache)?);
            }
            combined_samples.push(combine(&vals));
            for (idx, v) in vals.into_iter().enumerate() {
                parent_samples[idx].push(v);
            }
            t_vals.push(t);
        }

        let mut parent_degs = Vec::with_capacity(parents.len());
        for samples in &parent_samples {
            parent_degs.push(Self::degree_of_homogeneous_samples(&t_vals, samples, max_d)?);
        }
        let combined_deg = Self::degree_of_homogeneous_samples(&t_vals, &combined_samples, max_d)?;
        Some((parent_degs, combined_deg))
    }

    /// 🌟 measure_group_degreesの2点(直線)特化版。resolve_demandsから使う。
    pub fn measure_line_affinity(&self, a: ClassId, b: ClassId, max_d: usize) -> Option<(usize, usize, usize)> {
        let (degs, combined) = self.measure_group_degrees(
            &[a, b],
            |vals| mmp_calculators::calc_line_through_points(&vals[0], &vals[1]),
            max_d,
        )?;
        Some((degs[0], degs[1], combined))
    }

    /// 🌟 measure_group_degreesの3点(外接円)特化版。ユーザー提案の「これを
    /// 3,4点とかでやったら」への対応。円は4成分(A,D,E,F)の同次ベクトルだが、
    /// degree_of_homogeneous_samples側が成分数を問わず扱えるため、
    /// measure_line_affinityと全く同じ枠組みでそのまま使える。deg(A)+deg(B)+
    /// deg(C)という素朴な和に対しCircumcircle(A,B,C)の次数が退化して小さい
    /// 3点の組は、A,B,Cが常に(あるいは頻繁に)同じ円に乗るような隠れた
    /// 構造を持っている兆候として「相性が良い」とみなせる。
    pub fn measure_circle_affinity(&self, a: ClassId, b: ClassId, c: ClassId, max_d: usize) -> Option<(usize, usize, usize, usize)> {
        let (degs, combined) = self.measure_group_degrees(
            &[a, b, c],
            |vals| mmp_calculators::calc_circumcircle(&vals[0], &vals[1], &vals[2]),
            max_d,
        )?;
        Some((degs[0], degs[1], degs[2], combined))
    }

    /// 🌟 measure_group_degreesの4点(複比)特化版。ユーザー提案:「複比の定理を
    /// 使うときは複比自体を次数を用いて生成に制限をかけて」への対応。
    /// calc_cross_ratioはScalar(k,1,1)を返す――第1,2成分が常に1という自明な
    /// (次数0の)定数なので、degree_of_homogeneous_samplesが最後の成分(常に1)
    /// で割ることは無害であり、実質的にkそのものの次数だけが結果を決める。
    /// 4点A,B,C,Dの次数の和に対し複比の次数が異常に高い(=無関係な4点の
    /// 組み合わせ)場合は生成自体を諦めるゲートに使う。
    pub fn measure_cross_ratio_affinity(&self, a: ClassId, b: ClassId, c: ClassId, d: ClassId, max_d: usize) -> Option<(usize, usize, usize, usize, usize)> {
        let (degs, combined) = self.measure_group_degrees(
            &[a, b, c, d],
            |vals| mmp_calculators::calc_cross_ratio(&vals[0], &vals[1], &vals[2], &vals[3])
                .map(|k| vec![k, ModInt::new(1), ModInt::new(1)])
                .unwrap_or_default(),
            max_d,
        )?;
        Some((degs[0], degs[1], degs[2], degs[3], combined))
    }

    /// 🌟 ユーザー提案:「複比同士の関係式からconjectureを発行して、そこから
    /// 定理適用の形を見つける」への対応。新しく作られた複比エンティティ
    /// new_idの値を、既存の他の全ての複比エンティティと(1回の乱数サンプルで)
    /// 数値的に比較し、値が一致するものがあればlog_conjecture_candidateで
    /// 予想として記録する(既存のprocess_pending_conjectures/heat_bonus
    /// フィードバック機構にそのまま乗る――現実の証明状態は一切変更しない
    /// 安全な拡張)。
    ///
    /// 🌟 なぜ「比例」ではなく「等値」判定か: 複比の評価値は[k, 1, 1]という
    /// 形で、第1,2成分が常に1に固定されているため、通常の点/直線のような
    /// 射影的スケール不変の比例判定は不要で、k自体の値がそのまま複比の値
    /// そのもの(Identical(CrossRatio1, CrossRatio2)が意味したいのはまさに
    /// この値の一致)。
    pub fn detect_cross_ratio_coincidences(&self, new_id: ClassId) {
        let new_rep = self.get_rep(new_id);
        // 🌟 CrossRatio(点の複比)とCrossRatioOfLines(線束の複比)の両方を
        // 対象にスキャンする――ユーザーが提案する定理A/B("点の複比→線束の
        // 複比"、"線束の複比→点の複比")が実際に成り立つ組み合わせは、まさに
        // 「点の複比のエンティティと線束の複比のエンティティが数値的に一致
        // する」という異なる種類どうしの一致として現れるため。
        let others: Vec<ClassId> = (0..self.entities.len())
            .filter(|&i| matches!(self.entities[i].original_definition, Definition::CrossRatio(..) | Definition::CrossRatioOfLines(..)))
            .map(ClassId)
            .map(|id| self.get_rep(id))
            .filter(|&rep| rep != new_rep)
            .collect();
        if others.is_empty() { return; }

        let mut visited = HashSet::new();
        let mut ancestors = Vec::new();
        self.collect_free_point_ancestors(new_rep, &mut visited, &mut ancestors);
        for &other in &others {
            self.collect_free_point_ancestors(other, &mut visited, &mut ancestors);
        }
        if ancestors.is_empty() { return; }

        let mut vars: FxHashMap<String, ModInt> = FxHashMap::default();
        if !self.assign_free_point_coords(&ancestors, &mut vars) { return; }
        let mut cache: FxHashMap<usize, Vec<ModInt>> = FxHashMap::default();
        let Some(v_new) = self.evaluate_node(new_rep, &vars, &mut cache) else { return; };
        if v_new.is_empty() { return; }

        for &other in &others {
            if let Some(v_other) = self.evaluate_node(other, &vars, &mut cache) {
                if !v_other.is_empty() && v_new[0].0 == v_other[0].0 {
                    self.log_conjecture_candidate(new_rep, other, "複比の値が一致(透視射影関係などの可能性)");
                }
            }
        }
    }

    /// 🌟 measure_numerical_degree系の共通処理: 祖先の自由点の中から
    /// 「他の構造的前提(直線/円の上にあること)を持たない」ものを1つ選んで
    /// mover(動点)とし、残りは(前提を満たす形で)1回だけ座標を固定する。
    /// 適切なmoverが見つからない場合はNone。
    fn setup_mover_and_base_vars(&self, ancestors: &[ClassId]) -> Option<(ClassId, FxHashMap<String, ModInt>)> {
        let mover = *ancestors.iter().find(|&&fp| !self.has_extraneous_incidence(fp))?;
        let others: Vec<ClassId> = ancestors.iter().copied().filter(|&fp| fp != mover).collect();
        let mut base_vars: FxHashMap<String, ModInt> = FxHashMap::default();
        if !self.assign_free_point_coords(&others, &mut base_vars) { return None; }
        Some((mover, base_vars))
    }

    /// 🌟 moverが動く先の「一般の位置にある直線」: 基点(x0,y0)と方向(dx,dy)を
    /// 無作為に選ぶ(moverの座標はx0+t*dx, y0+t*dyとしてtでパラメータ化される)。
    fn random_mover_line() -> (ModInt, ModInt, ModInt, ModInt) {
        (
            ModInt::new(rand::random::<i64>()),
            ModInt::new(rand::random::<i64>()),
            ModInt::new(rand::random::<i64>()),
            ModInt::new(rand::random::<i64>()),
        )
    }
}

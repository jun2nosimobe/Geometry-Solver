//! 🌟 数値評価環境(MMPテスト用)と、それを土台にした健全性チェック。
//! ここでの数値計算はあくまでテスト・事後検証のためのものであり、
//! メインの証明導出(合同閉包・定理適用)は一切これに依存しない。

use std::collections::HashSet;
use rustc_hash::FxHashMap;
use crate::mmp_math::ModInt;
use crate::mmp_calculators;
use super::{ClassId, Definition, EntityType, EGraph};

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
            Definition::AnglePair(d1, d2) => {
                let v1 = self.evaluate_node_inner(*d1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*d2, vars, cache, in_progress)?;
                if v1.len() >= 2 && v2.len() >= 2 {
                    // 外積(sin)と内積(cos)で有向角を一意に表現
                    let cross = v1[0] * v2[1] - v1[1] * v2[0];
                    let dot = v1[0] * v2[0] + v1[1] * v2[1];
                    Some(vec![cross, dot, ModInt::new(1)])
                } else {
                    None
                }
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
            Definition::Circumcircle(p1, p2, p3) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                let v3 = self.evaluate_node_inner(*p3, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_circumcircle(&v1, &v2, &v3))
            }
            Definition::TangentLine(c, p) => {
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                let vp = self.evaluate_node_inner(*p, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_tangent_line(&vc, &vp))
            }
            Definition::HarmonicConjugateOf(a, b, c) => {
                let va = self.evaluate_node_inner(*a, vars, cache, in_progress)?;
                let vb = self.evaluate_node_inner(*b, vars, cache, in_progress)?;
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                Self::to_option(mmp_calculators::calc_harmonic_conjugate(&va, &vb, &vc))
            }
            _ => None,
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
    fn log_conjecture_candidate(&self, a: ClassId, b: ClassId, hypothesis: &str) {
        let rep_a = self.get_rep(a);
        let rep_b = self.get_rep(b);
        if rep_a == rep_b { return; } // 既に記号的に証明済みなら予想ではない
        let name_a = &self.entities[rep_a.0].name;
        let name_b = &self.entities[rep_b.0].name;
        println!(
            "  🔮 [予想候補] {} と {} は独立な乱数サンプルで数値的に一致しました(仮説: {})。\
             まだ証明はされていませんが、偶然の確率は約10億分の1なので実在する関係の可能性が高いです。",
            name_a, name_b, hypothesis
        );
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
        curve_defs.iter().any(|def| {
            def.get_parents().iter().any(|&p| self.get_rep(p) == point_rep)
        })
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
            .filter(|&s| matches!(self.entities[s.0].entity_type, EntityType::Line | EntityType::Circle))
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
            .find(|&s| matches!(self.entities[s.0].entity_type, EntityType::Line | EntityType::Circle)
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

    /// 🌟 Circumcircleの定義から、その円に(定義上)乗っていることが保証されている
    /// 点を1つ返す(3つの生成元のうち最初のもの)。
    fn circle_definition_known_point(&self, circle: ClassId) -> Option<ClassId> {
        let rep = self.get_rep(circle);
        let comp = self.entities[rep.0].components.first()?;
        comp.definitions.iter().find_map(|def| {
            if let Definition::Circumcircle(p1, _, _) = def { Some(*p1) } else { None }
        })
    }

    /// 🌟 円circleの上にあるランダムな点を1つサンプリングする。
    /// 円の方程式 A(x²+y²)+Dx+Ey+F=0 に対し、円自身の定義から既に乗っていると
    /// 分かっている点(known_point)を通るランダムな直線を引き、その直線と
    /// 円のもう一方の交点を求める。known_pointに対応する解(t=0)が既知なので、
    /// Vietaの公式から残りの解が線形に求まり、平方剰余(sqrt)を一切必要としない
    /// (このプロジェクトの法 998244353 は p≡1 (mod 4) でTonelli-Shanksが
    /// 面倒になる法なので、これは実装上都合が良い)。
    /// 🐛 注意: calc_circumcircle/calc_tangent_lineのコメントは係数の並びを
    /// [D,E,F,A]と書いているが、実際にcalc_circumcircleがこの順で返す値を
    /// 検証したところ [A,D,E,F] (0番目がx²+y²の係数)だった(コメント自体が
    /// 誤りだが、calc_tangent_line側は数値評価経路でしか使われず既存12問題の
    /// 症状として顕在化していなかったので、ここではそちらには触れず、
    /// 実際に検証した正しい並びだけをこの関数で使う)。
    fn sample_point_on_circle(&self, circle: ClassId, vars: &FxHashMap<String, ModInt>, cache: &mut FxHashMap<usize, Vec<ModInt>>) -> Option<(ModInt, ModInt)> {
        if !self.free_point_ancestors_ready(circle, vars) { return None; }
        let coeffs = self.evaluate_node(circle, vars, cache)?;
        if coeffs.len() < 4 { return None; }
        let (a_coef, d, e, f) = (coeffs[0], coeffs[1], coeffs[2], coeffs[3]);

        if a_coef.0 == 0 {
            // 退化(3生成点が同一直線上など): 実質的に直線 Dx+Ey+F=0 として扱う
            return Self::sample_point_on_line_coeffs(d, e, f);
        }

        let known_point = self.circle_definition_known_point(circle)?;
        // known_pointはcircleの生成元自身なので、free_point_ancestors_ready(circle, ..)が
        // 真であれば必ずその祖先もvarsに揃っている(部分集合関係)。
        let kp = self.evaluate_node(known_point, vars, cache)?;
        if kp.len() < 3 || kp[2].0 == 0 { return None; }
        let (x1, y1) = (kp[0] / kp[2], kp[1] / kp[2]);

        let two = ModInt::new(2);
        for _ in 0..8 {
            let dx = ModInt::new(rand::random::<i64>());
            let dy = ModInt::new(rand::random::<i64>());
            let a1 = a_coef * (dx * dx + dy * dy);
            if a1.0 == 0 { continue; } // 縮退方向(理論上ごく低確率)。引き直す
            let b1 = a_coef * two * (x1 * dx + y1 * dy) + d * dx + e * dy;
            let t = -(b1 / a1);
            return Some((x1 + t * dx, y1 + t * dy));
        }
        None
    }

    /// 🌟 has_extraneous_incidence(fp)が真の自由点について、find_incidence_constraintで
    /// 選んだ直線/円の上に乗るランダムな座標をサンプリングする。
    fn sample_point_on_constraint(&self, fp: ClassId, vars: &FxHashMap<String, ModInt>, cache: &mut FxHashMap<usize, Vec<ModInt>>) -> Option<(ModInt, ModInt)> {
        let rep = self.get_rep(fp);
        let curve = self.find_incidence_constraint(rep)?;
        match self.entities[curve.0].entity_type {
            EntityType::Line => self.sample_point_on_line(curve, vars, cache),
            EntityType::Circle => self.sample_point_on_circle(curve, vars, cache),
            _ => None,
        }
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
}

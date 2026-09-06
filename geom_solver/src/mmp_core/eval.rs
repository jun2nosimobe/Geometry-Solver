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
                Some(mmp_calculators::calc_midpoint(&v1, &v2))
            }
            Definition::LineThroughPoints(p1, p2) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                Some(mmp_calculators::calc_line_through_points(&v1, &v2))
            }
            Definition::Intersection(l1, l2) => {
                let v1 = self.evaluate_node_inner(*l1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*l2, vars, cache, in_progress)?;
                Some(mmp_calculators::calc_intersection(&v1, &v2))
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
                    Some(mmp_calculators::normalize(&[v[1], -v[0], ModInt::new(0)]))
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
                Some(vec![mmp_calculators::calc_squared_distance(&v1, &v2), ModInt::new(1), ModInt::new(1)])
            }
            Definition::PerpendicularLine(l, p) => {
                let vl = self.evaluate_node_inner(*l, vars, cache, in_progress)?;
                let vp = self.evaluate_node_inner(*p, vars, cache, in_progress)?;
                Some(mmp_calculators::calc_perpendicular(&vl, &vp))
            }
            // 🌟 以前は未実装で、ParallelLine型のエンティティ(まだ他の定義と
            // マージされていないもの)を数値サニティチェック(numeric_plausibility_check)
            // で評価できず、健全性チェックが素通りしてしまう抜け穴になっていた。
            Definition::ParallelLine(l, p) => {
                let vl = self.evaluate_node_inner(*l, vars, cache, in_progress)?;
                let vp = self.evaluate_node_inner(*p, vars, cache, in_progress)?;
                Some(mmp_calculators::calc_parallel(&vl, &vp))
            }
            // 🌟 同上の理由でPerpDirectionOfも実装する。方向ベクトル(dx,dy)を
            // 90度回転させるだけ((dx,dy) -> (-dy,dx))。
            Definition::PerpDirectionOf(d) => {
                let v = self.evaluate_node_inner(*d, vars, cache, in_progress)?;
                if v.len() >= 2 {
                    // DirectionOfと同じ理由でz成分0を付けた3要素の同次座標に統一する。
                    Some(mmp_calculators::normalize(&[-v[1], v[0], ModInt::new(0)]))
                } else {
                    None
                }
            }
            Definition::Circumcircle(p1, p2, p3) => {
                let v1 = self.evaluate_node_inner(*p1, vars, cache, in_progress)?;
                let v2 = self.evaluate_node_inner(*p2, vars, cache, in_progress)?;
                let v3 = self.evaluate_node_inner(*p3, vars, cache, in_progress)?;
                Some(mmp_calculators::calc_circumcircle(&v1, &v2, &v3))
            }
            Definition::TangentLine(c, p) => {
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                let vp = self.evaluate_node_inner(*p, vars, cache, in_progress)?;
                Some(mmp_calculators::calc_tangent_line(&vc, &vp))
            }
            Definition::HarmonicConjugateOf(a, b, c) => {
                let va = self.evaluate_node_inner(*a, vars, cache, in_progress)?;
                let vb = self.evaluate_node_inner(*b, vars, cache, in_progress)?;
                let vc = self.evaluate_node_inner(*c, vars, cache, in_progress)?;
                Some(mmp_calculators::calc_harmonic_conjugate(&va, &vb, &vc))
            }
            _ => None,
        }
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
        // a, b それぞれの祖先(依存する図形)だけを辿り、そこに構造的前提を持つ
        // FreePointが1つでもあれば、この特定の比較だけを信用せずNone
        // (判定不能)を返す。グラフ全体を見て一律に諦めるのではなく、
        // 実際にa, bの値に影響し得る範囲だけで判断することで、無関係な箇所に
        // 構造的前提があるだけの他のケース(orthocenter問題など)では
        // 引き続きチェックが働くようにしている。
        let mut visited = HashSet::new();
        let mut ancestors = Vec::new();
        self.collect_free_point_ancestors(a, &mut visited, &mut ancestors);
        self.collect_free_point_ancestors(b, &mut visited, &mut ancestors);

        let has_structurally_constrained_free_point = ancestors.iter().any(|&fp| self.has_extraneous_incidence(fp));
        if has_structurally_constrained_free_point { return None; }

        let free_point_names: Vec<String> = ancestors.iter().map(|&fp| self.entities[fp.0].name.clone()).collect();
        if free_point_names.is_empty() { return None; }

        for _ in 0..trials {
            let mut vars: FxHashMap<String, ModInt> = FxHashMap::default();
            for name in &free_point_names {
                vars.insert(format!("{}_x", name), ModInt::new(rand::random::<i64>()));
                vars.insert(format!("{}_y", name), ModInt::new(rand::random::<i64>()));
            }
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

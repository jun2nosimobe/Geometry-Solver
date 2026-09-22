//! 🌟 EGraphの状態を問い合わせるだけの読み取り専用ユーティリティ
//! (接続関係の判定、共通の円の探索、デバッグ用の状態ダンプなど)。

use super::{ClassId, Definition, EntityType, EGraph};

/// 目標の状態(EGraph::goal_status)。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GoalStatus {
    /// まだ導けていない。
    NotYet,
    /// 導けていて、数値の検算にも矛盾しない。
    Reached,
    /// 自由点どうしが同じ同値類に入った(図が潰れていて、どんな目標も「証明」できてしまう)。値は2つの自由点の名前。
    Collapsed(String, String),
    /// 構造的には導けたが、前提を満たす座標で検算すると成り立たない(どこかの局所マージが誤っている)。
    NumericallyFalse,
}

impl EGraph {
    /// 🌟 目標に到達したか。solve・serve・discover の証明試行で共通の判定。
    /// 図の崩壊は目標に関係なく先に調べる(崩壊した図からは何でも従うので、到達しても証明と認めない)。
    /// Identical は前提を満たす座標で検算し、明確に矛盾すれば NumericallyFalse(座標を組み立てられない・評価
    /// できない比較は判定不能なので、構造的な証明をそのまま信用する)。Concyclic と Connected はまだ検算しない。
    pub fn goal_status(&self, target: Option<&(String, Vec<ClassId>)>) -> GoalStatus {
        if let Some((p, q)) = self.merged_free_points() {
            return GoalStatus::Collapsed(p, q);
        }
        let Some(target) = target else { return GoalStatus::NotYet };
        if !self.goal_reached(target) { return GoalStatus::NotYet; }
        let (kind, args) = target;
        if kind == "Identical" && self.numeric_plausibility_check(args[0], args[1], 3) == Some(false) {
            return GoalStatus::NumericallyFalse;
        }
        GoalStatus::Reached
    }

    /// 目標が構造的に導けているか(崩壊と数値の検算は見ない。goal_status の一部)。
    pub fn goal_reached(&self, (kind, args): &(String, Vec<ClassId>)) -> bool {
        match kind.as_str() {
            "Identical" => self.get_rep(args[0]) == self.get_rep(args[1]),
            "Concyclic" => {
                let reps: Vec<ClassId> = args.iter().map(|&id| self.get_rep(id)).collect();
                self.points_share_a_circle(&reps)
            }
            "Connected" => self.is_connected(self.get_rep(args[0]), self.get_rep(args[1])),
            _ => false,
        }
    }

    /// 🌟 id に接続している実体のうち、型が ty のものの数(代表元で重複除去)。logic_core::cost の estimate_cost が
    /// 「片側だけ束縛された Connected」の分岐数を見積もるのに使う(接続先が2つか12個かで分岐の大きさが全く違う)。
    /// matcher.rs の列挙と同じく subobjects を rep 化して数えるが、厳密な一致は要らない(並べ替えの順序が合えばよい)。
    pub fn count_neighbors_of_type(&self, id: ClassId, ty: EntityType) -> usize {
        let rep = self.get_rep(id);
        let mut seen = rustc_hash::FxHashSet::default();
        for comp in &self.entities[rep.0].components {
            for &sub in &comp.subobjects {
                let s = self.get_rep(sub);
                if s == rep { continue; }
                if self.entities[s.0].entity_type != ty { continue; }
                if !self.entities[s.0].is_active() { continue; }
                seen.insert(s.0);
            }
        }
        seen.len()
    }

    /// 🌟 現在アクティブな(=自身が代表元である)エンティティの数。マージが
    /// 実際にいくつ起きたかの粗い指標として使う(MCTSの報酬評価、予想候補の
    /// 価値推定(eval.rs::estimate_conjecture_value)などで共有する)。
    pub fn count_active_classes(&self) -> usize {
        (0..self.entities.len()).filter(|&i| self.get_rep(ClassId(i)).0 == i).count()
    }

    /// 🌟 この Scalar が有向角(AnglePair)か。型では区別できないので、この ID が吸収してきた全ての定義のどれかが
    /// AnglePair かで判定する(original_definition だけを見ると、Ang90/Ang0 のような別起源の実体に吸収された場合を
    /// 見逃す)。角度の定理の自己束縛候補を、長さや複比の Scalar まで広げないために使う。
    pub fn is_angle_value(&self, id: ClassId) -> bool {
        let rep = self.get_rep(id);
        self.entities[rep.0].components.first()
            .is_some_and(|c| c.definitions.iter().any(|d| matches!(d, Definition::AnglePair(_, _))))
    }

    /// 🌟 is_angle_value と同じ発想で、この Scalar が CrossRatioOfLines(線束の複比)由来か。シュタイナーの定理の逆の
    /// 自己束縛(SelfBindPool::CrossRatioOfLines)の候補を絞るのに使う。
    pub fn is_cross_ratio_of_lines_value(&self, id: ClassId) -> bool {
        let rep = self.get_rep(id);
        self.entities[rep.0].components.first()
            .is_some_and(|c| c.definitions.iter().any(|d| matches!(d, Definition::CrossRatioOfLines(_, _, _, _))))
    }

    pub fn is_connected(&self, id1: ClassId, id2: ClassId) -> bool {
        let r1 = self.get_rep(id1);
        let r2 = self.get_rep(id2);

        for comp in &self.entities[r1.0].components {
            if comp.subobjects.iter().any(|&s| self.get_rep(s) == r2) { return true; }
        }
        for comp in &self.entities[r2.0].components {
            if comp.subobjects.iter().any(|&s| self.get_rep(s) == r1) { return true; }
        }
        false
    }

    /// 🌟 points の全ての点が乗っている共通の円があるか(共円の目標判定などに使う)。円は数が少ないので全て舐めても軽い。
    /// Conic 型であるだけでなく I,J の両方に接続している(本物の円である)ことも確認する(一般の二次曲線を共円と
    /// 誤判定しない)。
    pub fn points_share_a_circle(&self, points: &[ClassId]) -> bool {
        if points.is_empty() { return false; }
        for i in 0..self.entities.len() {
            let cand = ClassId(i);
            if self.get_rep(cand) != cand { continue; }
            if self.entities[i].entity_type != EntityType::Conic { continue; }
            if !self.is_connected(cand, self.circ_i) || !self.is_connected(cand, self.circ_j) { continue; }
            if points.iter().all(|&p| self.is_connected(p, cand)) {
                return true;
            }
        }
        false
    }

    pub fn format_definition(&self, def: &Definition) -> String {
        self.format_definition_with(def, |id| self.entities[self.get_rep(id).0].name.clone())
    }

    /// 🌟 format_definitionの汎用版: 各親の表示に使う名前をname_ofに委ねる。
    /// discover.rs(自由探索の発見レポート)が、実体本来の名前(自動生成の
    /// たびに親の名前を連結するため、構成が深くなると際限なく長くなる)の
    /// 代わりに短い付け替え名(P1, L1, M1...)を割り当てて表示するために
    /// 追加した――既存の呼び出し元(dump_state, mcts.rs::describe_action)は
    /// 全てformat_definition経由でこれまで通りの実際の名前を使う。
    pub fn format_definition_with<F: Fn(ClassId) -> String>(&self, def: &Definition, name_of: F) -> String {
        let get_name = |id: &ClassId| name_of(*id);
        match def {
            Definition::GivenPoint => "GivenPoint".to_string(),
            Definition::FreePoint => "FreePoint".to_string(),
            Definition::Intersection(a, b) => format!("Intersection({}, {})", get_name(a), get_name(b)),
            Definition::LineThroughPoints(a, b) => format!("LineThrough({}, {})", get_name(a), get_name(b)),
            Definition::Midpoint(a, b) => format!("Midpoint({}, {})", get_name(a), get_name(b)),
            Definition::DirectionOf(a) => format!("DirectionOf({})", get_name(a)),
            Definition::PerpDirectionOf(a) => format!("PerpDirectionOf({})", get_name(a)),
            Definition::AnglePair(a, b) => format!("AnglePair({}, {})", get_name(a), get_name(b)),
            Definition::PerpendicularLine(l, p) => format!("Perpendicular({} ⟂ {})", get_name(l), get_name(p)),
            Definition::ParallelLine(l, p) => format!("Parallel({} ∥ {})", get_name(l), get_name(p)),
            Definition::LengthSq(a, b) => format!("LengthSq({}, {})", get_name(a), get_name(b)),
            Definition::Circumcircle(a, b, c) => format!("Circumcircle({}, {}, {})", get_name(a), get_name(b), get_name(c)),
            Definition::TangentLine(c, p) => format!("TangentLine({}, {})", get_name(c), get_name(p)),
            Definition::HarmonicConjugateOf(a, b, c) => format!("HarmonicConjugate({}, {}; {})", get_name(a), get_name(b), get_name(c)),
            Definition::CrossRatio(a, b, c, d) => format!("CrossRatio({}, {}; {}, {})", get_name(a), get_name(b), get_name(c), get_name(d)),
            Definition::CrossRatioOfLines(a, b, c, d) => format!("CrossRatioOfLines({}, {}; {}, {})", get_name(a), get_name(b), get_name(c), get_name(d)),
            Definition::ConstantHomogeneous(a, b, c) => format!("Constant({:?}, {:?}, {:?})", a, b, c),
            Definition::ConicThrough5Points(a, b, c, d, e) => format!("ConicThrough5Points({}, {}, {}, {}, {})", get_name(a), get_name(b), get_name(c), get_name(d), get_name(e)),
            Definition::Product(a, b) => format!("Product({}, {})", get_name(a), get_name(b)),
            Definition::SecondIntersectionOfLineAndConic(p, l, c) => format!("SecondIntersection({}; {}, {})", get_name(p), get_name(l), get_name(c)),
            Definition::RadicalAxis(c1, c2) => format!("RadicalAxis({}, {})", get_name(c1), get_name(c2)),
            Definition::SecondIntersectionOfCircles(p, c1, c2) => format!("SecondIntersectionOfCircles({}; {}, {})", get_name(p), get_name(c1), get_name(c2)),
        }
    }

    /// 🌟 自由点どうしが同じ同値類に入っていないか(= e-graph が崩壊していないか)を調べ、崩壊していれば最初に
    /// 見つけた組を返す。自由点は独立に置けるので、正しい推論だけを積んだ限り一致しない。一致しているなら局所マージが
    /// 無関係な図形を結合して図全体が潰れており、そこからは任意の目標が「証明」できてしまう(崩壊した e-graph の定義を
    /// 辿るので、目標の数値チェックもそれに騙される)。
    /// 戻り値は2つの自由点の名前。merge_entities は吸収された側の name を奪うので、作られた順に名前を控えながら走査する。
    pub fn merged_free_points(&self) -> Option<(String, String)> {
        let mut seen: std::collections::HashMap<usize, String> = std::collections::HashMap::new();
        for i in 0..self.entities.len() {
            let e = &self.entities[i];
            if e.entity_type != EntityType::Point { continue; }
            if !matches!(e.original_definition, Definition::FreePoint) { continue; }
            // 吸収済みなら name は空なので、その場合は作成順の番号で示す。
            let label = if e.name.is_empty() { format!("#{}", i) } else { e.name.clone() };
            let rep = self.get_rep(ClassId(i));
            if let Some(other) = seen.get(&rep.0) {
                return Some((other.clone(), label));
            }
            seen.insert(rep.0, label);
        }
        None
    }

    /// 現在のE-Graphの有効な同値類と、その作図履歴・関係を出力する
    pub fn dump_state(&self) {
        println!("\n=== 📊 E-Graph State Dump ===");
        let mut active_nodes = Vec::new();
        for i in 0..self.entities.len() {
            let id = ClassId(i);
            if self.get_rep(id) == id { // 代表元のみを抽出
                active_nodes.push(id);
            }
        }

        println!("Active Equivalence Classes: {}", active_nodes.len());

        // 型ごとにソートして出力すると見やすい
        active_nodes.sort_by_key(|&id| format!("{:?}", self.entities[id.0].entity_type));

        for &id in &active_nodes {
            let e = &self.entities[id.0];
            println!("🔹 [{:?}] {}", e.entity_type, e.name);

            for comp in &e.components {
                // 定義（どうやって作られたか）
                for def in &comp.definitions {
                    if !matches!(def, Definition::FreePoint | Definition::GivenPoint) {
                        println!("    └─ Def: {}", self.format_definition(def));
                    }
                }
                // 所属・接続関係 (Incidence)
                if !comp.subobjects.is_empty() {
                    let mut subs: Vec<String> = comp.subobjects.iter()
                        .map(|s| self.entities[self.get_rep(*s).0].name.clone())
                        .collect();
                    subs.sort();
                    subs.dedup();
                    println!("    └─ Contains/On: {:?}", subs);
                }
            }
        }
        println!("=============================\n");
    }
}

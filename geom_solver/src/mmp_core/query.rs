//! 🌟 EGraphの状態を問い合わせるだけの読み取り専用ユーティリティ
//! (接続関係の判定、共通の円の探索、デバッグ用の状態ダンプなど)。

use super::{ClassId, Definition, EntityType, EGraph};

impl EGraph {
    /// 🌟 現在アクティブな(=自身が代表元である)エンティティの数。マージが
    /// 実際にいくつ起きたかの粗い指標として使う(MCTSの報酬評価、予想候補の
    /// 価値推定(eval.rs::estimate_conjecture_value)などで共有する)。
    pub fn count_active_classes(&self) -> usize {
        (0..self.entities.len()).filter(|&i| self.get_rep(ClassId(i)).0 == i).count()
    }

    /// 🌟 EntityType::Angle撤廃(mmp_core/mod.rs::EntityTypeのドキュメント参照)
    /// により、「この値が有向角(AnglePair)か、それとも別の(長さ・積・複比等の)
    /// Scalarか」はもう型では区別できない。代わりに、このIDが吸収してきた
    /// 全ての定義(merge_entitiesが両側の定義集合を合流させて蓄積する)の
    /// どれかがAnglePairかどうかで判定する――単にoriginal_definitionだけを
    /// 見ると、AnglePairで作られた実体が後からAng90/Ang0(GivenPoint定義)の
    /// ような非AnglePair起源の実体に吸収された場合を見逃す。
    /// logic_core.rsの自己束縛候補の絞り込み(角度追跡系定理の
    /// Identical(Ang1,Ang2)シードが、無関係な長さ・複比のScalarまで
    /// 候補に含めてしまわないようにする)で使う。
    pub fn is_angle_value(&self, id: ClassId) -> bool {
        let rep = self.get_rep(id);
        self.entities[rep.0].components.first()
            .is_some_and(|c| c.definitions.iter().any(|d| matches!(d, Definition::AnglePair(_, _))))
    }

    /// 🌟 is_angle_valueと同じ発想: このScalarがCrossRatioOfLines(線束の複比)
    /// 由来かどうかを、吸収してきた定義のどれかがCrossRatioOfLinesかどうかで
    /// 判定する。「シュタイナーの定理の逆」のIdentical(CR_P1,CR_P5)自己束縛
    /// (logic_core.rs::match_identical_fact)が、長さ・積・点の複比まで
    /// 無差別に含む自己束縛候補プールに埋もれて無関係な値ばかり試すのを防ぐ
    /// ために使う(miquel_quadrilateralで実際に観測した、この自己束縛が
    /// dfs_capを繰り返し使い切る性能問題への対応)。
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

    /// 🌟 points に含まれる全ての点が乗っている共通の円が存在するかを判定する。
    /// Concyclicを専用Factで持たなくなったので、目標判定などでこれを使う。
    /// 円の数は通常ごく少数なので、全円を舐めても軽い。
    /// 🌟 EntityType::Circle撤廃(mmp_core/mod.rs::EntityTypeのドキュメント
    /// 参照)により、円は今やEntityType::Conicの特殊な場合(I,Jを通る)として
    /// しか区別できない。この関数は「共円(Concyclic)」という円に固有の
    /// 目標を判定するためのものなので、単にConic型であるだけでなく、
    /// I,Jの両方に接続している(=本物の円である)ことも確認する――そうしないと
    /// 円ではない一般の二次曲線(ConicThrough5Points)まで「共円」と誤判定
    /// してしまう。
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
        }
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

//! 🌟 複数のエンティティ生成を伴う補助構成。現状は調和共役点の
//! 完全四辺形作図のみ(円錐曲線を一切使わず、直線と交点だけで作る)。

use std::collections::HashSet;
use super::{ClassId, Definition, EntityType, EGraph, Justification};

impl EGraph {
    /// 🌟 与えられた図形群すべてが乗っている共通の直線を(あれば)1つ返す。
    /// 調和共役点の抽象エンティティを、実際にA,B,Cが乗っている直線に
    /// リンクするために使う(見つからなくても構成自体は成立するので失敗は許容)。
    pub fn find_common_line(&self, ids: &[ClassId]) -> Option<ClassId> {
        if ids.is_empty() { return None; }
        let mut candidates: Option<HashSet<ClassId>> = None;
        for &id in ids {
            let rep = self.get_rep(id);
            let lines: HashSet<ClassId> = self.entities[rep.0].components.first()
                .map(|c| c.subobjects.iter().map(|&s| self.get_rep(s))
                    .filter(|&s| self.entities[s.0].entity_type == EntityType::Line)
                    .collect())
                .unwrap_or_default();
            candidates = Some(match candidates {
                None => lines,
                Some(prev) => prev.intersection(&lines).copied().collect(),
            });
        }
        candidates.and_then(|s| s.into_iter().next())
    }

    /// 🌟 調和共役点の具体的な作図(完全四辺形)。円錐曲線を一切使わず、
    /// 直線と交点だけで A,B を固定点とする対合による C の像 D を作る:
    ///   1. 直線ABC上にない補助点 P を取る
    ///   2. 直線PC上に(P,Cと異なる)補助点 Q を取る
    ///   3. R = 直線AQ と 直線PB の交点
    ///   4. S = 直線BQ と 直線PA の交点
    ///   5. D = 直線RS と 直線ABC の交点
    /// (これは古典的な複比調和点の作図で、補助点P,Qの取り方に依らずDは一意に
    /// 定まることが射影幾何の定理として知られている。本エンジンはこの独立性を
    /// 内部で証明するのではなく、Midpoint/Circumcircle等と同様に既知の結果として
    /// 前提にし、実際に1回具体的に作図した点を抽象的な
    /// Definition::HarmonicConjugateOf(A,B,C) に紐付けることで、以後は
    /// 合同閉包だけで再利用できるようにする)。
    ///
    /// あわせて、対合性 H(A,B,D)=C と 交叉比のペア交換対称性
    /// (A,B;C,D)=-1 ⟹ (C,D;A,B)=-1 つまり H(C,D,A)=B も構造的に登録する。
    /// PerpDirectionOfと同じ理由(無限再帰の回避)で、HarmonicConjugateOf自体は
    /// apply_trivial_relationsの汎用ディスパッチには載せず、この関数だけが
    /// 有限個(3つ)の追加エンティティを明示的に作る。
    pub fn construct_harmonic_conjugate(&mut self, a: ClassId, b: ClassId, c: ClassId) -> ClassId {
        let a = self.get_rep(a);
        let b = self.get_rep(b);
        let c = self.get_rep(c);
        let name = |id: ClassId, eg: &Self| eg.entities[eg.get_rep(id).0].name.clone();

        // 直線ABC: A,Bを通る直線を(既存なら再利用して)確定させる。呼び出し側は
        // Cがこの直線上にあることを前提として呼ぶこと(既に共線でなければ
        // 「調和共役点」という概念自体が意味を持たないので、これは前提条件)。
        let line_abc = self.create_entity(format!("Line_{}_{}_(Aux)", name(a, self), name(b, self)), Definition::new_line(a, b), EntityType::Line);

        // 1. 補助点 P (直線ABC上にない自由点)
        let p = self.create_entity(format!("P_Harm_{}_{}_{}_(Aux)", name(a, self), name(b, self), name(c, self)), Definition::FreePoint, EntityType::Point);
        // 2. 補助点 Q (直線PC上の、P,Cと異なる自由点)
        // 🐛 FIX: 以前はQをFreePointとして作り、link_logical_incidenceで
        // 直線PC上にあることを構造的にだけ主張していた。これだとQの座標は
        // 完全に無拘束のままなので、健全性チェック(numeric_plausibility_check)が
        // 「Qは本当に直線PC上にあるか」を検証できず、Qに依存する数値評価を
        // 一律に信用しない扱いにせざるを得なくなってしまう。P,Cの中点を
        // 採用すれば、Q,Cとは異なる(P≠Cである限り)直線PC上の点という要件を
        // 満たしつつ、実際に座標から導出可能になる。
        // (Midpointのapply_trivial_relationsが、PC間の直線を自動的に生成/再利用して
        // Qをその直線上にリンクしてくれるので、ここで直線を明示的に作る必要はない)
        let q = self.create_entity(format!("Q_Harm_{}_{}_{}_(Aux)", name(a, self), name(b, self), name(c, self)), Definition::Midpoint(p, c), EntityType::Point);

        // 3. R = AQ ∩ PB
        let line_aq = self.create_entity(format!("Line_{}_{}_(Aux)", name(a, self), name(q, self)), Definition::new_line(a, q), EntityType::Line);
        let line_pb = self.create_entity(format!("Line_{}_{}_(Aux)", name(p, self), name(b, self)), Definition::new_line(p, b), EntityType::Line);
        let r = self.create_entity(format!("R_Harm_{}_{}_{}_(Aux)", name(a, self), name(b, self), name(c, self)), Definition::Intersection(line_aq, line_pb), EntityType::Point);

        // 4. S = BQ ∩ PA
        let line_bq = self.create_entity(format!("Line_{}_{}_(Aux)", name(b, self), name(q, self)), Definition::new_line(b, q), EntityType::Line);
        let line_pa = self.create_entity(format!("Line_{}_{}_(Aux)", name(p, self), name(a, self)), Definition::new_line(p, a), EntityType::Line);
        let s = self.create_entity(format!("S_Harm_{}_{}_{}_(Aux)", name(a, self), name(b, self), name(c, self)), Definition::Intersection(line_bq, line_pa), EntityType::Point);

        // 5. D = RS ∩ ABC
        let line_rs = self.create_entity(format!("Line_{}_{}_(Aux)", name(r, self), name(s, self)), Definition::new_line(r, s), EntityType::Line);
        let d_concrete = self.create_entity(format!("D_Harm_{}_{}_{}_(Aux)", name(a, self), name(b, self), name(c, self)), Definition::Intersection(line_rs, line_abc), EntityType::Point);

        self.apply_congruence_closure();

        // 抽象的な調和共役点エンティティを作り、具体的な作図結果に結びつける
        let hc_def = self.normalize_definition(&Definition::HarmonicConjugateOf(a, b, c));
        let d_abstract = self.create_entity(format!("Harm_{}_{}_{}_(Auto)", name(a, self), name(b, self), name(c, self)), hc_def, EntityType::Point);
        self.merge_entities_justified(d_abstract, d_concrete, Justification::Trivial {
            reason: "調和共役点の完全四辺形作図により、抽象的な調和共役点と実際の交点が一致".to_string(),
        });
        let d = self.get_rep(d_abstract);
        self.link_logical_incidence(d, line_abc);

        // 対合性: H(A,B,D) ≡ C
        let inv_def = self.normalize_definition(&Definition::HarmonicConjugateOf(a, b, d));
        let inv_id = self.create_entity(format!("Harm_{}_{}_{}_(Auto)", name(a, self), name(b, self), name(d, self)), inv_def, EntityType::Point);
        self.merge_entities_justified(inv_id, c, Justification::Trivial {
            reason: "調和共役点の対合性: H(A,B,H(A,B,C)) は C に一致する".to_string(),
        });

        // 交叉比のペア交換対称性: (A,B;C,D)=-1 ⟹ (C,D;A,B)=-1 つまり H(C,D,A) ≡ B
        let c_after = self.get_rep(c);
        let d_after = self.get_rep(d);
        let swap_def = self.normalize_definition(&Definition::HarmonicConjugateOf(c_after, d_after, a));
        let swap_id = self.create_entity(format!("Harm_{}_{}_{}_(Auto)", name(c_after, self), name(d_after, self), name(a, self)), swap_def, EntityType::Point);
        self.merge_entities_justified(swap_id, b, Justification::Trivial {
            reason: "交叉比のペア交換対称性: (A,B;C,D)=-1 ⟹ (C,D;A,B)=-1".to_string(),
        });

        self.apply_congruence_closure();
        self.get_rep(d)
    }
}

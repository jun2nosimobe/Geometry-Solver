//! 🌟 探索の中で目標を Wu の方法(mmp_core/symbolic.rs)で示す。
//! 最初に、目標の次数 d(共通の写像の次数、natural_degree.rs)から決めた上限 1000·2^(d/2) 回の掛け算(#102 の実測で、示せた
//! 問題の掛け算の回数の中央値がおよそこれ。予算の 1/16 まで)で試す。その後は、Wu の方法が使った掛け算が探索の仕事量を
//! 超えないように(Wu の方法と探索で予算をおおよそ半分ずつ)、手詰まりのときと、探索が次の上限の分だけ進んだときに試す。
//! 上限は試すたびに2倍。上限に達して諦めた試みで値の出来た実体は覚えておき、次はその続きから計算する。探索が打つ手を使い
//! 果たして止まるときだけ、残りの予算の全部で試す。掛け算 160 回を仕事量 1 と数える(約 2×10⁷ 回/秒、dfs_match 1回 ≈ 8.2µs)。
//! 示せたら目標を「代数計算(Wu の方法)」で閉じる。前提は、目標の作図の祖先で前提の曲線に乗せた自由点の接続(Wu の方法が使う
//! のは作図の定義と、その接続だけ。作図の定義は前提に書かない)。

use rustc_hash::FxHashSet;

use crate::mmp_core::{ClassId, Definition, EntityType, Justification, WuMemo};

use super::BlackboardEngine;

pub const WU_THEOREM: &str = "代数計算(Wu の方法)";
pub const WU_MULTS_PER_WORK: u64 = 160;
const WU_MAX_TERMS: usize = 1_000_000;

/// いつ試すか(上限の決め方)。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WuTry {
    /// 探索の前: 最初の上限。
    Start,
    /// 手詰まり・探索が進んだとき: 次の上限(探索の仕事量から Wu の方法が使った分を引いたものが、それに届いたときだけ)。
    Credit,
    /// 探索が尽きたとき: 残りの予算の全部。
    Last,
}

/// Wu の方法の試し方と結果。
#[derive(Debug, Clone)]
pub struct WuSchedule {
    /// 最初の上限と、次に試すときの上限(掛け算の回数)。
    pub first: u64,
    pub next: u64,
    pub tries: u32,
    pub mults: u64,
    pub proved: bool,
    /// 上限を上げても示せないと分かった理由(記号計算に無い作図・作図から従わない前提など)。分かったら以後は試さない。
    pub stopped: Option<String>,
    /// 前の試みの途中の値。
    pub(crate) memo: WuMemo,
}

impl WuSchedule {
    /// budget: 探索の仕事量の予算。
    pub fn new(goal_degree: Option<u32>, budget: u64) -> Self {
        let d = goal_degree.unwrap_or(8).min(60);
        let first = (1000u64 << (d / 2)).min(budget.saturating_mul(WU_MULTS_PER_WORK) / 16).max(1);
        WuSchedule { first, next: first, tries: 0, mults: 0, proved: false, stopped: None, memo: WuMemo::default() }
    }
}

impl BlackboardEngine {
    /// Wu の方法がこれから使ってよい掛け算の回数: 探索がそれまでに使った仕事量から、Wu の方法が使った分を引いたもの。
    fn wu_credit(&self, w: &WuSchedule) -> u64 {
        let searched = self.prover.work_done().saturating_sub(w.mults / WU_MULTS_PER_WORK);
        searched.saturating_mul(WU_MULTS_PER_WORK).saturating_sub(w.mults)
    }

    /// 探索が Wu の方法の次の上限の分だけ進んだか(手詰まりでなくても試す)。
    pub fn wu_due(&self) -> bool {
        self.wu.as_ref().is_some_and(|w| !w.proved && w.stopped.is_none() && self.wu_credit(w) >= w.next)
    }

    /// 目標を Wu の方法で示せたら、目標を閉じて true。
    pub fn try_wu(&mut self, target: &(String, Vec<ClassId>), when: WuTry) -> bool {
        let Some(w) = self.wu.as_ref().filter(|w| !w.proved && w.stopped.is_none()) else { return false };
        let remaining = self.work_limit.saturating_sub(self.prover.work_done()).saturating_mul(WU_MULTS_PER_WORK);
        let cap = match when {
            WuTry::Start => w.first,
            WuTry::Credit => w.next.min(self.wu_credit(w)),
            WuTry::Last => remaining,
        }.min(remaining);
        // 次の上限の分がまだ溜まっていなければ試さない(一番重い1つの計算が上限に収まるまで、小さい試みは同じ所で止まるだけ)。
        if cap == 0 || (when == WuTry::Credit && cap < w.next.min(remaining)) { return false; }
        let (kind, args) = target;
        let mut memo = std::mem::take(&mut self.wu.as_mut().expect("上で確かめた").memo);
        let (r, _, _, mults, fail) = self.prover.egraph.symbolic_prove_with(kind, args, WU_MAX_TERMS, cap, &mut memo);
        let used = mults.min(cap);
        // AR の行演算と同じ、定理の照合以外の仕事の数え口。
        self.prover.egraph.spiral_prop_work += used / WU_MULTS_PER_WORK;
        let w = self.wu.as_mut().expect("上で確かめた");
        w.memo = memo;
        w.tries += 1;
        w.mults += used;
        w.next = w.next.max(cap.saturating_mul(2));
        match r {
            Some(true) => {}
            Some(false) => { w.stopped = Some("目標の式が恒等的に 0 でない".into()); return false; }
            None => {
                // 掛け算の上限に達しただけなら、上限を上げて試し直す。
                if mults <= cap { w.stopped = Some(fail.unwrap_or_default()); }
                return false;
            }
        }
        w.proved = true;
        w.memo = WuMemo::default();
        let tries = w.tries;
        if !self.close_by_wu(kind, args) { return false; }
        println!("  🧮 [代数計算] Wu の方法で目標を示しました({} 回目、掛け算 {} 回)", tries, used);
        true
    }

    /// Wu の方法で示した事実(kind, args)を e-graph に入れる: 等しい → 併合、接続 → 接続、共円 → 最初の3点を通る円(無ければ作る)に
    /// 残りの点を接続。根拠は「代数計算(Wu の方法)」で、前提は事実の作図の祖先にあって前提の曲線に乗せた自由点の接続。
    pub(crate) fn close_by_wu(&mut self, kind: &str, args: &[ClassId]) -> bool {
        let eg = &mut self.prover.egraph;
        let incidences = eg.premise_incidences.clone().unwrap_or_default();
        let mut seen: FxHashSet<usize> = FxHashSet::default();
        let mut stack: Vec<ClassId> = args.to_vec();
        while let Some(x) = stack.pop() {
            if !seen.insert(x.0) { continue; }
            stack.extend(eg.entities[x.0].original_definition.get_parents());
            stack.extend(incidences.iter().filter(|&&(p, _)| eg.frozen_free_key(p) == eg.frozen_free_key(x)).map(|&(_, c)| c));
        }
        let premises: Vec<(String, Vec<ClassId>)> = incidences.iter().filter(|&&(p, _)| seen.contains(&p.0))
            .map(|&(p, c)| ("Connected".to_string(), vec![p, c])).collect();
        let j = Justification::Theorem { name: WU_THEOREM.to_string(), premises };
        match (kind, args) {
            ("Identical", [a, b]) => { eg.merge_entities_justified(*a, *b, j); }
            ("Connected", [a, b]) => { let (p, c) = eg.point_and_curve(*a, *b); eg.link_logical_incidence_justified(c, p, j); }
            ("Concyclic", [a, b, c, rest @ ..]) => {
                let reps: Vec<ClassId> = [*a, *b, *c].iter().map(|&x| eg.get_rep(x)).collect();
                let circle = match eg.find_shared_circle(&reps) {
                    Some(o) => o,
                    None => {
                        let name = format!("Circle_{}_{}_{}", eg.entities[a.0].name, eg.entities[b.0].name, eg.entities[c.0].name);
                        eg.create_entity(name, Definition::Circumcircle(*a, *b, *c), EntityType::Conic)
                    }
                };
                for &p in rest { eg.link_logical_incidence_justified(circle, p, j.clone()); }
            }
            _ => return false,
        }
        eg.apply_congruence_closure();
        true
    }
}

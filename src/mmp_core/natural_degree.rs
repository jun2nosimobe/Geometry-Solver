//! 🌟 次数の代数幾何的な定式化。
//!
//! 配置空間 C: 自由点ごとに、前提の曲線が無ければ P²(2つの媒介変数)、前提の直線・円の上なら P¹(曲線の媒介変数)、その積。
//! Pic(C) は塊(自由点)ごとの超平面類で生成される Z^k。作図した実体(点・直線・円・比のスカラー)は有理写像 φ: C ⇢ P^n で、
//! その次数は φ*O(1) の移動部分(成分の公約式で割ったもの)の類 ∈ Z^k ― 次数のベクトル。成分 d_j は、自由点 j だけを一般の
//! 直線の上で動かし(他の自由点は一般の位置に固定)、成分の公約式で割った t の次数(動点法でその点を動かしたときの次数)。
//! スカラーの次数は、各塊の超平面類の和という自然な偏極についての次数 Σ_j d_j。
//! 事実(定理)は2つの作図が同じ写像になるという恒等式で、その次数は共通の写像の次数(fact_census.rs)。
//! どの定義(作図)から計算しても同じ写像なので、同値類のどの実体で測っても同じ値になる(覚えは実体ごとでよい)。
//! 測り方は記号計算(symbolic.rs の塊モード)で、乱数の点での値の比較やランク判定は使わない。

use rustc_hash::FxHashMap;

use super::symbolic::{cross_ratio_reduced, join_reduced, line_degree, SymMemo, Symbolic, V};
use super::{ClassId, Definition, EGraph};

/// 次数の覚え(EGraph の中に持つ)。
#[derive(Clone, Default)]
pub(crate) struct NaturalDegrees {
    /// 塊: 元の定義が自由点の実体(番号の順)。
    blocks: Vec<ClassId>,
    /// 実体を数え終えた位置(新しく自由点ができたら作り直す)。
    scanned: usize,
    /// 塊ごとの記号計算の覚え。
    memos: Vec<SymMemo>,
    /// 実体ごとの次数のベクトル。
    results: FxHashMap<usize, Option<Vec<u32>>>,
}

impl EGraph {
    fn refresh_degree_blocks(&self, nd: &mut NaturalDegrees) {
        if nd.scanned == self.entities.len() && nd.scanned > 0 { return; }
        let new_free = nd.scanned == 0 || self.entities[nd.scanned..].iter().any(|e| matches!(e.original_definition, Definition::FreePoint));
        if new_free {
            nd.blocks = (0..self.entities.len()).map(ClassId).filter(|&i| matches!(self.entities[i.0].original_definition, Definition::FreePoint)).collect();
            nd.memos = vec![SymMemo::default(); nd.blocks.len()];
            nd.results.clear();
        }
        nd.scanned = self.entities.len();
    }

    /// 次数のベクトルの並び(元の定義が自由点の実体)。
    pub(crate) fn degree_blocks(&self) -> Vec<ClassId> {
        let mut nd = self.natural_degrees.borrow_mut();
        self.refresh_degree_blocks(&mut nd);
        nd.blocks.clone()
    }

    /// f(塊モードの記号計算で値を作る)の次数のベクトル。どこかの塊で値を作れなければ None。
    pub(crate) fn multidegree_with(&self, f: &dyn Fn(&mut Symbolic) -> Option<V>) -> Option<Vec<u32>> {
        let mut nd = self.natural_degrees.borrow_mut();
        self.refresh_degree_blocks(&mut nd);
        let mut out = Vec::with_capacity(nd.blocks.len());
        for j in 0..nd.blocks.len() {
            let memo = std::mem::take(&mut nd.memos[j]);
            let mut s = Symbolic::on_block(self, Some(nd.blocks[j]), memo);
            let r = f(&mut s);
            nd.memos[j] = s.into_memo();
            out.push(line_degree(&r?));
        }
        Some(out)
    }

    /// 実体の次数のベクトル。
    pub fn multidegree(&self, id: ClassId) -> Option<Vec<u32>> {
        {
            let mut nd = self.natural_degrees.borrow_mut();
            self.refresh_degree_blocks(&mut nd);
            if let Some(r) = nd.results.get(&id.0) { return r.clone(); }
        }
        let r = self.multidegree_with(&|s| s.value(id));
        self.natural_degrees.borrow_mut().results.insert(id.0, r.clone());
        r
    }

    /// 実体の次数(各塊の超平面類の和についての次数、次数のベクトルの成分の和)。
    pub fn natural_degree(&self, id: ClassId) -> Option<usize> {
        self.multidegree(self.get_rep(id)).map(|v| v.iter().map(|&d| d as usize).sum())
    }

    /// 2つの直線の交点(まだ作っていない候補)の次数のベクトル。
    pub fn intersection_multidegree(&self, l1: ClassId, l2: ClassId) -> Option<Vec<u32>> {
        self.multidegree_with(&|s| Some(join_reduced(&s.value(l1)?, &s.value(l2)?)))
    }

    /// 複比(4点、または共点の4直線)の次数のベクトル。
    pub fn cross_ratio_multidegree(&self, a: ClassId, b: ClassId, c: ClassId, d: ClassId) -> Option<Vec<u32>> {
        self.multidegree_with(&|s| Some(cross_ratio_reduced(&s.value(a)?, &s.value(b)?, &s.value(c)?, &s.value(d)?)))
    }

    /// 2点 A, B と、それを通る直線の次数(成分の和)。直線の次数が deg A + deg B より小さい組は、2点を通る直線の写像に
    /// 基点があり(A, B が他の点と常に一直線上にあるなど)、隠れた事実が効いている兆候(「相性が良い」)。
    pub fn measure_line_affinity(&self, a: ClassId, b: ClassId) -> Option<(usize, usize, usize)> {
        let sum = |v: Vec<u32>| v.iter().map(|&d| d as usize).sum::<usize>();
        let line = self.multidegree_with(&|s| Some(join_reduced(&s.value(a)?, &s.value(b)?)))?;
        Some((self.natural_degree(a)?, self.natural_degree(b)?, sum(line)))
    }

}

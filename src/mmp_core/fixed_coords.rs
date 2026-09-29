//! 🌟 固定座標の数値モデル。探索の前に自由点の座標を前提どおりに一度だけ置き、各実体の値を**その実体の元の定義**から
//! 一度だけ計算して覚える。
//!
//! 同値類の定義で評価する従来の経路(eval.rs の numeric_samples)は、構造が変わるたびに(実体の生成・マージ・接続の
//! たびに)座標を置き直して全てを再評価していたうえ、値がマージに依存した: 同値類に誤った定義や循環する定義が
//! 入ると、それ以後の検算がその値と比べてしまう。ここでは値が実体の元の定義だけで決まるので、マージが何をしても
//! 変わらず、一度計算すれば捨てなくてよい。マージの検算は2つの代表元の値の比較、接続の検算は代入1回になる。
//!
//! 使うのは solve の経路で、前提が数値的に成り立つ問題だけ(fix_coordinates)。使えないときは従来の経路に落ちる。

use super::eval::modint_construct as modint_construct_pub;
use super::{ClassId, Definition, EGraph, EntityType};
use crate::mmp_math::ModInt;

/// 標本の数。検算は各標本で一致を確かめる。
const SAMPLES: usize = 2;

#[derive(Clone, Default)]
pub(crate) struct FixedCoords {
    /// [標本][実体] の値。外側の None はまだ計算していない、内側の None は値が定まらない(退化した作図)。
    values: [Vec<Option<Option<Vec<ModInt>>>>; SAMPLES],
}

impl EGraph {
    /// 探索の前に呼ぶ(freeze_premise_incidences の後)。自由点を前提どおりに置けなければ false で、従来の経路のまま。
    pub fn fix_coordinates(&mut self) -> bool {
        let mut fixed = FixedCoords::default();
        let points = self.all_free_points();
        for k in 0..SAMPLES {
            let mut vars = rustc_hash::FxHashMap::default();
            if !self.assign_free_point_coords(&points, &mut vars) { return false; }
            // 自由点・定数の値はこの時点の名前で引くので、名前がマージで変わる前にここで全て確定させる。
            let slot = &mut fixed.values[k];
            slot.resize(self.entities.len(), None);
            for i in 0..self.entities.len() {
                if let Some(v) = self.constant_or_free_value(ClassId(i), &vars) { slot[i] = Some(Some(v)); }
            }
        }
        *self.fixed_coords.borrow_mut() = Some(fixed);
        // 残りの実体(作図されたもの)は元の定義から計算する。ここで全部埋めておく(以後は新しい実体の分だけ)。
        for k in 0..SAMPLES {
            for i in 0..self.entities.len() { let _ = self.entity_value(ClassId(i), k); }
        }
        true
    }

    pub(crate) fn fixed_active(&self) -> bool { self.fixed_coords.borrow().is_some() }

    fn constant_or_free_value(&self, id: ClassId, vars: &rustc_hash::FxHashMap<String, ModInt>) -> Option<Vec<ModInt>> {
        // 有向角の定数は複比 (I,J;D1,D2) の値(直角は -1、0度は 1)。
        if id == self.ang90 { return Some(vec![ModInt::new(-1), ModInt::new(1), ModInt::new(1)]); }
        if id == self.ang0 { return Some(vec![ModInt::new(1), ModInt::new(1), ModInt::new(1)]); }
        match &self.entities[id.0].original_definition {
            Definition::FreePoint | Definition::GivenPoint => {
                // 置いた座標は、置いた時点の代表元の名前で入っている。
                let rep = self.get_rep(id);
                let name = &self.entities[rep.0].name;
                match (vars.get(&format!("{}_x", name)), vars.get(&format!("{}_y", name))) {
                    (Some(&x), Some(&y)) => Some(vec![x, y, ModInt::new(1)]),
                    // 無限遠直線などの GivenPoint は (0,0,1)。
                    _ if matches!(self.entities[id.0].original_definition, Definition::GivenPoint) => Some(vec![ModInt::new(0), ModInt::new(0), ModInt::new(1)]),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// 実体 id の(標本 k での)値。元の定義と、その親の実体の値だけで決まる。値が定まらなければ None。
    pub(crate) fn entity_value(&self, id: ClassId, k: usize) -> Option<Vec<ModInt>> {
        {
            let mut fc = self.fixed_coords.borrow_mut();
            let fc = fc.as_mut()?;
            let slot = &mut fc.values[k];
            if slot.len() < self.entities.len() { slot.resize(self.entities.len(), None); }
            if let Some(v) = &slot[id.0] { return v.clone(); }
        }
        let def = self.entities[id.0].original_definition.clone();
        let value = match def {
            // 固定した後に作られた自由点(solve の経路では作らない)は値を持たない。
            Definition::FreePoint | Definition::GivenPoint => None,
            _ => modint_construct_pub(self, &def, &mut |q| self.entity_value(q, k)),
        };
        if let Some(fc) = self.fixed_coords.borrow_mut().as_mut() {
            fc.values[k][id.0] = Some(value.clone());
        }
        value
    }

    /// 同値類の値: 代表元の元の定義の値。それが定まらないときだけ、同値類の他の定義を親の実体の値で作って使う。
    pub(crate) fn class_value(&self, id: ClassId, k: usize) -> Option<Vec<ModInt>> {
        let rep = self.get_rep(id);
        if let Some(v) = self.entity_value(rep, k) { return Some(v); }
        let defs = self.entities[rep.0].components.first().map(|c| c.definitions.clone()).unwrap_or_default();
        defs.iter().find_map(|d| match d {
            Definition::FreePoint | Definition::GivenPoint => None,
            _ => modint_construct_pub(self, d, &mut |q| self.entity_value(q, k)),
        })
    }

    /// まだ図に無い作図 def の(標本 k での)値。親は同値類の値で評価する。補助作図の候補を図に足さずに試作するため。
    pub(crate) fn fixed_def_value(&self, def: &Definition, k: usize) -> Option<Vec<ModInt>> {
        if !self.fixed_active() { return None; }
        modint_construct_pub(self, def, &mut |q| self.class_value(q, k))
    }

    /// 標本の数(補助作図の試作が全標本で確かめるため)。
    pub(crate) fn fixed_samples(&self) -> usize { SAMPLES }

    /// 固定座標での一致の検算。固定座標を使っていなければ None(呼び出し側は従来の経路へ)。
    pub(crate) fn fixed_equal(&self, a: ClassId, b: ClassId) -> Option<Option<bool>> {
        if !self.fixed_active() { return None; }
        for k in 0..SAMPLES {
            let (Some(va), Some(vb)) = (self.class_value(a, k), self.class_value(b, k)) else { return Some(None) };
            if !Self::numeric_values_proportional(&va, &vb) { return Some(Some(false)); }
        }
        Some(Some(true))
    }

    /// 固定座標での接続の検算(point が curve に乗っているか)。
    pub(crate) fn fixed_incidence(&self, point: ClassId, curve: ClassId, curve_type: EntityType) -> Option<Option<bool>> {
        if !self.fixed_active() { return None; }
        for k in 0..SAMPLES {
            let (Some(p), Some(c)) = (self.class_value(point, k), self.class_value(curve, k)) else { return Some(None) };
            if !point_lies_on(&p, &c, curve_type) { return Some(Some(false)); }
        }
        Some(Some(true))
    }

    /// 固定座標での共線の判定。
    pub(crate) fn fixed_collinear(&self, pts: &[ClassId]) -> Option<Option<bool>> {
        if !self.fixed_active() { return None; }
        if pts.len() < 3 { return Some(Some(true)); }
        for k in 0..SAMPLES {
            let Some(vals) = pts.iter().map(|&p| self.class_value(p, k)).collect::<Option<Vec<_>>>() else { return Some(None) };
            if vals.iter().any(|v| v.len() != 3) { return Some(None); }
            let (a, b) = (&vals[0], &vals[1]);
            for c in &vals[2..] {
                let det = a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0]) + a[2] * (b[0] * c[1] - b[1] * c[0]);
                if det != ModInt::new(0) { return Some(Some(false)); }
            }
        }
        Some(Some(true))
    }

    /// 固定座標で、def を作ると値が定まらないか(親は全て定まるのに def だけが定まらない)。
    pub(crate) fn fixed_degenerate(&self, def: &Definition) -> Option<bool> {
        if !self.fixed_active() { return None; }
        let mut parents_ok = true;
        let value = modint_construct_pub(self, def, &mut |q| {
            let v = self.class_value(q, 0);
            if v.is_none() { parents_ok = false; }
            v
        });
        Some(parents_ok && value.is_none())
    }
}

pub(crate) fn point_lies_on(point: &[ModInt], v: &[ModInt], curve_type: EntityType) -> bool {
    if point.len() < 3 { return false; }
    let (x, y, z) = (point[0], point[1], point[2]);
    match curve_type {
        EntityType::Line if v.len() >= 3 => (v[0] * x + v[1] * y + v[2] * z).0 == 0,
        EntityType::Conic if v.len() >= 6 =>
            (v[0] * x * x + v[1] * x * y + v[2] * y * y + v[3] * x * z + v[4] * y * z + v[5] * z * z).0 == 0,
        _ => false,
    }
}

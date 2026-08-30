use crate::mmp_math::{ModInt};

pub struct MMPTester {
    pub t_samples: Vec<ModInt>,
}

impl MMPTester {
    pub fn new() -> Self {
        // ModIntのMOD (998244353) に基づくサンプルプールを生成
        let t_samples = (1..=400).map(|i| ModInt::new(i * 1234567)).collect();
        Self { t_samples }
    }

    /// 2つのエンティティの数値的一致を有限体上で検証 (Schwartz-Zippel Lemma)
    pub fn verify_numerical_match(&self, v1: &[ModInt], v2: &[ModInt]) -> bool {
        if v1.len() != v2.len() || v1.is_empty() { return false; }
        
        // 3次元配列（同次座標）の場合
        if v1.len() == 3 {
            let zero1 = v1[0] * v2[1] - v1[1] * v2[0];
            let zero2 = v1[1] * v2[2] - v1[2] * v2[1];
            let zero3 = v1[2] * v2[0] - v1[0] * v2[2];
            return zero1.0 == 0 && zero2.0 == 0 && zero3.0 == 0;
        }
        
        // 2次元または4次元（円係数など）の場合
        for (a, b) in v1.iter().zip(v2.iter()) {
            if (a.0 - b.0).abs() != 0 {
                // スケーリングファクターの考慮が必要な場合のフォールバック
                return false;
            }
        }
        true
    }

    /// 3点が共線（同一直線上）にあるかを外積の determinante で判定
    pub fn check_collinear(&self, p1: &[ModInt], p2: &[ModInt], p3: &[ModInt]) -> bool {
        if p1.len() < 3 || p2.len() < 3 || p3.len() < 3 { return false; }
        // x1(y2 - y3) + x2(y3 - y1) + x3(y1 - y2) == 0
        let area = p1[0] * (p2[1] - p3[1]) + p2[0] * (p3[1] - p1[1]) + p3[0] * (p1[1] - p2[1]);
        area.0 == 0
    }

    /// 4点が共円（同一円周上）にあるかを判定
    pub fn check_concyclic(&self, z: &[ModInt], p1: &[ModInt], p2: &[ModInt], p3: &[ModInt]) -> bool {
        // 3点から円を算出し、4点目がその円の方程式を満たすかチェック
        let circle = crate::mmp_calculators::calc_circumcircle(p1, p2, p3);
        if circle.len() != 4 || z.len() < 3 { return false; }
        
        let (u, v, w, s) = (circle[0], circle[1], circle[2], circle[3]);
        let (x, y, z_coord) = (z[0], z[1], z[2]);
        
        let val = u * (x * x + y * y) + v * x * z_coord + w * y * z_coord + s * z_coord * z_coord;
        val.0 == 0
    }

    pub fn verify_identical(&self, v1: &[ModInt], v2: &[ModInt]) -> bool {
        if v1.len() != v2.len() || v1.is_empty() { return false; }
        if v1.len() == 3 {
            let z1 = v1[0] * v2[1] - v1[1] * v2[0];
            let z2 = v1[1] * v2[2] - v1[2] * v2[1];
            let z3 = v1[2] * v2[0] - v1[0] * v2[2];
            return z1.0 == 0 && z2.0 == 0 && z3.0 == 0;
        }
        v1.iter().zip(v2.iter()).all(|(a, b)| a.0 == b.0)
    }

    pub fn is_canonical_angle_order(&self, d1: &[ModInt], d2: &[ModInt]) -> bool {
        if d1.len() < 2 || d2.len() < 2 { return true; }
        let cross = d1[0] * d2[1] - d1[1] * d2[0];
        if cross.0 == 0 {
            return d1[0].0 < d2[0].0;
        }
        cross.0 < (998244353 / 2)
    }
}
use std::ops::{Add, Sub, Mul, Div, AddAssign, SubAssign, MulAssign, DivAssign, Neg};

// Python版と同一の法(MOD)を設定
pub const PRIME: i64 = 998244353;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
pub struct ModInt(pub i64);

impl ModInt {
    pub fn new(mut v: i64) -> Self {
        v %= PRIME;
        if v < 0 { v += PRIME; }
        ModInt(v)
    }

    pub fn inv(self) -> Self {
        if self.0 == 0 { panic!("Zero division in ModInt"); }
        self.pow(PRIME - 2)
    }

    pub fn pow(self, mut exp: i64) -> Self {
        let mut res = 1;
        let mut base = self.0;
        while exp > 0 {
            if exp % 2 == 1 { res = (res * base) % PRIME; }
            base = (base * base) % PRIME;
            exp /= 2;
        }
        ModInt(res)
    }
}

// === 四則演算のトレイト実装 ===

impl Add for ModInt {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output { ModInt::new(self.0 + rhs.0) }
}

impl Sub for ModInt {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output { ModInt::new(self.0 - rhs.0) }
}

impl Mul for ModInt {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output { ModInt::new(self.0 * rhs.0) }
}

impl Div for ModInt {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output { self * rhs.inv() }
}

impl Neg for ModInt {
    type Output = Self;
    fn neg(self) -> Self::Output { ModInt::new(-self.0) }
}

// === 代入演算 (+=, -=, *=, /=) のトレイト実装 ===

impl AddAssign for ModInt {
    fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl SubAssign for ModInt {
    fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl MulAssign for ModInt {
    fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl DivAssign for ModInt {
    fn div_assign(&mut self, rhs: Self) { *self = *self / rhs; }
}

/// 🌟 汎用のn×n行列式(ガウス消去法、体上のpivotで割るので特異でなければ
/// 常に厳密に計算できる)。行列式の値(行入替の符号反転込み)を返す。
/// 二次曲線の5点復元(calc_conic_through_5_points)で、5×6行列の零空間を
/// 「6本の5×5小行列式」として求めるために使う(3D外積の6次元への一般化)。
/// 特異(=途中の列に非ゼロのpivotが見つからない)なら0を返す。
pub fn determinant_mod(matrix: &mut Vec<Vec<ModInt>>) -> ModInt {
    let n = matrix.len();
    if n == 0 || matrix.iter().any(|row| row.len() != n) { return ModInt::new(0); }

    let mut det = ModInt::new(1);
    for col in 0..n {
        let pivot_r = (col..n).find(|&r| matrix[r][col].0 != 0);
        let pivot_r = match pivot_r {
            Some(r) => r,
            None => return ModInt::new(0), // 特異行列
        };
        if pivot_r != col {
            matrix.swap(pivot_r, col);
            det = -det;
        }
        det *= matrix[col][col];
        let inv_val = matrix[col][col].inv();
        for r in (col + 1)..n {
            let factor = matrix[r][col] * inv_val;
            if factor.0 != 0 {
                for c in col..n {
                    let sub = factor * matrix[col][c];
                    matrix[r][c] -= sub;
                }
            }
        }
    }
    det
}

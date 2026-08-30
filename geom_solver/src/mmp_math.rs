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

// === 行列ランク計算 ===

pub fn matrix_rank_mod(matrix: &mut Vec<Vec<ModInt>>) -> usize {
    if matrix.is_empty() || matrix[0].is_empty() { return 0; }
    let rows = matrix.len();
    let cols = matrix[0].len();
    let mut rank = 0;

    for c in 0..cols {
        let mut pivot_r = None;
        for r in rank..rows {
            if matrix[r][c].0 != 0 {
                pivot_r = Some(r);
                break;
            }
        }

        if let Some(r) = pivot_r {
            if r != rank {
                matrix.swap(r, rank);
            }
            let inv_val = matrix[rank][c].inv();
            for j in c..cols {
                matrix[rank][j] *= inv_val;
            }
            for i in (rank + 1)..rows {
                let factor = matrix[i][c];
                if factor.0 != 0 {
                    for j in c..cols {
                        let sub_val = factor * matrix[rank][j];
                        matrix[i][j] -= sub_val;
                    }
                }
            }
            rank += 1;
        }
    }
    rank
}


pub fn get_numerical_degree(t_values: &[ModInt], x_values: &[ModInt], max_d: usize) -> usize {
    let n = t_values.len();
    for d in 0..=max_d {
        let cols = 2 * d + 2;
        if n < cols { continue; }
        
        let mut a = vec![vec![ModInt::new(0); cols]; n];
        for i in 0..n {
            let t = t_values[i];
            let x = x_values[i];
            for k in 0..=d {
                let t_k = t.pow(k as i64);
                a[i][k] = t_k;
                a[i][d + 1 + k] = -x * t_k;
            }
        }
        if matrix_rank_mod(&mut a) < cols {
            return d;
        }
    }
    max_d
}
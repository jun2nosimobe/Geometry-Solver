//! 🌟 図形を「退化」させたときの振る舞いから、関連の深い図形を見つけるための p 進の算術。
//! 2点A,Bに「mod p では一致するが mod p² 以上では一致しない」座標を与え(B=A+ε で ε→0 の極限を追うことの p 進版)、
//! 依存する全ての図形を mod p^4 で計算してから、同次座標に共通する p の最大べきで割って mod p を取ると、退化の極限で
//! その図形がどこへ収束するかが読める。独立に構成された2つの図形がこの極限で一致すれば、関係がある強い兆候。
//! numeric_plausibility_check(一般の配置で常に一致するか)とは別の軸で、「特定の退化の極限でだけ一致するか」を見る。
//! 基数は ModInt::PRIME(998244353)をそのまま使う。桁ごとに計算するので、桁同士の積(<P²<2^60)は i64/u128 に収まる。

use rand::Rng;

/// Z/P^PRECZ の基数(桁の底)。主系のModInt::PRIMEと同じ素数をそのまま使う
/// (オーバーフローの心配が無いなら別の素数を用意する必要は無い、という
/// ユーザー判断による)。
pub const P: i64 = crate::mmp_math::PRIME;

/// 追跡するP進桁数。A,Bの差がp^3のオーダーまで縮退しても(=3次まで
/// 消える量まで)まだ識別できるだけの精度を持たせてある。
pub const PREC: usize = 4;

/// Z/P^PRECZ の元。digits[0]が最下位桁(=通常のmod P剰余そのもの)、
/// digits[i]がP^iの係数。「基数Pの4桁ビッグ整数」を素直に実装したもの。
/// Hashは「同じ値の線分の長さをまとめて数える」等、値でバケツ分けするため。
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PInt {
    digits: [i64; PREC],
}

impl PInt {
    #[allow(dead_code)]   // 桁を直接与えて作る口。今は乱数生成と演算だけで足りている
    pub fn from_digits(digits: [i64; PREC]) -> Self {
        debug_assert!(digits.iter().all(|&d| (0..P).contains(&d)), "各桁は[0,P)の範囲であるべき: {:?}", digits);
        Self { digits }
    }

    pub fn zero() -> Self { Self { digits: [0; PREC] } }
    pub fn one() -> Self { let mut d = [0; PREC]; d[0] = 1; Self { digits: d } }
    fn two() -> Self { let mut d = [0; PREC]; d[0] = 2; Self { digits: d } }

    /// 通常の i64 を Z/P^PRECZ の元として正しく持ち込む(基数Pで桁分解する)。負の数は絶対値を桁分解してから0から引く
    /// (-1 は全桁が P-1 の元で、0桁目だけが P-1 の元とは別物)。
    pub fn from_i64_mod_p(v: i64) -> Self {
        let neg = v < 0;
        let mut mag = v.unsigned_abs();
        let mut d = [0i64; PREC];
        for slot in d.iter_mut() {
            *slot = (mag % P as u64) as i64;
            mag /= P as u64;
        }
        let out = Self { digits: d };
        if neg { Self::zero().sub(&out) } else { out }
    }

    /// 0桁目が非ゼロ(=P進付値0、単数)な乱数元。自由点の"一般的な"座標
    /// (退化させない側)に使う。
    pub fn random_unit(rng: &mut impl Rng) -> Self {
        let mut d = [0i64; PREC];
        d[0] = rng.gen_range(1..P);
        for i in 1..PREC { d[i] = rng.gen_range(0..P); }
        Self { digits: d }
    }

    /// 完全に一様な乱数元(0桁目もゼロになりうる)。退化の"ずれ"(δ)の
    /// ような、単数性を仮定したくない箇所に使う。
    pub fn random_any(rng: &mut impl Rng) -> Self {
        let mut d = [0i64; PREC];
        for i in 0..PREC { d[i] = rng.gen_range(0..P); }
        Self { digits: d }
    }

    /// P倍する(=桁を1つ上へシフト、最上位桁は精度PRECの外にあふれて消える)。
    /// 「A≡B (mod P)だがP^2では一致しない」ような退化配置を作るのに使う
    /// (B + P*random_any() のように)。
    pub fn scaled_by_p(&self) -> Self {
        let mut d = [0i64; PREC];
        for i in 1..PREC { d[i] = self.digits[i - 1]; }
        Self { digits: d }
    }

    /// P進付値(=最初の非ゼロ桁のインデックス)。全桁ゼロ(=この精度PRECの
    /// 範囲内では付値が判定できないほど深く消えている)ならNone。
    pub fn valuation(&self) -> Option<usize> {
        self.digits.iter().position(|&d| d != 0)
    }

    /// 付値vで割る(桁をv個下へシフトする)。呼び出し側はv <= 自身の
    /// 実際の付値(またはNone、その場合は結果全体が精度不足のゼロになる
    /// だけで安全)であることを保証すること。
    pub fn shift_down(&self, v: usize) -> Self {
        let mut d = [0i64; PREC];
        if v < PREC {
            for i in 0..(PREC - v) { d[i] = self.digits[i + v]; }
        }
        Self { digits: d }
    }

    /// 0桁目(=通常のmod P剰余)を取り出す。
    pub fn digit0(&self) -> i64 { self.digits[0] }

    fn add_digits(a: &[i64; PREC], b: &[i64; PREC], sign: i64) -> [i64; PREC] {
        // sign=+1で加算、-1で減算(繰り上がり/繰り下がりを素直に伝播)。
        let mut out = [0i64; PREC];
        let mut carry: i64 = 0;
        for i in 0..PREC {
            let mut v = a[i] + sign * b[i] + carry;
            carry = 0;
            while v < 0 { v += P; carry -= 1; }
            while v >= P { v -= P; carry += 1; }
            out[i] = v;
        }
        out
    }

    pub fn add(&self, other: &Self) -> Self { Self { digits: Self::add_digits(&self.digits, &other.digits, 1) } }
    pub fn sub(&self, other: &Self) -> Self { Self { digits: Self::add_digits(&self.digits, &other.digits, -1) } }
    pub fn neg(&self) -> Self { Self::zero().sub(self) }

    /// 基数Pの筆算掛け算(4x4の桁積を溜めてから繰り上がりを伝播)。
    /// PREC桁を超える寄与(i+j>=PREC)はmod P^PRECで恒等的に0なので、
    /// そもそも積を取らずに捨てる。
    pub fn mul(&self, other: &Self) -> Self {
        let mut acc = [0u128; PREC];
        for i in 0..PREC {
            if self.digits[i] == 0 { continue; }
            for j in 0..(PREC - i) {
                acc[i + j] += self.digits[i] as u128 * other.digits[j] as u128;
            }
        }
        let mut out = [0i64; PREC];
        let mut carry: u128 = 0;
        for i in 0..PREC {
            let v = acc[i] + carry;
            out[i] = (v % (P as u128)) as i64;
            carry = v / (P as u128);
        }
        Self { digits: out }
    }

    /// 単数(付値0、0桁目が非ゼロ)の逆元。ヘンゼルのNewton反復で
    /// mod P^1の逆元(高速べき乗)からmod P^PRECまで2倍精度ずつ持ち上げる。
    pub fn unit_inverse(&self) -> Self {
        debug_assert!(self.digits[0] != 0, "単数(付値0)にのみ呼べる");
        // mod P上の逆元をフェルマーの小定理で計算。
        let inv0 = mod_pow(self.digits[0], P - 2, P);
        let mut u = { let mut d = [0i64; PREC]; d[0] = inv0; Self { digits: d } };
        let mut prec = 1usize;
        while prec < PREC {
            // u_new = u*(2 - x*u)  (Hensel/Newton反復、精度が2倍になる)
            let xu = self.mul(&u);
            let two_minus_xu = Self::two().sub(&xu);
            u = u.mul(&two_minus_xu);
            prec *= 2;
        }
        u
    }
}

fn mod_pow(mut base: i64, mut exp: i64, modulus: i64) -> i64 {
    let mut res: i64 = 1;
    base %= modulus;
    while exp > 0 {
        if exp & 1 == 1 { res = (res as i128 * base as i128 % modulus as i128) as i64; }
        base = (base as i128 * base as i128 % modulus as i128) as i64;
        exp >>= 1;
    }
    res
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DivOutcome {
    /// 商が(この精度の範囲で)確定した。
    Finite(PInt),
    /// 分母が分子より深く消えている(=射影的には無限遠へ発散する比)。
    Infinite,
    /// 精度PRECの範囲では判定できない(両方とも見た目上ゼロ、等)。
    Indeterminate,
}

impl PInt {
    pub fn checked_div(&self, other: &Self) -> DivOutcome {
        let ov = match other.valuation() { Some(v) => v, None => return DivOutcome::Indeterminate };
        if ov == 0 {
            return DivOutcome::Finite(self.mul(&other.unit_inverse()));
        }
        match self.valuation() {
            None => DivOutcome::Indeterminate,
            Some(sv) if sv < ov => DivOutcome::Infinite,
            Some(_) => {
                let self_shifted = self.shift_down(ov);
                let other_shifted = other.shift_down(ov);
                DivOutcome::Finite(self_shifted.mul(&other_shifted.unit_inverse()))
            }
        }
    }
}

// ============================================================
// 🌟 同次座標(3成分)での幾何プリミティブ。mmp_calculators.rsの
// cross_product/calc_intersection/calc_perpendicular/calc_midpointと
// 全く同じ式を、正規化(normalize、0でない成分で割って先頭を1にする処理)
// を省いたままPInt上で再実装したもの。正規化を挟まない理由: 除算は
// 付値情報を破壊しうる(単数でない成分で割ると発散したり精度を失ったり
// する)ため、退化の"次数"を追跡したい今回の用途では、比較する直前まで
// 生の同次座標のまま保持するのが正しい。
// ============================================================

pub type Triple = [PInt; 3];

pub fn cross3(a: &Triple, b: &Triple) -> Triple {
    [
        a[1].mul(&b[2]).sub(&a[2].mul(&b[1])),
        a[2].mul(&b[0]).sub(&a[0].mul(&b[2])),
        a[0].mul(&b[1]).sub(&a[1].mul(&b[0])),
    ]
}

/// 2点を通る直線の同次座標(=2点の同次座標のクロス積、射影双対性)。
pub fn line_through_points(p: &Triple, q: &Triple) -> Triple { cross3(p, q) }

/// 2直線の交点(直線を点とみなした場合と全く同じクロス積)。
pub fn intersection(l1: &Triple, l2: &Triple) -> Triple { cross3(l1, l2) }

/// 直線lに垂直で点pを通る直線。mmp_calculators::calc_perpendicularと同じ:
/// lの方向(l[1],-l[0])を無限遠点[l0,l1,0]として持ち上げ、pとの直線を取る。
pub fn perpendicular_line(l: &Triple, p: &Triple) -> Triple {
    let inf_pt: Triple = [l[0], l[1], PInt::zero()];
    cross3(&inf_pt, p)
}

/// 直線lに平行で点pを通る直線。
pub fn parallel_line(l: &Triple, p: &Triple) -> Triple {
    let inf_pt: Triple = [l[1].neg(), l[0], PInt::zero()];
    cross3(&inf_pt, p)
}

/// 中点。calc_midpointと同じ式: (x1*z2+x2*z1, y1*z2+y2*z1, 2*z1*z2)。
pub fn midpoint(p: &Triple, q: &Triple) -> Triple {
    let z_term = p[2].mul(&q[2]);
    [
        p[0].mul(&q[2]).add(&q[0].mul(&p[2])),
        p[1].mul(&q[2]).add(&q[1].mul(&p[2])),
        z_term.add(&z_term),
    ]
}

/// 通常の(有限、退化していない)アフィン点(x,y)をP進数の同次座標に持ち上げる。
pub fn affine_point(x: PInt, y: PInt) -> Triple { [x, y, PInt::one()] }

// ============================================================
// 🌟 「最後に定数倍をずらしてからmod pを取る」ステップ。同次座標3成分の
// 共通するPの最大べき(=3成分の付値の最小値)で割ってから、各成分を
// mod Pの通常の整数として取り出す。これが退化の極限でその図形が実際に
// どこへ収束するかを表す「先頭項」。
// ============================================================

/// (付値, 先頭項をmod Pで見た同次座標3つ組)。3成分ともこの精度PRECの
/// 範囲でゼロに見える(=もっと深い次数まで消えている)場合はNone。
pub fn leading_order(t: &Triple) -> Option<(usize, [i64; 3])> {
    let v = t.iter().filter_map(|x| x.valuation()).min()?;
    let shifted: Vec<i64> = t.iter().map(|x| x.shift_down(v).digit0()).collect();
    Some((v, [shifted[0], shifted[1], shifted[2]]))
}

/// 2つの「mod Pの同次座標3つ組」が射影的に等しいか(クロス積が0か)を
/// 判定する。両方ゼロ([0,0,0])の場合は判定不能としてfalseを返す
/// (退化しすぎて比較する意味が無い)。
pub fn projectively_equal_mod_p(a: [i64; 3], b: [i64; 3]) -> bool {
    if a == [0, 0, 0] || b == [0, 0, 0] { return false; }
    let cross = |i: usize, j: usize| -> i64 {
        ((a[i] as i128 * b[j] as i128 - a[j] as i128 * b[i] as i128).rem_euclid(P as i128)) as i64
    };
    cross(0, 1) == 0 && cross(1, 2) == 0 && cross(0, 2) == 0
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand::rngs::StdRng;

    fn rng() -> StdRng { StdRng::seed_from_u64(20240910) }

    #[test]
    fn add_sub_are_inverse() {
        let mut r = rng();
        for _ in 0..50 {
            let a = PInt::random_any(&mut r);
            let b = PInt::random_any(&mut r);
            assert_eq!(a.add(&b).sub(&b), a);
        }
    }

    #[test]
    fn mul_matches_hand_computed_small_case() {
        // (P+2) * (P+3) = P^2 + 5P + 6 なので、桁表現は[6,5,1,0]になるはず。
        let a = PInt::from_digits([2, 1, 0, 0]);
        let b = PInt::from_digits([3, 1, 0, 0]);
        let prod = a.mul(&b);
        assert_eq!(prod.digits, [6, 5, 1, 0]);
    }

    #[test]
    fn unit_inverse_is_correct_mod_p4() {
        let mut r = rng();
        for _ in 0..50 {
            let a = PInt::random_unit(&mut r);
            let inv = a.unit_inverse();
            assert_eq!(a.mul(&inv), PInt::one(), "a * a^-1 は1であるべき: a={:?}", a);
        }
    }

    #[test]
    fn valuation_detects_p_power_factors() {
        let mut r = rng();
        let u = PInt::random_unit(&mut r);
        assert_eq!(u.valuation(), Some(0));
        let once = u.scaled_by_p();
        assert_eq!(once.valuation(), Some(1));
        let twice = once.scaled_by_p();
        assert_eq!(twice.valuation(), Some(2));
        assert_eq!(PInt::zero().valuation(), None);
    }

    #[test]
    fn checked_div_reports_infinite_when_denominator_vanishes_faster() {
        let mut r = rng();
        let num = PInt::random_unit(&mut r); // 付値0
        let den = PInt::random_unit(&mut r).scaled_by_p(); // 付値1
        assert_eq!(num.checked_div(&den), DivOutcome::Infinite);
    }

    #[test]
    fn checked_div_reports_finite_when_valuations_match() {
        let mut r = rng();
        let unit_num = PInt::random_unit(&mut r);
        let unit_den = PInt::random_unit(&mut r);
        let num = unit_num.scaled_by_p();
        let den = unit_den.scaled_by_p();
        match num.checked_div(&den) {
            DivOutcome::Finite(q) => {
                // q * den == num のはず
                assert_eq!(q.mul(&den), num);
            }
            other => panic!("Finiteが期待されたが{:?}が返った", other),
        }
    }

    /// 🌟 本題の検証: 三角形の頂点B,Cを退化(C=B+P*v、B≡C mod PだがP^2
    /// 以上では一致しない)させたとき、外心O(2本の垂直二等分線の交点)を
    /// 「最後にスケールをずらしてからmod pを取る」ことで読み取った極限点
    /// が、退化を一切使わない独立な古典公式(A,Bを固定したまま「Bで方向v
    /// に接する円の中心」=ABの垂直二等分線と、Bを通り方向vに垂直な直線
    /// との交点)と一致することを確認する。前者は「未知の極限をP進数の
    /// 精度で数値的に暴く」経路、後者は「古典幾何の言葉で直接組み立てる」
    /// 経路であり、これが一致することがパイプライン自体(桁の繰り上がり・
    /// 付値の判定・スケール調整)の正しさの検証になる
    /// (最初に「Oは無限遠に発散するはず」という誤った予想で書いたところ
    /// 実際には有限の値に収束することが判明し、この対照実験に書き直した
    /// ――三角形の2頂点が"特定の方向から"近づいて重なる場合、外接円は
    /// 一般には発散せず、残る頂点を通りその方向に接する円に収束するのが
    /// 正しい古典的事実)。
    #[test]
    fn circumcenter_limit_matches_classical_tangent_circle_formula() {
        let mut r = rng();
        let ax = PInt::random_unit(&mut r);
        let ay = PInt::random_unit(&mut r);
        let a = affine_point(ax, ay);

        let bx = PInt::random_unit(&mut r);
        let by = PInt::random_unit(&mut r);
        let b = affine_point(bx, by);

        // v = (dx,dy): Cが近づいてくる方向。C = B + P*v なので
        // B≡C (mod P) だがmod P^2では一般に一致しない(付値ちょうど1)。
        let dx = PInt::random_unit(&mut r);
        let dy = PInt::random_unit(&mut r);
        let c = affine_point(bx.add(&dx.scaled_by_p()), by.add(&dy.scaled_by_p()));

        // (1) 退化した配置から、P進演算で外心を計算し先頭項を読み取る。
        let mid_ab = midpoint(&a, &b);
        let mid_ac = midpoint(&a, &c);
        let line_ab = line_through_points(&a, &b);
        let line_ac = line_through_points(&a, &c);
        let pb_ab = perpendicular_line(&line_ab, &mid_ab);
        let pb_ac = perpendicular_line(&line_ac, &mid_ac);
        let o_degenerate = intersection(&pb_ab, &pb_ac);
        let (_v, o_leading) = leading_order(&o_degenerate).expect("外心の極限は(この乱数drawでは)有限のはず");

        // (2) 対照実験: 退化を一切使わない古典公式を同じ法Pの上で直接計算。
        let inf_v: Triple = [dx, dy, PInt::zero()];
        let line_v_at_b = line_through_points(&b, &inf_v);
        let perp_v_at_b = perpendicular_line(&line_v_at_b, &b);
        let o_limit = intersection(&pb_ab, &perp_v_at_b);
        let o_limit_mod_p = [o_limit[0].digit0(), o_limit[1].digit0(), o_limit[2].digit0()];

        assert!(projectively_equal_mod_p(o_leading, o_limit_mod_p),
            "退化極限から読み取った外心と、古典的な接円公式による外心が一致するべき: {:?} vs {:?}", o_leading, o_limit_mod_p);
    }
}

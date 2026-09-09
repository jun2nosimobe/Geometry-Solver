use std::ops::{Add, Sub, Mul, Div, AddAssign, SubAssign, MulAssign};
use crate::mmp_math::ModInt;

// 同次座標の正規化 (P[2] が 1 になるように割る)
pub fn normalize(v: &[ModInt]) -> Vec<ModInt> {
    if v.is_empty() { return v.to_vec(); }
    let mut res = v.to_vec();
    if let Some(non_zero) = res.iter().find(|&&x| x.0 != 0) {
        let inv = non_zero.inv();
        for x in &mut res {
            *x = *x * inv;
        }
    }
    res
}

// 2直線（または点と直線）のクロス積（外積/交点計算）
// 🐛 FIX: 以前は長さチェックが一切無く、退化した入力(例: calc_line_through_points
// が2点の座標が数値的に一致した際に返す空Vec)がここに渡されるとv1[2]等の
// インデックスアクセスでpanicしていた(orthocenter --mctsで実際に発生)。
// evaluate_node系はNoneで「計算不能」を表現する設計なので、ここでは例外を
// 投げず空Vecを返し、呼び出し側(calc_intersection等、そしてeval.rs側の
// to_option)が「計算不能」として一貫して扱えるようにする。
pub fn cross_product(v1: &[ModInt], v2: &[ModInt]) -> Vec<ModInt> {
    if v1.len() < 3 || v2.len() < 3 { return vec![]; }
    vec![
        v1[1] * v2[2] - v1[2] * v2[1],
        v1[2] * v2[0] - v1[0] * v2[2],
        v1[0] * v2[1] - v1[1] * v2[0],
    ]
}

// 2点を通る直線 / 直線の方程式の計算
pub fn calc_line_through_points(p1: &[ModInt], p2: &[ModInt]) -> Vec<ModInt> {
    if p1.len() < 3 || p2.len() < 3 { return vec![]; }
    let cx = p1[1] * p2[2] - p1[2] * p2[1];
    let cy = p1[2] * p2[0] - p1[0] * p2[2];
    let cz = p1[0] * p2[1] - p1[1] * p2[0];
    
    if cx.0 == 0 && cy.0 == 0 && cz.0 == 0 {
        return vec![];
    }
    normalize(&[cx, cy, cz])
}

// 中点の計算
pub fn calc_midpoint(p1: &[ModInt], p2: &[ModInt]) -> Vec<ModInt> {
    if p1.len() < 3 || p2.len() < 3 { return vec![]; }
    let z_term = p1[2] * p2[2];
    let x = p1[0] * p2[2] + p2[0] * p1[2];
    let y = p1[1] * p2[2] + p2[1] * p1[2];
    let z = z_term + z_term;
    normalize(&[x, y, z])
}

// 外接円 (Circumcircle) の方程式の係数 (u, v, w, s) 計算
pub fn calc_circumcircle(p1: &[ModInt], p2: &[ModInt], p3: &[ModInt]) -> Vec<ModInt> {
    if p1.len() < 3 || p2.len() < 3 || p3.len() < 3 { return vec![]; }
    
    // 座標の展開を追加
    let (x1, y1, z1) = (p1[0], p1[1], p1[2]);
    let (x2, y2, z2) = (p2[0], p2[1], p2[2]);
    let (x3, y3, z3) = (p3[0], p3[1], p3[2]);
    
    let sq1 = x1 * x1 + y1 * y1;
    let sq2 = x2 * x2 + y2 * y2;
    let sq3 = x3 * x3 + y3 * y3;

    let u = z1 * z2 * z3 * (x1 * (y2 * z3 - y3 * z2) - y1 * (x2 * z3 - x3 * z2) + z1 * (x2 * y3 - x3 * y2));
    let v = -(sq1 * (y2 * z2 * z3 * z3 - y3 * z3 * z2 * z2) - y1 * z1 * (sq2 * z3 * z3 - sq3 * z2 * z2) + z1 * z1 * (sq2 * y3 * z3 - sq3 * y2 * z2));
    let w = sq1 * (x2 * z2 * z3 * z3 - x3 * z3 * z2 * z2) - x1 * z1 * (sq2 * z3 * z3 - sq3 * z2 * z2) + z1 * z1 * (sq2 * x3 * z3 - sq3 * x2 * z2);
    let s = -(sq1 * (x2 * z2 * y3 * z3 - x3 * z3 * y2 * z2) - x1 * z1 * (sq2 * y3 * z3 - sq3 * y2 * z2) + y1 * z1 * (sq2 * x3 * z3 - sq3 * x2 * z2));

    normalize(&[u, v, w, s])
}

pub fn calc_intersection(l1: &[ModInt], l2: &[ModInt]) -> Vec<ModInt> {
    normalize(&cross_product(l1, l2))
}


pub fn calc_perpendicular(l: &[ModInt], p: &[ModInt]) -> Vec<ModInt> {
    if l.len() < 3 || p.len() < 3 { return vec![]; }
    let inf_pt = [l[0], l[1], ModInt::new(0)];
    normalize(&cross_product(&inf_pt, p))
}

pub fn calc_parallel(l: &[ModInt], p: &[ModInt]) -> Vec<ModInt> {
    if l.len() < 3 || p.len() < 3 { return vec![]; }
    let inf_pt = [-l[1], l[0], ModInt::new(0)];
    normalize(&cross_product(&inf_pt, p))
}

// 🐛 FIX: 以前は長さチェックも、z成分(同次座標の第3要素)が0(=無限遠点)かの
// チェックも無かった。z==0の点を渡すと `v1[0]/v1[2]` がModInt::inv()内で
// ゼロ除算panicを起こす(0.inv()はpanicする実装になっている)。戻り値を
// Option<ModInt>にして、計算不能な場合はNoneで表現する。
pub fn calc_squared_distance(v1: &[ModInt], v2: &[ModInt]) -> Option<ModInt> {
    if v1.len() < 3 || v2.len() < 3 || v1[2].0 == 0 || v2[2].0 == 0 { return None; }
    let x1 = v1[0] / v1[2];
    let y1 = v1[1] / v1[2];
    let x2 = v2[0] / v2[2];
    let y2 = v2[1] / v2[2];
    let dx = x1 - x2;
    let dy = y1 - y2;
    Some(dx * dx + dy * dy)
}


// 🌟 調和共役点(第4調和点)の直接計算。A,B,Cが同一直線上にあるとき
// (A,B;C,D) = -1 となる D を求める。A,Bを基底とみなしC = p*A + q*B と
// 分解し(同次座標なので係数比のみ意味を持つ)、D = p*A - q*B とすれば
// クロス比が丁度 -1 になる(A,Bをそれぞれ媒介変数0, ∞とみなす標準的な事実)。
// construct_harmonic_conjugate による完全四辺形の作図結果が、この閉じた式と
// 数値的に一致することをテストで検証するために用いる(証明本体では使わない)。
pub fn calc_harmonic_conjugate(a: &[ModInt], b: &[ModInt], c: &[ModInt]) -> Vec<ModInt> {
    if a.len() < 3 || b.len() < 3 || c.len() < 3 { return vec![]; }

    let try_pair = |i: usize, j: usize| -> Vec<ModInt> {
        let row1 = [a[i], b[i], -c[i]];
        let row2 = [a[j], b[j], -c[j]];
        cross_product(&row1, &row2)
    };

    let mut pql = try_pair(0, 1);
    if pql.iter().all(|x| x.0 == 0) { pql = try_pair(1, 2); }
    if pql.iter().all(|x| x.0 == 0) { pql = try_pair(0, 2); }
    let (p, q) = (pql[0], pql[1]);

    let d = [
        p * a[0] - q * b[0],
        p * a[1] - q * b[1],
        p * a[2] - q * b[2],
    ];
    normalize(&d)
}

// 🌟 複比 (A,B;C,D) の直接計算。A,B,C,Dが同一直線上にあるとき、C,Dを
// それぞれA,Bの1次結合 X = p_X*A + q_X*B (同次座標としての比のみ意味を持つ、
// calc_harmonic_conjugateと同じ分解トリック)に分解し、A,Bを媒介変数0,∞と
// みなした時の"座標" τ_X = q_X/p_X を使って (A,B;C,D) := τ_D / τ_C として
// 求める。D = H(A,B,C)(調和共役点)のときはτ_D = -τ_Cとなるため、この式は
// ちょうど-1を返す ── これをテストでの正しさの検算に使う。
// A,B,C,Dのいずれかが縮退している(C=BまたはD=A、あるいは分解不能)場合はNone。
pub fn calc_cross_ratio(a: &[ModInt], b: &[ModInt], c: &[ModInt], d: &[ModInt]) -> Option<ModInt> {
    if a.len() < 3 || b.len() < 3 || c.len() < 3 || d.len() < 3 { return None; }

    let decompose = |x: &[ModInt]| -> Option<(ModInt, ModInt)> {
        let try_pair = |i: usize, j: usize| -> Vec<ModInt> {
            let row1 = [a[i], b[i], -x[i]];
            let row2 = [a[j], b[j], -x[j]];
            cross_product(&row1, &row2)
        };
        let mut pql = try_pair(0, 1);
        if pql.iter().all(|v| v.0 == 0) { pql = try_pair(1, 2); }
        if pql.iter().all(|v| v.0 == 0) { pql = try_pair(0, 2); }
        if pql.len() < 2 || (pql[0].0 == 0 && pql[1].0 == 0) { return None; }
        Some((pql[0], pql[1]))
    };

    let (p_c, q_c) = decompose(c)?;
    let (p_d, q_d) = decompose(d)?;
    // p_c==0 は C=B(τ_Cが未定義=分母ゼロ)、q_d==0 は D=A(τ_Dが未定義)に相当し、
    // どちらも複比が定義不能な退化ケース。
    if p_c.0 == 0 || q_d.0 == 0 { return None; }
    Some((q_c * p_d) / (p_c * q_d))
}

// 🐛 FIX: 以前は長さチェックも、vp(接点)のz成分が0(=無限遠点)かのチェックも
// 無かった。cross_productと同様、退化した入力に対してpanicせずvec![]
// (計算不能)を返すようにする。
pub fn calc_tangent_line(vc: &[ModInt], vp: &[ModInt]) -> Vec<ModInt> {
    // vc: [A, D, E, F] (A(x^2+y^2) + Dx + Ey + F = 0)
    // vp: [x, y, z] (接点)
    // 🐛 FIX: 以前はここを[D,E,F,A](Aが最後)だと思ってvc[0..3]を読んでいたが、
    // calc_circumcircleが実際に返す並びは[A,D,E,F](Aが先頭)だった
    // (eval.rs::sample_point_on_circleのコメント、および
    // test_tangent_line_to_circle_is_numerically_correctで非対称な円
    // (D,E,Fが全て非自明な値を持つ配置)を使って実測・確認済み――対称な
    // 単位円ではD=E=0になり、この食い違いが偶然打ち消し合って検出でき
    // なかった)。この食い違いはtangent_orthic.rs等の既存問題では、証明が
    // 純粋に記号的な定理適用(接弦定理)だけで届き、接線の数値そのものを
    // 検算する経路を一度も通っていなかったため症状として顕在化していな
    // かった。射影版(シュタイナーの定理)の接弦定理を二次曲線の接線を使って
    // 構築するにあたり、複比という本質的に数値/代数的な量を経由するため、
    // 誤った係数のままでは正しく動かない。
    if vc.len() < 4 || vp.len() < 3 || vp[2].0 == 0 { return vec![]; }
    let a_val = vc[0];
    let d = vc[1];
    let e = vc[2];
    let f = vc[3];
    
    let x0 = vp[0] / vp[2];
    let y0 = vp[1] / vp[2];
    
    let two = ModInt::new(2);
    let a = a_val * x0 + d / two;
    let b = a_val * y0 + e / two;
    let c = (d / two) * x0 + (e / two) * y0 + f;
    
    normalize(&[a, b, c])
}

// 🌟 二次曲線(5点)の係数復元で使う、3D外積[cross_product]の6次元への一般化。
// 3D外積 a×b は行列式 det([[e1,e2,e3],[a1,a2,a3],[b1,b2,b3]]) を第1行(基底
// ベクトル)で展開したもの ―― 第k成分 = (-1)^k * (a,bから第k列を除いた
// 2×2小行列式)という構成そのものであり、これは「5本のベクトル+6次元」に
// そのまま一般化できる(以下、成分数を6, 入力ベクトル数を5に一般化した版)。
// 結果は入力の5本全てに直交する(証明: 結果を計算する際に使うのと全く同じ
// 余因子で、ある入力行r_iをもう一度「基底の行」の位置に代入して6×6行列式を
// 展開すると、行列に同じ行r_iが2回現れるため恒等的に0になる。これが
// ちょうどr_i・結果 の余因子展開そのもの)。
fn generalized_cross_6(rows: &[Vec<ModInt>; 5]) -> Vec<ModInt> {
    (0..6).map(|j| {
        let mut minor: Vec<Vec<ModInt>> = rows.iter()
            .map(|row| row.iter().enumerate().filter(|(k, _)| *k != j).map(|(_, v)| *v).collect())
            .collect();
        let det = crate::mmp_math::determinant_mod(&mut minor);
        if j % 2 == 0 { det } else { -det }
    }).collect()
}

// 🌟 5点を通る一般二次曲線 Ax²+Bxy+Cy²+Dxz+Eyz+Fz²=0 の係数[A,B,C,D,E,F]を
// 求める。calc_circumcircleの一般化(円は「x²とy²の係数が等しくxyの係数が0」
// という特殊な二次曲線)だが、二次曲線は6係数(射影空間としては5自由度)が
// 独立なので、外接円のような3×4行列の零空間ではなく5×6行列の零空間が必要。
// 各点(x,y,z)が二次曲線に乗る条件 A x²+B xy+C y²+D xz+E yz+F z² = 0 は
// 係数[A..F]に関する1次方程式なので、5点それぞれの単項式ベクトル
// [x²,xy,y²,xz,yz,z²]を5本並べた5×6行列の零空間(のはずの1次元の解)を、
// generalized_cross_6(3点円の場合のcross_productに相当)でそのまま求める。
// 5点が一般の位置に無い(4点が同一直線上にある等でランク落ちする)場合は
// 全成分0になり、退化(計算不能)として空Vecを返す。
pub fn calc_conic_through_5_points(pts: &[Vec<ModInt>]) -> Vec<ModInt> {
    if pts.len() != 5 || pts.iter().any(|p| p.len() < 3) { return vec![]; }
    let rows: [Vec<ModInt>; 5] = std::array::from_fn(|i| {
        let (x, y, z) = (pts[i][0], pts[i][1], pts[i][2]);
        vec![x * x, x * y, y * y, x * z, y * z, z * z]
    });
    let coeffs = generalized_cross_6(&rows);
    if coeffs.iter().all(|v| v.0 == 0) { return vec![]; }
    normalize(&coeffs)
}
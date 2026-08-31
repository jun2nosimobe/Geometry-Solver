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
pub fn cross_product(v1: &[ModInt], v2: &[ModInt]) -> Vec<ModInt> {
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

pub fn calc_squared_distance(v1: &[ModInt], v2: &[ModInt]) -> ModInt {
    let x1 = v1[0] / v1[2];
    let y1 = v1[1] / v1[2];
    let x2 = v2[0] / v2[2];
    let y2 = v2[1] / v2[2];
    let dx = x1 - x2;
    let dy = y1 - y2;
    dx * dx + dy * dy
}


pub fn calc_tangent_line(vc: &[ModInt], vp: &[ModInt]) -> Vec<ModInt> {
    // vc: [D, E, F, A] (A(x^2+y^2) + Dx + Ey + F = 0)
    // vp: [x, y, z] (接点)
    let d = vc[0];
    let e = vc[1];
    let f = vc[2];
    let a_val = vc[3];
    
    let x0 = vp[0] / vp[2];
    let y0 = vp[1] / vp[2];
    
    let two = ModInt::new(2);
    let a = a_val * x0 + d / two;
    let b = a_val * y0 + e / two;
    let c = (d / two) * x0 + (e / two) * y0 + f;
    
    normalize(&[a, b, c])
}
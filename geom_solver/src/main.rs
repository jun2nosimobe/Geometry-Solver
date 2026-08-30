mod mmp_math;
mod mmp_core;
mod logic_core;
mod mmp_calculators;
mod mmp_tester;

use mmp_math::ModInt;

fn main() {
    println!("=== 幾何ソルバー Rustコア デバッグ開始 ===");

    let a = ModInt::new(10);
    let b = ModInt::new(3);
    println!("10 / 3 mod PRIME = {}", (a / b).0);

    let p1 = vec![ModInt::new(0), ModInt::new(0), ModInt::new(1)];
    let p2 = vec![ModInt::new(1), ModInt::new(1), ModInt::new(1)];
    let line = mmp_calculators::calc_line_through_points(&p1, &p2);
    let line_coords: Vec<i64> = line.iter().map(|m| m.0).collect();
    println!("Line through (0,0) and (1,1): {:?}", line_coords);
}
//! 🌟 問題の初期作図に、証明と無関係な作図をノイズとして足す(`--noise=N`)。
//!
//! 狙い(方針E): 難しい問題では探索そのものが大量の補助図形を作るので、最小限のきれいな図でしか解けない
//! ソルバーは難問に届かない。足すのは図を大きくするだけの作図で、問題の主張の真偽には影響しない ―
//! それで解けなくなったり仕事量が跳ね上がったりするなら、探索が図の大きさに弱いということ。
//!
//! 作るもの: 2点を通る直線 / 2点の中点 / 点から直線への垂線 / 2直線の交点 / 3点の外接円。
//! 材料は既にある有限の点と直線だけで、新しい自由点は置かない(自由点を足すと図の自由度が変わってしまう)。
//! 同じ `--noise-seed` なら毎回同じ図になる。

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};

/// count 個の無関係な作図を足す。戻り値は実際に増えた実体の数(既にある作図は数えない)。
pub fn add_noise(egraph: &mut EGraph, count: usize, seed: u64) -> usize {
    let mut rng = StdRng::seed_from_u64(seed);
    let before = egraph.entities.len();

    for i in 0..count {
        // 作れるものが見つかるまで数回試す(同じ作図が既にある・材料が足りないときは引き直す)。
        for _ in 0..16 {
            let points = finite_points(egraph);
            let lines = plain_lines(egraph);
            let pick = |rng: &mut StdRng, v: &[ClassId]| v[rng.gen_range(0..v.len())];
            let (def, ty) = match rng.gen_range(0..5) {
                0 if points.len() >= 2 => {
                    let (a, b) = two_of(&mut rng, &points);
                    (Definition::new_line(a, b), EntityType::Line)
                }
                1 if points.len() >= 2 => {
                    let (a, b) = two_of(&mut rng, &points);
                    (Definition::Midpoint(a, b), EntityType::Point)
                }
                2 if !points.is_empty() && !lines.is_empty() => {
                    let p = pick(&mut rng, &points);
                    let l = pick(&mut rng, &lines);
                    (Definition::PerpendicularLine(l, p), EntityType::Line)
                }
                3 if lines.len() >= 2 => {
                    let (l1, l2) = two_of(&mut rng, &lines);
                    (Definition::Intersection(l1, l2), EntityType::Point)
                }
                4 if points.len() >= 3 => {
                    let (a, b) = two_of(&mut rng, &points);
                    let c = pick(&mut rng, &points);
                    if c == a || c == b { continue; }
                    (Definition::Circumcircle(a, b, c), EntityType::Conic)
                }
                _ => continue,
            };
            let n = egraph.entities.len();
            egraph.create_entity(format!("Noise{}", i + 1), def, ty);
            if egraph.entities.len() > n { break; }   // 新しく作れた
        }
    }

    egraph.apply_congruence_closure();
    egraph.entities.len() - before
}

fn two_of(rng: &mut StdRng, v: &[ClassId]) -> (ClassId, ClassId) {
    let a = v[rng.gen_range(0..v.len())];
    loop {
        let b = v[rng.gen_range(0..v.len())];
        if b != a { return (a, b); }
    }
}

/// 有限の点(無限遠直線上の点=方向は除く)。
fn finite_points(egraph: &EGraph) -> Vec<ClassId> {
    egraph.iter_reps_of_type(EntityType::Point)
        .filter(|&id| egraph.entities[id.0].is_active())
        .filter(|&id| !egraph.is_connected(id, egraph.line_infinity))
        .collect()
}

/// 普通の直線(無限遠直線は除く)。
fn plain_lines(egraph: &EGraph) -> Vec<ClassId> {
    egraph.iter_reps_of_type(EntityType::Line)
        .filter(|&id| egraph.entities[id.0].is_active() && id != egraph.line_infinity)
        .collect()
}

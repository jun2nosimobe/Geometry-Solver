//! 🌟 HAGeo-409ベンチマーク問題群(bench_*.rs)で繰り返し使う補助構成。
//! 「垂線の足」「外心」は既存の各問題ファイル(simson.rs, circumcenter.rs等)
//! でもその都度手書きされていたパターンだが、ベンチマークを一括で増やすに
//! あたり重複が大きくなったのでここに共通化した。挙動は既存ファイルの
//! パターンと完全に同じ(新しい定理・構成要素は一切導入していない)。

use crate::mmp_core::{ClassId, Definition, EGraph, EntityType};

/// 点`from`から直線`line`へ下ろした垂線の足。
/// (simson.rsのD,E,F等と同じ「PerpendicularLine→Intersection」の2段構成)
pub fn foot(egraph: &mut EGraph, from: ClassId, line: ClassId, name: &str) -> ClassId {
    let perp = egraph.create_entity(format!("Perp_{}_(Aux)", name), Definition::PerpendicularLine(line, from), EntityType::Line);
    egraph.create_entity(format!("Foot_{}", name), Definition::Intersection(line, perp), EntityType::Point)
}

/// 三角形(3点)の外心。circumcenter.rsと同じく、2辺の垂直二等分線の交点として
/// 構成する(3本目の垂直二等分線も同じ点を通ることの証明は既存のcircumcenter.rs
/// 側で別途扱っており、ここでは「外心は存在する」という既知の前提として使う)。
pub fn circumcenter(egraph: &mut EGraph, a: ClassId, b: ClassId, c: ClassId, name: &str) -> ClassId {
    let l_ab = egraph.create_entity(format!("Line_{}_AB_(Aux)", name), Definition::new_line(a, b), EntityType::Line);
    let l_ac = egraph.create_entity(format!("Line_{}_AC_(Aux)", name), Definition::new_line(a, c), EntityType::Line);
    let mid_ab = egraph.create_entity(format!("Mid_{}_AB_(Aux)", name), Definition::Midpoint(a, b), EntityType::Point);
    let mid_ac = egraph.create_entity(format!("Mid_{}_AC_(Aux)", name), Definition::Midpoint(a, c), EntityType::Point);
    let pb_ab = egraph.create_entity(format!("PB_{}_AB_(Aux)", name), Definition::PerpendicularLine(l_ab, mid_ab), EntityType::Line);
    let pb_ac = egraph.create_entity(format!("PB_{}_AC_(Aux)", name), Definition::PerpendicularLine(l_ac, mid_ac), EntityType::Line);
    egraph.create_entity(format!("Circumcenter_{}", name), Definition::Intersection(pb_ab, pb_ac), EntityType::Point)
}

/// 有向角(dir1,dir2)がang90に等しい、という「直交」の目標/仮定を作る便利関数。
pub fn angle_pair(egraph: &mut EGraph, dir1: ClassId, dir2: ClassId, name: &str) -> ClassId {
    egraph.create_entity(format!("Ang_{}", name), Definition::AnglePair(dir1, dir2), EntityType::Angle)
}

pub fn direction_of(egraph: &mut EGraph, line: ClassId, name: &str) -> ClassId {
    egraph.create_entity(format!("Dir_{}", name), Definition::DirectionOf(line), EntityType::Point)
}

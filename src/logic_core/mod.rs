//! 🌟 定理の探索エンジン。役割ごとに分けてある:
//!
//!   theorem.rs    定理の書き方(パターン・構成・結論)とその補助関数
//!   prover.rs     証明器の状態と、マッチ成立後の作図・結論の適用
//!   cost.rs       次にどのパターンを見るかの見積もりと、候補の絞り方(枝刈り)
//!   matcher.rs    パターン列を消費していく深さ優先探索の本体
//!   blackboard.rs タスク待ち行列と、行き詰まったときの需要駆動の補助作図
//!   wu.rs         最初と手詰まりのときに目標を Wu の方法で示す試み
//!   degree_search.rs 次数の順に事実を確定していく探索(--degree-search)
//!
//! 以前は1ファイル3100行に全部入っていた。中身は分割時に1文字も
//! 変えていない(挙動が同じことは消費仕事量が1ステップも変わらないことで
//! 確認済み)。

mod blackboard;
mod cost;
mod matcher;
mod numeric_aux;
pub(crate) mod ar;
mod prover;
mod theorem;
mod wu;
mod degree_search;

pub use blackboard::*;
pub use prover::*;
pub use theorem::*;
pub use wu::*;

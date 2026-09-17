# 設計ノート

ソースのコメントから移した、設計の経緯・実測・直したバグ・試して採らなかった案の記録。

| ノート | 対象 |
|---|---|
| [mmp_core.md](mmp_core.md) | `src/mmp_core/`(e-graph・合同閉包・数値評価・証明の抽出)と `src/mmp_calculators.rs` |
| [theorems.md](theorems.md) | `src/theorems.rs`(定理の定義) |
| [discover.md](discover.md) | `src/discover.rs`・`src/padic*.rs`・`src/serve.rs`・`src/discover_viz.rs`(自由探索による発見と作図画面) |
| [mcts.md](mcts.md) | `src/action_space.rs`・`src/mcts.rs`(MCTS、既定では無効) |
| [diagnostics.md](diagnostics.md) | `src/trace.rs`・`src/sketch.rs`・`src/sweep.rs`・`src/cli.rs`・問題ファイル |

各項目の引用は移した時点の原文のまま。ファイル名(`main.rs`・`logic_core.rs`)や数値(`NN/96`・`37問` など)は当時のもので、今のコードとは食い違うことがある。今の挙動はソースのコメントとコードを正とする。

## コメントとドキュメントの置き場所

| 書くこと | 置き場所 |
|---|---|
| そのコードが今どう動くか、なぜその形なのか(不変条件・前提・落とし穴) | ソースのコメント(短く) |
| そうなった経緯、実測の数値、直したバグの詳しい話、試して採らなかった案 | このディレクトリのノート |
| 変更の単位での判断と測定結果(何を変えて、ベンチがどう動いたか) | [atlas の来歴](../ledger.html) |
| まだ手を付けていない改善候補 | [atlas の改善候補](../backlog.html) |

コードのコメントに経緯を書き足したくなったら、コメントには今の理由だけを1〜3行で書き、経緯はノートの該当する見出しの下に足す。
ノートを指す必要があるときは `経緯: docs/notes/<ファイル>.md「見出し」` の形で書く(行番号は腐るので使わない)。

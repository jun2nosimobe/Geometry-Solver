# MCTS と行動候補の設計ノート

`src/action_space.rs` などのソースコメントから移した経緯と実測。MCTS は既定では無効(atlas の来歴を参照)。

## 目次

- [MCTS の行動候補(action_space.rs)](#mcts-の行動候補action_spacers)
- [その他(短く書き直したコメントの原文)](#その他短く書き直したコメントの原文)

## MCTS の行動候補(action_space.rs)

`src/action_space.rs` — `fn target_weight_bonus(egraph: &EGraph, id: ClassId, target: &Option<(String, Vec<ClassId>` の直前にあったコメント:

> 証明目標の図形への構造的な近さによる重みボーナス。mcts.rsの
> target_bonus(報酬評価側、行動を実行し終えた「後」で使う)と同じ考え方
> だが、こちらは行動生成そのもの(=どの点・直線を組み合わせの候補として
> サンプリングするか)を目標寄りに偏らせるために使う。
>
> 以前はget_possible_actionsが完全に目標を知らないまま、純粋に
> entity_weight(構造的な次数・熱)だけでサンプリングしていた。これだと
> num_samples(12〜30)という限られたサンプル数の大半が、次数は高くても
> 目標とは無関係な組み合わせに費やされてしまい、MCTSの探索効率を
> 損なっていた(証明目標周辺の図形をいくら「面白い」と評価しても、
> そもそも候補として作図案に挙がらなければ報酬評価まで辿り着けない)。
> 代数は使わず、直接一致/構造的な直接接続(is_connected)だけを見る点は
> target_bonusと同じ。

`src/action_space.rs` — `if let (Some(&dx), Some(&dy)) = (` の直前にあったコメント:

> FIX(無駄な退化構成の抑制): 2直線が既に平行だと構造的に
> わかっている場合、その「交点」は新しい有限点ではなく、
> 2直線が共有する無限遠点(DirectionOfで既に表現済みの実体)
> そのものである。以前はEntityType::Direction撤廃前で、この
> Intersection(l1,l2)が(常にPoint型で作られてしまうため)本物の
> Direction型の実体と型をまたいで統合されるバグの温床でもあった
> (discover.rsの自由探索で実測: ParallelLine(l,p)で作った新しい
> 線と元のlを later intersectionする形で頻発し、Line_infinityの
> 接続点が汚染され、無関係な方向どうしを誤って同一視しようとする
> 健全性チェック却下のスパムを大量に引き起こしていた)。
> EntityType::Direction撤廃(方向はL∞に接続されたただのPoint)に
> よりその型混同自体はもう構造的に起こり得なくなったが、この
> チェックは引き続き「どうせ既存の方向実体に統合されるだけの
> Point実体を新規に作る」という無駄自体を候補生成の時点で
> 省く効果があるので残す。
> 両方向がまだ実体化されていない場合は判定できないので素通しする
> (その場合はIntersectionが先に試され、その時点で初めて2つの
> 方向が統合されるので、以後のサンプリングではこの分岐で弾かれる)。

`src/action_space.rs` — `for &l in self.weighted_pick(&lines, egraph, (num_samples / 4).max(1), target).iter() {` の直前にあったコメント:

> 6. 調和共役点: 既に共線であることが構造的にわかっている3点があれば、
> その第4調和点を作る完全四辺形作図を候補にする(円錐曲線は使わない)。
> FIX(自由探索モードの実測で判明): ここは1〜5と違って
> weighted_pickによるサンプリングをせず「全ての直線」に対して
> 毎回1件ずつ候補を積んでいた。調和共役の作図(construction.rs)は
> それ自体がP,Q,R,Sという補助点と複数の補助直線を生むため、
> 「調和共役を作る→直線が増える→次のラウンドで調和共役候補が
> さらに増える」という正のフィードバックが成立し、実測では
> 60秒48ステップの探索で生成された予想候補のほぼ全てが
> Harm(Harm(Harm(...)))という入れ子の足場だけを指す状態になって
> いた(古典的な構図に一切到達できない)。他の候補生成と同じく
> 重み付きサンプリングで少数の直線に絞る。

`src/action_space.rs` — `let mut pts_on_l: Vec<ClassId> = egraph.entities[l.0].components.first()` の直前にあったコメント:

> FIX: comp.subobjectsは同じ代表元を指す異なる(マージ前の)ClassIdを
> 重複して持ちうる(get_rep後の値が同じでも別々のスロットとして
> 積まれたまま)。dedupしないままweighted_pickに渡すと、同じ点が
> 「2つの別々の候補」として選ばれ、HarmonicConjugate(B,B,B)のような
> 退化した(3引数が同一点の)作図が実際に生成されてしまう(自由探索
> モードの実測で発見)。sort_unstable_by_key+dedupで候補プール自体を
> 一意な代表元だけにしてから渡す。

`src/action_space.rs` — `.filter(|&s| egraph.entities[s.0].mcts_depth <= Self::MAX_MCTS_CHAIN_DEPTH)` の直前にあったコメント:

> FIX: Action::HarmonicConjugateはtry_push_defを経由せず
> actions.pushで直接積まれるため、Constructの候補生成が
> entities_of_typeで課しているmcts_depthのハード上限を
> 唯一すり抜けていた。その結果、調和共役だけが3段・4段と
> 無制限に入れ子になれる(実測でHarm(Harm(Harm(...)))を確認)。
> 入力点にも同じ上限・同じ除外(無限遠点/内部定数)を課す。

`src/action_space.rs` — `const MAX_MCTS_CHAIN_DEPTH: usize = 2;` の直前にあったコメント:

> MCTSがMCTS自身の産物の上にさらにMCTS産物を積み重ねる連鎖
> (GeoEntity::mcts_depth参照)の深さの上限。base_importanceを下げる
> (mcts.rs::run_stepで採用した補助構成に0.3を設定)だけでは、確率的な
> サンプリングである以上0にはならず、長時間の実行で「中点のまた中点の
> また中点…」のような無意味な入れ子が実際に積み上がることが実測で
> 確認された。これはentity_weightのuses.len()項が、何かを積み増す
> たびに親側のuses(=依存度)を底上げし、さらに選ばれやすくなるという
> 正のフィードバックも一因。ここでは「MCTS産物の上にMCTS産物」という
> 連鎖だけを対象にした深さでハード上限を設け、確率に頼らず物理的に
> 遮断する。問題文で最初から与えられている点・直線や需要駆動の補助線は
> mcts_depth=0のままなので、この上限の影響を一切受けない。
> 2に設定した理由: 1段目(真の点・直線から直接作った補助構成、例:
> 対辺への垂線)、2段目(その交点、例:垂心候補)までは典型的な定理の
> 証明で普通に必要になる一方、3段目以降(その上にさらに中点/直線などを
> 積む)は今回観測された無意味な入れ子のパターンそのものであり、
> 実質的に価値を生まないまま組み合わせだけが爆発する。

`src/action_space.rs` — `fn is_special_constant(egraph: &EGraph, id: ClassId) -> bool {` の直前にあったコメント:

> ユーザー提案(自由探索モードでの改善点の洗い出し)への対応。
> Line_infinity/CircI/CircJ/Ang0/Ang90は、有向角・複比といった
> 射影的な計算機構を成立させるための内部的な定数(EGraph::new参照)で
> あって、人間が「補助構成として選ぶ」対象ではない。しかしbase_importance
> はどれも既定値1.0のままで、entity_typeも普通のLine/Direction/Angleと
> 見分けが付かないため、これまでentities_of_typeの候補プールに紛れ込み、
> 「Line_infinityとの交点」「Line_infinityへの垂線」のような、名前だけ
> 見ても何を意味するか分からない退化した作図案がMCTSの候補に混ざる
> 原因になっていた(discover.rsでの自由探索の実測で確認)。目標に向けた
> 通常の証明探索でもこれらが有用な補助構成先になることは無いため、
> 除外しても既存問題への悪影響は無いはず(31問題スイートで検証済み)。

`src/action_space.rs` — `#[test]` の直前にあったコメント:

> 目標指向ヒューリスティックの効果を、実際のorthocenter問題の初期状態
> (探索は一切進めず、setup直後のまま)に対して直接測定する回帰テスト。
> get_possible_actionsを繰り返し呼んだ時に生成される候補アクションのうち、
> 実際に目標(H_AltA_AltB/H_AltB_AltC、あるいはそれらに直接接続している
> 垂線Alt_A/Alt_B/Alt_C)を参照するものの割合を、目標バイアス有効/無効で
> 比較する。
>
> 測定メモ: orthocenter --mctsを実際に何秒か走らせて比較する方法
> (マージ数・健全性チェック却下数など)も試したが、探索が進むにつれて
> 状態が大きく分岐すること・orthocenterが三角形の退化(既知のリスク)を
> 起こしやすいことから、両条件の総計算量自体が実行ごとに大きく異なって
> しまい、指標として使うには交絡が大きすぎた(例: ある実行では却下数が
> 数百件、別の実行では数万件という桁違いのばらつきが出た)。この
> テストはそれとは独立に、「固定された同一状態からget_possible_actions
> を呼んだ時、目標バイアスが実際に候補の分布を目標寄りに変えているか」
> だけを検証する、交絡の少ない直接測定であり、実測では目標バイアス
> 有効時98.0%・無効時66.6%(候補アクション延べ13000件超)と、
> 明確で一貫した差が出た。

`src/mcts.rs` — `if sim_idx % 20 == 19 {` の直前にあったコメント:

> 直結: 以前はmain.rsのメインループ側だけがprocess_pending_conjectures
> を呼んでおり、MCTS自身がこのrun_step呼び出しの中で発見した予想は、
> このrun_stepが終わって呼び出し元に戻り、次のメインループの
> ティックが回ってくるまでheat_bonusに反映されなかった
> (=同じrun_step内の残りのシミュレーションには一切効かなかった)。
> ここで20シミュレーションに1回、EGraph::process_pending_conjectures
> を直接呼ぶことで、MCTSが自分の手番の中で見つけた「あと数個で
> マッチングできそうな」予想を、同じ呼び出し内の後続シミュレーション
> のentity_weight(=get_possible_actions/weighted_pickが読む値)に
> 即座に反映させる。呼び出し1回あたりの評価件数上限(MAX_PER_CALL=3)
> はprocess_pending_conjectures側でそのまま維持されるので、頻度を
> 上げても評価コスト(クローン+合同閉包1回)は「20シミュレーションに
> つき高々3件」に留まり、組み合わせ爆発は起きない。

## その他(短く書き直したコメントの原文)

`src/action_space.rs` — `let conics: Vec<ClassId> = self.entities_of_type(egraph, EntityType::Conic);` の直前にあったコメント:

> 7. 直線×二次曲線 -> もう一方の交点。ユーザー指示(「無闇に定理を
> 追加してもノイズが増えるだけなので、ondemand作図やMCTSによる
> 補助点作図の改善もすべき」)への対応: オリンピック幾何で頻出する
> 「直線を延長して既存の円/二次曲線と再び交わる点」という補助構成
> (例: 「AOの延長が外接円と再び交わる点」)を、個別の定理を増やす
> 代わりにMCTSの一般的な作図候補として追加した。
> Definition::SecondIntersectionOfLineAndConicは「既に両方に乗って
> いる1点(known_point)」を要求するので、各二次曲線について「既に
> その曲線に乗っている点」→「その点を通る既存の直線」という2段階で
> 候補を絞り込む(is_connectedの構造的な事実だけで判定できるので、
> 数値計算は一切不要)。

`src/action_space.rs` — `fn entities_of_type(&self, egraph: &EGraph, ty: EntityType) -> Vec<ClassId> {` の直前にあったコメント:

> EntityType::Direction撤廃(方向はL∞に接続されたただのPointに
> 統一)への対応: entities_of_type(Point)がそのままだと、以前は型で
> 自動的に分かれていた「有限点」と「無限遠点(旧Direction)」が
> 一緒くたに返ってしまう。中点・外接円・垂線/平行線の"点"引数などは
> 元々ずっと有限点だけを候補にしてきた(Midpoint(A, 無限遠点)や
> Circumcircle(A, B, 無限遠点)は退化していて意味がない)ため、
> Point型を要求する呼び出しではここで無限遠点を明示的に除外し、
> 型撤廃前と全く同じ候補プールを保つ。

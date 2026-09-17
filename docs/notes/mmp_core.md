# mmp_core(図形の表現)の設計ノート

`src/mmp_core/` のソースコメントから移した、設計の経緯・実測・直したバグの記録。
コードには「今どう動くか・なぜそうするか」だけを残し、「どうしてそうなったか」はここに置く。
引用は移した時点の原文のままなので、ファイル名や数値(`NN/96` など)は当時のもの。

## 目次

- [Direction / Circle / Angle 型の撤廃](#direction--circle--angle-型の撤廃)
- [線束の複比 CrossRatioOfLines](#線束の複比-crossratiooflines)
- [第2交点・根軸を定理ではなく作図プリミティブにした理由](#第2交点根軸を定理ではなく作図プリミティブにした理由)
- [merge_generation](#merge_generation)
- [却下済みの二次曲線ペアのキャッシュ](#却下済みの二次曲線ペアのキャッシュ)
- [型インデックスと type_generation(書き込みの4ゲートウェイ)](#型インデックスと-type_generation書き込みの4ゲートウェイ)
- [退化グループによる熱ボーナス](#退化グループによる熱ボーナス)
- [決定性: 反復順序](#決定性-反復順序)
- [EntityOrigin(誰が作ったか)](#entityorigin誰が作ったか)
- [original_definition と証明の出どころ](#original_definition-と証明の出どころ)
- [熱量の式の集約](#熱量の式の集約)
- [一意性の局所伝播で見つかったバグ(共有点の数え間違い)](#一意性の局所伝播で見つかったバグ共有点の数え間違い)
- [複比の一意性(透視射影不変性の逆)](#複比の一意性透視射影不変性の逆)
- [数値評価で直した退化入力と panic](#数値評価で直した退化入力と-panic)
- [予想(conjectures)の記録と評価](#予想conjecturesの記録と評価)
- [is_natural_incidence の判定基準](#is_natural_incidence-の判定基準)
- [数値チェックの座標割り当て(制約付きサンプリング)](#数値チェックの座標割り当て制約付きサンプリング)
- [numeric_plausibility_check の役割](#numeric_plausibility_check-の役割)
- [動点法の次数](#動点法の次数)
- [証明の抽出(raw_proof.rs / proof.rs)](#証明の抽出raw_proofrs--proofrs)
- [問い合わせ(query.rs)](#問い合わせqueryrs)
- [数値計算の退化入力(mmp_calculators.rs)](#数値計算の退化入力mmp_calculatorsrs)
- [その他(短く書き直したコメントの原文)](#その他短く書き直したコメントの原文)

## Direction / Circle / Angle 型の撤廃

`src/mmp_core/mod.rs` — `#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]` の直前にあったコメント:

> 2. 図形の種類
>
> EntityType::Direction撤廃の経緯: 「方向」はかつて独立した型として
> 存在したが、実体としては常に「無限遠直線L∞(line_infinity)上の点」
> (link_logical_incidenceで接続されたPoint)そのものだった。これが独立した
> 型タグとしても存在していたことが、平行な2直線をIntersectionしてしまうと
> (常にPoint型で作られる)本物のDirection型の実体と統合しようとして型が
> 混ざる、という実際のバグ(triangle_centersプリセットでの自由探索中に
> 発見)の温床になっていた。ユーザー提案「directionはL∞上にあるという
> 条件が付与されたPoint型のオブジェクトで、検索もL∞上の点を探せばよい」
> を型システムのレベルで徹底し、Directionという型タグ自体を廃止した――
> 「無限遠点かどうか」はもう型ではなく、L∞へのincidence(is_connected)
> という構造的事実だけで表現される。これにより上記の型混同はそもそも
> 起こりようがなくなった(action_space.rs::entities_of_typeがPointの
> 候補プールからL∞に繋がる点を明示的に除外しているのは、この設計の
> 一部として「有限点だけを候補にしたい」既存の意図を保つため)。
> EntityType::Circle撤廃の経緯: 円は古典的に「円周点(circular points at
> infinity) I=(1,i,0), J=(1,-i,0) を通る二次曲線」として特徴づけられる
> (実際、外接円Circumcircle(A,B,C)は今やConicThrough5Points(A,B,C,I,J)と
> 全く同じ計算で作られる――eval.rs参照)。EntityType::Directionの撤廃と
> 全く同じ理由で、「円かどうか」を独立した型タグで持つのではなく、
> I,Jへのincidence(is_connected)という構造的事実だけで表現することにした
> (apply_trivial_relationsがCircumcircle生成時にI,Jへのlink_logical_incidenceを
> 張る)。これによりpropagate_circle_uniqueness(円は3点で一意という特別扱い)も
> propagate_conic_uniqueness(二次曲線は5点で一意)へ統合できた――円どうしが
> 実点3点を共有していれば、構造的に共有しているI,Jの2点と合わせて常に5点
> 共有になるので、特別扱いなしに同じ規則から「円は3点で決まる」が導かれる。
> EntityType::Angle撤廃の経緯: 有向角AnglePair(D1,D2)の数値評価は既に
> 「無限遠直線上の4点I,J,D1,D2の複比」として実装されていた(circ_i/circ_jの
> ドキュメント参照)――つまり角度は数値的には最初からただのScalar(複比値)
> だった。EntityType::Direction/Circle撤廃と全く同じ理由で、この事実を
> 型システムにも反映し、AnglePairの結果もEntityType::Scalarにした
> (Definition::AnglePair自体は2引数のまま残す――CrossRatioへの書き換えは
> せず、あくまで「この構成が作る実体の型タグ」だけを変える、Circumcircleと
> 同じ最小限のアプローチ)。有向角の加法性・交替律・二等辺三角形の底角
> といった定理は、角度どうしのIdentical比較でしか使われておらず、角度値の
> 向き(flip)の一致判定(logic_core.rs::apply_conclusions/is_already_proven)は
> 実はEntityTypeではなくFlipStates(allow_flipで"AnglePair"ターゲットの
> DefinedByだけが populate する、文字列ベースで既に型非依存な機構)で
> 完結していたため、型タグの撤廃で追加の分岐は一切必要なかった。

`src/mmp_core/mod.rs` — `pub circ_i: ClassId,` の直前にあったコメント:

> 円周点(circular points at infinity) I, J。有向角AnglePair(D1,D2)を
> 「無限遠直線上の4点D1,D2,I,Jの複比」として扱うための固定参照点。
> ユーザー提案「有向角を複比として扱う」への対応で、AnglePairの数値評価
> (eval.rs)がこの2点とcalc_cross_ratioを使うように変更されている。
> I,Jは古典的に(1,±i,0)(iは虚数単位)で、この複比 (I,J;D1,D2) は
> Möbius変換の比として D1→D2→D3 の加法性(掛け算則)・交替律
> (a/b=c/d ⟹ a/c=b/d)をそのまま満たすため、既存の「有向角の加法性」
> 「有向角の交替律」定理(AnglePairの値をIdenticalで比較するだけの
> 純粋に構造的な定理で、値の具体的な計算式には一切依存しない)は
> パターン・定理側を一切変更せずにそのまま複比としての意味を持つ。

`src/mmp_core/mod.rs` — `pub angle_generation: u64,` の直前にあったコメント:

> EntityType::Angle撤廃(このモジュールのEntityTypeドキュメント参照)
> により、有向角(AnglePair)は他の全てのScalar(長さ・積・複比等)と
> 同じEntityType::Scalarを共有し、type_generation[Scalar]も
> 共有するようになった。これをそのまま角度連鎖定理の自己束縛
> キャッシュ(logic_core.rs::identical_self_bind_angle_cache)の
> 無効化判定に使うと、無関係な長さ・積の新規生成のたびに角度側の
> キャッシュまで無効化されてしまい、統合前には無かったキャッシュ
> ヒット率の急落(=無関係イベントによる過剰な再計算)を招く
> (実測でベンチマーク合格率が69/96→57/96に悪化する回帰として
> 顕在化した)。そこでtype_generation[Scalar]はこれまで通り
> (他の消費者が依存する「全てのScalarの変化で必ず上がる」という
> 健全性は崩さず)残したまま、「実際に角度(AnglePair)が絡む変化か
> どうか」だけを追跡する専用カウンタを別途持つ。plain_scalar_
> generationはその裏返し(角度以外のScalarの変化だけを追跡する)で、
> 角度側と対称にキャッシュを分離することで、非角度の自己束縛
> クエリが逆に角度側の変化で無駄に無効化されるのも防ぐ。
> note_type_changedと同じ4つのゲートウェイ(create_entity/
> merge_entities/insert_memo。link_logical_incidenceは対象外――
> 接続関係の追加はEntityType::Scalarの「代表元集合」自体を
> 変えないため、この2カウンタが守る自己束縛候補プールには無関係)
> だけがこれを更新する。

`src/mmp_core/mod.rs` — `egraph.link_logical_incidence(egraph.circ_i, egraph.line_infinity);` の直前にあったコメント:

> EntityType::Direction撤廃に伴うFIX: I,Jは同次座標のz成分が0
> (=無限遠直線L∞上の点)という意味で、これまでDirectionという型タグで
> それを表現していた。型を撤廃した今、この事実は他の全ての方向と
> 同じくlink_logical_incidenceによるL∞への明示的な接続で表現する
> 必要がある(ConstantHomogeneousのapply_trivial_relationsには
> これに対応する分岐が無いため、ここで直接張る)。

`src/mmp_core/mod.rs` — `self.link_logical_incidence(new_id, self.circ_i);` の直前にあったコメント:

> EntityType::Circle撤廃(円周点I,Jを通るという条件で
> 「円かどうか」を判定する、mmp_core/mod.rs::EntityTypeの
> ドキュメント参照): 外接円は今やConicThrough5Points(p1,p2,p3,I,J)
> と全く同じ計算(eval.rs::Definition::Circumcircle参照)で
> 作られているので、その事実を構造的にも表現しておく。これにより
> propagate_conic_uniquenessが「実点3つ共有」を自動的に
> 「5点共有(実点3つ+I+J)」として扱え、円専用の特別扱いが
> 不要になる。

`src/mmp_core/congruence.rs` — `EntityType::Scalar => {` の直前にあったコメント:

> 「方向」はもはや独立したEntityTypeではなく、L∞
> (line_infinity)にlink_logical_incidenceで接続しているだけの
> ただのPointである(EntityType::Direction撤廃、
> ユーザー提案「directionを検索するときもL∞上の点を探せば
> よい」を型システムのレベルで徹底した)。そのためこの分岐は
> 単純にEntityType::Pointだけを見ればよく、以前のように
> 「PointとDirectionをここでは同じに扱う」という特別扱いの
> コメントも不要になった。
> スカラー(複比)の一致から、点の一致を導く。
> propagate_cross_ratio_uniqueness のドキュメント参照。

`src/mmp_core/congruence.rs` — `fn propagate_line_uniqueness(&mut self, line: ClassId) -> bool {` の直前にあったコメント:

> 「直線の一致条件」の局所伝播版。
> line 自身が乗っている点(局所・少数)だけを見て、それらの点が他に
> 乗っている直線との共有点数を調べる。全直線を舐めない。
>
> 「方向」はEntityType::Directionという独立した型ではなく、L∞
> (line_infinity)にlink_logical_incidenceで接続しているだけの
> ただのPointなので(EntityType::Direction撤廃)、ここでPoint以外を
> 特別扱いする必要はない。これにより「2直線が1点を共有しかつ方向が
> 同じなら同一直線」という以前の特別扱い(same_dir)は、単に
> 「無限遠直線上の共有点も含めて2点共有」という同じルールに統合される
> (平行なだけの別々の直線は無限遠点1つしか共有しないので誤ってマージ
> されない。同一直線は通常の点+無限遠点の2つを共有するので正しく
> マージされる)。

`src/mmp_core/congruence.rs` — `fn propagate_conic_uniqueness(&mut self, conic: ClassId) -> bool {` の直前にあったコメント:

> 「二次曲線の一致条件」の局所伝播版。propagate_line_uniquenessと
> 全く同じ発想だが、直線が2点で一意に決まるのに対し二次曲線は
> (一般の位置にある)5点で一意に決まるため、しきい値が2→5になる。
>
> EntityType::Circle撤廃の経緯(mmp_core/mod.rs::EntityTypeのドキュメント
> 参照)で、旧propagate_circle_uniqueness(円は3点で一意という特別扱い、
> しきい値3)をこの二次曲線版(しきい値5)へ統合した。円どうしが実点を
> 3つ共有していれば、円は構造的に必ずI,Jにもincidenceで繋がっている
> (apply_trivial_relationsのCircumcircle分岐)ため、共有点数は自動的に
> 3+I+J=5になり、特別扱いなしに同じ規則から「円は3点で決まる」が導かれる
> (非circleな一般の二次曲線どうしが3点だけ共有していても、5点未満なので
> 誤ってマージされない――旧実装は"円"という前提を暗黙に置いていたため、
> もし将来3点だけ共有する非円の二次曲線が現れたら誤マージし得た)。
>
> HAGeo-409ベンチマークの調査で判明した問題への対応: 例えば
> Circumcircle(A,B,C)とCircumcircle(A,B,D)がどちらも「A,B,C,Dの4点が
> 乗っている」ことまで構造的に分かっていても、この伝播が無いと
> 永遠に別々の円エンティティのまま残り、(a)エンティティ数が無駄に
> 膨れ上がりマッチングを遅くする、(b)片方の円だけに乗っている
> 情報(接線・他の点の接続等)がもう片方には伝わらず証明が断絶する、
> という2つの問題を引き起こしていた。

`src/mmp_core/congruence.rs` — `if self.numeric_plausibility_check(existing_rep, point_rep, 2) == Some(false) {` の直前にあったコメント:

> 経緯: 以前はDirectionが独立したEntityTypeで、平行な2直線を
> Intersectionしてしまうと(常にPoint型で作られる)「Point型の
> 実体とDirection型の実体を統合しようとする」型混同が起こり
> 得た。ここに型不一致を弾くガードを試みたこともあったが、
> orthocenter/nine_point_fullがまさにこの「2直線が実は平行 ⟹
> 交点は無限遠点」という同一視に正しく依存していたため回帰した。
> ユーザー提案(directionはL∞上のPointとして扱い、検索も
> incidenceで行う)に沿ってEntityType::Directionを撤廃した今は、
> existing/point はどちらも常にPointであり、この種の型混同は
> 構造的に起こり得ない――ここで型を気にする必要が無くなった
> こと自体が、その設計変更の直接の効果。
> 健全性の穴の修正: propagate_line_uniquenessと同様、マージを
> 確定する前に数値的な裏付けを取る。

`src/mmp_core/eval.rs` — `Definition::AnglePair(d1, d2) => {` の直前にあったコメント:

> ユーザー提案「有向角を複比として扱う」への対応。
> D1,D2は既にDirectionOf/PerpDirectionOf経由で無限遠直線上の点
> (x,y,0)として評価されるので、同じく無限遠直線上の固定点である
> 円周点I,Jと合わせて4点(I,J,D1,D2)は常に共線 ―― 通常の
> CrossRatio(4点が共線な直線上の点)と全く同じcalc_cross_ratioの
> 式でそのまま複比 (I,J;D1,D2) が計算できる(「円も係数を射影空間の
> 点だと思えばOK」「線束も点とみなせる」と同じ発想を、方向にも
> 適用しただけ)。I,Jを基準(A,B)側に固定して測る(D1,D2を「動く」
> C,D側に置く)ことで、D1を基準としたτ_D2/τ_D1というMöbius変換上の
> 比になり、既存の「有向角の加法性」「有向角の交替律」定理
> (AnglePairの値をIdenticalで比較するだけの純粋に構造的な定理)が
> 求める代数法則(τ_a/τ_b * τ_b/τ_c = τ_a/τ_c、および
> a/b=c/d ⟹ a/c=b/d)をそのまま満たす。したがって定理・パターン
> 側は一切変更せずに、この評価式の変更だけで「有向角=複比」化が
> 完了する。

`src/mmp_core/eval.rs` — `Definition::Circumcircle(p1, p2, p3) => {` の直前にあったコメント:

> ユーザー提案(射影幾何への移植: circle型を完全にconic型にする):
> 円は古典的に「円周点(circular points at infinity) I,J を通る
> 二次曲線」として特徴づけられる。この事実をそのまま実装にし、
> 外接円の作図をcalc_circumcircle(円専用の3点公式)ではなく
> 「3点+I+Jを通る二次曲線」(calc_conic_through_5_points、
> シュタイナーの定理の接線版と全く同じ計算)として行う。
> これにより外接円もEntityType::Conic(6係数[A,B,C,D,E,F])として
> 一様に扱えるようになり(apply_trivial_relationsでI,Jへの
> incidenceを張ることで「I,Jを通る=円である」ことを構造的にも
> 表現する)、円専用のEntityType::Conicという型タグが不要になる。

`src/mmp_core/eval.rs` — `fn conic_definition_known_point(&self, conic: ClassId) -> Option<ClassId> {` の直前にあったコメント:

> EntityType::Circle撤廃(円もConic)により、以前ここにあった
> circle_definition_known_point/sample_point_on_circle(4係数専用、
> Vietaの公式)は不要になり削除した。円もConicThrough5Pointsと全く同じ
> 経路(conic_definition_known_point/sample_point_on_conic、6係数)で
> サンプリングされる――円は実質的に「実点3つ+I+Jという5点」なので、
> 同じVietaの理屈がそのまま平方根なしに使える(削除の前提となった
> 旧コメントが指摘していたcalc_circumcircleの係数並び順の食い違いも、
> Circumcircleの評価自体をcalc_conic_through_5_points経由に統一した
> ことで解消済み)。
>
> Circumcircle/ConicThrough5Pointsの定義から、その二次曲線に
> (定義上)乗っていることが保証されている点を1つ返す。Circumcircleの
> 3生成元はどれも本物の(L∞上ではない)点なので先頭でよいが、
> ConicThrough5Pointsの5生成元は(将来的にI,Jを直接生成元に含む
> 二次曲線が構築される可能性に備えて)L∞上の点(=無限遠点、z=0で
> Vietaのサンプリングに使えない)を避けて最初の"普通の"点を選ぶ。

## 線束の複比 CrossRatioOfLines

`src/mmp_core/mod.rs` — `CrossRatioOfLines(ClassId, ClassId, ClassId, ClassId),` の直前にあったコメント:

> ユーザー提案:「複比の透視射影不変性は、4点複比(A,B;C,D)→4直線の
> 複比(PA,PB;PC,PD)→4点複比(A',B';C',D')として扱えばマッチングが楽に
> なりそう」への対応。4本の共点(同じ点を共有する)直線がなす線束の複比。
> 「円も係数を射影空間の点だと思えばOK」と全く同じ発想で、直線の同次係数
> (a,b,c)を射影平面の"点"とみなせば、4直線が共点である(=双対平面上で
> 4つの係数点が共線)ときのCrossRatioと、通常のCrossRatio(4点の共線)は
> 全く同じ計算式(calc_cross_ratio)で扱える。これにより「透視射影不変性」
> という1つの巨大な定理(自由変数9個、天然のシードが無くdfs_capを
> 食い潰す)を、
>   定理A: 点の複比(直線L上のA,B,C,D) = 線束の複比(Oを通るPA,PB,PC,PD)
>   定理B: 線束の複比(Oを通るPA,PB,PC,PD) = 点の複比(直線L'上のA',B',C',D')
> という2つの小さな定理に分解できる――CrossRatioOfLines(PA,PB,PC,PD)を
> 共通の"ハブ"として経由することで、それぞれの定理が同時に束縛すべき
> 自由変数の数が減り(定理Aは実質O,A,B,C,Dの5点)、かつ定理Bの4直線は
> 「Oに繋がっている既存の直線」というConnected(O,_)由来の自然なシードで
> 絞り込める(定理Aが作ったPA..PDがまさにその候補になる)。

## 第2交点・根軸を定理ではなく作図プリミティブにした理由

`src/mmp_core/mod.rs` — `SecondIntersectionOfLineAndConic(ClassId, ClassId, ClassId),` の直前にあったコメント:

> ユーザー指示(「無闇に定理を追加してもノイズが増えるだけなので、
> ondemand作図やMCTSによる補助点作図の改善もすべき」)への対応:
> オリンピック幾何で頻出する「直線を延長して既存の円/二次曲線と
> 再び交わる点」という補助構成を、個別の定理ではなく汎用の作図
> プリミティブとして追加した。(known_point, line, conic)の3引数――
> known_pointは既にlineとconicの両方に乗っていることが前提の
> 「もう一方ではない方」の交点で、順不同にはならない(3者はそれぞれ
> 役割が違う)。計算はmmp_calculators::calc_second_intersection_of_
> line_and_conicのドキュメント参照(直線をP+tRとパラメータ化し、
> Pが根であることを使ってもう一方の根を斉次座標のまま求める)。

`src/mmp_core/mod.rs` — `RadicalAxis(ClassId, ClassId),` の直前にあったコメント:

> ユーザー指示(「円関連の作図(接線、交点が一つわかっている時に、
> もう一個の円と円、円と直線の交点を作図するなど)の方が、よりいろんな
> 結果を作れる」)への対応。2円の根軸(radical axis)。順不同。
> 2円が交わるならその2交点を通る直線であり、交わらなくても常に定義される
> (方冪が等しい点の軌跡)。計算は mmp_calculators::calc_radical_axis 参照。
> 「3円の根軸は1点(根心)で交わる」のように、根軸そのものが、すぐには
> 示しにくい結果を生む源になる。

`src/mmp_calculators.rs` — `pub fn calc_radical_axis(c1: &[ModInt], c2: &[ModInt]) -> Vec<ModInt> {` の直前にあったコメント:

> ユーザー指示(「円関連の作図(接線、交点が一つわかっている時に、もう一個の
> 円と円、円と直線の交点を作図するなど)の方が、よりいろんな結果を作れる」)への
> 対応その1: 2円の根軸(radical axis)。
>
> 円は「x²とy²の係数が等しくxyの係数が0」という特殊な二次曲線なので、
> 2つの円 c1, c2 を「二次の項が打ち消し合う」ように定数倍して引くと、
> 二次の項が完全に消えて1次式(=直線)だけが残る。これが根軸であり、
> 2円が交わる場合はその2交点を通る直線そのものになる。
>
> これを独立した作図プリミティブとして持つ意味は2つある:
>   (a)「一方の交点Pが既知のとき、もう一方の交点」を
>      SecondIntersectionOfLineAndConic(P, 根軸, c1) として、平方根を一切
>      使わずに斉次座標のまま作図できる(2交点は根軸上にあるため)。
>   (b) 根軸そのものが「3円の根軸は1点(根心)で交わる」のような、すぐには
>      示しにくい結果の源になる。
>
> 入力は calc_conic_through_5_points と同じ6係数[A,B,C,D,E,F]
> (Ax²+Bxy+Cy²+Dxz+Eyz+Fz²=0)。互換のため旧来の円4係数[A,D,E,F]も受ける。
> 二次の項が実際には消えない(=少なくとも一方が円ではない)場合は、
> 差が直線にならないので空ベクトルを返す。

## merge_generation

`src/mmp_core/mod.rs` — `pub merge_generation: u64,` の直前にあったコメント:

> 実際にunion-findの併合が起きるたび(merge_entities内で root1 != root2
> だった回数だけ)単調増加するカウンタ。logic_core.rs::MatchTaskが
> dfs_cap到達で再キューされる際、そのタスク専用のfailed_paths
> (このタスクの中でどのbind/flip_states状態が「これ以上進めない」と
> 分かったかのハッシュキャッシュ)を安全に持ち越せるかどうかの判定に使う。
> failed_pathsはget_rep()した後のClassIdをハッシュに含めているため、
> キャッシュを作った時点から1回でもマージが起きていれば、同じハッシュが
> 別の(今はマージにより到達可能になったかもしれない)状態を指してしまい
> 得る。そのため「保存時のこの値」と「再開時のこの値」が一致する場合
> だけ再利用し、1つでもずれていれば安全側に倒して空から作り直す。

## 却下済みの二次曲線ペアのキャッシュ

`src/mmp_core/mod.rs` — `pub rejected_conic_pairs: rustc_hash::FxHashMap<(usize, usize), u64>,` の直前にあったコメント:

> propagate_circle_uniqueness用の「却下済みペア」キャッシュ。
> キーは(小さい方の代表元インデックス, 大きい方の代表元インデックス)、
> 値はそのペアを数値的健全性チェックで却下した時点のmerge_generation。
> 円は直線よりも同一点集合上に多数の重複エンティティが積み上がりやすく
> (HAGeo-409ベンチマークで実測: ある問題では全円エンティティの100%が
> 統合されるべき重複だった)、あるペアが一度「共有点はあるが数値的には
> 別の円」と判定されても、そのペアの片方に別の(無関係な)点がマージ
> されるたびに(円自体のrepは変わっていなくても)再チェックされてしまい、
> 同じ却下を何度も繰り返すことがrealorthocenterで実測された(壁時計時間
> 4.5秒→17.5秒への劣化の主因)。マージが1件も起きていない間は再チェック
> しても結果が変わりようがないので、merge_generationが前回の却下時点から
> 変わっていなければ即座にスキップする。

## 型インデックスと type_generation(書き込みの4ゲートウェイ)

`src/mmp_core/mod.rs` — `pub type_index: rustc_hash::FxHashMap<EntityType, Vec<ClassId>>,` の直前にあったコメント:

> ユーザー提案(定理マッチングの最適化)への対応その1: EntityTypeごとの
> 生成済みエンティティID一覧のインデックス。create_entity内で追記するだけの
> 単調増加リストで、union-findのマージでは更新しない(吸収された側の
> ClassIdもそのまま残る)。そのため利用側は必ずget_rep()で正規化された
> 代表元だけを拾う(iter_reps_of_type参照)。
>
> 従来、logic_core.rs側の複数箇所(Identical/Connectedの両変数未束縛分岐、
> DefinedByの親変数も未束縛な場合のフルスキャン分岐)が「特定の型を持つ
> 代表元」を探すために self.egraph.entities を毎回全件ループしていた。
> 定理が増えるほどエンティティ数(補助図形)も増えるため、この種の
> フルスキャンのコストが線形に効いてくる。型ごとに索引を引けるように
> しておけば、目的の型のエンティティ数だけのスキャンで済む
> (特にCircle/Conicのような個体数の少ない型で効果が大きい)。

`src/mmp_core/mod.rs` — `pub type_generation: rustc_hash::FxHashMap<EntityType, u64>,` の直前にあったコメント:

> ユーザー提案(定理マッチングの最適化・案3→ゲートウェイ集約による
> リファクタリング)への対応: EntityTypeごとに独立した「この型に関する
> マッチング候補集合(候補エンティティ・接続関係・memo経由の到達可能性)が
> 最後に変化した世代」のカウンタ。logic_core.rs::MatchTaskのfailed_paths
> 持ち越し判定に使う――単一のグローバルmerge_generationだと「e-graphの
> どこかで1回でも変化が起きたか」しか区別できず、無関係な型の変化でも
> 全タスクのキャッシュを巻き添えで捨てていたため、型ごとに絞り込めるよう
> 分解した。
>
> この値を正しく保つには「マッチングに影響し得る構造
> (components/subobjects/uses/memo)を変更する操作を漏れなくここに
> 通知する」ことが不可欠で、実際に最初の実装では複数箇所を見落として
> (新規エンティティ生成、接続関係の新規追加、apply_congruence_closure内で
> 既存エンティティにmemoを事後登録するケースの3つ)HAGeo-409ベンチマークの
> 複数問題で回帰を起こした。そこで生の構造フィールドへの書き込みを
> create_entity/merge_entities/link_logical_incidence/insert_memoの
> 4つのゲートウェイ関数だけに集約し(この4つ以外がentities[..].components/
> subobjects/usesやself.memoに直接書き込むことは無い、という不変条件を
> 保つ)、それぞれの内部でnote_type_changedを呼ぶことで「この値を
> 更新し忘れる」余地を構造的に無くした。

`src/mmp_core/mod.rs` — `pub fn count_of_type(&self, ty: EntityType) -> usize {` の直前にあったコメント:

> このEntityTypeの実体数。
>
> logic_core.rs::estimate_cost の Connected(未束縛, 未束縛) 分岐が
> 「親の型がグラフに何個あるか」で見積もるために呼ぶ。estimate_cost は
> DFSの各ノードで残りパターンの数だけ呼ばれるホットパスなので、
> 以前のように毎回 entities を全走査すると、実体数が数百になる
> 自由作図後は見積もりだけで無視できない量になる。
> type_generation が動いていなければ前回の値をそのまま返す
> (返す値は全走査と完全に同じなので、探索の経路は一切変わらない。
> 実測でも simson / nine_point_full / orthocenter / bench_2012egmop1 の
> 消費仕事量が1ステップも変わらないことを確認済み)。

`src/mmp_core/mod.rs` — `fn insert_memo(&mut self, def: Definition, id: ClassId) {` の直前にあったコメント:

> self.memoへの書き込みを一箇所に集約するゲートウェイ。以前は
> create_entityとapply_congruence_closure(congruence.rs)の2箇所が
> それぞれ直接self.memo.insertを呼んでおり、後者(既存エンティティに
> 対して正規化後の定義を事後的にmemo登録するケース)がnote_type_changedの
> 呼び出し漏れの原因になっていた(HAGeo-409ベンチマークで実際に
> 回帰として顕在化)。memoへの新規登録は「このDefinitionから
> このエンティティへ到達できるようになった」という、defined_by_valid_nodes等の
> memoルックアップの結果を変え得る変化なので、登録したエンティティの
> 型を必ずnote_type_changedに通知する。

`src/mmp_core/congruence.rs` — `self.insert_memo(norm_def, u_rep); // 🌟 グローバルにも登録` の直前にあったコメント:

> ゲートウェイ集約(type_generationのドキュメント参照):
> 以前はここが直接self.memo.insertしており、
> note_type_changedの呼び出し漏れの原因になっていた
> (このエンティティは既存だがこの正規化後の定義では
> 初めてmemoに載る、というケースなので、他のタスクの
> memoルックアップ結果を変え得る)。insert_memo経由に
> 統一する。

## 退化グループによる熱ボーナス

`src/mmp_core/mod.rs` — `pub degeneration_groups: Option<crate::padic_eval::DegenerationRelations>,` の直前にあったコメント:

> ユーザー提案:「図形を退化させた時の振る舞いを観察して関連が深い
> オブジェクトを発見し、それをheatのボーナスに使う」への対応
> (padic.rs/padic_eval.rsのドキュメント参照)。既定ではNone(計算しない
> 限り一切のコストが無い)。discover_degenerate::compute_degeneration_groups
> で計算した結果をここへ差し込むと、bump_heat_bonusが同じグループの
> 他のメンバーにも(小さい)ボーナスを伝播するようになる。

`src/mmp_core/mod.rs` — `pub fn bump_heat_bonus(&mut self, id: ClassId, amount: f64) {` の直前にあったコメント:

> ユーザー提案:「同じ退化グループにあるかはすぐ判定できるはずだから
> それを用いてheatにボーナスすることを考えている」への対応。通常の
> heat_bonus加算をこの関数経由に統一し、degeneration_groupsが計算済み
> (Some)であれば、退化のもとで直接関連が観測された他のエンティティにも
> (割り引いた)ボーナスを伝播する(推移閉包は取らない、padic_eval.rs::
> DegenerationRelationsのドキュメント参照――union-findで推移閉包を
> 取ると異なる退化パターンの関係まで無差別に合併され、実測で明確な
> 悪化を引き起こしたため、直接観測された辺だけを使う設計にした)。
> degeneration_groupsがNone(既定、計算していない問題)の場合は従来通り
> entities[rep].heat_bonus += amountと完全に同じ挙動になり、このボーナス
> 伝播機構を使わない既存の全ての呼び出し元・全ての問題に一切の副作用が
> 無い。

## 決定性: 反復順序

`src/mmp_core/mod.rs` — `pub subobjects: Vec<ClassId>,` の直前にあったコメント:

> 以前は std::collections::HashSet<ClassId>(標準のRandomState、
> プロセスごとに異なるランダムシード)だった。重複除去自体は必要だが、
> その反復順序がプロセス起動のたびに変わってしまうため、これに依存する
> 局所伝播(propagate_line_uniqueness/propagate_point_uniqueness)や
> 定理マッチングの候補列挙の探索順序までプロセスごとに変わってしまい、
> 同じ問題・同じロジックでも実行時間が実行のたびに大きくばらつく
> (実測: miquelで0.35秒/1.05秒の二峰性)原因になっていた。挿入順を保持する
> Vecに変え、重複除去はlink_logical_incidence/merge_entities側で
> 明示的に行う(小規模なので線形探索で十分)ことで、探索順序を完全に
> 再現可能にする。

`src/mmp_core/congruence.rs` — `let mut merged_defs: Vec<Definition> = Vec::new();` の直前にあったコメント:

> FIX: definitionsも以前は std::collections::HashSet(標準の
> RandomState、インスタンスごとに異なるランダムな鍵)に溜めて、
> そのまま into_iter().collect() していた。
> LogicalComponent::subobjects が全く同じ理由で既にVec化されている
> (そちらのドキュメント参照)のに、同じ構造体のdefinitionsだけが
> 取り残されていた。
>
> 評価器は「コンポーネント内の全定義を、計算できるものが見つかる
> まで順に試す」ので、この並び順が変わると探索そのものが変わる。
> 実測でも nine_point_full を同じ引数で3回流すと、出力が
> 6560行 / 4832行 / 4832行 と実行ごとに別物になっていた。
> subobjectsと同じく挿入順を保持するVecに変え、重複除去は明示的に
> 行う(コンポーネントは小さいので線形探索で十分)。

## EntityOrigin(誰が作ったか)

`src/mmp_core/mod.rs` — `#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]` の直前にあったコメント:

> その図形を「誰が作ったか」。探索の途中で作られた補助構成が実際に
> 証明へ効いているのかを後から測るために、create_entity の時点で一度だけ
> 刻む(以後どれだけマージが起きても書き換えない)。
>
> 動機(ユーザー要望): オンデマンド作図(resolve_*_demands)と、定理の
> マッチングが DefinedBy パターンを満たすためにその場で作る図形は、
> どちらも「行き詰まったら図を増やす」という同じ賭けをしている。賭けが
> 当たっているのか(=作ったものが本当に証明に使われているのか)はこれまで
> 一切測れていなかった。名前の接尾辞 (Auto) は「定義からの自動派生」と
> 「マッチャのその場生成」の両方に使われていて事後には区別できないので、
> 作る側で印を付けるしかない。

## original_definition と証明の出どころ

`src/mmp_core/mod.rs` — `pub original_definition: Definition,` の直前にあったコメント:

> create_entity時に一度だけ設定され、以後マージが起きても絶対に
> 書き換えられない、そのスロット固有の不変な「元の定義」。components側は
> merge_entities で(生き残った側に)吸収された実体からstd::mem::takeされ
> 空になってしまうため、「このIDは元々どんな(引数の)定義で作られたか」を
> 後から(raw_proof::dump_raw_proofが)正確に復元するために必要。
> extract_proofの「DefinedBy(d1,d2,result)前提は、実は名前付き定理の合流の
> 産物であることが多いのに一律『定義から自明』と表示してしまう」問題を、
> 全合流履歴の総当たり列挙ではなく、この特定の(d1,d2)組み合わせを
> 最初に持っていた"元の"実体1つとその実体からresultまでの最短合流経路だけを
> ピンポイントで特定する形で解消するために導入した(ユーザー提案の
> 「証明の先頭からDPで証明木を構築する」方針への対応)。

## 熱量の式の集約

`src/mmp_core/mod.rs` — `impl GeoEntity {` の直前にあったコメント:

> 熱関連処理の統一(ユーザー要望「熱関連の処理をリファクタリングして整理」)。
> 以前は「base_importance + heat_bonus + uses.len()*0.5」という同じ式が
> calc_bind_heat/estimate_cost(logic_core.rs)とaction_space.rs::entity_weightの
> 計3箇所に、「base_importance + heat_bonus」(次数抜き)がmatch_identical_fact
> の自己束縛ソート/heat_capped_connected_candidates/match_connected_factの
> 局所スキャンソートの計3箇所に、それぞれ独立にコピーされていた
> (後者は前者から「次数の項だけ」意図的に省いた別の式で、単なる重複ではなく
> 実際に2種類の式が使い分けられている――この違いも含めてここに集約する)。
> DFSのbind順序付け・MCTSの行動サンプリング/報酬評価のどちらでも「何が
> 面白い図形か」を判定する箇所は、常にこの2メソッドのどちらかを呼ぶことに
> 統一し、式そのものを直接書く場所を無くす。

## 一意性の局所伝播で見つかったバグ(共有点の数え間違い)

`src/mmp_core/congruence.rs` — `let lines: Vec<ClassId> = self.entities[rep_id.0].components.first()` の直前にあったコメント:

> FIX: 点/方向が変化(他の点/方向とマージ)しても、それを
> 含む直線側の「直線の一致条件」判定は自動的には再トリガー
> されない(propagate_line_uniquenessは直線自身のrepが
> 変化したときしか呼ばれないため)。このため「2直線が
> 既に1点を共有していて、後から同位角判定などで方向まで
> 一致した」というケースで、方向の一致が確立された直後に
> 直線同士の合流だけが見逃されてStallする実例が
> orthocenter_altで見つかった(同位角による平行判定で
> Dir_Alt_A≡Dir_Line_AHが確立された直後、Alt_A≡Line_AHへの
> 合流だけが起きなかった)。この点/方向を含む直線それぞれ
> についてもpropagate_line_uniquenessを再実行することで
> これを修正する。

`src/mmp_core/congruence.rs` — `loop {` の直前にあったコメント:

> FIX: 共有点を数える前に、この直線上の点(無限遠点を含む)どうしの
> 「2直線の交点の一意性」を先に局所的な不動点まで確定させておく。
> これをやらないと、本来は同一になるはずだがまだ別IDのままの2つ
> (例: 外心の候補O1とO2、あるいはまだ別々に導出された同じ方向)を
> 「別々の2つの共有点」と誤認し、無関係な直線を誤ってマージして
> しまうことがある(外心の証明で実際に発生した)。

`src/mmp_core/congruence.rs` — `let mut distinct_shared: Vec<ClassId> = Vec::new();` の直前にあったコメント:

> propagate_conic_uniquenessと全く同じ構造のバグ
> (ユーザー指摘「そもそも誤った結合は起こらないはず」への
> 対応): sharedはline自身の点として重複除去済みだが、まだ
> e-graph上で正式にマージされていない2つの異なる代表元が
> 実は同じ幾何学的な点を指している場合を区別できず、真に
> 相異なる共有点が実際には1点しかないのに2点と誤カウント
> され得る。1点だけの共有では直線の一意性を主張できない
> (直線は2点で決まる)ため、ここでも数値的に等しい代表元を
> 1つにまとめてから改めて閾値判定する。

`src/mmp_core/congruence.rs` — `loop {` の直前にあったコメント:

> propagate_line_uniquenessと同じ理由: 共有点を数える前に、この
> 二次曲線上の点どうしの「2直線の交点の一意性」を先に局所的な不動点
> まで確定させておく。これをやらないと、本来は同一になるはずだが
> まだ別IDのままの2点を「別々の2点」と誤認し、共有点数を過小評価して
> 本来マージすべき二次曲線を見逃すことがある。

`src/mmp_core/congruence.rs` — `let mut distinct_shared: Vec<ClassId> = Vec::new();` の直前にあったコメント:

> 実際に発見されたバグ(ユーザー指摘「そもそも誤った結合は
> 起こらないはず」への対応): sharedは「conic自身の点として
> 重複除去済み」なだけで、まだe-graph上で正式にマージされて
> いない2つの異なる代表元が、実は同じ幾何学的な点(例:
> 「2本の高さの交点」として別々に構築された、同じ垂心H)を
> 指している場合を区別できない。この場合、真に相異なる
> 共有点は実際には5点未満なのに、5点以上あるかのように
> 誤ってカウントされ、本来は一意に定まらない(5点未満でしか
> 共有していない)2つの二次曲線を「同じ曲線だ」と誤って
> 提案してしまう(orthocenterで実際に観測: H_AltA_AltBと
> H_AltB_AltCが2重カウントされ、真の共有点はI,J,H,Hcの4点
> しかないのに5点と誤認された)。数値的に等しい(=同じ点の
> 可能性が高い)代表元どうしをここで1つにまとめてから、
> 改めて5点以上あるかを判定する――数が少ない(shared.len()
> が5前後)候補でしか実行されないため、O(shared.len()²)の
> numeric_plausibility_check呼び出しはコスト上無視できる。

## 複比の一意性(透視射影不変性の逆)

`src/mmp_core/congruence.rs` — `fn propagate_cross_ratio_uniqueness(&mut self, scalar: ClassId) -> bool {` の直前にあったコメント:

> 「2直線の交点の一意性」の局所伝播版。
> point(方向を含む)自身が乗っている直線(局所・少数)のペアについて、
> その交点が memo に既に登録されていないかをO(1)参照するだけ。全点を舐めない。
>
> 方向(Direction)は Definition::Intersection(line, 無限遠直線) ではなく
> Definition::DirectionOf(line) という別のDefinitionで登録されている
> (定理側のパターンを変えずに済ませるため、あえて既存の表現のままにしてある)。
> そのため、ペアのどちらかが無限遠直線のときは DirectionOf での読み替えも試す。
> 「複比の透視射影不変性の逆」。ユーザー要望で追加。
>
> 共線な4点の複比 (A,B;C,D) は、A,B,C を固定すると D の射影座標そのもの
> (D についての1次分数変換)なので、D について単射。したがって
>
>   (A,B;C,D) = (A,B;C,E) かつ A,B,C が相異なり、5点が同じ直線上 ⟹ D = E
>
> 既存の射影の定理5つのうち4つは「接続を前提にスカラーの等式を結論する」
> 向きで、逆向き(スカラーの等式から接続を結論する)はシュタイナーの定理の
> 逆しか無かった。ところが探索が見つけるのは共点・共線という接続の主張
> なので、証明に使いたいのはまさにこの逆向きで、実測でも複比の発見は
> 0/5しか証明できていなかった。これは比についての古典的な主張
> (メネラウス・チェバの逆)を射影的に言い換えたものでもある。
>
> dfs_matchの定理(TheoremDef)ではなく合同閉包の局所伝播として書いて
> ある。CrossRatioはV4クライン群 {(a,b,c,d),(b,a,d,c),(c,d,a,b),(d,c,b,a)}
> で正準化される(normalize_definition参照)ため、「3つが同じで1つだけ
> 違う」がどのスロットに現れるかが ClassId の大小で変わってしまい、
> パターンで書くと4通りに分裂して探索コストも4倍になる。ここなら軌道を
> 自分で回して照合できる。HarmonicConjugateOf/PerpDirectionOf の対合性を
> apply_trivial_relations に構造的に登録しているのと同じ方針。

## 数値評価で直した退化入力と panic

`src/mmp_core/eval.rs` — `let result = mmp_calculators::calc_line_through_points(&v1, &v2);` の直前にあったコメント:

> FIX: calc_line_through_pointsは2点の座標が数値的に一致した場合
> (退化)にvec![]を返す。以前はここでSome(vec![])として素通りさせて
> しまい、この空Vecが後続のIntersection計算等でcross_productに
> 渡されてindex out of bounds panicを起こしていた(orthocenter --mctsで
> 実際に発生)。to_optionで確実にNone(計算不能)に変換する。

`src/mmp_core/eval.rs` — `Self::to_option(mmp_calculators::normalize(&[v[1], -v[0], ModInt::new(0)]))` の直前にあったコメント:

> 直線 ax + by + c = 0 の方向ベクトルは (b, -a)。
> FIX: 以前は2要素[dx,dy]のまま返していたが、これだと
> 「無限遠直線との交点」として計算される3要素の同次座標
> (Intersection(Line_infinity, l) = cross_product([0,0,1], v))
> と要素数が食い違い、数値サニティチェック(numeric_plausibility_check)
> が両者を「別の値」と誤判定してしまう(この2つは設計上、
> 常に同じ点=方向を表すべきもの)。z成分0を付けた3要素の
> 同次座標として統一する。
> FIX: lが無限遠直線[0,0,c]だと(v[0]=v[1]=0のため)
> 結果が[0,0,0]という「方向として定義不能」な退化値になる。
> to_optionで全成分ゼロもNoneとして弾く。

`src/mmp_core/eval.rs` — `mmp_calculators::calc_squared_distance(&v1, &v2)` の直前にあったコメント:

> FIX: calc_squared_distanceは同次座標のz成分が0(無限遠点)だと
> 内部の除算(ModInt::inv())でpanicしていたため、Option<ModInt>を
> 返す実装に変更済み(mmp_calculators.rs参照)。ここではmapで
> Vec<ModInt>形式に包み直すだけ。

`src/mmp_core/eval.rs` — `fn to_option(v: Vec<ModInt>) -> Option<Vec<ModInt>> {` の直前にあったコメント:

> calc_*系のヘルパーが退化した入力(座標が数値的に一致した2点、
> 平行な2直線等)に対して返す空Vecを、evaluate_definition全体で一貫して
> 「計算不能」(None)に変換する。これが無いと、空Vecがあたかも妥当な値
> であるかのようにSome(vec![])として上流(呼び出し元のevaluate_node_inner
> のキャッシュ・そのまた呼び出し元)に伝播してしまい、後続の計算
> (cross_product等の固定インデックスアクセス)でindex out of bounds
> panicを起こす(orthocenter --mctsで実際に発生した既知のバグ。
> mmp_calculators.rs側でもcross_product/calc_squared_distance/
> calc_tangent_line自体に長さ・ゼロ除算ガードを追加したが、それとは
> 独立に、ここでも「空=計算不能」という変換を一箇所に集約しておく)。
>
> FIX: 長さが正しくても全成分が0の同次座標(例: cross_productが
> 「数値的に同一な2直線」の交点を求めようとした時に返す[0,0,0])は、
> 射影平面上の点として定義不能(P^2の点は少なくとも1成分が非ゼロで
> なければならない)なのに、以前は「空ではない」という理由だけで
> Some([0,0,0])として素通りしていた。normalize()は全ゼロ入力を
> そのまま(全ゼロのまま)返す実装なので、cross_product/normalizeの
> 長さガードだけではこのケースを検出できない。ここで全ゼロも
> 明示的にNoneとして弾く(orthocenter --mctsの問題設定自体に退化の
> 原因があるわけではなく、MCTSが生成する補助構成が、探索中はまだ
> 記号的にマージされていない2つの直線/点をたまたま同じ数値サンプルで
> 数値的に一致させてしまうケースがこれに当たる)。

`src/mmp_core/eval.rs` — `if p.len() < 3 || p[2].0 == 0 { return None; }` の直前にあったコメント:

> 2直線が(この標本で)平行だと交点は無限遠(z=0)にあり、下の
> x/z で ModInt の 0 除算になってプロセスごと落ちる。交点の需要の候補が
> 「垂線とその足の直線」だけだと平行になり得ないので表に出ていなかったが、
> 候補を定理のパターンから広げる実験(atlas §05)で7問が落ちて発覚した。
> 有限の交点が無いなら次数は測れない。

## 予想(conjectures)の記録と評価

`src/mmp_core/eval.rs` — `pub(crate) fn log_conjecture_candidate(&self, a: ClassId, b: ClassId, hypothesis: &str) {` の直前にあったコメント:

> 🔮 CONJECTURE: 記号的にはまだ別物として扱われている2つの図形a, bが、
> 独立にランダムサンプリングした座標の下で数値的に一致してしまった
> (LineThroughPointsの2点が同一点になった/Intersectionの2直線が
> 同一直線になった)ことを目立つ形でログに残す。
>
> 独立一様分布(法998244353)からサンプリングした2つの値が偶然一致する
> 確率は約10億分の1なので、単発の観測でもほぼ確実に偶然ではなく、
> a と b の間に(まだ証明されていない)何らかの構造的な同一性が
> 実在することを強く示唆する(Schwartz-Zippel補題の逆読み)。
> これは証明ではなく、あくまで「調べる価値の高い予想」の提示に過ぎない
> ―― 経路によっては数値的に偶然近い値になるだけの見せかけの一致も
> 理論上あり得るため、実際に証明したい場合は改めてtrials回数を
> 増やした再現確認や、記号的な証明の探索が必要になる。
> pub(crate)化: 数値評価が独立に見つけた偶然の一致だけでなく、
> logic_core.rs側の「仮説駆動の定理プロービング」(BlackboardEngine::
> probe_conjecture)が見つけた"条件付きの"発見も、同じconjectures
> マップ・同じ重複排除ロジックに乗せたい(2種類の発見経路を別々の
> 仕組みで管理すると、process_pending_conjectures側の評価・報告が
> 二重化してしまう)ため、クレート内限定で公開する。

`src/mmp_core/eval.rs` — `let mut map = self.conjectures.borrow_mut();` の直前にあったコメント:

> 同じペアは観測のたびに(場合によっては数百回)何度も検出される
> (orthocenter --mctsの実測で1回の実行あたり最大2000回超)。コンソールを
> 埋め尽くさないよう、ログ出力は初回だけにし、以降はconjecturesマップの
> occurrencesカウンタを静かに増やすだけにする(BlackboardEngine側の
> process_pending_conjecturesが、蓄積されたこの情報を後でまとめて処理する)。
>
> FIX: union-find(get_rep)は経路圧縮やマージにより、同じ「論理的な
> 実体」(例: H_AltA_AltBという交点)の代表元ClassIdが実行時間の経過で
> 変わり得る。以前は単純にrep_a.0/rep_b.0そのものをキーにしていたため、
> 代表元が変わるたびに全く同じ論理的関係が新しいキーとして再登録され、
> 実測でorthocenterの中心的な予想(H_AltA_AltB≡H_AltB_AltC)が
> "1つの関係"ではなく約800個の別々のエントリとして蓄積されてしまう
> 深刻な重複が発生していた。ここで、既存キーをCURRENT get_repで
> 再解決した結果が今回のキーと一致するものが無いか線形探索し、
> 見つかればそのエントリを現在のキーへ付け替えて更新する
> (マップは論理的に別個な関係の数だけ、通常は数十件以内に収まるので、
> この線形探索のコストは無視できる)。

`src/mmp_core/eval.rs` — `pub fn absorb_conjectures_from(&self, other: &EGraph) {` の直前にあったコメント:

> 使い捨てクローン(MCTSのsim_egraph等)側で検出された予想候補を、
> 実際の(現実の)EGraphの予想マップへ合流させる。
>
> 背景: EGraph全体をクローンするとconjectures(RefCell)の中身も
> そのまま複製されるが、これは複製先(独立したRefCell)であり、複製元とは
> 一切共有されない。MCTSは1シミュレーションごとに使い捨てのsim_egraphを
> 作り、その中でapply_congruence_closureを回すため、log_conjecture_candidate
> がそこで検出した予想はシミュレーション終了時にsim_egraphごと丸ごと
> 破棄され、現実のegraph側には一切反映されないまま失われていた
> (実測: 1回の実行で"初回検出"ログが900件超出ても、実際に現実の
> マップに記録され後続処理されたのはそのうち1件だけ、という深刻な
> 取りこぼしが起きていた)。
>
> ここでは、クローン側で新しく作られた実体(=現実のegraphにはまだ
> 存在しないClassId、シミュレーション内でしか意味を持たない補助構成)を
> 参照する予想は除外し、両方の実体が現実のegraphにも実在するものだけを
> 合流させる(存在しない実体へのheat_bonusフィードバックは意味を
> 持たないため)。合流時は現実のegraph側の"今の"代表元で正規化し直す
> (log_conjecture_candidateの重複排除ロジックと同じ理由)。

`src/mmp_core/eval.rs` — `pub fn process_pending_conjectures(&mut self, target: &Option<(String, Vec<ClassId>)>) -> ` の直前にあったコメント:

> log_conjecture_candidateが蓄積した「証明されていないが数値的根拠の
> ある予想」を処理する。まだ評価していない予想それぞれについて
> estimate_conjecture_valueで(使い捨てクローン上で)価値を見積もり、
> 一定以上の価値があれば、その予想が指す2つの実体のheat_bonusを引き上げて
> 以後のDFS/MCTS探索がそちらを優先的に調べるよう仕向ける。現実のegraphの
> 証明状態(union-find/memo/facts)は一切変更しない、あくまで優先度付けの
> ヒント。
>
> 元々BlackboardEngine側にあったが、MCTS(mcts.rs::run_step)からも
> 自分自身が発見した予想を同じrun_step呼び出しの中で即座に評価・反映
> (以後の同じ呼び出し内のシミュレーションのentity_weightに直結)したく
> なったため、BlackboardEngineを介さずEGraph単体で完結するようここに
> 移した。BlackboardEngine::process_pending_conjecturesは薄い委譲に
> なっている。
>
> 組み合わせ爆発対策:
> 1. 予想ごとの評価はestimate_conjecture_value側で合同閉包1回だけの
>    浅い見積もりに固定し、定理マッチングや「予想の予想」への再帰的な
>    連鎖は一切行わない。
> 2. 同じ(a,b)ペアは(何度観測されても)ConjectureEntry.testedにより
>    一度しか評価しない。
> 3. 呼び出し1回あたりに新規評価する予想の数をMAX_PER_CALLで絞り、
>    大量の予想が一度に湧いても評価コストが1呼び出しに集中しないように
>    分散させる(mainループの毎イテレーション、及びMCTSの各run_step内で
>    複数回呼ばれる想定)。

`src/mmp_core/eval.rs` — `pub fn detect_cross_ratio_coincidences(&self, new_id: ClassId) {` の直前にあったコメント:

> ユーザー提案:「複比同士の関係式からconjectureを発行して、そこから
> 定理適用の形を見つける」への対応。新しく作られた複比エンティティ
> new_idの値を、既存の他の全ての複比エンティティと(1回の乱数サンプルで)
> 数値的に比較し、値が一致するものがあればlog_conjecture_candidateで
> 予想として記録する(既存のprocess_pending_conjectures/heat_bonus
> フィードバック機構にそのまま乗る――現実の証明状態は一切変更しない
> 安全な拡張)。
>
> なぜ「比例」ではなく「等値」判定か: 複比の評価値は[k, 1, 1]という
> 形で、第1,2成分が常に1に固定されているため、通常の点/直線のような
> 射影的スケール不変の比例判定は不要で、k自体の値がそのまま複比の値
> そのもの(Identical(CrossRatio1, CrossRatio2)が意味したいのはまさに
> この値の一致)。

## is_natural_incidence の判定基準

`src/mmp_core/eval.rs` — `pub(crate) fn is_natural_incidence(&self, point: ClassId, curve: ClassId) -> bool {` の直前にあったコメント:

> 健全性の穴を塞ぐための数値的裏付けチェック。
>
> propagate_line_uniqueness / propagate_point_uniqueness の
> 「十分な数の接続関係を共有していれば同一とみなす」ショートカットは、
> 手作りの定理適用や素直な作図からしか合流が起きない前提では
> ほぼ常に正しいが、MCTSのような無方向な探索が持ち込む偶然の一致が
> 重なると、本来別々であるべき直線・点を誤って同一視してしまうことが
> 実際にあった(orthocenter問題で"垂線 ≡ 辺"のような偽の等式が生成され、
> 三角形が1本の直線に潰れる退化が発生した)。
>
> マージを確定する前に、FreePointにランダムな座標を割り当てた具体例で
> 両者が本当に等しい値になるかを検算し(Schwartz-Zippel的な考え方)、
> 明確に矛盾するならSome(false)を返して却下する。有向角(Ang90など)の
> ように座標を持たない記号的な定義しか無く判定不能な場合はNoneを返し、
> 呼び出し側は(従来通り)構造的な証明をそのまま信用してよい。
>
> これは証明の主経路に座標計算を持ち込むものではなく、あくまで
> 「安すぎて信用しすぎていたショートカットに対する事後検証」であり、
> このチェック自体が新しい事実を証明するわけではない。
> 直線/円curveへのpointの接続(incidence)が、curve自身の定義から
> 自然に(座標的に矛盾なく)従うものかどうかを判定する。
> 例: Line_AB=LineThroughPoints(A,B) に対する A の接続は、AがLine_ABの
> 定義の親そのものなので「自然」(常に座標的に正しい)。一方、
> Line_CAD=LineThroughPoints(C,A) に対する D の接続(miquel.rs等の
> 「DはこのCircle上にある」のような直接のlink_logical_incidence)は、
> Dがその定義の親に含まれないので「自然ではない」(座標的な裏付けがない、
> 構造だけの前提)。

`src/mmp_core/eval.rs` — `let mut memo = rustc_hash::FxHashMap::default();` の直前にあったコメント:

> FIX (HAGeo-409ベンチマークで判明、propagate_circle_uniquenessの
> 導入で顕在化): 以前はcurve_defsの「いずれか」の定義でpointが親なら
> 自然な接続とみなしていた。しかしpropagate_line_uniqueness/
> propagate_circle_uniquenessが「異なる点ペア(3点組)から作られた
> 同じ直線(円)」を正しく統合すると、その直線(円)のdefinitionsは
> 両方の点ペア(3点組)のUNIONになる――例えばLineThroughPoints(A,B)
> と後から合流したLineThroughPoints(A,F)が両方残る。ここで「いずれか」
> 判定をすると、Fは「line_ab上にある」という証明された(が本質的には
> A,Bという真の生成点に対しては従属した)事実によってではなく、
> 「LineThroughPoints(A,F)というdefinitionの親だから自然」という
> 理由でnatural=trueになってしまい、以後Fの数値サンプリングが
> 「line_ab上にある」という制約を無視した完全な乱数になる
> (実測: miquelでこれが原因でLineAB自身とその需要駆動の複製が
> 誤って「別の直線」と判定され、本来解けていた証明が解けなくなった)。
> 対策として、curve_defsの中から常に同じ1つ(canonical_shape_definition、
> 親のClassIdが辞書順最小のもの)だけを「真の自由な生成点の定義」として
> 採用する。後から合流した(=canonicalではない)definitionの親は、
> 直線/円が確かに通ることが証明された点ではあっても、それ自体は
> 従属点として引き続き制約付きサンプリング(sample_point_on_constraint)
> の対象にする――これは不健全化ではなく、むしろより正確な扱いになる
> (F自身の座標はどのみちline_ab上に拘束されるべきものなので)。
> 以前はここで canonical_shape_definition(親のClassIdが辞書順最小の
> 定義)という代理指標を使っていたが、それは「どの定義で評価されるか」
> とは無関係に決まるので、両者が食い違うと図が壊れる。
>
> 実際に踏んだ例(ユーザ報告): 「x3 = ABにAで立てた垂線」の上に
> 自由点Eを置くと、直線の一意性伝播が x3 と Line(A,E) を結合する。
> すると x3 の同値類の定義は {PerpendicularLine(l1,A), LineThroughPoints(A,E)}
> になり、代理指標は後者を選んで「Eはx3の生成点だから自然な接続」
> と判定し、Eを制約なしの乱数座標に置いていた。ところが評価器は
> PerpendicularLine 側で x3 を計算するので、E は x3 の上に無い。
> 結果、「Intersection(x3,l2) と E は一致するはずなのに数値が違う」という
> 健全性チェックの却下が数千件出て、何も推論できなくなっていた。
>
> 正しい基準は「その点無しで曲線を評価できるか」で、これは
> evaluation_requires_point がそのまま答える(全ての定義がその点を
> 必要とするときだけ true)。評価できるなら接続は本物の制約なので
> 制約付きサンプリングに回すし、評価できない(=循環する)なら
> 自然な接続として放っておけばよい。垂線の例では
> PerpendicularLine(l1,A) がEを必要としないので false → 正しく制約になる。
>
> この厳密な判定は発見モード側(padic_eval.rs::compute_incidence_constraints)
> では既に採用済みで、そちらのコメントに「証明エンジン側は回帰のため
> 元の緩い判定のままにしてある」と書いてあった。ここで揃える。

`src/mmp_core/eval.rs` — `pub(crate) fn evaluation_requires_point(&self, point_rep: ClassId, node: ClassId,` の直前にあったコメント:

> nodeを数値評価するのに point_rep の座標が不可欠かどうか。
>
> 経緯: is_natural_incidence(「pointのcurveへの接続は、curve自身の定義
> から自然に従うものか」)の判定を、ClassIdの小ささを代理指標にする
> canonical_shape_definition方式からこの直接判定に差し替えたとき、
> 一度は「32問の回帰が27/32 → 24/32に落ちた」と記録して見送っていた。
> しかしその測定は予算がまだ壁時計だった頃のもので、同じバイナリでも
> machineの混み具合だけで24〜29/32の間を揺れていた時期にあたる
> (logic_core::work_done のドキュメント参照)。仕事量予算にして測り直すと
> 44問で31/44・解けない13問の顔ぶれも変わらず、消費仕事量はむしろ0.6%
> 減った ― 回帰は無かった。現在は発見モードと証明エンジンの両方が
> この厳密判定を使う。
>
> 定義: nodeがpoint自身なら不可欠。そうでなければ「nodeの持つ全ての
> 定義が、その親のどれかを通じてpointを必要とする」ときに限り不可欠
> ――言い換えると、pointを含まない評価経路が1本でもあれば不可欠ではない。
> FreePoint/GivenPointのような親を持たない定義は「pointなしで評価できる
> 経路」そのものなので、そこで不可欠性は崩れる。
> 循環(定義が互いを参照する。証明が進んだe-graphでは普通に起きる)に
> 出会ったら「不可欠」側に倒す ―― 制約付きサンプリングが循環すると
> 座標割り当てそのものが解けなくなるため、そちらの方が安全。
> メモ化必須: 定義グラフはDAG(同じ部分構成が何度も参照される)なので、
> 素朴な再帰だと同じ節点を指数回訪れる。実測では、系統的作図後の
> e-graphでこの判定が事実上終わらなくなった。循環に当たって
> 「必要」と倒した結果はその経路に依存するのでメモ化しない。

## 数値チェックの座標割り当て(制約付きサンプリング)

`src/mmp_core/eval.rs` — `fn free_point_ancestors_ready(&self, id: ClassId, vars: &FxHashMap<String, ModInt>) -> boo` の直前にあったコメント:

> idの祖先(FreePoint)がすべてvarsに座標を持っているか。
> evaluate_node/evaluate_definitionはFreePointの座標がvarsに無くても
> (0,0)にフォールバックして黙って計算を続けてしまう(既存の呼び出しは
> 必ず全自由点の座標を事前に埋めてから呼ぶ前提のため、これが問題に
> ならなかった)。ここでの用途では「まだ座標が決まっていない自由点に
> 依存する評価」を(0,0)で誤魔化さず確実に弾く必要があるため、
> evaluate_nodeを呼ぶ前に明示的にチェックする。

`src/mmp_core/eval.rs` — `let mut stack = HashSet::new();` の直前にあったコメント:

> 以前は「全ての定義の全ての祖先に座標があるか」を見ていた。マージで
> 定義が同居した同値類(外接円が Circumcircle(A,B,C) と Circumcircle(B,C,D)
> を両方持つなど)では、どれか1つの定義で評価できれば十分なのに、同居する
> 別の定義がまだ座標の無い点を含むだけで「準備できていない」になっていた。

`src/mmp_core/eval.rs` — `fn sample_point_on_constraint(&self, fp: ClassId, vars: &FxHashMap<String, ModInt>, cache:` の直前にあったコメント:

> has_extraneous_incidence(fp)が真の自由点について、乗っていると
> 分かっている直線/円/二次曲線の上に乗るランダムな座標をサンプリングする。
>
> FIX (HAGeo-409ベンチマークで判明): 以前はfind_incidence_constraint
> (複数の「構造的前提」のうち最初の1つだけを返す)が選んだ制約だけを
> 満たす座標を割り当てていた。1点が2本以上の直線に乗っていること
> (例: 「Fはline_ab上」という前提に加え、後からpropagate_line_uniqueness/
> propagate_circle_uniquenessの需要駆動作図が「Fはline_bf上」という
> 別の前提を追加した場合)が構造的には両立するはずの状況でも、
> 最初に見つかった1本だけを満たす座標では、選ばれなかった側の直線とは
> 数値的に食い違ってしまい、本来正しいはずの合流をnumeric_plausibility_checkが
> 誤って却下する(実測: miquelでLine_B_F_(Demand)とLineAB自体が
> 誤って「別の直線」と判定された)。乗っている直線が2本以上あって
> どちらも(依存する自由点の座標が既に揃っていて)評価可能なら、
> 1本だけ選ぶのではなくその2本の交点を計算することで、両方の前提を
> 同時に満たす一意な座標が求まる(2直線の交点は常に一意なので、
> 3本以上あっても最初の2本だけで位置は確定し、残りは自動的に
> 満たされているはずの構造的主張と整合する)。

`src/mmp_core/eval.rs` — `let mut visited = HashSet::new();` の直前にあったコメント:

> FIX: このプロジェクトの問題設定は、しばしば「PはこのCircleに乗っている」
> 「D,A,Cはこの順に一直線上」のような前提を、実際の座標制約としてではなく
> link_logical_incidenceによる純粋に構造的な事実として直接与える
> (simson.rs, miquel.rs, two_circles_reim.rs、あるいはMCTSの調和共役点の
> 補助点P,Q等)。これは代数計算を避けるという設計方針そのものであり
> 正しい設計だが、そのようなFreePointに完全に無作為な座標を割り当てると、
> 本来満たすべき構造的な前提を満たさない具体例になってしまい、この
> 健全性チェックが正しいマージまで誤って却下してしまう
> (miquel/two_circles_reimで実際に発生した)。
> 以前はここでNone(判定不能)を返して検証そのものを諦めていたが、
> 現在はassign_free_point_coordsが、構造的前提を持つ自由点には
> その前提(直線/円の上にあること)を実際に満たす座標をサンプリングする
> (sample_point_on_line/sample_point_on_circle)。前提を満たす座標を
> 組み立てられなかった場合(未対応の前提や循環依存)だけ、従来通り
> Noneに倒す。

## numeric_plausibility_check の役割

`src/mmp_core/eval.rs` — `pub(crate) fn numeric_plausibility_check(&self, a: ClassId, b: ClassId, trials: usize) -> ` の直前にあったコメント:

> congruence.rs の propagate_line_uniqueness / propagate_point_uniqueness
> から、マージを確定する前のゲートとして呼ばれる(crate内の他モジュールから
> 呼べるようpub(crate)にしてある)。

## 動点法の次数

`src/mmp_core/eval.rs` — `pub fn measure_numerical_degree(&self, entity: ClassId, max_d: usize) -> Option<usize> {` の直前にあったコメント:

> Method of Moving Points(動点法)の「次数」を、実際に1つの自由点を
> 動かして数値的に測定する。以前のPython版にあったnumerical_degree/
> get_numerical_degreeに相当する機能で、mmp_math.rsには既に移植されて
> いた(matrix_rank_mod/get_numerical_degree)が、これまでどこからも
> 呼ばれていなかった(ユーザーが添付したMMP解説PDFの指摘で判明)。
>
> naive_degree的な「親の次数の単純和」という構造的な上界と違い、これは
> 実際にmover(祖先の自由点のうち1つ)を直線に沿って動かして複数の
> パラメータ値でサンプリングし、有限体上のランク判定(get_numerical_degree)
> で座標が実際に満たす有理関数の次数を検出する。これにより、
> Midpoint(中点)のような「構造的には2つの入力の合成に見えても、実際
> には次数が上がらない」操作を正しく低次数と判定できる一方、無関係な
> 2直線を繰り返し交差させるような操作は素直に次数が積み上がっていく
> ため、「次数が低い補助点を優先し、異常に高い補助点は避ける」という
> 判定に使える。
>
> mover(前提を持たない自由点祖先)が見つからない、あるいはいずれかの
> サンプルで評価不能(退化)だった場合はNone(次数不明)を返す――
> 呼び出し側は安全側に倒し、次数による足切りをしない扱いにすること。

`src/mmp_core/eval.rs` — `pub fn cached_degree(&self, id: ClassId, max_d: usize) -> Option<usize> {` の直前にあったコメント:

> measure_numerical_degreeのメモ化版。ユーザー要望: 「複比の透視射影
> 不変性のように関連するオブジェクトが非常に多い定理を、次数を
> ヒューリスティックに使って最適な順序でマッチングしたい」への対応で、
> logic_core.rs::match_defined_by_fact が「候補が多いDefinedByパターンの
> マッチ候補を、次数の低い(単純な)ものから先に試す」ために呼ぶ。
> 定理マッチングは同じエンティティに対して何度も呼ばれ得るホットパスなので、
> 一度測定した代表元についてはGeoEntity::degree_cacheに結果を記憶し、以後は
> 再測定しない(measure_numerical_degree自体は複数回のevaluate_node呼び出しと
> 有限体上のランク判定を伴うため、無条件に呼び続けると探索そのものより
> 重くなりかねない)。キャッシュは(ユーザー指摘によりheat_bonus/uses等と
> 同じ場所に置くよう変更した)代表元自身のGeoEntity::degree_cacheに持たせる
> ――もし後からその代表元がさらに別のクラスへ吸収されても、古いスロットの
> キャッシュ値がどこかから誤って読まれることはない(get_repは常に現在の
> 代表元を指すインデックスへ解決するため)。

`src/mmp_core/eval.rs` — `fn degree_of_homogeneous_samples(t_vals: &[ModInt], samples: &[Vec<ModInt>], max_d: usize)` の直前にあったコメント:

> ある同次座標ベクトルの時系列サンプル(t_valsに対応する各tでの値)から
> 次数を測る共通処理。ユーザー指摘:「円も係数を射影空間の点だと思えば
> OK」への対応で、成分数を2D点/直線の3に固定していた旧実装を一般化した。
> 同次座標なので絶対スケールに意味は無く、比だけが意味を持つ――
> 最後の成分を基準に他の全成分を割った値それぞれの次数を測り、その
> 最大値を返す(3成分の点(x,y,1)/直線(a,b,c)なら常にindex 2で割って
> いた旧実装と完全に後方互換。円の係数(A,D,E,F)のような4成分でも
> そのまま同じ枠組みで動く)。基準成分がいずれかのサンプルで0になって
> いたら(退化)測定不能としてNoneを返す。

`src/mmp_core/eval.rs` — `pub fn measure_group_degrees(` の直前にあったコメント:

> ユーザー提案: 「点の組A,Bについて、線分ABの次数がdeg(A)+deg(B)という
> 素朴な上界に比べて退化して小さい組は、何らかの隠れた定理・偶然の一致が
> 効いている兆候として『相性が良い』とみなせるのではないか」「多点での
> 評価を導入する」への対応。parents(2点でも3点でも4点でも良い)それぞれの
> 次数と、combineで組み合わせた結果(任意の成分数の同次座標ベクトル)の
> 次数を、同じmover・同じ他の自由点座標を使う1回の一貫したサンプリング
> パスで測定する。combineが返すベクトルは(円の係数(A,D,E,F)のような
> 4成分でも)degree_of_homogeneous_samplesにそのまま渡せる「射影空間の点」
> として扱う。
>
> なぜ一貫した測定が必要か: measure_numerical_degreeをparentsの数だけ
> バラバラに呼ぶと、それぞれが(祖先集合が異なれば)別のmoverを選んだり、
> 「他の」自由点に別々の乱数座標を割り当てたりし得るため、次数どうしを
> 単純に比較することに意味がなくなる(比較したいのは「同じ1つの動きに
> 対して、各parentがどれだけ複雑に動くか・組み合わせ結果がどれだけ
> 複雑に動くか」という相対関係であり、測定条件を揃える必要がある)。

`src/mmp_core/eval.rs` — `#[allow(dead_code)]   // まだ探索のヒューリスティックに繋いでいない` の直前にあったコメント:

> measure_group_degreesの3点(外接円)特化版。ユーザー提案の「これを
> 3,4点とかでやったら」への対応。円は4成分(A,D,E,F)の同次ベクトルだが、
> degree_of_homogeneous_samples側が成分数を問わず扱えるため、
> measure_line_affinityと全く同じ枠組みでそのまま使える。deg(A)+deg(B)+
> deg(C)という素朴な和に対しCircumcircle(A,B,C)の次数が退化して小さい
> 3点の組は、A,B,Cが常に(あるいは頻繁に)同じ円に乗るような隠れた
> 構造を持っている兆候として「相性が良い」とみなせる。

`src/mmp_core/eval.rs` — `pub fn measure_cross_ratio_affinity(&self, a: ClassId, b: ClassId, c: ClassId, d: ClassId,` の直前にあったコメント:

> measure_group_degreesの4点(複比)特化版。ユーザー提案:「複比の定理を
> 使うときは複比自体を次数を用いて生成に制限をかけて」への対応。
> calc_cross_ratioはScalar(k,1,1)を返す――第1,2成分が常に1という自明な
> (次数0の)定数なので、degree_of_homogeneous_samplesが最後の成分(常に1)
> で割ることは無害であり、実質的にkそのものの次数だけが結果を決める。
> 4点A,B,C,Dの次数の和に対し複比の次数が異常に高い(=無関係な4点の
> 組み合わせ)場合は生成自体を諦めるゲートに使う。

## 証明の抽出(raw_proof.rs / proof.rs)

`src/mmp_core/raw_proof.rs` — `use super::{EGraph, Justification};` の直前にあったコメント:

> raw_proof: e-graphの全マージ履歴(union-findの「証明の森」+ incidenceの
> 由来)を、人間が読むためではなくRust側で読み書きしやすい単純なテキスト
> 形式でダンプ/復元するモジュール。
>
> proof.rs::generate_proofは「目標から遡って実際に使われたステップだけ」
> を人間可読な文章として復元するのに対し、こちらは役割を2段階に分ける:
>   1. `EGraph::dump_raw_proof` — main.rsが実行のたびに、EGraphが保持する
>      証明関連情報(proof_edges, incidence_provenance, 全エンティティの
>      名前/型)を一切フィルタせず丸ごとテキストへシリアライズする。
>   2. `RawProof::parse` + `verify_identical` — 保存されたテキストを
>      (実行中のEGraphとは完全に独立に)読み込み直し、目標の等式から
>      遡ってTheoremのpremisesまで再帰的に検証することで、「本当に
>      最初から最後まで証明が繋がっているか、途中にLineUniqueness/
>      PointUniqueness/Trivialのような数値サンプリングや構造的近似だけに
>      頼った(=名前付き定理の連鎖による形式的な演繹ではない)ギャップが
>      眠っていないか」を監査する。
>
> なぜ2段階に分けるか: generate_proof/EGraph::proof_uses_numeric_shortcut
> は目標そのものの直接のマージ経路(explain_identicalが返す最上位の辺)しか
> 見ないため、Theoremの前提(premises)自体がさらに別のLineUniqueness等の
> ショートカットに依存しているケースを見逃しうる(実際にcircumcenterの
> 調査でこの種の深い依存が実在することが判明した)。ここではTheoremの
> premisesを再帰的に遡ることで、そのような深いところに隠れたギャップも
> 検出する。またテキストファイルとして永続化しておくことで、ソルバーを
> 再実行せずに後から(あるいは別プロセスから)同じ検証をやり直せる。
>
> フォーマット: 依存クレートを増やさないための独自の単純なTSV風形式。
> 各行はタブ区切りで、最初の数フィールドだけを厳密にタブ分割し、残りは
> 「行の残り全部」として1つのペイロード文字列に詰める(Theoremの前提や
> Congruenceの定義文字列にカンマ・コロン・括弧が出てきても、それらは
> ペイロード内部の記法であって行の区切りには使わないため安全)。
>   E\t{id}\t{original_name}\t{entity_type}
>   P\t{from_id}\t{to_id}\t{kind}\t{payload}      (proof_edges 1件)
>   I\t{a_id}\t{b_id}\t{kind}\t{payload}          (incidence_provenance 1件)
> kind は Given/Theorem/Congruence/LineUniqueness/PointUniqueness/Trivial の
> いずれか。payloadのkind別の中身は encode_justification を参照。

`src/mmp_core/raw_proof.rs` — `fn build_step(` の直前にあったコメント:

> 「深い証明」の中核: 1本の辺をDeepStepツリーへ再帰的に展開する。
> Given/Congruence/Trivialは子を持たない基底ケース。Theoremは
> premisesそれぞれを子ノードとして再帰的に展開する。LineUniqueness/
> PointUniqueness(「2点/2直線の共有」という構造的観察)は、共有点/
> 共有直線の由来(それ自身のマージ履歴 + incidence_provenance)を子
> ノードとして展開する――これにより「2直線が2点を共有」という
> ショートカット自体を、その根拠まで含めて完全に人間可読な形で
> 追跡できる(ユーザー指摘: 「共有によるマージも履歴に残せば証明を
> 完全に辿ることができないか」への直接の回答)。
>
> visitedで(種別タグ, 対象id列)の組を覚えておき、同じ前提/同じ辺を
> 何度も展開する無駄・循環を防ぐ(有向角の加法性/交替律など、多くの
> 定理が同じAng90絡みの前提を共有するため、これが無いと組み合わせ的に
> 膨れ上がる)。既に展開済みの箇所は、内容を繰り返さず「(既出、上記で
> 検証済み)」という参照だけの葉ノードにする。

`src/mmp_core/raw_proof.rs` — `if let Some(sources) = self.reverse_edges.get(&entity) {` の直前にあったコメント:

> FIX: 共有点/共有直線や、DefinedByの結果として参照されるClassIdは、
> 多くの場合そのマージの当時から今も代表元であり続けている側(=誰かが
> こちらへ吸収されてきた側)であるため、上のpath_to_root(前向き)だけ
> では何も出てこない(代表元自身はproof_edges上で"from"にはならない
> ため)。逆に「誰がこの実体に合流してきたか」をreverse_edgesで辿る
> ことで、例えば「別の方向が同位角判定などの定理チェーンでこの方向に
> 合流した」という、まさに知りたい経緯を拾い上げる(orthocenter_alt
> の調査でこの取りこぼしが実際に発覚した)。

`src/mmp_core/raw_proof.rs` — `fn build_structural_incidence_step(` の直前にあったコメント:

> 接続の由来が incidence に記録されていない場合の基底ケース。
>
> 以前はここで無条件に「作図時点の構造的な接続(定義から機械的に従う)」
> という葉にしていた。しかしそれが本当なのは「いま問われている直線・円
> そのものが、定義上その点を通る」場合だけで、実際には
> 「定義上その点を通る別の実体が、後からこの直線・円と合流した」
> ケースが混ざる。その合流こそが名前付き定理の仕事なので、基底扱いに
> すると証明の本体が丸ごと消える。
>
> orthocenter がまさにこれだった: 目標は結局
> 「H_AltB_AltC が Alt_A 上にある」に帰着するが、その接続の記録は無い。
> 定義上 H_AltB_AltC を通るのは Line_A_H_AltB_AltC で、これが
> 「同位角による平行判定」→「直線の一意性」で Alt_A と合流したことが
> 垂心定理の本体である。以前の extract_proof はこれを落としたまま
> 「7ステップ全て厳密」と報告していた。

`src/mmp_core/raw_proof.rs` — `fn build_result_ancestry_step(` の直前にあったコメント:

> DefinedBy前提(の結果として参照される実体)や、Identical(X,X)の
> ように「既に同じ実体を指している」premiseは、一見すると「定義から
> 機械的に従う自明な基底事実」に見えるが、実際にはその実体がこれまで
> 他の実体を(named theoremによって)吸収してきた結果として初めて
> 成立しているケースが多い(ユーザー指摘: orthocenter_altやsimsonの
> extracted_proofで、本来は円周角の定理・有向角の交替律が使われている
> はずの箇所が「定義より従う」で片付けられていた問題への対応)。
> この実体のmerge_ancestry_steps(合流してきた実体の履歴)を子ノードと
> して展開し、合流履歴が無ければ初めて「本当に自明な基底事実」として
> 扱う。
>
> 精度の限界: raw_proofは「どのDefinitionがどの合流によって
> 加わったか」までは記録していないため、この実体に合流履歴が複数
> あれば全て列挙する(この特定の引数の組と無関係な合流が混ざる
> 可能性はゼロではない)。それでも「定義から機械的に従う」と一律に
> 片付けるよりは遥かに正直な提示になる。

`src/mmp_core/raw_proof.rs` — `fn build_defined_by_step(` の直前にあったコメント:

> Definition単位の由来トラッキング(by_definition索引)を使い、
> DefinedBy前提を「resultの合流履歴を総当たりで列挙する」のではなく
> 「この特定の(引数の組)を最初に持っていた実体1つ + そこからresultへの
> 最短合流経路」だけにピンポイントで絞り込む。ユーザー提案(「証明の
> 先頭からDPで証明木を構築する」)への対応: 各実体の"元の定義"は
> create_entity時点で確定する不変情報なので、それを起点に「この定義は
> 最初どのIDに属していたか」を逆引きし、そこから目的のresultまでの
> 経路だけを辿ればよい。
>
> fact_typeが"DefinedBy:{type_name}"の形(target_type付き)でない場合
> (理論上は無いはずだが後方互換のため)は、従来通りbuild_result_ancestry_step
> (resultの合流履歴全体)にフォールバックする。

`src/mmp_core/proof.rs` — `pub fn proof_uses_numeric_shortcut(edges: &[ProofEdge]) -> bool {` の直前にあったコメント:

> 証明経路の中に、名前付き定理の連鎖(Given/Theorem/Congruence/Trivial)
> ではなく、局所伝播のショートカット(LineUniqueness/PointUniqueness)だけを
> 根拠にしたステップが含まれているかを判定する。
>
> 背景: propagate_line_uniqueness/propagate_point_uniqueness(「2直線が
> 十分な点/方向を共有していれば同一視する」「2直線の交点は一意」)は、
> マージを確定する前にnumeric_plausibility_checkで有限体上のランダムな
> 1点(または少数)による数値的裏付けを取ってはいるものの、これは
> あくまで「ランダムに選んだ具体例で矛盾が見つからなかった」という
> 確率的な根拠(Schwartz-Zippel的な議論)であり、名前付き定理を
> 前提から結論へ連鎖させる形式的な演繹ではない。この2つのJustification
> だけがそれに該当する(Congruenceは定義の構造的な一致、Trivialは
> apply_trivial_relations由来の定義から機械的に従う結合なので、
> どちらも数値サンプリングには依存しない)。
>
> MCTSのような無方向な探索は、この局所伝播だけを頼りに大量の補助構成を
> 経由して目標へ到達することがあり(実測: orthocenter_altで観測)、
> 個々のステップは(numeric_plausibility_checkにより)偽陽性ではなさそうで
> あっても、その経路全体を「形式的な証明」と呼ぶのは正確ではない。
> generate_proof/main.rsの🎉表示で、この違いを利用者に明示するために使う。

## 問い合わせ(query.rs)

`src/mmp_core/query.rs` — `pub fn count_neighbors_of_type(&self, id: ClassId, ty: EntityType) -> usize {` の直前にあったコメント:

> id に接続している実体のうち、型が ty のものの数(代表元で重複除去)。
>
> logic_core/cost.rs の estimate_cost が「片側だけ束縛された Connected」の
> 分岐数を見積もるために使う。以前そこは固定値だったため、接続先が2つの
> 点と12の点を区別できず、分岐の大きい Connected を安いものとして先に
> 選んでしまっていた(--profile の「枝の出どころ」で、全dfs呼び出しの
> 56〜76%がこの分岐から伸びていると判明)。
>
> matcher.rs の列挙と同じく subobjects を rep 化して数えるが、
> accept_point の Direction/Circle の特別扱いまでは見ない ― 見積もりは
> 並べ替えの順序さえ合っていればよく、厳密な一致は要らない。

`src/mmp_core/query.rs` — `pub fn is_angle_value(&self, id: ClassId) -> bool {` の直前にあったコメント:

> EntityType::Angle撤廃(mmp_core/mod.rs::EntityTypeのドキュメント参照)
> により、「この値が有向角(AnglePair)か、それとも別の(長さ・積・複比等の)
> Scalarか」はもう型では区別できない。代わりに、このIDが吸収してきた
> 全ての定義(merge_entitiesが両側の定義集合を合流させて蓄積する)の
> どれかがAnglePairかどうかで判定する――単にoriginal_definitionだけを
> 見ると、AnglePairで作られた実体が後からAng90/Ang0(GivenPoint定義)の
> ような非AnglePair起源の実体に吸収された場合を見逃す。
> logic_core.rsの自己束縛候補の絞り込み(角度追跡系定理の
> Identical(Ang1,Ang2)シードが、無関係な長さ・複比のScalarまで
> 候補に含めてしまわないようにする)で使う。

`src/mmp_core/query.rs` — `pub fn is_cross_ratio_of_lines_value(&self, id: ClassId) -> bool {` の直前にあったコメント:

> is_angle_valueと同じ発想: このScalarがCrossRatioOfLines(線束の複比)
> 由来かどうかを、吸収してきた定義のどれかがCrossRatioOfLinesかどうかで
> 判定する。「シュタイナーの定理の逆」のIdentical(CR_P1,CR_P5)自己束縛
> (logic_core.rs::match_identical_fact)が、長さ・積・点の複比まで
> 無差別に含む自己束縛候補プールに埋もれて無関係な値ばかり試すのを防ぐ
> ために使う(miquel_quadrilateralで実際に観測した、この自己束縛が
> dfs_capを繰り返し使い切る性能問題への対応)。

`src/mmp_core/query.rs` — `pub fn merged_free_points(&self) -> Option<(String, String)> {` の直前にあったコメント:

> 現在のE-Graphの有効な同値類と、その作図履歴・関係を出力する
> 自由点どうしが同じ同値類に入っていないか(= e-graphが崩壊して
> いないか)を調べ、崩壊していれば最初に見つけた組を返す。
>
> 自由点は互いに独立に置けるから自由点なので、正しい推論だけを積んだ
> 限り絶対に一致しない。一致しているなら、どこかの局所マージが無関係な
> 図形を結合して図全体が潰れており、その状態からは「矛盾から何でも
> 従う」形で任意の目標が"証明"できてしまう。
>
> これを入れた経緯: bench_2018chnwesternmop5 がまさにこの状態で
> 「証明完了」を出していた。5つの自由点A..Eのうち C と E が消え、
> 最終的な同値類が13個(正常に解ける問題は78〜362個)、生き残った
> スカラーに LengthSq(B,B)(=0)まで混ざっていた。目標が
> Identical(LengthSq, LengthSq) だったので数値サニティチェックは
> 走っていたが、潰れたe-graphの定義をたどって評価するため、
> そのチェック自体が騙されていた。
> 戻り値は見つかった2つの自由点の名前。merge_entities は吸収された側の
> name を std::mem::take で奪ってしまうので、崩壊を検出した時点で
> entities[..].name を読んでも空文字になっている。作られた順に
> 名前を控えながら走査して、元の名前を返す。

## 数値計算の退化入力(mmp_calculators.rs)

`src/mmp_calculators.rs` — `pub fn cross_product(v1: &[ModInt], v2: &[ModInt]) -> Vec<ModInt> {` の直前にあったコメント:

> 2直線（または点と直線）のクロス積（外積/交点計算）
> FIX: 以前は長さチェックが一切無く、退化した入力(例: calc_line_through_points
> が2点の座標が数値的に一致した際に返す空Vec)がここに渡されるとv1[2]等の
> インデックスアクセスでpanicしていた(orthocenter --mctsで実際に発生)。
> evaluate_node系はNoneで「計算不能」を表現する設計なので、ここでは例外を
> 投げず空Vecを返し、呼び出し側(calc_intersection等、そしてeval.rs側の
> to_option)が「計算不能」として一貫して扱えるようにする。

`src/mmp_calculators.rs` — `pub fn calc_squared_distance(v1: &[ModInt], v2: &[ModInt]) -> Option<ModInt> {` の直前にあったコメント:

> FIX: 以前は長さチェックも、z成分(同次座標の第3要素)が0(=無限遠点)かの
> チェックも無かった。z==0の点を渡すと `v1[0]/v1[2]` がModInt::inv()内で
> ゼロ除算panicを起こす(0.inv()はpanicする実装になっている)。戻り値を
> Option<ModInt>にして、計算不能な場合はNoneで表現する。

`src/mmp_calculators.rs` — `if vc.len() < 4 || vp.len() < 3 || vp[2].0 == 0 { return vec![]; }` の直前にあったコメント:

> vc: [A, D, E, F] (A(x^2+y^2) + Dx + Ey + F = 0)
> vp: [x, y, z] (接点)
> FIX: 以前はここを[D,E,F,A](Aが最後)だと思ってvc[0..3]を読んでいたが、
> calc_circumcircleが実際に返す並びは[A,D,E,F](Aが先頭)だった
> (eval.rs::sample_point_on_circleのコメント、および
> test_tangent_line_to_circle_is_numerically_correctで非対称な円
> (D,E,Fが全て非自明な値を持つ配置)を使って実測・確認済み――対称な
> 単位円ではD=E=0になり、この食い違いが偶然打ち消し合って検出でき
> なかった)。この食い違いはtangent_orthic.rs等の既存問題では、証明が
> 純粋に記号的な定理適用(接弦定理)だけで届き、接線の数値そのものを
> 検算する経路を一度も通っていなかったため症状として顕在化していな
> かった。射影版(シュタイナーの定理)の接弦定理を二次曲線の接線を使って
> 構築するにあたり、複比という本質的に数値/代数的な量を経由するため、
> 誤った係数のままでは正しく動かない。

## その他(短く書き直したコメントの原文)

`src/mmp_core/mod.rs` — `mod congruence;` の直前にあったコメント:

> mmp_core はファイルが肥大化していたため、関心事ごとにサブモジュールへ分割した。
> 型定義・EGraphの基本操作(生成・union-find・論理リンク)はこのmod.rs自身に残し、
> それ以外は以下のサブモジュールへ委譲する:
>   congruence  - 合同閉包エンジン (merge_entities, propagate_*, apply_congruence_closure)
>   eval        - 数値評価/健全性チェック (evaluate_node系, numeric_plausibility_check系)
>   proof       - 証明復元 (Justification/ProofEdgeを人間可読な証明文へ変換)
>   construction- 調和共役点など、複数のエンティティ生成を伴う補助構成
>   query       - is_connected等、EGraphの状態を問い合わせるだけの読み取り専用ユーティリティ
> いずれも同じ EGraph 型への impl ブロックを追加しているだけなので、
> 呼び出し側(main.rs, logic_core.rs等)から見た公開APIは一切変わらない。

`src/mmp_core/mod.rs` — `ConstantHomogeneous(ModInt, ModInt, ModInt),` の直前にあったコメント:

> 固定された同次座標を持つ定数エンティティ。GivenPointは(名前を
> varsから引くが誰も登録しないので実質)常に(0,0,1)に評価されるだけで
> 任意の定数は表現できないため、円周点(circular points) I=(1,i,0),
> J=(1,-i,0)(有向角を複比として扱うための固定参照点。i=√-1はこの
> プロジェクトの法998244353がp≡1(mod4)なので体内に存在する)のような
> 「常にこの値」という定数を導入するために追加した。

`src/mmp_core/mod.rs` — `pub degeneration_heat_factor: f64,` の直前にあったコメント:

> bump_heat_bonusが退化グループの他のメンバーに伝播するボーナスの
> 割合(0.5=元の半分)。main.rsの--degen-heat-factor=Xでチューニング
> 実験できるようにCLIから調整可能にしてある。

`src/mmp_core/mod.rs` — `pub degree_cache: std::cell::Cell<Option<Option<usize>>>,` の直前にあったコメント:

> MMP(動点法)の次数(measure_numerical_degree)のメモ化キャッシュ。
> heat_bonus/base_importance/usesと同じく「そのエンティティ固有の
> 派生情報」なので、EGraph側に別立てのHashMapを持つのではなくここに
> 置く(ユーザー指摘: 次数はGeoEntityの中にあった方が自然)。
> None=未計算、Some(None)=計算済みだが測定不能、Some(Some(d))=次数d。
> Cell(RefCellではない)で足りるのは中身がCopyだから。定理マッチングの
> ホットパス(logic_core.rs::match_defined_by_fact)から&selfのまま
> 読み書きできるようにするための内部可変性。

`src/mmp_core/mod.rs` — `#[derive(Debug, Clone, PartialEq, Eq, Hash)]` の直前にあったコメント:

> Concyclic/Collinear は専用のFact型として持つのをやめた。
> 「N点が同じ円/直線に乗っている」ことは、各点をその円/直線に
> link_logical_incidence で構造的につなぐだけで既に表現できており
> (Connected述語で汎用的に問い合わせられる)、別建てのN項Factとして
> 二重に記録・維持する必要がなかった。実際、記録し忘れるバグの温床にも
> なっていた(simson/cyclic_quadで発生)。

`src/mmp_core/mod.rs` — `let dir1_name = self.entities[self.get_rep(dir1_id).0].name.clone();` の直前にあったコメント:

> 射影的な表現を追加: dir2 は「dir1に垂直な方向」そのものとして
> PerpDirectionOfでも構造的に登録しておく(対合性 perp(perp(D))=D
> も両方向に登録する)。これにより「同じ直線への垂線は全て平行」
> のような事実が、専用の角度チェイス定理を経由せず、
> f(a)=f(b) if a=b という通常の合同閉包(create_entityのmemo)
> だけで自動的に導かれるようになる。既存のAng90ベースの定理には
> 一切影響しない、純粋な追加。
> バグ修正: 1つ目のmerge_entities(perp1_id, dir2_id)によって
> dir2_id側の生のエンティティ格納先が「敗者」になった場合、
> その.nameはmerge_entities内でstd::mem::takeされて空文字になる。
> その後dir2_idという生の(mergeを経ていない)IDのままself.entities[..].name
> を読むと空文字を拾ってしまい、"PerpDir__(Auto)"のような名前になる。
> 常にget_repを通した代表元の名前を読むようにする。

`src/mmp_core/mod.rs` — `let la_def = self.normalize_definition(&Definition::LengthSq(*a, new_id));` の直前にあったコメント:

> 中点の定義から直に従う「MA = MB」をここで出していなかった。
> そのため discover モードのスカラー検出器が、中点を作るたびに
> この自明な等式を「発見」し直していた(ユーザ指摘:
> 「長さが等しいという発見が多すぎる」)。垂線→Ang90 や
> 外接円→生成元の接続と同じく、定義から機械的に従う事実は
> ここで構造的に登録するのがこのエンジンの方針。
> 検出器が黙るだけでなく、証明側もこの等式を前提として使えるようになる。

`src/mmp_core/congruence.rs` — `let rep_id = self.get_rep(changed_id); // 上のuses処理でrepが動いた可能性があるので取り直す` の直前にあったコメント:

> [構造的マージ] 点・直線の接続関係(incidence)から従う合同閉包を、
> 全図形×全図形の総当たりではなく、"今回変化した図形(rep_id)の
> 局所的な隣接関係(subobjects)だけを辿る" DFS的な伝播で行う。
>
> - 直線が変化した場合:「直線の一致条件」(2直線が2点を共有、
>   または1点を共有しつつ方向も等しいなら同一直線)を、
>   この直線上の点それぞれが他にどの直線に乗っているかだけを見て判定する。
> - 点が変化した場合:「2直線の交点の一意性」(この点が乗っている
>   2直線の交点として既に登録済みの点があれば同一点)を、
>   memoへのO(1)参照だけで判定する(全点を舐めない)。
>
> 以前はここを「全直線ペア×全点」のO(直線数^2 × 点数)の総当たりで
> 実行しており(apply_congruence_closureが呼ばれるたびに無条件で
> 走っていた)、かつ「点の一致」版は専用のBlackboard定理として
> dfs_match経由でしか判定できず、どちらも無駄が大きかった。
> ここでのマージも merge_entities 経由で worklist に積まれるので、
> 連鎖的な合流はこの while ループが自然に続けて処理する。

`src/mmp_core/congruence.rs` — `let conics: Vec<ClassId> = self.entities[rep_id.0].components.first()` の直前にあったコメント:

> 同じ理由で、この点が乗っている二次曲線側の「一致条件」も
> 再トリガーする(HAGeo-409ベンチマークで、同じ4点が乗って
> いるはずのCircumcircleが別実体のまま統合されない問題が
> 見つかったことへの対応。EGraph::merge_generationのドキュメント
> 参照のような大掛かりな仕組みは不要で、直線と全く同じ
> パターンで解決できる)。円周点I,Jはどの円(Circumcircle)にも
> 構造的に乗っているため、I,J自身が変化した場合はconicsが
> 多め(全ての円)になり得るが、I,Jはほぼ固定の定数で
> 他の実体と統合されることが無いため実害は無い。

`src/mmp_core/congruence.rs` — `if self.numeric_plausibility_check(line, other_line, 2) == Some(false) {` の直前にあったコメント:

> 健全性の穴の修正: マージを確定する前に、ランダムな座標での
> 具体例で本当にこの2直線が等しいかを検算する。数値的に明確に
> 矛盾する場合(Some(false))はこの偶然の一致を却下し、このペアは
> マージしない(判定不能なSome(true)/Noneの場合は従来通り進める)。

`src/mmp_core/eval.rs` — `let result = if vc.len() >= 6 {` の直前にあったコメント:

> 射影幾何への移植(接弦定理→シュタイナーの定理の接線版):
> TangentLineの第1引数はCircle(4係数[A,D,E,F])だけでなく
> 一般のConic(6係数[A,B,C,D,E,F]、calc_conic_through_5_points参照)
> にもなり得るようにした。円と二次曲線は係数ベクトルの長さが
> 4/6で必ず異なる(円は「4点目の生成元」を要求しないので同じ
> Definitionを共有していても混同しない)ため、長さで振り分ける。

`src/mmp_core/eval.rs` — `Definition::CrossRatioOfLines(a, b, c, d) => {` の直前にあったコメント:

> 4本の共点直線がなす線束の複比。直線の同次係数(a,b,c)を
> 射影平面の"点"とみなせば(ユーザー指摘:「円も係数を射影空間の
> 点だと思えばOK」と同じ発想)、4直線が共点(=双対平面上で係数が
> 共線)であるときのCrossRatioOfLinesは、通常のCrossRatio(4点が
> 共線)と全く同じcalc_cross_ratioの式でそのまま計算できる。

`src/mmp_core/eval.rs` — `fn sample_point_on_conic(&self, conic: ClassId, vars: &FxHashMap<String, ModInt>, cache: &` の直前にあったコメント:

> 二次曲線conicの上にあるランダムな点を1つサンプリングする。
> sample_point_on_circleの一般化: 二次曲線の方程式
> A x²+B xy+C y²+D x+E y+F=0 に、既に乗っていると分かっている点
> known_point=(x1,y1)を通るランダムな直線(x1+t dx, y1+t dy)を代入すると、
> tの2次方程式 α t²+β t+γ=0 のうちγ(定数項)はknown_pointが解であることから
> 恒等的に0になるので、t(αt+β)=0 の非自明な解 t=-β/α が(円の場合と全く
> 同じVietaの理屈で)平方根なしに直接求まる。

`src/mmp_core/eval.rs` — `let others: Vec<ClassId> = (0..self.entities.len())` の直前にあったコメント:

> CrossRatio(点の複比)とCrossRatioOfLines(線束の複比)の両方を
> 対象にスキャンする――ユーザーが提案する定理A/B("点の複比→線束の
> 複比"、"線束の複比→点の複比")が実際に成り立つ組み合わせは、まさに
> 「点の複比のエンティティと線束の複比のエンティティが数値的に一致
> する」という異なる種類どうしの一致として現れるため。

`src/mmp_core/raw_proof.rs` — `fn format_location(&self, from: usize, to: usize, is_incidence: bool) -> String {` の直前にあったコメント:

> gapの(またはノードの)location文字列を組み立てる。fromとedge.toの
> 関係が「等しい」(proof_edges由来、explain_identicalの辺)なのか
> 「接続している」(incidence_provenance由来、点が直線/円に乗っている)
> なのかで表記を変える(以前は両方とも"≡"と表示しており、"A ≡ Circ"の
> ような誤解を招く出力になっていた)。

`src/mmp_core/raw_proof.rs` — `let Some((fact_type, args_str)) = premise.rsplit_once(':') else { continue; };` の直前にあったコメント:

> FIX: DefinedBy前提はfact_type自体が"DefinedBy:AnglePair"の
> ようにコロンを含むようになったため、split_once(':')(最初の
> コロン)ではなくrsplit_once(':')(最後のコロン)で区切る必要が
> ある。引数部分は常にカンマ区切りの数字だけなので、最後の
> コロンの後ろが引数、それより前が(コロンを含み得る)fact_type
> という区切り方は常に一意に定まる。

`src/mmp_core/raw_proof.rs` — `fn clean_label(s: &str) -> String {` の直前にあったコメント:

> エンティティ名に付いた"_(Auto)"/"_(Demand)"ラベルを取り除く。これらは
> 「resolve_demands系のオンデマンド作図によって生まれた」という実装都合の
> 印であり、命名時に親の名前をそのまま埋め込むため入れ子(例:
> "Dir_Line_A_B_(Auto)_(Auto)")になることもあるが、str::replaceは文字列中の
> 全ての出現を1回の呼び出しで置換するため、ネストの回数によらず1回の
> 置換呼び出しずつで全て取り除ける。証明の可読性(ユーザー要望)のためだけの
> 整形であり、名前からラベルを消しても指しているClassId自体は変わらないので
> 曖昧さは生じない(重複排除のキーには使わない――compressed_proof側で
> 別途headline文字列そのものをキーにする)。

`src/mmp_core/raw_proof.rs` — `pub fn format_compressed(&self) -> String {` の直前にあったコメント:

> ユーザー要望: 「extracted_proofから、(Auto)/(Demand)ラベルを除き、
> 前提から結論へ上から順に書き、既に証明済みの前提の重複はスキップした
> compressed_proofを作りたい」への対応。
>
> format_deepは「目標→なぜ成り立つか→そのまた根拠」という目標始点の
> 再帰的な入れ子(インデント)構造で、同じ事実が複数箇所から必要と
> されるとその都度(既出: 上記で検証済みなので省略)という葉で参照だけ
> 残す。ここではその木を**post-order**(子=前提を先に、親=結論を後に
> 処理する)で辿って1本のステップ列に平坦化することで、実際に人が
> 書く数学の証明のように「まず基本的な事実を確認し、それらを使って
> 次第に目標に近づく」という順序に並べ替える。同じheadlineを持つ
> ノードが複数箇所に現れる場合(既出プレースホルダ自身も含む)は
> 新しいステップを作らず、既存のステップ番号への参照(「Step N より」)
> に置き換えることで重複を圧縮する。

`src/mmp_core/query.rs` — `pub fn points_share_a_circle(&self, points: &[ClassId]) -> bool {` の直前にあったコメント:

> points に含まれる全ての点が乗っている共通の円が存在するかを判定する。
> Concyclicを専用Factで持たなくなったので、目標判定などでこれを使う。
> 円の数は通常ごく少数なので、全円を舐めても軽い。
> EntityType::Circle撤廃(mmp_core/mod.rs::EntityTypeのドキュメント
> 参照)により、円は今やEntityType::Conicの特殊な場合(I,Jを通る)として
> しか区別できない。この関数は「共円(Concyclic)」という円に固有の
> 目標を判定するためのものなので、単にConic型であるだけでなく、
> I,Jの両方に接続している(=本物の円である)ことも確認する――そうしないと
> 円ではない一般の二次曲線(ConicThrough5Points)まで「共円」と誤判定
> してしまう。

`src/mmp_core/proof.rs` — `pub fn find_shared_circle(&self, points: &[ClassId]) -> Option<ClassId> {` の直前にあったコメント:

> pointsの全てが乗っている共通の円を(あれば)1つ返す。
> query.rs::points_share_a_circleと同じ理由(EntityType::Circle撤廃
> により、円は今やI,Jへのincidenceでしか区別できない)で、単なる
> Conic型ではなくI,Jの両方に接続していることも確認する。

`src/mmp_core/proof.rs` — `pub fn generate_proof(&self, fact_type: &str, target_args: &[ClassId]) -> String {` の直前にあったコメント:

> ユーザー要望: 「e-graphのマージ履歴から証明を作ってresultに出力する
> 仕組み」。Python版のextract_proof.pyは全ログを無差別にダンプするだけ
> だったため無関係な定理まで大量に混入していたが、こちらはexplain_identical/
> find_incidence_justificationで「実際に目標へ辿り着くのに使われた
> ステップだけ」を証明の森から遡って再構成するので、不要な定理は
> 原理的に混入しない。

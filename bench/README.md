# ベンチの回し方

検証は二段構え。**選抜で絞り込み、採用・コミット・記録の直前にだけ全問を回す。**
1手ごとに全問を回すと1回1時間近くかかり、試行が進まない(来歴 §04 #52)。

## 段1: 選抜(33問) ― 普段はこちら

```sh
bench/build.sh mychange          # いまの作業ツリーをビルドして bench/bin/mychange に置く
bench/quick.sh mychange          # 6設定 × 33問。基準(bench/res/qbase_*.tsv)と比べる
bench/quick.sh mychange "--my-flag"   # 全設定に足すフラグ
```

`bench/tier1.txt` は全44問から**どの設定でも一度も解けたことがない11問**を外したもの。
その11問は毎回ステップ予算を使い切るだけで、仕事量の 52〜77% を食っていた。
6設定で8分22秒〜8分44秒で終わり、基準を1ステップも違わず再現する。
同じ機械での全44問(段2)は36分59秒なので、**約4.3倍**速い。

選抜が見るのは「解けている問題が壊れていないか」だけ。
**新しく解けるようになったのは捕まえられない**ので、採用の判断は必ず段2で取り直す。

## 段2: 確認(44問) ― 採用・コミット・記録の直前

```sh
bench/compare.sh mychange
```

## 基準の作り方と更新

`bench/res/<label>_<config>.tsv` が結果。基準は固定名で、
段2が `baseline_<config>.tsv`(44問)、段1が `qbase_<config>.tsv`(33問)。

**変更を採用したら基準も更新する。** 忘れると、以後ずっと「採用済みの改善分だけ
良く見える」比較になってしまう。採用した版の44問の結果を `baseline_*` に写し、
`qbase_*` はそれを `tier1.txt` の33問に絞るだけで作れる(回し直す必要はない):

```sh
for c in default extras skip noise5 noise10 noise20; do
  cp bench/res/<採用した label>_$c.tsv bench/res/baseline_$c.tsv
  grep -Ff bench/tier1.txt bench/res/baseline_$c.tsv > bench/res/qbase_$c.tsv
done
```

## 落とし穴

- **古いバイナリで測らない。** 必ず `build.sh` を通す。コミットの短縮ハッシュと md5 を出す。
- **問題リストを Windows 側で書かない。** CRLF になると最後の1問が `varignon
` という
  名前で渡り、証明器が異常終了しているのに「未解決」として静かに数えられる。
- 仕事量(`dfs_match` の回数)は機械の混み具合に依らないが、**壁時計の時間は依る**。
  時間を比べるときは他のベンチと同時に回さないこと。

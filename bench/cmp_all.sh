#!/usr/bin/env bash
# usage: cmp_all.sh <label> : compare.sh の結果(res/<label>_<設定>.tsv)を基準と問題ごとに対にして比べる。
# 合計は重い数問に引きずられるので、幾何平均・中央値・20%超の悪化/改善の数と、落ちた/増えた問題を並べる(backlog b43)。
S=$(cd "$(dirname "$0")" && pwd)
for c in default extras skip noise5 noise10 noise20; do
  f=$S/res/$1_$c.tsv
  [ -s "$f" ] || { echo "== $c (missing)"; continue; }
  echo "== $c"; python3 "$S/cmp.py" "$S/res/baseline_$c.tsv" "$f"
done

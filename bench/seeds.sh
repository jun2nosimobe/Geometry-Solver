#!/usr/bin/env bash
# usage: seeds.sh <binary-label> [extra-flags]
# ノイズの seed を変えて、選抜33問を noise5/10/20 で回す(seed 2 と 3。通常の quick.sh は seed 12345 の1つだけ)。
# 1つの seed の引きに合わせた調整になっていないかを、採用の直前に確かめる用。
# 基準は bench/res/qbase_noise{5,10,20}_s{2,3}.tsv(無ければ、この binary を基準として保存する: 基準の binary で1回流すこと)。
set -u
S=$(cd "$(dirname "$0")" && pwd)
L="$1"; EXTRA="${2:-}"
for seed in 2 3; do
  for n in 5 10 20; do
    out="$S/res/${L}_qnoise${n}_s$seed.tsv"
    if [ "${BENCH_RESUME:-0}" = 1 ] && [ -s "$out" ]; then :; else "$S/qbench.sh" "$S/bin/$L" "$out" "--noise=$n --noise-seed=$seed $EXTRA" > /dev/null; fi
    base="$S/res/qbase_noise${n}_s$seed.tsv"
    printf 'noise%-3s seed=%s ' "$n" "$seed"
    if [ -s "$base" ] && [ "$base" != "$out" ]; then
      awk -F'\t' 'NR==FNR{s[$1]=$2; w[$1]=$3; next} {ds+=$2-s[$1]; ns+=$2; if(s[$1]==1&&$2==1){bw+=$3; bs+=w[$1]} if(s[$1]!=$2) chg=chg " " $1 "(" s[$1] "->" $2 ")"}
        END{printf "solved %d (diff %+d) both-solved work %+.1f%%%s\n", ns, ds, (bw-bs)*100.0/bs, chg}' "$base" "$out"
    else
      awk -F'\t' '{ns+=$2; w+=$3} END{printf "solved %d (基準が無いので保存のみ)\n", ns}' "$out"
      [ -s "$base" ] || cp "$out" "$base"
    fi
  done
done

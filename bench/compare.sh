#!/usr/bin/env bash
# usage: compare.sh <binary-label>  : 既定3設定とノイズ3水準を回し、基準(head / noise)と比べる
set -u
S=$(cd "$(dirname "$0")" && pwd)
L="$1"; B="$S/bin/$L"; EXTRA="${2:-}"
run() { name="$1"; base="$2"; shift 2; out="$S/res/${L}_${name}.tsv"; printf '%-18s ' "$name"
  # BENCH_RESUME=1 なら、既に結果のある設定は回さずに飛ばす(中断からの再開用)。
  if [ "${BENCH_RESUME:-0}" = 1 ] && [ -s "$out" ]; then echo "(済み・再利用)"
  else "$S/bench.sh" "$B" "$out" "$EXTRA $*"; fi
  if [ -f "$S/res/$base.tsv" ]; then
    diff "$S/res/$base.tsv" "$out" > /dev/null && echo "  identical to $base" || {
      awk -F'\t' 'NR==FNR{s[$1]=$2; w[$1]=$3; next} {ds+=$2-s[$1]; if(s[$1]==1&&$2==1){bw+=$3; bs+=w[$1]} if(s[$1]!=$2) print "  solved change: " $1 " " s[$1] "->" $2}
        END{printf "  solved diff %+d / both-solved work %d -> %d (%+.1f%%)\n", ds, bs, bw, (bw-bs)*100.0/bs}' "$S/res/$base.tsv" "$out"
    }
  fi
}
run default   baseline_default
run extras    baseline_extras   --steps=1000000 --length-theorems --central-angle --midpoint-demands
run skip      baseline_skip     --steps=1000000 --skip-recovery=angle,target
run noise5    baseline_noise5   --noise=5
run noise10   baseline_noise10  --noise=10
run noise20   baseline_noise20  --noise=20

#!/usr/bin/env bash
# usage: quick.sh <binary-label> [extra-flags]
# 一度も解けたことがない11問を外した33問(tier1.txt)で、6設定を回して基準と比べる。
# 採用前の確認は compare.sh(全44問)で行うこと。
set -u
S=$(cd "$(dirname "$0")" && pwd)
L="$1"; B="$S/bin/$L"; EXTRA="${2:-}"
run() { name="$1"; base="$2"; shift 2; printf '%-18s ' "$name"; "$S/qbench.sh" "$B" "$S/res/${L}_q$name.tsv" "$EXTRA $*";
  if [ -f "$S/res/$base.tsv" ]; then
    diff "$S/res/$base.tsv" "$S/res/${L}_q$name.tsv" > /dev/null && echo "  identical to $base" || {
      awk -F'\t' 'NR==FNR{s[$1]=$2; w[$1]=$3; next} {ds+=$2-s[$1]; if(s[$1]==1&&$2==1){bw+=$3; bs+=w[$1]} if(s[$1]!=$2) print "  solved change: " $1 " " s[$1] "->" $2}
        END{printf "  solved diff %+d / both-solved work %d -> %d (%+.1f%%)\n", ds, bs, bw, (bw-bs)*100.0/bs}' "$S/res/$base.tsv" "$S/res/${L}_q$name.tsv"
    }
  fi
}
run default   qbase_default
run extras    qbase_extras   --steps=1500000 --length-theorems --central-angle --midpoint-demands
run skip      qbase_skip     --steps=1500000 --skip-recovery=angle,target
run noise5    qbase_noise5   --noise=5
run noise10   qbase_noise10  --noise=10
run noise20   qbase_noise20  --noise=20

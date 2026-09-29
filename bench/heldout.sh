#!/usr/bin/env bash
# usage: heldout.sh <binary-label> [extra-flags]
# 保留問題(bench/heldout.txt: HAGeo-409 から機械的に読み込んだ、調整に使っていない問題)を、既定とノイズ5で回す。
# 結果は bench/res/heldout_<label>_{default,noise5}.tsv。**調整には使わない**(採用の直前に測って報告するだけ)。
# 保留問題が解けなかった理由を調べて規則や語彙を足すと、その問題は保留でなくなる。足したら heldout.txt から外し、
# 新しい問題(data/hageo409.tsv の別の問題)で置き換えること。
set -u
S=$(cd "$(dirname "$0")" && pwd)
L="$1"; EXTRA="${2:-}"
P=$(tr -d '\015' < "$S/heldout.txt")
for cfg in "default:" "noise5:--noise=5"; do
  name=${cfg%%:*}; flags=${cfg#*:}
  out="$S/res/heldout_${L}_$name.tsv"
  if [ "${BENCH_RESUME:-0}" = 1 ] && [ -s "$out" ]; then echo "$name (済み・再利用)"; continue; fi
  printf '%-8s ' "$name"
  "$S/bench.sh" "$S/bin/$L" "$out" "$flags $EXTRA" $P
done

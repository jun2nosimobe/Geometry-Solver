#!/usr/bin/env bash
# usage: hageo.sh <binary-label> [extra-flags]
# HAGeo-409 から機械的に読める問題のうち、保留問題(heldout.txt)と手で写した bench_* を除いたもの(bench/hageo.txt)を
# 既定の設定で回す。結果は bench/res/hageo_<label>.tsv。語彙を足して読める問題が増えたら hageo.txt を作り直す
# (`geom_solver hageo-list` の「読める」から heldout と bench_* を除く)。
# 規則を足すときの判断には tier1 / 全44問を使い、ここは結果を報告する広い集合として使う(ここの問題に合わせて調整すると
# 汎化を測れなくなる)。
set -u
S=$(cd "$(dirname "$0")" && pwd)
L="$1"; EXTRA="${2:-}"
P=$(tr -d '\015' < "$S/hageo.txt")
out="$S/res/hageo_$L.tsv"
if [ "${BENCH_RESUME:-0}" = 1 ] && [ -s "$out" ]; then echo "(済み・再利用)"; exit 0; fi
"$S/qbench.sh" "$S/bin/$L" "$out" "$EXTRA" $P

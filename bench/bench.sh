#!/usr/bin/env bash
# usage: bench.sh <binary> <out.tsv> "<flags>" [problems...]
# 各問題: 名前 / 解けたか / 消費仕事量 / 推論ログ(マージ・リンク・作図・自動マージ行)のmd5
set -u
BIN="$1"; OUT="$2"; FLAGS="$3"; shift 3
if [ $# -gt 0 ]; then PROBS="$*"; else
  PROBS=$(grep -oP '^\s+"\K[a-z0-9_]+(?=",)' ~/Geometry-Solver/src/problems/mod.rs | awk '!seen[$0]++' | head -44)
fi
WORK=$(mktemp -d "$(dirname "$OUT")/run.XXXXXX")
export BIN FLAGS WORK
one() {
  p="$1"; d="$WORK/$p"; mkdir -p "$d"; cd "$d"
  timeout 900 "$BIN" "$p" $FLAGS > out.txt 2>&1
  solved=0; grep -q '🎉 証明完了' out.txt && solved=1
  work=$(grep -oP '消費した仕事量: \K[0-9]+' out.txt | tail -1)
  h=$(grep -E '🟢|⚙️|💡|🚫|SKETCH' out.txt | md5sum | cut -c1-12)
  printf '%s\t%s\t%s\t%s\n' "$p" "$solved" "${work:--}" "$h"
}
export -f one
printf '%s\n' $PROBS | xargs -P 12 -I{} bash -c 'one {}' | sort > "$OUT"
rm -rf "$WORK"
awk -F'\t' '{s+=$2; w+=$3} END {printf "solved %d/%d  work %d\n", s, NR, w}' "$OUT"

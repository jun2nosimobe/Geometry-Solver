#!/usr/bin/env bash
# usage: degree_levels.sh <binary-label> [extra-flags] : 全44問と HAGeo の広い集合を --degree-search で解き、次数ごとの
# 事実の数(DEGREE_LEVEL: 問題 / 次数 / 事実 / 既知 / AR で分かった / Wu の方法で示した / 示せない)を res/dlevels_<label>.tsv に、
# 問題ごとの 解けたか / 仕事量 を res/dlevels_<label>.sum に集める(集計は degree_levels_sum.py)。
set -u
S=$(cd "$(dirname "$0")" && pwd)
L="$1"; EXTRA="${2:-}"; OUT="$S/res/dlevels_$L.tsv"
BIN="$S/bin/$L"
PROBS="$(grep -oP '^\s+"\K[a-z0-9_]+(?=",)' ~/Geometry-Solver/src/problems/mod.rs | awk '!seen[$0]++' | head -44) $(tr -d '\015' < "$S/hageo.txt")"
WORK=$(mktemp -d "$S/res/dlevels.XXXXXX")
export BIN EXTRA WORK
one() {
  p="$1"; d="$WORK/$(echo "$p" | tr ':/' '__')"; mkdir -p "$d"; cd "$d" || return
  ( ulimit -v 2500000; timeout 900 "$BIN" "$p" --degree-search $EXTRA > out.txt 2>&1 )
  s=0; grep -q '🎉 証明完了' out.txt && s=1
  w=$(grep -oP '消費した仕事量: \K[0-9]+' out.txt | tail -1)
  printf 'SUM\t%s\t%s\t%s\n' "$p" "$s" "${w:--}"
  grep -P '^DEGREE_LEVEL\t' out.txt
  rm -rf "$d"
}
export -f one
printf '%s\n' $PROBS | xargs -P 12 -I{} bash -c 'one "$1"' _ {} > "$WORK/all"
grep -P '^DEGREE_LEVEL\t' "$WORK/all" | cut -f2- | sort > "$OUT"
grep -P '^SUM\t' "$WORK/all" | cut -f2- | sort > "${OUT%.tsv}.sum"
rm -rf "$WORK"
awk -F'\t' '{n++; s+=$2} END {printf "solved %d/%d\n", s, n}' "${OUT%.tsv}.sum"

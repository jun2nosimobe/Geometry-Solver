#!/usr/bin/env bash
# usage: facts.sh <binary-label> : 全44問と HAGeo の広い集合で `geom_solver facts`(図の事実を次数の順に数える)を走らせ、
# 要約の行 FACTS を res/facts_<label>.tsv に集める(問題 / 目標の次数 / 目標が成り立つか / 媒介変数 / 実体 / 実体の次数の最大 /
# 事実 / 未知の事実 / 目標より次数の低い未知の事実 / 秒)。
set -u
S=$(cd "$(dirname "$0")" && pwd)
L="$1"; OUT="$S/res/facts_$L.tsv"
BIN="$S/bin/$L"
PROBS="$(grep -oP '^\s+"\K[a-z0-9_]+(?=",)' ~/Geometry-Solver/src/problems/mod.rs | awk '!seen[$0]++' | head -44) $(tr -d '\015' < "$S/hageo.txt")"
export BIN
one() {
  p="$1"; d=$(mktemp -d); cd "$d" || return
  line=$( ( ulimit -v 4000000; timeout 120 "$BIN" facts "$p" 2>&1 ) | grep -P '^FACTS\t' | cut -f2-)
  [ -n "$line" ] || line="$p	timeout"
  printf '%s\n' "$line"
  cd / && rm -rf "$d"
}
export -f one
printf '%s\n' $PROBS | xargs -P 12 -I{} bash -c 'one "$1"' _ {} | sort > "$OUT"
wc -l < "$OUT"

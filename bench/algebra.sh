#!/usr/bin/env bash
# usage: [SUFFIX=_wu] algebra.sh <binary-label> [extra-flags] : 全44問と HAGeo の広い集合で `geom_solver algebra`(記号計算。
# 既定は Wu の方法、--method=cert で次数を区切った線形結合)を試し、res/algebra_<label><SUFFIX>.tsv に 問題 / 結果(proved・nonzero・gave-up・timeout) / 秒 / 変数の数 / 最大の項数 / 掛け算の回数 / 諦めた理由 を出す。
set -u
S=$(cd "$(dirname "$0")" && pwd)
L="$1"; EXTRA="${2:-}"; OUT="$S/res/algebra_$L${SUFFIX:-}.tsv"
BIN="$S/bin/$L"
PROBS="$(grep -oP '^\s+"\K[a-z0-9_]+(?=",)' ~/Geometry-Solver/src/problems/mod.rs | awk '!seen[$0]++' | head -44) $(tr -d '\015' < "$S/hageo.txt")"
export BIN EXTRA
one() {
  p="$1"; d=$(mktemp -d); cd "$d" || return
  line=$( ( ulimit -v 4000000; timeout 60 "$BIN" algebra "$p" $EXTRA 2>&1 ) | grep -P '^ALGEBRA\t' | cut -f2-)
  [ -n "$line" ] || line="$p	timeout	60"
  printf '%s\n' "$line"
  cd / && rm -rf "$d"
}
export -f one
printf '%s\n' $PROBS | xargs -P 12 -I{} bash -c 'one "$1"' _ {} | sort > "$OUT"
awk -F'\t' '{n[$2]++} END {for (k in n) printf "%s %d  ", k, n[k]; print ""}' "$OUT"

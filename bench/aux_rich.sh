#!/usr/bin/env bash
# usage: aux_rich.sh <label> [extra flags] : 216問を GS_AUX_RICH=1 で解き、証明に使った補助点の定義(AUXPT)と、補助点の候補の測定
# (AUXDIST・AUXRANK・AUXHIT・AUXGH・AUXSKIP)を res/auxrich_<label>/ に集める(来歴 #110)。集計は aux_rich_sum.py <label>。
# 途中で止めても、.sum のある問題は飛ばして再開できる。
set -u
G=~/Geometry-Solver
L=$1; shift; EXTRA="$*"
OUT=$G/bench/res/auxrich_$L; mkdir -p "$OUT"
cp $G/target/release/geom_solver "$OUT/bin"
PROBS="$(grep -oP '^\s+"\K[a-z0-9_]+(?=",)' $G/src/problems/mod.rs | awk '!seen[$0]++' | head -44) $(tr -d '\015' < $G/bench/hageo.txt)"
export OUT EXTRA GS_AUX_RICH=1 GS_AUX_RICH_TOP=1
one() { p=$1; f="$OUT/$(echo "$p" | tr ':/' '__').sum"; [ -s "$f" ] && return; d=$(mktemp -d); cd "$d" || return
  ( ulimit -v 2500000; timeout 900 "$OUT/bin" "$p" --origins $EXTRA > out.txt 2>&1 )
  s=0; grep -q '🎉 証明完了' out.txt && s=1
  { printf 'RUN\t%s\t%s\n' "$p" "$s"; grep -P '^(AUXPT|AUXRANK|AUXDIST|AUXGH|AUXSKIP|AUXHIT)\t' out.txt; } > "$f"
  cd; rm -rf "$d"; }
export -f one
printf '%s\n' $PROBS | xargs -P 11 -I{} bash -c 'one "$1"' _ {}
echo "AUXRICH_DONE $L"

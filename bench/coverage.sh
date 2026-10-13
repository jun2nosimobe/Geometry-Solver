#!/usr/bin/env bash
# usage: coverage.sh <binary-label> [extra-flags] : 全44問と HAGeo の広い集合を既定の設定と --fact-census で解き、探索の前の図の事実を
# 探索の後に知っているかを res/coverage_<label>.tsv に集める(集計は coverage_sum.py)。
# 1行 = 問題 / 次数 / 種類 / 事実 / 探索の前に既知 / 探索の後に既知(e-graph) / AR を1回回せば分かる(FACT_COUNT)。
# 要約の FACT_COVERAGE の行は res/coverage_<label>.sum、次数ごとの関係の階数 FACT_RANK(全て / 前 / 後 / AR)は .rank、
# 点の差の乗法的関係の格子の要約 LATTICE は .lattice に置く(来歴 #106)。
set -u
S=$(cd "$(dirname "$0")" && pwd)
L="$1"; EXTRA="${2:-}"; OUT="$S/res/coverage_$L.tsv"
BIN="$S/bin/$L"
PROBS="$(grep -oP '^\s+"\K[a-z0-9_]+(?=",)' ~/Geometry-Solver/src/problems/mod.rs | awk '!seen[$0]++' | head -44) $(tr -d '\015' < "$S/hageo.txt")"
WORK=$(mktemp -d "$S/res/coverage.XXXXXX")
export BIN EXTRA WORK
one() {
  p="$1"; d="$WORK/$(echo "$p" | tr ':/' '__')"; mkdir -p "$d"; cd "$d" || return
  ( ulimit -v 2500000; timeout 900 "$BIN" "$p" --fact-census $EXTRA > out.txt 2>&1 )
  grep -P '^(FACT_(COUNT|COVERAGE|RANK)|LATTICE)\t' out.txt
  grep -q '^FACT_COVERAGE' out.txt || printf 'FACT_COVERAGE\t%s\tfailed\n' "$p"
  rm -rf "$d"
}
export -f one
printf '%s\n' $PROBS | xargs -P 12 -I{} bash -c 'one "$1"' _ {} > "$WORK/all"
grep -P '^FACT_COUNT\t' "$WORK/all" | cut -f2- | sort > "$OUT"
grep -P '^FACT_COVERAGE\t' "$WORK/all" | cut -f2- | sort > "${OUT%.tsv}.sum"
grep -P '^FACT_RANK\t' "$WORK/all" | cut -f2- | sort > "${OUT%.tsv}.rank"
grep -P '^LATTICE\t' "$WORK/all" | cut -f2- | sort > "${OUT%.tsv}.lattice"
rm -rf "$WORK"
wc -l < "${OUT%.tsv}.sum"

#!/usr/bin/env bash
# usage: census.sh <label> [extra-flags]
# 全44問を --audit-merges で回し、全てのマージ・接続を数値で確かめた結果を問題ごとに res/census_<label>/<問題>.sum に残す。
# 規則だけで健全かを確かめるときは --no-merge-checks を付ける(マージ前の検査を外しても偽のマージが起きないか)。
# 集計は census_sum.py <label>。途中で止めても、.sum のある問題は飛ばして再開できる。
# 問題は CENSUS_PROBS(空白区切り)で差し替えられる(例: HAGeo の広い集合 "$(cat bench/hageo.txt)")。
# 使うバイナリは CENSUS_BIN(既定は target/release/geom_solver)を最初にコピーしたもの。
set -u
S=$(cd "$(dirname "$0")" && pwd)
L=$1; shift; EXTRA="$*"
OUT=$S/res/census_$L; mkdir -p "$OUT"
cp "${CENSUS_BIN:-$S/../target/release/geom_solver}" "$OUT/bin"
PROBS=${CENSUS_PROBS:-}; [ -n "$PROBS" ] || PROBS=$(grep -oP '^\s+"\K[a-z0-9_]+(?=",)' "$S/../src/problems/mod.rs" | awk '!seen[$0]++' | head -44)
export OUT EXTRA
one() { p=$1; [ -s "$OUT/$p.sum" ] && return; d=$(mktemp -d); cd "$d" || return
  ( ulimit -v 2500000; timeout 900 "$OUT/bin" "$p" --audit-merges $EXTRA > out.txt 2>&1 ); ec=$?
  s=0; grep -q '🎉 証明完了' out.txt && s=1
  w=$(grep -oP '消費した仕事量: \K[0-9]+' out.txt | tail -1)
  { printf 'RUN\t%s\t%s\t%s\t%s\n' "$p" "$s" "${w:--}" "$ec"
    grep -E '^MERGE_CENSUS(_FALSE)?\s' out.txt | sed "s/^MERGE_CENSUS_FALSE/FALSE\t$p/"; } > "$OUT/$p.sum"
  cd; rm -rf "$d"; }
export -f one
printf '%s\n' $PROBS | xargs -P ${CENSUS_JOBS:-10} -I{} bash -c 'one "$1"' _ {}
echo "CENSUS_DONE $L"

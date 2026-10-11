#!/usr/bin/env bash
# usage: unsolved.sh <binary-label> : HAGeo の広い集合を既定で解き直し、未解決の分類に使う診断を res/unsolved_<label>.tsv に出す
# (集計・分類は unsolved_sum.py)。1行 = 問題 / 解けたか / 仕事量 / 秒 / 終了コード / AR の回数 / 相似の行演算が1回の上限
# (AR_ROUND_OPS_CAP)に達した回 / 相似の組が上限(400)に達した回 / 最後の回の三角形の数 / 最後の回の格子の行数・記号の数。
set -u
S=$(cd "$(dirname "$0")" && pwd)
L="$1"; OUT="$S/res/unsolved_$L.tsv"
BIN="$S/bin/$L"
WORK=$(mktemp -d "$S/res/unsolved.XXXXXX")
export BIN WORK
one() {
  p="$1"; d="$WORK/$(echo "$p" | tr ':/*' '___')"; mkdir -p "$d"; cd "$d" || return
  s0=$(date +%s.%N)
  ( ulimit -v 2500000; GS_DEBUG_AR=1 timeout 300 "$BIN" "$p" --stats > out.txt 2>&1 ); code=$?
  s1=$(date +%s.%N)
  solved=0; grep -q '🎉 証明完了' out.txt && solved=1
  work=$(grep -oP '消費した仕事量: \K[0-9]+' out.txt | tail -1)
  rounds=$(grep -c 'AR_STAGE similarity' out.txt)
  capops=$(grep -oP 'AR_STAGE similarity\s+\S+\s+\K[0-9]+' out.txt | awk '$1>=380000' | wc -l)
  cappairs=$(grep -oP 'sim-AA .* pairs=\K[0-9]+' out.txt | awk '$1>=400' | wc -l)
  tris=$(grep -oP 'sim-AA .* tris=\K[0-9]+' out.txt | tail -1)
  rows=$(grep -oP 'AR_DEBUG classes=.* rows=\K[0-9]+' out.txt | tail -1)
  atoms=$(grep -oP 'AR_DEBUG classes=.* atoms=\K[0-9]+' out.txt | tail -1)
  printf '%s\t%s\t%s\t%.1f\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$p" "$solved" "${work:--}" "$(echo "$s1 - $s0" | bc)" "$code" \
    "$rounds" "$capops" "$cappairs" "${tris:-0}" "${rows:-0}" "${atoms:-0}"
  rm -rf "$d"
}
export -f one
tr -d '\015' < "$S/hageo.txt" | tr ' ' '\n' | grep . | xargs -P 12 -I{} bash -c 'one "$1"' _ {} | sort > "$OUT"
rm -rf "$WORK"
awk -F'\t' '{s+=$2} END {printf "solved %d/%d\n", s, NR}' "$OUT"

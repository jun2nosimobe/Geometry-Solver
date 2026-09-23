#!/usr/bin/env bash
# usage: qbench.sh <binary> <out.tsv> "<flags>" [problems...]
# bench.sh と同じ4列を出しつつ、<out.tsv>.time に問題ごとの秒数も残す(長い棒を見つける用)。
set -u
BIN="$1"; OUT="$2"; FLAGS="$3"; shift 3
if [ $# -gt 0 ]; then PROBS="$*"; else PROBS=$(cat "$(dirname "$0")/tier1.txt"); fi
PROBS=$(printf '%s\n' $PROBS | tr -d '\015')
WORK=$(mktemp -d "$(dirname "$OUT")/run.XXXXXX")
export BIN FLAGS WORK
one() {
  p="$1"; d="$WORK/$p"; mkdir -p "$d"; cd "$d" || return
  t0=$(date +%s.%N)
  timeout 900 "$BIN" "$p" $FLAGS > out.txt 2>&1
  rc=$?
  t1=$(date +%s.%N)
  # 問題名の打ち間違いなどで証明器が異常終了したら、静かに「未解決」として数えず目立たせる。
  if [ "$rc" != 0 ] && [ "$rc" != 124 ]; then echo "!! $p exited $rc" >&2; fi
  solved=0; grep -q '🎉 証明完了' out.txt && solved=1
  work=$(grep -oP '消費した仕事量: \K[0-9]+' out.txt | tail -1)
  h=$(grep -E '🟢|⚙️|💡|🚫|SKETCH' out.txt | md5sum | cut -c1-12)
  printf '%s\t%s\t%s\t%s\t%.1f\n' "$p" "$solved" "${work:--}" "$h" "$(echo "$t1-$t0" | bc)"
}
export -f one
printf '%s\n' $PROBS | xargs -P 12 -I{} bash -c 'one {}' | sort > "$OUT.raw"
cut -f1-4 "$OUT.raw" > "$OUT"
cut -f1,5 "$OUT.raw" | sort -k2 -g -r > "$OUT.time"
rm -rf "$WORK" "$OUT.raw"
awk -F'\t' '{s+=$2; w+=$3} END {printf "solved %d/%d  work %d\n", s, NR, w}' "$OUT"

#!/usr/bin/env bash
# usage: ar_usage.sh <binary-label> <out-label> [extra-flags] : 全44問と HAGeo の広い集合を --ar-usage で解き、証明に使った定理と
# 代数的な追跡の結論が使った等式の種類を res/usage_<out-label>.tsv に集める(集計は ar_usage_sum.py)。
# 1行 = 問題 / 解けたか / 種類(T: 定理, K: AR の等式の種類) / 名前 / 回数(T: 証明に使った回数, K: その種類を使った AR の結論の数) / (K のみ)等式の数
set -u
S=$(cd "$(dirname "$0")" && pwd)
L="$1"; OUT="$S/res/usage_$2.tsv"; EXTRA="${3:-}"
BIN="$S/bin/$L"
PROBS="$(grep -oP '^\s+"\K[a-z0-9_]+(?=",)' ~/Geometry-Solver/src/problems/mod.rs | awk '!seen[$0]++' | head -44) $(tr -d '\015' < "$S/hageo.txt")"
WORK=$(mktemp -d "$S/res/usage.XXXXXX")
export BIN EXTRA WORK
one() {
  p="$1"; d="$WORK/$(echo "$p" | tr ':/' '__')"; mkdir -p "$d"; cd "$d" || return
  ( ulimit -v 2500000; timeout 900 "$BIN" "$p" --ar-usage $EXTRA > out.txt 2>&1 )
  s=0; grep -q '🎉 証明完了' out.txt && s=1
  printf '%s\t%s\t-\t-\t0\n' "$p" "$s"
  grep -P '^PROOF_THEOREM\t' out.txt | awk -F'\t' -v p="$p" -v s="$s" '{printf "%s\t%s\tT\t%s\t%s\n", p, s, $2, $3}'
  grep -P '^PROOF_AR_KIND\t' out.txt | awk -F'\t' -v p="$p" -v s="$s" '{printf "%s\t%s\tK\t%s\t%s\t%s\n", p, s, $2, $3, $4}'
  rm -rf "$d"
}
export -f one
printf '%s\n' $PROBS | xargs -P 12 -I{} bash -c 'one "$1"' _ {} | sort > "$OUT"
rm -rf "$WORK"
awk -F'\t' '$3=="-"{n++; s+=$2} END {printf "solved %d/%d\n", s, n}' "$OUT"

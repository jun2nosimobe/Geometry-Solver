#!/usr/bin/env bash
# usage: audit.sh <binary-label> [extra-flags] : 基準(res/baseline_default.tsv)で解ける問題を全部解き直し、証明の時刻つきの監査の要約
# (検証したステップ数・全てが厳密に辿れたか・循環の数・圧縮後のステップ数)を res/audit_<label>.tsv に出す。
# 採用前の確認用(来歴 #87・#90・#91)。strict=1 かつ cycles=0 でない行があれば、その問題を解き直して out.txt と result/ を見る。
set -u
S=$(cd "$(dirname "$0")" && pwd)
L="$1"; shift
export BIN="$S/bin/$L" EXTRA="$*"
WORK=$(mktemp -d "$S/res/audit.XXXXXX"); export WORK
PROBS=$(awk -F'\t' '$2==1{print $1}' "$S/res/baseline_default.tsv")
one() {
  p="$1"; d="$WORK/$p"; mkdir -p "$d"; cd "$d" || return
  ( ulimit -v 2500000; timeout 900 "$BIN" "$p" $EXTRA > out.txt 2>&1 )
  solved=$(grep -c '証明完了' out.txt)
  steps=$(grep -oP '検証した\K[0-9]+' out.txt | head -1)
  ok=$(grep -c '全てが厳密に辿れました' out.txt)
  cyc=$(grep -c '循環: いま検証している' "result/extracted_proof_$p.txt" 2>/dev/null)
  comp=$(grep -c '^Step' "result/compressed_proof_$p.txt" 2>/dev/null)
  printf '%s\tsolved=%s\tsteps=%s\tstrict=%s\tcycles=%s\tcompressed=%s\n' "$p" "$solved" "${steps:--}" "$ok" "${cyc:-0}" "${comp:--}"
}
export -f one
printf '%s\n' $PROBS | xargs -P "${AUDIT_JOBS:-10}" -I{} bash -c 'one "$1"' _ {} | sort > "$S/res/audit_$L.tsv"
awk -F'\t' '{n++; if ($2=="solved=1" && $4=="strict=1" && $5=="cycles=0") ok++} END {printf "audit: %d/%d problems solved, strict, no cycles\n", ok, n}' "$S/res/audit_$L.tsv"
grep -v 'solved=1.*strict=1	cycles=0' "$S/res/audit_$L.tsv" | sed 's/^/  /'
rm -rf "$WORK"

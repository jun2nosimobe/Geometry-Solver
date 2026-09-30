#!/usr/bin/env bash
# usage: theorem_stats.sh [extra-flags]
# 全44問を既定設定(+ extra-flags)で回し、定理ごとの実測を集める(docs/gen_theorem_atlas.py が読む)。
# 出力(タブ区切り、1行=1問×1定理): 問題 解けたか 定理 試行回数 cap到達 平均dfs_call マッチ数 証明に登場
#   マッチ数 = 「前提条件がすべて満たされました」の行の数(結論を適用する直前。既に成り立っていた分は数えない)
#   証明に登場 = extract_proof の深い証明にその定理名が現れた回数(解けた問題だけ)
set -u
S=$(cd "$(dirname "$0")" && pwd)
EXTRA="${1:-}"
WORK=$(mktemp -d "$S/res/tstats.XXXXXX")
# 途中でビルドし直してもバイナリが入れ替わらないよう、最初にコピーして使う。
cp "$S/../target/release/geom_solver" "$WORK/geom_solver"
BIN=$WORK/geom_solver
PROBS=$(grep -oP '^\s+"\K[a-z0-9_]+(?=",)' "$S/../src/problems/mod.rs" | awk '!seen[$0]++' | head -44)
export BIN EXTRA WORK
one() {
  p="$1"; d="$WORK/$p"; mkdir -p "$d"; cd "$d" || return
  ( ulimit -v 2500000; timeout 900 "$BIN" "$p" --stats $EXTRA > out.txt 2>&1 )
  solved=0; grep -q '🎉 証明完了' out.txt && solved=1
  grep -E '回試行 \(うちcap到達' out.txt | while IFS= read -r line; do
    name=$(echo "$line" | sed -E 's/.* : //')
    att=$(echo "$line" | grep -oP '^\s*\K[0-9]+(?=回試行)')
    cap=$(echo "$line" | grep -oP 'cap到達 *\K[0-9]+')
    avg=$(echo "$line" | grep -oP '平均dfs_call +\K[0-9]+')
    m=$(grep -F "定理「$name」の前提条件" out.txt | wc -l)
    pr=0; [ -f "result/extracted_proof_$p.txt" ] && pr=$(grep -oF "$name" "result/extracted_proof_$p.txt" | wc -l)
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$p" "$solved" "$name" "$att" "$cap" "$avg" "$m" "$pr"
  done
  rm -rf "$d"
}
export -f one
printf '%s\n' $PROBS | xargs -P 12 -I{} bash -c 'one "$1"' _ {} | sort
rm -rf "$WORK"

#!/usr/bin/env bash
# usage: adopt.sh <binary-label> : <label> の全44問×6設定の結果(res/<label>_<config>.tsv、compare.sh の出力)を新しい基準にする。
# 選抜(tier1.txt)は「どれかの設定で解けた問題」から作り直す。直前の基準は res/prev_baseline/ に残す(最初の1回分だけ)。
R=$(cd "$(dirname "$0")" && pwd); L="$1"
cd $R
mkdir -p res/prev_baseline && cp -n res/baseline_*.tsv res/qbase_*.tsv tier1.txt res/prev_baseline/ 2>/dev/null
for c in default extras skip noise5 noise10 noise20; do
  test -s res/${L}_$c.tsv || { echo "missing res/${L}_$c.tsv"; exit 1; }
  cp res/${L}_$c.tsv res/baseline_$c.tsv
done
awk -F'\t' '$2==1 {print $1}' res/baseline_*.tsv | sort -u > tier1.txt
for c in default extras skip noise5 noise10 noise20; do
  awk -F'\t' 'NR==FNR {t[$1]=1; next} ($1 in t)' tier1.txt res/baseline_$c.tsv > res/qbase_$c.tsv
done
echo "tier1: $(wc -l < tier1.txt) problems (was $(wc -l < res/prev_baseline/tier1.txt))"
for c in default extras skip noise5 noise10 noise20; do echo "$c: full solved $(awk -F'\t' '{s+=$2} END{print s}' res/baseline_$c.tsv)/44, tier1 rows $(wc -l < res/qbase_$c.tsv)"; done

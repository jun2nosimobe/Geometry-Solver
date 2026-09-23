#!/usr/bin/env bash
# usage: suite.sh <label>   (bin/<label> を全設定で回し res/<label>_*.tsv に保存)
set -u
S=$(cd "$(dirname "$0")" && pwd)
L="$1"; B="$S/bin/$L"
run() { name="$1"; shift; flags="$1"; shift; printf '%-12s ' "$name"; "$S/bench.sh" "$B" "$S/res/${L}_${name}.tsv" "$flags" "$@"; }
SK="bench_2012chnwesternmop5 bench_2016armog10p2 bench_2008armog10p6 bench_2000usatstp2"
run proj    "--steps=1500000 --projective"
run extras  "--steps=1500000 --length-theorems --central-angle --midpoint-demands"
run seeded  "--steps=1500000 --seeded-rematch"
run bandit  "--steps=1500000 --bandit"
run skaux   "--steps=1500000 --sketch=aux" $SK
run sk2     "--steps=1500000 --sketch=2" $SK

#!/usr/bin/env python3
"""census.sh の結果の集計。usage: census_sum.py <label>

出どころ(規則)ごとの 真/偽/判定不能 と、問題ごとの最初の偽のマージ(偽の連鎖の根)を出す。
前提が乱数座標で成り立たない問題(tag が hypothesis)の「偽」は誤警報の可能性があるので、集計から外して名前だけ出す。
"""
import collections
import glob
import os
import sys

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'res', 'census_' + sys.argv[1])
tot = collections.defaultdict(lambda: [0, 0, 0])
probs_f = collections.defaultdict(set)
first, runs, hyp = {}, {}, {}
for f in sorted(glob.glob(D + '/*.sum')):
    for line in open(f, encoding='utf-8'):
        c = line.rstrip('\n').split('\t')
        if c[0] == 'RUN':
            runs[c[1]] = c[2:]
        elif c[0] == 'MERGE_CENSUS':
            p, src, t, fa, u, tag = c[1], c[2], int(c[3]), int(c[4]), int(c[5]), c[6]
            hyp[p] = tag
            if tag != 'ok':
                continue
            for i, v in enumerate((t, fa, u)):
                tot[src][i] += v
            if fa:
                probs_f[src].add(p)
        elif c[0] == 'FALSE' and c[1] not in first:
            first[c[1]] = (int(c[2]), c[3], c[4][:150])
print('解けた', sum(1 for r in runs.values() if r[0] == '1'), '/', len(runs),
      ' 前提が乱数座標で成り立たない問題(集計外):', sorted(p for p, t in hyp.items() if t != 'ok'))
print('--- 偽のあった出どころ: 偽 真 判定不能 問題数 出どころ')
for s, v in sorted(tot.items(), key=lambda x: -x[1][1]):
    if v[1]:
        print(f'{v[1]:>7} {v[0]:>8} {v[2]:>8}  {len(probs_f[s]):>2}  {s}')
print('--- 問題ごとの最初の偽(偽の連鎖の根)')
for p, (seq, src, d) in sorted(first.items()):
    if hyp.get(p) == 'ok':
        print(f'{p:28} 解けた={runs.get(p, ["?"])[0]} #{seq:<6} {src} | {d}')

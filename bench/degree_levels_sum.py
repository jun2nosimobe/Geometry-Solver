#!/usr/bin/env python3
"""usage: degree_levels_sum.py <ラベル>

res/dlevels_<ラベル>.tsv(degree_levels.sh)を次数の区間ごとに集計する: 事実 / 見る前から既知 / AR で分かった / Wu の方法で示した
(低い次数の事実から線形には従わない「次数 d の新しい事実」)/ 示せない。解けた問題と解けなかった問題に分ける。"""
import os
import sys
from collections import defaultdict

R = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'res')
EDGES = [2, 4, 6, 8, 12, 16, 24]


def bucket(d):
    lo = 0
    for e in EDGES:
        if d <= e:
            return (lo, f'{lo}–{e}')
        lo = e + 1
    return (lo, f'{lo}+')


def main():
    label = sys.argv[1]
    solved = {}
    for line in open(os.path.join(R, f'dlevels_{label}.sum'), encoding='utf-8'):
        r = line.rstrip('\n').split('\t')
        solved[r[0]] = r[1] == '1'
    rows = [line.rstrip('\n').split('\t') for line in open(os.path.join(R, f'dlevels_{label}.tsv'), encoding='utf-8') if line.strip()]
    print(f'問題 {len(solved)}、解けた {sum(solved.values())}')
    for want, title in [(True, '解けた問題'), (False, '解けなかった問題')]:
        t = defaultdict(lambda: [0] * 5)
        for p, d, *n in rows:
            if solved.get(p) != want:
                continue
            for k, x in enumerate(map(int, n)):
                t[bucket(int(d))][k] += x
        print(f'== {title}')
        print('次数\t事実\t既知\tAR\tWu の方法\t示せない')
        for (_, name), n in sorted(t.items()):
            print(name, *n, sep='\t')


if __name__ == '__main__':
    main()

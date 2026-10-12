#!/usr/bin/env python3
"""usage: coverage_sum.py <ラベル>

res/coverage_<ラベル>.tsv(coverage.sh)を集計する。図の事実(探索の前の一覧)のうち、探索の前に既知・探索の後に e-graph が知っている・
AR を1回回せば分かる、の数を 次数 / 目標の次数との差 / 種類 ごとに、解けた問題と解けなかった問題に分けて出す。
「探索で増えた」は、探索の前に未知だった事実のうち探索の後に分かったものの割合。"""
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


def rel_bucket(x):
    for lo, hi, name in [(-999, -9, '≤ −9'), (-8, -5, '−8〜−5'), (-4, -1, '−4〜−1'), (0, 0, '0(目標と同じ)'), (1, 4, '+1〜+4'), (5, 999, '≥ +5')]:
        if lo <= x <= hi:
            return (lo, name)
    return (0, '?')


def pct(a, b):
    return f'{100 * a / b:5.1f}%' if b else '    -'


def table(title, rows):
    print(f'== {title}')
    print('区間\t事実\t前\t後\tAR\t後/事実\tAR/事実\t探索で増えた(後)\t(AR)')
    for (_, name), n in sorted(rows.items()):
        f, b, a, r = n
        print(f'{name}\t{f}\t{b}\t{a}\t{r}\t{pct(a, f)}\t{pct(r, f)}\t{pct(a - b, f - b)}\t{pct(r - b, f - b)}')


def main():
    label = sys.argv[1]
    info = {}
    for line in open(os.path.join(R, f'coverage_{label}.sum'), encoding='utf-8'):
        r = line.rstrip('\n').split('\t')
        info[r[0]] = dict(x.split('=', 1) for x in r[1:] if '=' in x)
    rows = [line.rstrip('\n').split('\t') for line in open(os.path.join(R, f'coverage_{label}.tsv'), encoding='utf-8') if line.strip()]
    failed = [p for p, kv in info.items() if 'solved' not in kv]
    print(f'問題 {len(info)}(解けた {sum(kv.get("solved") == "1" for kv in info.values())}、測れなかった {len(failed)})')
    for solved_want, title in [('1', '解けた問題'), ('0', '解けなかった問題')]:
        by_deg, by_rel, by_kind = defaultdict(lambda: [0] * 4), defaultdict(lambda: [0] * 4), defaultdict(lambda: [0] * 4)
        for p, d, kind, *n in rows:
            kv = info.get(p, {})
            if kv.get('solved') != solved_want:
                continue
            n = list(map(int, n))
            d = int(d)
            for t in (by_deg[bucket(d)], by_kind[(0, kind)]):
                for k in range(4):
                    t[k] += n[k]
            g = kv.get('goal_degree', '-')
            if g.isdigit():
                t = by_rel[rel_bucket(d - int(g))]
                for k in range(4):
                    t[k] += n[k]
        table(f'{title}: 事実の次数', by_deg)
        table(f'{title}: 事実の次数 − 目標の次数', by_rel)
        table(f'{title}: 種類', by_kind)


if __name__ == '__main__':
    main()

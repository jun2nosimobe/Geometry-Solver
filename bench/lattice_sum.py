#!/usr/bin/env python3
"""usage: lattice_sum.py <ラベル>

coverage.sh の res/coverage_<ラベル>.rank・.lattice・.sum を集計する(来歴 #106)。
- 格子: 図の点の差・直線の方向の乗法的関係の格子の階数(完全な AR が知りうる全て)と、図の事実が張る階数。
- 取りこぼし: 目標の次数より下・目標の次数まで・全体で、事実が張る階数のうち 既知・探索の後・AR が張る分。
  階数で数えるので、同じことを言い直した事実の重複に左右されない(独立な関係の本数)。"""
import os
import statistics
import sys

R = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'res')


def kv(cols):
    return dict(c.split('=', 1) for c in cols if '=' in c)


def main():
    label = sys.argv[1]
    base = os.path.join(R, f'coverage_{label}')
    info = {r[0]: kv(r[1:]) for r in (l.rstrip('\n').split('\t') for l in open(base + '.sum', encoding='utf-8'))}
    lat = {r[0]: kv(r[1:]) for r in (l.rstrip('\n').split('\t') for l in open(base + '.lattice', encoding='utf-8'))}
    ranks = {}
    for l in open(base + '.rank', encoding='utf-8'):
        p, d, *n = l.rstrip('\n').split('\t')
        ranks.setdefault(p, []).append((int(d), *map(int, n)))
    for v in ranks.values():
        v.sort()

    n = len(lat)
    g = lambda k: [int(x[k]) for x in lat.values()]
    lr, fr, secs = g('lattice_rank'), g('facts_rank'), [float(x['secs']) for x in lat.values()]
    print(f'問題 {n}: 格子の階数 合計 {sum(lr)}(中央値 {statistics.median(lr)})、図の事実が張る階数 合計 {sum(fr)}({100 * sum(fr) / max(1, sum(lr)):.1f}%)、'
          f'成り立たないと出た事実 {sum(g("not_relation"))}、時間 中央値 {statistics.median(secs):.2f}秒・最長 {max(secs):.2f}秒、基底 中央値 {statistics.median(g("base"))}')

    def at(p, dmax):
        best = (0, 0, 0, 0)
        for d, *r in ranks.get(p, []):
            if d <= dmax:
                best = tuple(r)
        return best

    for want, title in [('1', '解けた問題'), ('0', '解けなかった問題')]:
        ps = [p for p, x in info.items() if x.get('solved') == want and x.get('goal_degree', '-').isdigit() and p in ranks]
        print(f'== {title}({len(ps)}問)')
        print('範囲\t事実の階数\t既知\t探索の後\tAR\t足りない(AR)\t全部そろう問題')
        for name, dm in [('目標の次数より下', lambda x: int(x) - 1), ('目標の次数まで', lambda x: int(x)), ('全て', lambda x: 10 ** 9)]:
            tot = [0, 0, 0, 0]
            full = 0
            for p in ps:
                r = at(p, dm(info[p]['goal_degree']))
                for k in range(4):
                    tot[k] += r[k]
                full += r[3] == r[0]
            pct = lambda k: f'{tot[k]}({100 * tot[k] / max(1, tot[0]):.1f}%)'
            print(f'{name}\t{tot[0]}\t{pct(1)}\t{pct(2)}\t{pct(3)}\t{tot[0] - tot[3]}\t{full}')


if __name__ == '__main__':
    main()

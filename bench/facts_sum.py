#!/usr/bin/env python3
"""usage: facts_sum.py <facts のラベル> [探索のラベル(既定 r102)] [記号計算のラベル(既定 alg4)]

res/facts_<ラベル>.tsv(facts.sh)を目標の次数で区切り、区間ごとに 問題数 / 探索で解けた数 / Wu の方法で示せた数 / どちらか を出す。
探索は res/<探索>_default.tsv(44問)と res/hageo_<探索>.tsv、記号計算は res/algebra_<記号計算>_wu.tsv。"""
import os
import statistics
import sys

R = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'res')
EDGES = [2, 4, 6, 8, 12, 16, 24]


def rows(name):
    path = os.path.join(R, name)
    if not os.path.exists(path):
        return []
    return [line.rstrip('\n').split('\t') for line in open(path, encoding='utf-8') if line.strip()]


def main():
    label = sys.argv[1]
    search = sys.argv[2] if len(sys.argv) > 2 else 'r102'
    alg = sys.argv[3] if len(sys.argv) > 3 else 'alg4'
    facts = {}
    for r in rows(f'facts_{label}.tsv'):
        kv = dict(x.split('=', 1) for x in r[1:] if '=' in x)
        facts[r[0]] = kv
    solved = {r[0]: r[1] == '1' for r in rows(f'{search}_default.tsv') + rows(f'hageo_{search}.tsv')}
    wu = {r[0]: r[1] == 'proved' for r in rows(f'algebra_{alg}_wu.tsv')}

    def bucket(d):
        lo = 0
        for e in EDGES:
            if d <= e:
                return f'{lo}–{e}'
            lo = e + 1
        return f'{lo}+'

    for title, pick in [('44問', lambda p: not p.startswith('hageo:')), ('HAGeo', lambda p: p.startswith('hageo:'))]:
        ps = [p for p in facts if pick(p)]
        degs = [int(facts[p]['goal_degree']) for p in ps if facts[p].get('goal_degree', '').isdigit()]
        print(f'== {title}: {len(ps)}問、目標の次数が測れた {len(degs)}問、中央値 {statistics.median(degs) if degs else "-"}')
        table = {}
        for p in ps:
            g = facts[p].get('goal_degree', '')
            b = bucket(int(g)) if g.isdigit() else '測れない'
            t = table.setdefault(b, [0, 0, 0, 0])
            s, w = solved.get(p, False), wu.get(p, False)
            t[0] += 1; t[1] += s; t[2] += w; t[3] += s or w
        order = [bucket(e) for e in EDGES] + [bucket(EDGES[-1] + 1), '測れない']
        print('目標の次数\t問題\t探索\tWu\tどちらか')
        for b in order:
            if b in table:
                print(b, *table[b], sep='\t')
    print('== 目標より次数の低い未知の事実(中央値): 探索で解けた / 解けなかった')
    for title, pick in [('44問', lambda p: not p.startswith('hageo:')), ('HAGeo', lambda p: p.startswith('hageo:'))]:
        out = []
        for want in (True, False):
            v = [int(facts[p]['unknown_below_goal']) for p in facts if pick(p) and solved.get(p, False) == want and facts[p].get('unknown_below_goal', '').isdigit()]
            out.append(f'{statistics.median(v) if v else "-"}({len(v)}問)')
        print(title, *out, sep='\t')


if __name__ == '__main__':
    main()

"""ar_usage.sh の結果を集計する。usage: ar_usage_sum.py <out-label> [<out-label> ...]
定理ごと: 証明に使った問題の数・回数(44問 / HAGeo を分けて)。AR の等式の種類ごと: 証明に残った AR の結論でその種類を使った問題の数・結論の数。
"""
import os, sys
from collections import defaultdict

S = os.path.dirname(os.path.abspath(__file__))
for label in sys.argv[1:]:
    rows = [l.rstrip('\n').split('\t') for l in open(os.path.join(S, 'res', f'usage_{label}.tsv'), encoding='utf-8')]
    solved = {r[0] for r in rows if r[2] == '-' and r[1] == '1'}
    group = lambda p: 'HAGeo' if p.startswith('hageo:') else '44問'
    n_solved = defaultdict(int)
    for p in solved: n_solved[group(p)] += 1
    print(f'== {label}: 解けた 44問 {n_solved["44問"]} / HAGeo {n_solved["HAGeo"]}')
    for kind, title in (('T', '定理(証明に使った問題の数 / 回数)'), ('K', 'AR の等式の種類(使った問題の数 / AR の結論の数 / 等式の数)')):
        stat = defaultdict(lambda: defaultdict(lambda: [0, 0, 0]))
        for r in rows:
            if r[2] != kind or r[0] not in solved: continue
            e = stat[r[3]][group(r[0])]
            e[0] += 1; e[1] += int(r[4]); e[2] += int(r[5]) if len(r) > 5 else 0
        print(f'-- {title}')
        for name in sorted(stat, key=lambda n: -sum(v[0] for v in stat[n].values())):
            cells = []
            for g in ('44問', 'HAGeo'):
                v = stat[name][g]
                cells.append(f'{g} {v[0]:3d} / {v[1]:5d}' + (f' / {v[2]:6d}' if kind == 'K' else ''))
            print(f'  {name:<40}  ' + '   '.join(cells))

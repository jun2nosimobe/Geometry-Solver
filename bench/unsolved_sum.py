"""HAGeo の未解決の分類。usage: unsolved_sum.py <label> [<census のラベル(予算800万)>]
unsolved.sh の診断(res/unsolved_<label>.tsv)、検査を外した監査(予算800万、res/census_<census>/*.sum の RUN 行)、
HAGeo-409 の問題文(難易度・作図・目標)をつないで、未解決の問題を次の順に分ける(先に当てはまったもの):
  予算: 予算800万(時刻の上限60秒)なら解ける
  AR の上限: 最後の半分の回で、相似の行演算が1回の上限に達している(AR が回しきれていない)
  その他: 推論の規則か補助作図が足りない(目標の述語・作図ごとに数える)
あわせて、未解決と解けた問題で作図の語の出現率を比べる。
"""
import glob, os, re, sys
from collections import Counter, defaultdict

S = os.path.dirname(os.path.abspath(__file__))
label = sys.argv[1]
census = sys.argv[2] if len(sys.argv) > 2 else None

data = {}
for l in open(os.path.join(S, '..', 'data', 'hageo409.tsv'), encoding='utf-8'):
    f = l.rstrip('\n').split('\t')
    if len(f) >= 3: data['hageo:' + f[0]] = (float(f[1]) if re.match(r'^[0-9.]+$', f[1]) else None, f[2])

def words(p):
    body, _, goal = data.get(p, (None, ''))[1].partition('Prove:')
    return {m for m in re.findall(r'=\s*([a-z_0-9]+)', body)}, (goal.split() or ['?'])[0]

rows = {}
for l in open(os.path.join(S, 'res', f'unsolved_{label}.tsv'), encoding='utf-8'):
    f = l.rstrip('\n').split('\t')
    rows[f[0]] = dict(solved=f[1] == '1', work=f[2], sec=float(f[3]), code=f[4], rounds=int(f[5]), capops=int(f[6]),
                      cappairs=int(f[7]), tris=int(f[8]), rows=int(f[9]), atoms=int(f[10]))
big = set()
if census:
    for path in glob.glob(os.path.join(S, 'res', f'census_{census}', '*.sum')):
        for l in open(path, encoding='utf-8'):
            f = l.rstrip('\n').split('\t')
            if f[0] == 'RUN' and f[2] == '1': big.add(f[1])

solved = [p for p, r in rows.items() if r['solved']]
unsolved = sorted(p for p, r in rows.items() if not r['solved'])
cls = {}
for p in unsolved:
    r = rows[p]
    if r['code'] not in ('0', '1'): cls[p] = f'異常終了(終了コード {r["code"]})'
    elif p in big: cls[p] = '予算(800万なら解ける)'
    elif r['rounds'] and r['capops'] * 2 >= r['rounds']: cls[p] = 'AR の上限(半分以上の回で相似が1回の上限)'
    else: cls[p] = '規則・補助作図が足りない'
print(f'== {label}: 解けた {len(solved)} / 未解決 {len(unsolved)} / 計 {len(rows)}')
by = defaultdict(list)
for p in unsolved: by[cls[p]].append(p)
for c, ps in sorted(by.items(), key=lambda x: -len(x[1])):
    diff = [data[p][0] for p in ps if data.get(p, (None,))[0] is not None]
    print(f'-- {c}: {len(ps)} 問(難易度の平均 {sum(diff)/max(len(diff),1):.2f})')
    goals = Counter(words(p)[1] for p in ps)
    print('   目標: ' + ', '.join(f'{g} {n}' for g, n in goals.most_common()))
    print('   ' + ' '.join(p.replace('hageo:', '') for p in ps))
dif_s = [data[p][0] for p in solved if data.get(p, (None,))[0] is not None]
print(f'(解けた問題の難易度の平均 {sum(dif_s)/max(len(dif_s),1):.2f})')
# 作図の語: 未解決(予算を除く)と解けた問題での出現率
hard = [p for p in unsolved if not cls[p].startswith('予算')]
fs, fu = Counter(w for p in solved for w in words(p)[0]), Counter(w for p in hard for w in words(p)[0])
print(f'-- 作図の語の出現率(予算で解けるものを除く未解決 {len(hard)} 問 / 解けた {len(solved)} 問)、未解決に偏っている順')
cand = [w for w in set(fs) | set(fu) if fu[w] >= 4]
cand.sort(key=lambda w: -((fu[w] + 0.5) / len(hard)) / ((fs[w] + 0.5) / len(solved)))
for w in cand[:15]:
    print(f'   {w:<28} 未解決 {fu[w]:3d}/{len(hard)}   解けた {fs[w]:3d}/{len(solved)}')
gs, gu = Counter(words(p)[1] for p in solved), Counter(words(p)[1] for p in hard)
print('-- 目標の述語(未解決 / 解けた): ' + ', '.join(f'{g} {gu[g]}/{gs[g]}' for g in sorted(set(gs) | set(gu), key=lambda g: -gu[g])))

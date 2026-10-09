"""AR の等式の種類を外した測定(res/abl/<種類>_hg.tsv、基準 res/abl/base_hg.tsv)で落ちた HAGeo の問題が、どんな作図・目標を
多く含むかを数える。usage: ablation_features.py
各種類について: 落ちた問題の数と、落ちた問題での語(作図の名前・目標の述語)の出現率 / 基準で解けた問題全体での出現率。
"""
import glob, os, re
from collections import Counter

S = os.path.dirname(os.path.abspath(__file__))
data = {}
for l in open(os.path.join(S, '..', 'data', 'hageo409.tsv'), encoding='utf-8'):
    f = l.rstrip('\n').split('\t')
    if len(f) >= 3: data['hageo:' + f[0]] = f[2]

def words(p):
    text = data.get(p, '')
    body, _, goal = text.partition('Prove:')
    ws = {m for m in re.findall(r'=\s*([a-z_0-9]+)', body)}
    g = goal.split()
    if g: ws.add('目標:' + g[0])
    return ws

def solved(path):
    return {f[0] for f in (l.rstrip('\n').split('\t') for l in open(path, encoding='utf-8')) if len(f) > 1 and f[1] == '1'}

base = solved(os.path.join(S, 'res', 'abl', 'base_hg.tsv'))
base_freq = Counter(w for p in base for w in words(p))
for path in sorted(glob.glob(os.path.join(S, 'res', 'abl', '*_hg.tsv'))):
    kind = os.path.basename(path)[:-len('_hg.tsv')]
    if kind == 'base': continue
    lost = sorted(base - solved(path))
    if not lost: continue
    freq = Counter(w for p in lost for w in words(p))
    top = sorted(freq, key=lambda w: -(freq[w] / len(lost)) / max(base_freq[w] / len(base), 1e-9))
    top = [w for w in top if freq[w] >= 2][:6]
    cells = ', '.join(f'{w} {freq[w]}/{len(lost)}(全体 {base_freq[w]}/{len(base)})' for w in top)
    print(f'{kind:<14} 落ちた {len(lost):2d}: {cells}')

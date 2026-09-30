# usage: cmp.py <基準.tsv> <新.tsv> : 両方で解けた問題の仕事量の比(合計・幾何平均・中央値・20%超の悪化/改善)と、落ちた/増えた問題。
import sys, math, statistics
def load(p):
    d = {}
    for l in open(p, encoding='utf-8'):
        f = l.rstrip('\n').split('\t')
        if len(f) < 3 or not f[1].isdigit(): continue
        d[f[0]] = (int(f[1]), int(f[2]) if f[2].isdigit() else None)
    return d
base = load(sys.argv[1]); new = load(sys.argv[2])
both = [p for p in base if p in new and base[p][0] == 1 and new[p][0] == 1 and base[p][1] and new[p][1]]
ratios = {p: new[p][1] / base[p][1] for p in both}
gm = math.exp(sum(math.log(r) for r in ratios.values()) / len(ratios)) if ratios else float('nan')
med = statistics.median(ratios.values()) if ratios else float('nan')
tot_b = sum(base[p][1] for p in both) or 1; tot_n = sum(new[p][1] for p in both)
lost = sorted(p for p in base if base[p][0] == 1 and (p not in new or new[p][0] != 1))
gained = sorted(p for p in new if new[p][0] == 1 and (p in base and base[p][0] != 1))
worse = sorted(((r, p) for p, r in ratios.items() if r > 1.2), reverse=True)
better = sorted(((r, p) for p, r in ratios.items() if r < 0.8))
print(f"solved {sum(v[0] for v in new.values())} (base {sum(v[0] for v in base.values())})  both-solved n={len(both)}  total {tot_n/tot_b-1:+.1%}  geomean {gm-1:+.1%}  median {med-1:+.1%}  worse>20%: {len(worse)}  better>20%: {len(better)}")
print("  lost:", lost, " gained:", gained)
print("  worst:", [(p, f"{r:.2f}x") for r, p in worse[:4]])
print("  best :", [(p, f"{r:.2f}x") for r, p in better[:4]])

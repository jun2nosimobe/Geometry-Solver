# usage: aux_rich_sum.py <label> : aux_rich.sh の結果(res/auxrich_<label>/)を集計する(来歴 #110)。
import glob, os, sys
d = os.path.join(os.path.dirname(os.path.abspath(__file__)), "res", "auxrich_" + sys.argv[1])
runs, ranks, dists, ghs, skips, auxpt, hits = {}, [], {}, [], [], [], []
for f in glob.glob(d + "/*.sum"):
    for line in open(f, encoding="utf-8"):
        t = line.rstrip("\n").split("\t")
        if t[0] == "RUN": runs[t[1]] = t[2] == "1"
        elif t[0] == "AUXRANK": ranks.append(t[1:])
        elif t[0] == "AUXDIST": dists[t[1]] = t[2:]
        elif t[0] == "AUXGH": ghs.append(t[1:])
        elif t[0] == "AUXSKIP": skips.append(t[1:])
        elif t[0] == "AUXPT": auxpt.append(t[1:])
        elif t[0] == "AUXHIT": hits.append(t[1:])
print(f"問題 {len(runs)} / 解けた {sum(runs.values())} / 測れた問題 {len(dists)}")
print(f"証明に使った補助点 {len(auxpt)}(問題 {len(set(a[0] for a in auxpt))}) → 測れた {len(ranks)}(問題 {len(set(r[0] for r in ranks))})")
sk = {}
for s in skips: sk[s[2]] = sk.get(s[2], 0) + 1
print("  測れなかった理由:", sk)
# AUXRANK: 0 problem 1 name 2 type 3 deg 4 nt 5 pg 6 pgl 7 gh 8 p_nt 9 p_pg 10 p_pgl 11 p_deg 12 nc 13 in_c 14 ghl
def mean(xs): return sum(xs) / len(xs) if xs else float("nan")
probs = sorted(set(r[0] for r in ranks))
def per_prob(idx): return mean([mean([float(r[idx]) for r in ranks if r[0] == p]) for p in probs])
print("使った補助点の候補の中での順位(0 = 最上位、0.5 = でたらめ、1 = 最下位。問題ごとに平均してから平均 / 補助点ごと)")
for name, idx in [("因子の共有", 8), ("事実の増え", 9), ("低い次数の事実の増え", 10), ("次数の低さ", 11)]:
    print(f"  {name:<12} {per_prob(idx):.3f} / {mean([float(r[idx]) for r in ranks]):.3f}")
for name, idx in [("因子の共有", 4), ("事実の増え", 5), ("低い次数の事実の増え", 6)]:
    print(f"  {name} が 0: {sum(1 for r in ranks if r[idx] == '0')}/{len(ranks)}")
print(f"  目標が入る(補助点の事実は全て): {sum(1 for r in ranks if r[7] == 'true')}/{len(ranks)}  (低い次数・定義だけ): {sum(1 for r in ranks if r[14] == 'true')}/{len(ranks)}")
by_type = {}
for r in ranks: by_type.setdefault(r[2], []).append(r)
for k, rs in sorted(by_type.items()):
    print(f"  {k:<34} {len(rs):>3}  共有>0 {sum(1 for r in rs if r[4] != '0'):>3}  事実>0 {sum(1 for r in rs if r[5] != '0'):>3}  低次>0 {sum(1 for r in rs if r[6] != '0'):>3}")
# AUXDIST: 0 ncands 1 neval 2 nt>0 3 max_nt 4 pg>0 5 max_pg 6 pgl>0 7 gh 8 goal_low 9 ghl
for lab, sel in [("解けた", True), ("解けなかった", False)]:
    ps = [p for p in dists if runs.get(p) == sel]
    ne = sum(int(dists[p][1]) for p in ps)
    if not ne: continue
    print(f"{lab} {len(ps)} 問・候補 {ne}: 因子の共有>0 {sum(int(dists[p][2]) for p in ps)/ne:.1%}  事実の増え>0 {sum(int(dists[p][4]) for p in ps)/ne:.1%}  低い次数の事実の増え>0 {sum(int(dists[p][6]) for p in ps)/ne:.1%}")
    print(f"    目標が入る候補(事実は全て) {sum(int(dists[p][7]) for p in ps)}(問題 {sum(1 for p in ps if int(dists[p][7]) > 0)})  (低い次数・定義だけ) {sum(int(dists[p][9]) for p in ps)}(問題 {sum(1 for p in ps if int(dists[p][9]) > 0)})  目標が初めから低い次数・既知の空間 {sum(1 for p in ps if dists[p][8] == 'Some(true)')}")
need = {p for p in dists if dists[p][8] != "Some(true)"}
for lab, sel in [("解けた", True), ("解けなかった", False)]:
    ps = [p for p in need if runs.get(p) == sel]
    hit = [p for p in ps if int(dists[p][9]) > 0]
    print(f"{lab}・目標が初めは低い次数・既知の空間に無い {len(ps)} 問: 補助点1つで入る候補がある問題 {len(hit)}(候補 {sum(int(dists[p][9]) for p in hit)})")
    for p in hit: print("   ", p, dists[p][9], "/", dists[p][1])
for g in ghs:
    if g[-1] == "true" and g[0] in need: print("GH_LOW", "解けた" if runs.get(g[0]) else "解けなかった", *g)
# AUXHIT: 0 problem 1 kind 2 deg 3 nt 4 pg 5 pgl 6 p_nt 7 p_pg 8 p_pgl 9 p_deg 10 nc
if hits:
    print(f"目標を低い次数の空間に入れる候補 {len(hits)} 個の順位: 因子の共有 {mean([float(h[6]) for h in hits]):.3f}  事実の増え {mean([float(h[7]) for h in hits]):.3f}  低い次数の事実の増え {mean([float(h[8]) for h in hits]):.3f}  次数の低さ {mean([float(h[9]) for h in hits]):.3f}")

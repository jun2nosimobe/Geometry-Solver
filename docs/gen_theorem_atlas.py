#!/usr/bin/env python3
"""Atlas §07 定理(docs/theorems.html)を作る。

入力(すべて docs/ の下):
  theorems.json              geom_solver theorem-atlas の出力(パターン・作図・結論・lint・証人・見積もりの順序)
  theorem_stats_default.tsv  bench/theorem_stats.sh の出力(既定の定理集合、全44問)
  theorem_stats_rules.tsv    bench/theorem_stats.sh "--rules=... --chord-theorems" の出力(既定外の定理と、AR が置き換える2定理の実測に使う)
  notes/theorem_catalog.md   手書きの「主張」と「問題点」(見出し = 定理名)

作り直し方(リポジトリ直下で):
  cargo build --release
  ./target/release/geom_solver theorem-atlas nine_point_full | sed -n '/^{"plan_problem"/,$p' > docs/theorems.json
  bench/theorem_stats.sh > docs/theorem_stats_default.tsv
  bench/theorem_stats.sh "--rules=chord,parallelogram,spiral --chord-theorems" > docs/theorem_stats_rules.tsv
  python3 docs/gen_theorem_atlas.py
"""
import html, json, os, re, sys
from collections import defaultdict

D = os.path.dirname(os.path.abspath(__file__))

def md_inline(s):
    s = html.escape(s, quote=False)
    s = re.sub(r'`([^`]+)`', r'<code>\1</code>', s)
    s = re.sub(r'\*\*([^*]+)\*\*', r'<b>\1</b>', s)
    s = re.sub(r'#(\d+)', r'<a class="secref" href="ledger.html#l\1">#\1</a>', s)
    s = re.sub(r'\b(b\d+)\b', r'<a class="secref" href="backlog.html#\1">\1</a>', s)
    return s

def md_block(lines):
    out, para, items = [], [], []
    def flush():
        nonlocal para, items
        if para:
            out.append('<p>' + md_inline(' '.join(para)) + '</p>'); para = []
        if items:
            out.append('<ul>' + ''.join('<li>' + md_inline(i) + '</li>' for i in items) + '</ul>'); items = []
    for raw in lines:
        l = raw.rstrip()
        if not l.strip():
            flush(); continue
        if l.startswith('- '):
            if para: flush()
            items.append(l[2:]); continue
        if l.startswith('  ') and items:
            items[-1] += ' ' + l.strip(); continue
        if items: flush()
        para.append(l.strip())
    flush()
    return '\n'.join(out)

def load_catalog():
    text = open(os.path.join(D, 'notes', 'theorem_catalog.md'), encoding='utf-8').read()
    text = re.sub(r'<!--.*?-->', '', text, flags=re.S)
    cat = {}
    for sec in re.split(r'^## ', text, flags=re.M)[1:]:
        name, _, body = sec.partition('\n')
        parts = {}
        for sub in re.split(r'^### ', body, flags=re.M)[1:]:
            h, _, b = sub.partition('\n')
            parts[h.strip()] = md_block(b.splitlines())
        cat[name.strip()] = parts
    return cat

def load_stats(fn):
    per = defaultdict(lambda: defaultdict(int))
    probs = set()
    proof = defaultdict(list)
    total_work = 0
    path = os.path.join(D, fn)
    if not os.path.exists(path): return per, probs, proof, 0
    for l in open(path, encoding='utf-8'):
        f = l.rstrip('\n').split('\t')
        if len(f) < 8: continue
        p, solved, name, att, cap, avg, m, pr = f[0], f[1] == '1', f[2], int(f[3]), int(f[4]), int(f[5]), int(f[6]), int(f[7])
        probs.add(p)
        s = per[name]
        s['att'] += att; s['cap'] += cap; s['work'] += att * avg; s['match'] += m
        s['probs'] += 1
        if m > 0: s['matched_probs'] += 1
        if solved and pr > 0:
            proof[name].append(p)
        total_work += att * avg
    return per, probs, proof, total_work

def main():
    js = open(os.path.join(D, 'theorems.json'), encoding='utf-8').read()
    data = json.loads(js[js.index('{"plan_problem"'):])
    cat = load_catalog()
    st_def = load_stats('theorem_stats_default.tsv')
    st_rul = load_stats('theorem_stats_rules.tsv')
    names = [t['name'] for t in data['theorems']]
    for n in cat:
        if n not in names: print('警告: カタログの見出しに一致する定理が無い:', n, file=sys.stderr)
    for n in names:
        if n not in cat: print('警告: カタログに見出しが無い定理:', n, file=sys.stderr)

    def stat_block(t):
        per, _, proof, total = st_def if t['group'] == '既定' else st_rul
        src = '既定設定・全44問' if t['group'] == '既定' else '既定設定 + ' + t['group'] + '・全44問'
        s = per.get(t['name'])
        if not s:
            return '<p class="muted">実測なし(' + html.escape(src) + ')</p>', None
        share = 100.0 * s['work'] / total if total else 0
        pp = proof.get(t['name'], [])
        rows = [
            ('試行した問題', f"{s['probs']}問"),
            ('試行回数(合計)', f"{s['att']:,}"),
            ('探索量(試行×平均 dfs_call)', f"{s['work']:,}(全定理の {share:.1f}%)"),
            ('上限(dfs_cap)到達', f"{s['cap']:,}回"),
            ('マッチ成立', f"{s['match']:,}回・{s['matched_probs']}問"),
            ('証明に登場した問題', (f"{len(pp)}問: " + ', '.join(pp)) if pp else '0問'),
        ]
        body = ''.join(f'<tr><th>{html.escape(k)}</th><td>{html.escape(v)}</td></tr>' for k, v in rows)
        return f'<p class="muted">{html.escape(src)}</p><table class="kv">{body}</table>', (share, len(pp), s['match'])

    def pattern_table(t):
        order = {i: k for k, (i, c) in enumerate(t['plan'])}
        cost = {i: c for (i, c) in t['plan']}
        rows = []
        for i, (kind, text) in enumerate(t['patterns']):
            cls = {'需要を立てる': 'demand', 'その場で作る': 'build', '照合': 'lookup'}.get(kind, '')
            c = cost.get(i)
            c = '∞' if c is None else f'{c:g}'
            rows.append(f'<tr class="{cls}"><td class="num">{i}</td><td>{html.escape(kind)}</td><td><code>{html.escape(text)}</code></td>'
                        f'<td class="num">{order[i] + 1}</td><td class="num">{c}</td></tr>')
        return ('<table class="pat"><tr><th>#</th><th>種類</th><th>パターン</th><th>選ばれる順</th><th>その時の見積もり</th></tr>'
                + ''.join(rows) + '</table>')

    missing = sorted(st_def[1] - st_rul[1])
    ar_rules = data.get('ar_rules', [])
    ar_rows = []
    for kind in ['等式', '検出→等式', '検出']:
        for r in [r for r in ar_rules if r['kind'] == kind]:
            ledger = '・'.join('#' + x for x in r['ledger'].split('・'))
            ar_rows.append(f'<tr><td>{html.escape(kind)}</td><td><b>{html.escape(r["name"])}</b></td><td>{md_inline(r["situation"])}</td>'
                           f'<td>{md_inline(r["relation"])}</td><td class="num">{md_inline(ledger)}</td></tr>')
    missing_note = (f'既定外の規則を足した測定では {len(missing)}問(' + '・'.join(f'<code>{html.escape(p)}</code>' for p in missing)
                    + ')の統計が取れていない(<code>theorem_stats.sh</code> の時間の上限 900秒で打ち切られ、<code>--stats</code> の表が出ない。2026-09-29 は2問とも)。') if missing else ''
    cards, summary = [], []
    for t in data['theorems']:
        c = cat.get(t['name'], {})
        demands = [p[1] for p in t['patterns'] if p[0] == '需要を立てる']
        builds = [p[1] for p in t['patterns'] if p[0] == 'その場で作る']
        sb, sm = stat_block(t)
        first_i, first_c = t['plan'][0]
        first = t['patterns'][first_i][1]
        n_pat = len(t['patterns'])
        over = t['vars'] > 20 or n_pat > 20
        lint = ''.join(f'<li><b>{html.escape(k)}</b>: {html.escape(v)}</li>' for k, v in t['lint'] if k not in ('需要を出す', 'その場で作る'))
        tags = [f'<span class="tag">{html.escape(t["group"])}</span>', f'<span class="tag">変数{t["vars"]}・パターン{n_pat}</span>']
        if over: tags.append('<span class="tag warn">規模が上限超過</span>')
        if demands: tags.append(f'<span class="tag">需要 {len(demands)}</span>')
        if not t['witness']: tags.append('<span class="tag">証人なし</span>')
        anchor = f"t{t['index']}"
        cards.append(f'''<details class="item" id="{anchor}" data-status="{'default' if t['group'] == '既定' else 'rules'}">
  <summary><span class="idx">{t['index']}</span><span class="t">{html.escape(t['name'])}</span>{''.join(tags)}</summary>
  <div class="body">
    <h4>主張</h4>{c.get('主張', '<p class="muted">(未記入)</p>')}
    <h4>作図の需要とその場の作図</h4>
    <p>{'需要を立てる(図に無ければ補助作図の候補にする): ' + '・'.join('<code>' + html.escape(d) + '</code>' for d in demands) if demands else '需要は立てない。'}</p>
    <p>{'その場で作る(親が揃えば図に足す): ' + '・'.join('<code>' + html.escape(b) + '</code>' for b in builds) if builds else 'その場では作らない。'}</p>
    <p>結論のときに作る: {'・'.join('<code>' + html.escape(x) + '</code>' for x in t['constructions']) or 'なし'}</p>
    <p>結論: {'・'.join('<code>' + html.escape(x) + '</code>' for x in t['conclusions'])}</p>
    <h4>見積もり(cost の estimate)</h4>
    <p>束縛が空の状態から、<code>dfs_match</code> と同じ選び方(いちばん安いパターン、同点なら先頭)で消費される順序と、そのときの <code>estimate_cost</code>。
    入口は <code>{html.escape(first)}</code>(見積もり {'∞' if first_c is None else f'{first_c:g}'})。</p>
    {pattern_table(t)}
    <h4>実測</h4>{sb}
    <h4>現状の問題点</h4>{c.get('問題点', '<p class="muted">(未記入)</p>')}
    {('<h4>lint の指摘</h4><ul>' + lint + '</ul>') if lint else ''}
    <p class="muted">証人(この定理が発火しないと解けない問題): {html.escape(t['witness'] or 'なし')}</p>
  </div>
</details>''')
        share = f'{sm[0]:.1f}%' if sm else '—'
        summary.append(f'<tr><td class="num">{t["index"]}</td><td><a href="#{anchor}">{html.escape(t["name"])}</a></td><td>{html.escape(t["group"])}</td>'
                       f'<td class="num">{t["vars"]}/{n_pat}</td><td class="num">{len(demands)}</td><td class="num">{share}</td>'
                       f'<td class="num">{sm[2] if sm else "—"}</td><td class="num">{sm[1] if sm else "—"}</td></tr>')

    page = f'''<!doctype html>
<html lang="ja">
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Atlas · 定理</title>
<link rel="stylesheet" href="atlas.css">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Fraunces:opsz,wght@9..144,500;9..144,600&family=IBM+Plex+Sans:wght@400;500;600&family=IBM+Plex+Mono:wght@400;500;600&display=swap">
<style>
  table.pat, table.kv, table.sum {{ border-collapse: collapse; font-size: 13px; margin: 6px 0; width: 100%; }}
  table.pat td, table.pat th, table.kv td, table.kv th, table.sum td, table.sum th {{ padding: 3px 8px; border-bottom: 1px solid var(--rule, #e3e3e3); text-align: left; vertical-align: top; }}
  table.pat tr.demand td {{ background: var(--warning-soft, #fff4db); }}
  table.pat tr.build td {{ background: var(--accent-soft, #eef3ff); }}
  td.num {{ text-align: right; font-variant-numeric: tabular-nums; white-space: nowrap; }}
  .muted {{ color: var(--ink-soft, #777); font-size: 13px; }}
  .tag.warn {{ background: var(--danger-soft, #fde2e2); color: var(--danger, #b00020); }}
  details.item h4 {{ margin: 14px 0 4px; font-size: 14px; }}
  .body code {{ font-size: 12.5px; }}
  .wrap-x {{ overflow-x: auto; }}
</style>
<nav class="topnav"><div class="in"><span class="brand">Geometry Solver Atlas</span><a href="atlas.html">概要 §00–03</a><a href="ledger.html">来歴 §04</a><a href="backlog.html">改善候補 §05</a><a href="notes.html">設計ノート §06</a><a href="theorems.html" aria-current="page">定理 §07</a></div></nav>
<div class="wrap">
<section id="theorems">
<div class="section-head"><span class="section-num">07</span><h2>定理</h2></div>
<p class="section-note">登録されている全定理({len(data['theorems'])}件)と、代数的な追跡(AR)の規則(<a href="#ar">{len(data.get('ar_rules', []))}件</a>)の、主張・作図の需要・見積もり・実測・現状の問題点。パターン・作図・結論・見積もりの順序は
コード(<code>geom_solver theorem-atlas</code>)から、実測はベンチ(<code>bench/theorem_stats.sh</code>)から、主張と問題点は
<a href="notes/theorem_catalog.md">notes/theorem_catalog.md</a> から <code>docs/gen_theorem_atlas.py</code> が作る。作り直し方はそのスクリプトの先頭。
見積もりの順序は <code>{html.escape(data['plan_problem'])}</code> の図の上で計算した(値は図に依存する)。</p>

<h3>見積もり(estimate_cost)の読み方</h3>
<div class="wrap-x"><table class="sum">
<tr><th>パターン</th><th>束縛の状態</th><th>見積もり</th></tr>
<tr><td>一致 a ≡ b</td><td>両方束縛 / 片方 / どちらも未束縛(自己束縛)</td><td>0 / 1 / 15</td></tr>
<tr><td>接続 child ∈ parent</td><td>両方束縛 / 片方 / どちらも未束縛</td><td>0 / 束縛側の隣接数+1 / 親の型の実体数×5+10</td></tr>
<tr><td>定義(照合・作る・需要)</td><td>全部束縛 / 一部 / どれも未束縛</td><td>0 / 10+未束縛の数×20 / 100+引数の数+種類の加点(中点・長さ・交点 0、直線・垂線・接線 10、方向・角・外接円 20、その他 5)</td></tr>
<tr><td>制約(相異なる・順序)・否定</td><td>全変数が束縛されるまで</td><td>∞(最後まで選ばれない。束縛済みの範囲は毎回検査して早く枝を切る)</td></tr>
</table></div>
<p class="section-note">束縛済みの変数の熱(<code>heat_with_degree</code>)の合計だけ安くする(基本の見積もりの半分まで)。
<b>どれも未束縛の一致(自己束縛)は 15 と安く、一部だけ束縛された定義(25 以上)より先に選ばれる</b> ― 角の一致を2つ持つ定理は、
2つの角の同値類を続けて選び、構造でつなぐ前に組み合わせを舐める(#71・スパイラル相似の分析)。自己束縛の候補は熱の順に並べて上限で切る
(通常 40。同じ型の自己束縛を2つ以上持つ定理は狭い上限 5 から始めて、手詰まりのたびに 40 まで広げる)。</p>

<h3>全体に共通する問題</h3>
<ul>
<li><b>「相異なる」の2つの役割。</b> <code>distinct</code> は e-graph 上で別の実体であることしか見ない。図の上では同じなのにまだ一致が証明されていない
2つの図形を別物として扱うと、退化した配置で偽の結論が出る(#75)。一致すると定理が偽になる相異は「非退化」(図の上でも相異なる)として書き、
完成したマッチで数値的に確かめる(#78)。これで、座標を置ける問題ではマージ前の検査(#76)を外しても偽のマージが起きない(#79)。
パターン表の種類「非退化」がそれ。</li>
<li><b>結論やその場の作図で図形を作る定理は、使われない発火で図を膨らませる。</b> 作られた有向角の9割以上・積のすべて・外接円のほとんどが証明に出ない(b7、#38)。
中点や直線を作らず「図にあるものだけ照合する」形にすると課税が消えることが多い(#68・#74)。</li>
<li><b>需要は探索の副作用として立つ。</b> 補助線の需要は、定理のマッチが直線を欲しがって空振りした回数で、探索の順序に依存する(b33)。</li>
<li><b>角の足し算を規則で総当たりしている。</b> 有向角の加法性・交替律・同位角の3つは有向角の線形な関係で、代数的な追跡(AR、#82)が同じ等式を出せる。
ただし規則は新しい角の実体も作るので、まだ外せない(外すと遅くなる問題が多い)。</li>
</ul>

<h3>一覧</h3>
<div class="wrap-x"><table class="sum">
<tr><th>#</th><th>定理</th><th>入り方</th><th>変数/パターン</th><th>需要</th><th>探索量の割合</th><th>マッチ</th><th>証明に登場(問)</th></tr>
{''.join(summary)}
</table></div>
<p class="section-note">探索量の割合・マッチ・証明に登場は、既定の定理は既定設定の全44問、既定外の定理はその規則を足した全44問での値。{missing_note}</p>

<div class="toolbar"><input type="search" id="q" placeholder="定理名・パターン・問題点を検索(空白区切りで AND)"><button type="button" data-filter="all" aria-pressed="true">すべて</button><button type="button" data-filter="default" aria-pressed="false">既定</button><button type="button" data-filter="rules" aria-pressed="false">既定外(--rules)</button><button type="button" id="expand">全て開く</button><button type="button" id="collapse">全て閉じる</button><span class="count" id="count"></span></div>
<div class="group"><div class="group-title">定理 · {len(data['theorems'])}件</div>
{chr(10).join(cards)}
</div>

<h3 id="ar">代数的な追跡(AR)の規則 · {len(ar_rules)}件</h3>
<p class="section-note"><code>logic_core/ar.rs</code>(既定、<code>--no-ar</code> で外す)。定理のようにパターンを照合して結論を出すのではなく、
手が止まるたびに図から<b>線形な関係式</b>を集めて整数の格子(ℤⁿ ⊕ ℤ/4、エルミート標準形)に積み、まとめて閉じる。規則は2種類:
<b>等式</b>は「図にこの状況があれば、格子にこの関係式を足す」(定理の代わり)、<b>検出</b>は「格子でこの式が 0 に還元されれば、e-graph にこの結論を入れる」。
<b>検出→等式</b>は、線形でない一歩(三角形が閉じる条件など)を検出で済ませてから関係式を足すもの。格子は毎回作り直す(#85)。<br>
記号: s(X,Y) は同じ直線の上の2点の差の形式的な対数(数値の対数は取らない。積・商が和・差になる)。β(D) は方向 D の角の記号、
θ_C(P) は円 C の上の点 P の記号、JX・IX は虚円点 J・I から点 X への線束の要素、T はねじれの記号(4T = 0、2T = log(−1)、T = log i)。
κ・c・log a は、その状況ごとに新しく置く定数の記号。一覧はコードの <code>AR_RULES</code> から作る。</p>
<div class="wrap-x"><table class="sum">
<tr><th>種類</th><th>規則</th><th>状況(前提)</th><th>格子に足す関係式 / 出す結論</th><th>来歴</th></tr>
{''.join(ar_rows)}
</table></div>

<h3>合同閉包に組み込まれた規則(定理ではない)</h3>
<p class="section-note">次の規則は定理のマッチングではなく、マージのたびに変化した実体の近傍だけを見る局所伝播として <code>mmp_core/congruence.rs</code> などに組み込まれている。どれも既にある実体をマージするだけで、図形を作らない。</p>
<ul>
<li><b>直線の一致</b>(<code>propagate_line_uniqueness</code>): 2点(無限遠点を含む)を共有する2直線は同じ。共有点は図の上でも相異なるものだけ数える。</li>
<li><b>交点の一意性</b>(<code>propagate_point_uniqueness</code>): 2直線の交点は1つ。非退化条件: 2直線が図の上でも別の直線(#78)。</li>
<li><b>二次曲線の一致</b>(<code>propagate_conic_uniqueness</code>): 3点(円)・5点を共有する二次曲線は同じ。非退化条件: 共有点から、どの4点も共線でない5点を選べる(#78)。
2直線に退化した二次曲線どうしは1本の直線を丸ごと共有でき、pappus の以前の証明はそこで誤ってマージしていた。</li>
<li><b>複比の一意性</b>(<code>propagate_cross_ratio_uniqueness</code>): 共線な3点を固定した複比が等しければ4点目は一致する(透視射影不変性の逆)。非退化条件: 固定した3点が図の上でも相異なる(#78)。
以前は証明の前提に「2つの複比が等しい」を記録していなかったので、その等式が偽のマージから来ていても証明は「厳密」に見えた(#76、centroid)。</li>
<li><b>代数的な追跡(AR)</b>: 上の<a href="#ar">代数的な追跡(AR)の規則</a>を参照。</li>
<li><b>自明な関係</b>(<code>apply_trivial_relations</code>): 垂線と直角、垂直方向の対合、調和共役の対合など、定義から機械的に従うもの。</li>
<li><b>スパイラル相似の局所伝播</b>(<code>mmp_core/spiral_prop.rs</code>、既定外 <code>--rules=spiral-prop</code>): 角の同値類に新しく合流した定義との組だけを見る差分評価。
結論の図形(中点・直線・角)が既にあるときだけマージする。課税は小さいが、2016ARMO は結論で図形を作らないと解けないので、既定では使わない(#75)。</li>
</ul>
</section>
<footer>Geometry Solver Atlas — docs/theorems.html(docs/gen_theorem_atlas.py が生成)</footer>
</div>
<script src="atlas.js"></script>
</html>
'''
    open(os.path.join(D, 'theorems.html'), 'w', encoding='utf-8', newline='\n').write(page)
    print('wrote docs/theorems.html:', len(data['theorems']), 'theorems')

if __name__ == '__main__':
    main()

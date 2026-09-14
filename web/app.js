'use strict';
// 作図インターフェース。
//
// ここは「作図手順(DAG)の編集器」であって、定理の真偽は一切判断しない。
// 画面に描くための浮動小数点評価だけを持ち、「この図で何が成り立つか」は
// serve.rs 経由でエンジン(有限体上の乱数評価)に投げる。
// 浮動小数点で「ほぼ一致」を見て何かを主張することは意図的にしていない。

// ============================================================
// モデル
// ============================================================
// obj = { name, kind:'point'|'line'|'circle', op, args:[name...], x, y, on }
//   x,y は自由点・曲線上の点だけが持つ(画面上のどこに置いたか)
//   on  は曲線上の点が乗っている曲線名
let objects = [];
let history = [];
// エンジンが自由作図で足してきた補助的な図形。ユーザーの作図とは分けて
// 持ち、薄い破線で描く。掴めないし、エンジンへ送り返しもしない
// (送り返すと補助作図の上にさらに補助作図が積まれて発散するため)。
// 「図に取り込む」を押したときだけ objects へ移す。
let aux = [];

const POINT_NAMES = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
function freshName(kind) {
  const used = new Set(objects.map(o => o.name));
  const pick = (cand) => { if (!used.has(cand)) return cand; return null; };
  if (kind === 'point') {
    for (const ch of POINT_NAMES) { const n = pick(ch); if (n) return n; }
    for (let i = 1; ; i++) for (const ch of POINT_NAMES) { const n = pick(ch + i); if (n) return n; }
  }
  const prefix = kind === 'line' ? 'l' : 'k';
  for (let i = 1; ; i++) { const n = pick(prefix + i); if (n) return n; }
}

function byName(n) { return objects.find(o => o.name === n); }

function snapshot() {
  history.push(JSON.stringify(objects));
  if (history.length > 200) history.shift();
}
function undo() {
  if (!history.length) return;
  objects = JSON.parse(history.pop());
  pending = [];
  invalidateFindings();
  refresh();
}

/** その図形に(直接・間接に)依存している図形も一緒に消す。 */
function removeCascade(name) {
  const doomed = new Set([name]);
  let grew = true;
  while (grew) {
    grew = false;
    for (const o of objects) {
      if (doomed.has(o.name)) continue;
      const deps = (o.args || []).concat(o.on ? [o.on] : []);
      if (deps.some(d => doomed.has(d))) { doomed.add(o.name); grew = true; }
    }
  }
  objects = objects.filter(o => !doomed.has(o.name));
}

// ============================================================
// 数値評価(描画専用)
// ============================================================
// point  -> {x, y}
// line   -> {a, b, c}  ax+by+c=0 を a²+b²=1 に正規化したもの
// circle -> {x, y, r}
// 計算できない(平行な2直線の交点、共線な3点の外接円など)ときは null。

function lineThrough(p, q) {
  if (!p || !q) return null;
  const a = p.y - q.y, b = q.x - p.x, c = p.x * q.y - q.x * p.y;
  const n = Math.hypot(a, b);
  if (n < 1e-9) return null;
  return { a: a / n, b: b / n, c: c / n };
}
function meet(l, m) {
  if (!l || !m) return null;
  const det = l.a * m.b - m.a * l.b;
  if (Math.abs(det) < 1e-9) return null;   // 平行
  return { x: (l.b * m.c - m.b * l.c) / det, y: (l.c * m.a - m.c * l.a) / det };
}
function perpLine(l, p) {
  if (!l || !p) return null;
  return { a: -l.b, b: l.a, c: l.b * p.x - l.a * p.y };
}
function paraLine(l, p) {
  if (!l || !p) return null;
  return { a: l.a, b: l.b, c: -(l.a * p.x + l.b * p.y) };
}
function circleThrough(p, q, r) {
  if (!p || !q || !r) return null;
  const d = 2 * (p.x * (q.y - r.y) + q.x * (r.y - p.y) + r.x * (p.y - q.y));
  if (Math.abs(d) < 1e-9) return null;     // 共線
  const sp = p.x * p.x + p.y * p.y, sq = q.x * q.x + q.y * q.y, sr = r.x * r.x + r.y * r.y;
  const cx = (sp * (q.y - r.y) + sq * (r.y - p.y) + sr * (p.y - q.y)) / d;
  const cy = (sp * (r.x - q.x) + sq * (p.x - r.x) + sr * (q.x - p.x)) / d;
  return { x: cx, y: cy, r: Math.hypot(p.x - cx, p.y - cy) };
}
function tangentAt(k, p) {
  if (!k || !p) return null;
  const a = p.x - k.x, b = p.y - k.y;
  const n = Math.hypot(a, b);
  if (n < 1e-9) return null;
  return { a: a / n, b: b / n, c: -((a / n) * p.x + (b / n) * p.y) };
}
function radicalAxis(k1, k2) {
  if (!k1 || !k2) return null;
  const a = 2 * (k2.x - k1.x), b = 2 * (k2.y - k1.y);
  const c = (k1.x * k1.x + k1.y * k1.y - k1.r * k1.r) - (k2.x * k2.x + k2.y * k2.y - k2.r * k2.r);
  const n = Math.hypot(a, b);
  if (n < 1e-9) return null;               // 同心円
  return { a: a / n, b: b / n, c: c / n };
}
/** 円k上の既知点pを通る直線lの、もう一方の交点。pが根なので1次で解ける。 */
function secondOnCircle(p, l, k) {
  if (!p || !l || !k) return null;
  const dx = -l.b, dy = l.a;               // 正規化済みなので単位ベクトル
  const t = -2 * (dx * (p.x - k.x) + dy * (p.y - k.y));
  return { x: p.x + t * dx, y: p.y + t * dy };
}
function projectOnLine(l, p) {
  const s = l.a * p.x + l.b * p.y + l.c;
  return { x: p.x - s * l.a, y: p.y - s * l.b };
}
function projectOnCircle(k, p) {
  const dx = p.x - k.x, dy = p.y - k.y;
  const n = Math.hypot(dx, dy);
  if (n < 1e-9) return { x: k.x + k.r, y: k.y };
  return { x: k.x + k.r * dx / n, y: k.y + k.r * dy / n };
}

/** 作図順に一度なめて、全図形の数値を出す。 */
function evaluate() {
  const V = new Map();
  const g = (n) => V.get(n) || null;
  for (const o of objects.concat(aux)) {
    let v = null;
    switch (o.op) {
      case 'free': v = { x: o.x, y: o.y }; break;
      case 'on': {
        const c = g(o.on);
        // 親が動くと乗っているはずの点が曲線から外れるので、毎回投影し直す。
        if (c) v = (c.r !== undefined) ? projectOnCircle(c, o) : projectOnLine(c, o);
        break;
      }
      case 'inter': v = meet(g(o.args[0]), g(o.args[1])); break;
      case 'mid': {
        const p = g(o.args[0]), q = g(o.args[1]);
        if (p && q) v = { x: (p.x + q.x) / 2, y: (p.y + q.y) / 2 };
        break;
      }
      case 'second_lc': v = secondOnCircle(g(o.args[0]), g(o.args[1]), g(o.args[2])); break;
      case 'second_cc': {
        const p = g(o.args[0]), k1 = g(o.args[1]), k2 = g(o.args[2]);
        const ax = radicalAxis(k1, k2);
        v = ax ? secondOnCircle(p, ax, k1) : null;
        break;
      }
      case 'through':
        v = (o.kind === 'line') ? lineThrough(g(o.args[0]), g(o.args[1]))
                                : circleThrough(g(o.args[0]), g(o.args[1]), g(o.args[2]));
        break;
      case 'perp': v = perpLine(g(o.args[0]), g(o.args[1])); break;
      case 'para': v = paraLine(g(o.args[0]), g(o.args[1])); break;
      case 'tangent': v = tangentAt(g(o.args[0]), g(o.args[1])); break;
      case 'radical': v = radicalAxis(g(o.args[0]), g(o.args[1])); break;
    }
    V.set(o.name, v);
  }
  return V;
}

// ============================================================
// 道具
// ============================================================
// need: クリックしてほしい図形の種類の列。prompts はその各段の案内。
const TOOLS = [
  { id: 'move', label: '動かす', need: [], prompts: ['自由点をドラッグしてください(背景をドラッグで平行移動、ホイールで拡大縮小)'] },
  { id: 'point', label: '点', need: [], prompts: ['どこかをクリック。直線や円の上をクリックすると、その上を動く点になります'] },
  { id: 'line', label: '直線', need: ['point', 'point'], prompts: ['1点目', '2点目'] },
  { id: 'circle', label: '円 (3点)', need: ['point', 'point', 'point'], prompts: ['1点目', '2点目', '3点目'] },
  { id: 'inter', label: '交点 (2直線)', need: ['line', 'line'], prompts: ['1本目の直線', '2本目の直線'] },
  { id: 'mid', label: '中点', need: ['point', 'point'], prompts: ['1点目', '2点目'] },
  { id: 'perp', label: '垂線', need: ['line', 'point'], prompts: ['垂直にしたい直線', '通る点'] },
  { id: 'para', label: '平行線', need: ['line', 'point'], prompts: ['平行にしたい直線', '通る点'] },
  { id: 'tangent', label: '接線', need: ['circle', 'point'], prompts: ['円', '円周上の接点'] },
  { id: 'second_lc', label: '第2交点 (直線と円)', need: ['point', 'line', 'circle'], prompts: ['分かっている方の交点', '直線', '円'] },
  { id: 'second_cc', label: '第2交点 (2円)', need: ['point', 'circle', 'circle'], prompts: ['分かっている方の交点', '1つ目の円', '2つ目の円'] },
  { id: 'radical', label: '根軸 (2円)', need: ['circle', 'circle'], prompts: ['1つ目の円', '2つ目の円'] },
  { id: 'del', label: '削除', need: [], prompts: ['消したい図形をクリック(それに依存する図形も消えます)'] },
];
let tool = TOOLS[1];
let pending = [];          // 選択途中の図形名

function selectTool(id) {
  tool = TOOLS.find(t => t.id === id) || TOOLS[0];
  pending = [];
  document.querySelectorAll('#toolbar button').forEach(b =>
    b.setAttribute('aria-pressed', String(b.dataset.tool === tool.id)));
  updateHint();
  draw();
}
function updateHint(msg) {
  const el = document.getElementById('hint');
  if (msg) { el.textContent = msg; return; }
  const step = tool.need.length ? tool.prompts[pending.length] : tool.prompts[0];
  el.textContent = tool.need.length
    ? `${tool.label}: ${step} を選んでください (${pending.length}/${tool.need.length})`
    : step;
}

// ============================================================
// 画面と世界の座標
// ============================================================
const canvas = document.getElementById('canvas');
const ctx = canvas.getContext('2d');
let view = { ox: 0, oy: 0, scale: 90 };

function toScreen(p) { return { x: view.ox + p.x * view.scale, y: view.oy - p.y * view.scale }; }
function toWorld(sx, sy) { return { x: (sx - view.ox) / view.scale, y: (view.oy - sy) / view.scale }; }

function resize() {
  const dpr = window.devicePixelRatio || 1;
  const r = canvas.getBoundingClientRect();
  canvas.width = Math.max(1, Math.round(r.width * dpr));
  canvas.height = Math.max(1, Math.round(r.height * dpr));
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  if (view.ox === 0 && view.oy === 0) { view.ox = r.width / 2; view.oy = r.height / 2; }
  draw();
}

// ============================================================
// 描画
// ============================================================
let highlight = new Set();

function css(name) { return getComputedStyle(document.documentElement).getPropertyValue(name).trim(); }

function draw() {
  const V = evaluate();
  const r = canvas.getBoundingClientRect();
  ctx.clearRect(0, 0, r.width, r.height);

  const colDraw = css('--draw'), colSoft = css('--draw-soft'),
        colSel = css('--sel'), colAcc = css('--accent');

  // 直線と円(補助作図は後ろに薄く)
  for (const o of aux.concat(objects)) {
    const v = V.get(o.name);
    if (!v) continue;
    const hot = highlight.has(o.name);
    const chosen = pending.includes(o.name);
    const isAux = o.auxiliary === true;
    ctx.strokeStyle = hot ? colAcc : (chosen ? colSel : colSoft);
    ctx.lineWidth = hot || chosen ? 2.2 : 1.2;
    ctx.globalAlpha = (isAux && !hot) ? 0.42 : 1;
    ctx.setLineDash(isAux ? [5, 4] : []);
    if (o.kind === 'line') {
      const seg = clipLine(v, r);
      if (!seg) continue;
      ctx.beginPath(); ctx.moveTo(seg.p1.x, seg.p1.y); ctx.lineTo(seg.p2.x, seg.p2.y); ctx.stroke();
      labelAt(seg.at, o.name, hot ? colAcc : colSoft, 5, -5);
    } else if (o.kind === 'circle') {
      const c = toScreen(v), rr = v.r * view.scale;
      if (!isFinite(rr) || rr > 1e6) continue;
      ctx.beginPath(); ctx.arc(c.x, c.y, rr, 0, Math.PI * 2); ctx.stroke();
      labelAt({ x: c.x + rr * 0.71, y: c.y - rr * 0.71 }, o.name, hot ? colAcc : colSoft, 4, -4);
    }
  }
  ctx.globalAlpha = 1;
  ctx.setLineDash([]);
  // 点は最前面
  for (const o of aux.concat(objects)) {
    if (o.kind !== 'point') continue;
    ctx.globalAlpha = (o.auxiliary && !highlight.has(o.name)) ? 0.5 : 1;
    const v = V.get(o.name);
    if (!v) continue;
    const s = toScreen(v);
    const hot = highlight.has(o.name), chosen = pending.includes(o.name);
    const movable = o.op === 'free' || o.op === 'on';
    ctx.beginPath(); ctx.arc(s.x, s.y, hot || chosen ? 5.5 : 4, 0, Math.PI * 2);
    ctx.fillStyle = hot ? colAcc : (chosen ? colSel : colDraw);
    ctx.fill();
    if (movable) { ctx.strokeStyle = css('--panel'); ctx.lineWidth = 1.5; ctx.stroke(); }
    labelAt(s, o.name, hot ? colAcc : colDraw, 8, -8);
  }
  ctx.globalAlpha = 1;
  document.getElementById('script').textContent = serialize() || '(まだ何もありません)';
}

function labelAt(s, text, color, dx, dy) {
  ctx.fillStyle = color;
  ctx.font = '12px ui-monospace, Consolas, monospace';
  ctx.fillText(text, s.x + dx, s.y + dy);
}

/** 直線を画面の矩形で切って線分にする。 */
function clipLine(l, r) {
  // 画面中心に最も近い点を基準に、両方向へ十分長く伸ばす。
  const c = toWorld(r.width / 2, r.height / 2);
  const s = l.a * c.x + l.b * c.y + l.c;
  const base = { x: c.x - s * l.a, y: c.y - s * l.b };
  const d = { x: -l.b, y: l.a };
  const L = (r.width + r.height) / view.scale;
  const p1 = toScreen({ x: base.x - d.x * L, y: base.y - d.y * L });
  const p2 = toScreen({ x: base.x + d.x * L, y: base.y + d.y * L });
  // ラベルは線分の端(画面外)ではなく、画面中心寄りの少しずらした位置に置く。
  const at = toScreen({ x: base.x + d.x * L * 0.16, y: base.y + d.y * L * 0.16 });
  return { p1, p2, at };
}

// ============================================================
// 当たり判定
// ============================================================
function hit(sx, sy, kind) {
  const V = evaluate();
  let best = null, bestD = Infinity;
  // 補助作図は掴めない(取り込んでから使う)。
  for (const o of objects) {
    if (kind && o.kind !== kind) continue;
    const v = V.get(o.name);
    if (!v) continue;
    let d = Infinity;
    if (o.kind === 'point') {
      const s = toScreen(v); d = Math.hypot(s.x - sx, s.y - sy);
      if (d > 10) d = Infinity;
    } else if (o.kind === 'line') {
      const w = toWorld(sx, sy);
      d = Math.abs(v.a * w.x + v.b * w.y + v.c) * view.scale;
      if (d > 7) d = Infinity;
    } else {
      const w = toWorld(sx, sy);
      d = Math.abs(Math.hypot(w.x - v.x, w.y - v.y) - v.r) * view.scale;
      if (d > 7) d = Infinity;
    }
    // 点は線・円より掴みやすくしたいので優先する。
    const rank = d + (o.kind === 'point' ? 0 : 3);
    if (rank < bestD) { bestD = rank; best = o; }
  }
  return best;
}

// ============================================================
// 操作
// ============================================================
let drag = null;   // {name} または {pan:true, ...}

canvas.addEventListener('pointerdown', (e) => {
  const r = canvas.getBoundingClientRect();
  const sx = e.clientX - r.left, sy = e.clientY - r.top;
  canvas.setPointerCapture(e.pointerId);

  if (tool.id === 'move') {
    const o = hit(sx, sy, 'point');
    if (o && (o.op === 'free' || o.op === 'on')) { snapshot(); drag = { name: o.name }; }
    else drag = { pan: true, sx, sy, ox: view.ox, oy: view.oy };
    canvas.classList.add('dragging');
    return;
  }
  if (tool.id === 'del') {
    const o = hit(sx, sy, null);
    if (o) { snapshot(); removeCascade(o.name); invalidateFindings(); refresh(); }
    return;
  }
  if (tool.id === 'point') {
    snapshot();
    const w = toWorld(sx, sy);
    const curve = hit(sx, sy, null);
    if (curve && curve.kind === 'point') {
      // 既にそこに点がある。重ねて置くと以後どちらを掴んでいるのか
      // 分からなくなるので、何もしない。
      history.pop();
      updateHint(`そこには既に点 ${curve.name} があります`);
      draw();
      return;
    }
    if (curve && curve.kind !== 'point') {
      const V = evaluate(), v = V.get(curve.name);
      const p = v.r !== undefined ? projectOnCircle(v, w) : projectOnLine(v, w);
      objects.push({ name: freshName('point'), kind: 'point', op: 'on', args: [], on: curve.name, x: p.x, y: p.y });
    } else {
      objects.push({ name: freshName('point'), kind: 'point', op: 'free', args: [], x: w.x, y: w.y });
    }
    invalidateFindings(); refresh();
    return;
  }

  // 複数クリックで作る道具
  const want = tool.need[pending.length];
  const o = hit(sx, sy, want);
  if (!o) { updateHint(`${tool.label}: ${tool.prompts[pending.length]} が見つかりません。${jp(want)}をクリックしてください`); draw(); return; }
  pending.push(o.name);
  if (pending.length === tool.need.length) {
    const complaint = validate(tool, pending);
    if (complaint) { pending = []; updateHint(complaint); draw(); return; }
    snapshot();
    build(tool, pending);
    pending = [];
    invalidateFindings(); refresh();
  } else { updateHint(); draw(); }
});

canvas.addEventListener('pointermove', (e) => {
  const r = canvas.getBoundingClientRect();
  const sx = e.clientX - r.left, sy = e.clientY - r.top;
  const w = toWorld(sx, sy);
  document.getElementById('coords').textContent = `x ${w.x.toFixed(2)}   y ${w.y.toFixed(2)}`;
  if (!drag) return;
  if (drag.pan) { view.ox = drag.ox + (sx - drag.sx); view.oy = drag.oy + (sy - drag.sy); draw(); return; }
  const o = byName(drag.name);
  if (o) { o.x = w.x; o.y = w.y; draw(); }
});

function endDrag(e) {
  if (drag && !drag.pan) invalidateFindings();
  drag = null;
  canvas.classList.remove('dragging');
  if (e) { try { canvas.releasePointerCapture(e.pointerId); } catch (_) {} }
}
canvas.addEventListener('pointerup', endDrag);
canvas.addEventListener('pointercancel', endDrag);

canvas.addEventListener('wheel', (e) => {
  e.preventDefault();
  const r = canvas.getBoundingClientRect();
  const sx = e.clientX - r.left, sy = e.clientY - r.top;
  const before = toWorld(sx, sy);
  const f = Math.exp(-e.deltaY * 0.0012);
  view.scale = Math.min(4000, Math.max(8, view.scale * f));
  const after = toWorld(sx, sy);
  view.ox += (after.x - before.x) * view.scale;
  view.oy -= (after.y - before.y) * view.scale;
  draw();
}, { passive: false });

function jp(kind) { return kind === 'point' ? '点' : kind === 'line' ? '直線' : '円'; }

/// 接線と第2交点は「その点が本当にその曲線の上にある」ことが前提の作図で、
/// 前提を外れた指定をしてもエンジンは黙って別の図形を作ってしまう。
/// 画面上の数値で明らかに外れている場合はここで止める
/// (真偽の判定ではなく、指定ミスを拾うためだけの許容誤差つきの確認)。
function validate(t, args) {
  const V = evaluate();
  const near = (p, curve) => {
    if (!p || !curve) return false;
    const d = (curve.r !== undefined)
      ? Math.abs(Math.hypot(p.x - curve.x, p.y - curve.y) - curve.r)
      : Math.abs(curve.a * p.x + curve.b * p.y + curve.c);
    return d * view.scale < 6;
  };
  if (t.id === 'tangent') {
    if (!near(V.get(args[1]), V.get(args[0])))
      return `接線: 点 ${args[1]} は円 ${args[0]} の上にありません。円周上の点を選んでください`;
  }
  if (t.id === 'second_lc') {
    if (!near(V.get(args[0]), V.get(args[1])) || !near(V.get(args[0]), V.get(args[2])))
      return `第2交点: 点 ${args[0]} は ${args[1]} と ${args[2]} の交点になっていません`;
  }
  if (t.id === 'second_cc') {
    if (!near(V.get(args[0]), V.get(args[1])) || !near(V.get(args[0]), V.get(args[2])))
      return `第2交点: 点 ${args[0]} は円 ${args[1]} と円 ${args[2]} の共有点になっていません`;
  }
  return null;
}

function build(t, args) {
  const kind = (t.id === 'circle') ? 'circle'
    : ['line', 'perp', 'para', 'tangent', 'radical'].includes(t.id) ? 'line' : 'point';
  const op = { line: 'through', circle: 'through', inter: 'inter', mid: 'mid', perp: 'perp',
               para: 'para', tangent: 'tangent', radical: 'radical',
               second_lc: 'second_lc', second_cc: 'second_cc' }[t.id];
  objects.push({ name: freshName(kind), kind, op, args: args.slice() });
}

// ============================================================
// エンジンとのやりとり
// ============================================================
function serialize() {
  return objects.map(o => {
    if (o.op === 'free') return `point ${o.name} free`;
    if (o.op === 'on') return `point ${o.name} on ${o.on}`;
    return `${o.kind} ${o.name} ${o.op} ${o.args.join(' ')}`;
  }).join('\n');
}

function invalidateFindings() {
  dropAux();
  const el = document.getElementById('findings');
  if (el.dataset.fresh === '1') {
    el.dataset.fresh = '0';
    lastFindings = [];
    document.getElementById('resulthead').hidden = true;
    el.className = 'empty';
    el.textContent = '作図が変わりました。もう一度調べてください。';
  }
  highlight.clear();
}

/// 画面の設定を、サーバが読む `config <キー> <値>` の行に直す。
function configLines(withProof) {
  const v = (id) => document.getElementById(id).value;
  return [
    `config rounds ${v('rounds')}`,
    `config seconds ${v('seconds')}`,
    `config cap ${v('cap')}`,
    `config per_kind ${v('per_kind')}`,
    `config sweep ${v('sweep')}`,
    `config top ${v('top')}`,
    `config prove_seconds ${withProof ? v('prove_seconds') : 0}`,
    `config prove_max ${v('prove_max')}`,
  ].join('\n');
}

/// 今の図(補助作図も取り込んだ状態とみなす)について、どれがすぐ証明できるかを
/// 確かめ直す。自由作図はやり直さない(段数0で送る)ので速い。
async function proveAll() {
  const btn = document.getElementById('proveall');
  const el = document.getElementById('findings');
  const auxScript = aux.map(o =>
    o.op === 'on' ? `point ${o.name} on ${o.on}`
                  : `${o.kind} ${o.name} ${o.op} ${o.args.join(' ')}`).join('\n');
  const script = [serialize(), auxScript].filter(Boolean).join('\n');
  const cfg = configLines(true).replace(/config rounds \d+/, 'config rounds 0');
  btn.disabled = true;
  const note = document.getElementById('sortnote');
  note.textContent = `証明を試しています… 1件あたり最大 ${document.getElementById('prove_seconds').value} 秒`;
  try {
    const res = await fetch('/discover', { method: 'POST', body: cfg + '\n' + script });
    const text = await res.text();
    // 補助作図は既に手元にあるので、返ってきたものでは置き換えない。
    const keep = aux;
    renderFindings(text);
    aux = keep;              // 返ってきた aux(段数0なので空)では置き換えない
    updateAuxBar();
    paintFindings();         // 「取り込む」ボタンは aux を戻してから描き直す
  } catch (err) {
    note.textContent = 'エンジンに繋がりませんでした。';
  } finally {
    btn.disabled = false;
  }
}

async function discover() {
  const btn = document.getElementById('discover');
  const el = document.getElementById('findings');
  const script = serialize();
  if (!script) { el.className = 'empty'; el.textContent = 'まず何か描いてください。'; return; }
  dropAux();
  btn.disabled = true;
  el.className = 'empty';
  const rounds = Number(document.getElementById('rounds').value);
  el.textContent = rounds > 0
    ? `自由作図(${rounds}段)をしてから調べています… 最大 ${document.getElementById('seconds').value} 秒`
    : '調べています…';
  try {
    const res = await fetch('/discover', { method: 'POST', body: configLines(false) + '\n' + script });
    const text = await res.text();
    renderFindings(text);
  } catch (err) {
    el.className = '';
    el.innerHTML = '<p class="err">エンジンに繋がりませんでした。geom_solver serve が動いているか確認してください。</p>';
  } finally {
    btn.disabled = false;
  }
}

const KIND_LABEL = {
  coincide: '一致', collinear: '共線', concurrent: '共点',
  circles: '3円共点', incident: '接続', concyclic: '共円',
};

function renderFindings(text) {
  const el = document.getElementById('findings');
  el.innerHTML = '';
  el.dataset.fresh = '1';
  const lines = text.split('\n').filter(Boolean);
  const err = lines.find(l => l.startsWith('error|'));
  if (err) {
    document.getElementById('resulthead').hidden = true;
    lastFindings = [];
    el.className = '';
    const p = document.createElement('p');
    p.className = 'err';
    p.textContent = '作図を読み取れませんでした\n' + err.slice(6);
    el.appendChild(p);
    return;
  }
  // 自由作図でエンジンが足した図形。ユーザーの作図と名前が衝突しない
  // ように来る(x1, x2, …)ので、そのまま評価器に載せられる。
  aux = [];
  for (const l of lines.filter(l => l.startsWith('aux|'))) {
    const t = l.slice(4).trim().split(/\s+/);
    if (t.length < 3) continue;
    const [kind, name, op, ...args] = t;
    const o = { name, kind, op, args, auxiliary: true };
    if (op === 'free') { o.x = 0; o.y = 0; }
    aux.push(o);
  }
  updateAuxBar();
  const findings = lines.filter(l => l.startsWith('finding|')).map(l => {
    const [, kind, textPart, idsPart, status] = l.split('|');
    return { kind, text: textPart, ids: (idsPart || '').split(',').filter(Boolean),
             status: status || 'untried' };
  });
  lastFindings = findings;
  if (!findings.length) {
    document.getElementById('resulthead').hidden = true;
    el.className = 'empty';
    el.textContent = 'この作図から、まだ知られていない関係は見つかりませんでした。';
    return;
  }
  paintFindings();
}

/// 件数が多いと枠からあふれるので、一覧だけをスクロールさせ、
/// 「自分の図に関わるものだけ」で絞れるようにしてある。
let lastFindings = [];

function paintFindings() {
  const el = document.getElementById('findings');
  const onlyMine = document.getElementById('onlymine').checked;
  const hideProved = document.getElementById('hideproved').checked;
  const mineNames = new Set(objects.map(o => o.name));
  const isMine = (f) => f.ids.some(n => mineNames.has(n));
  let shown = lastFindings;
  if (onlyMine) shown = shown.filter(isMine);
  if (hideProved) shown = shown.filter(f => f.status !== 'proved');
  document.getElementById('resulthead').hidden = false;
  document.getElementById('count').textContent =
    shown.length === lastFindings.length ? `${lastFindings.length}件`
                                         : `${shown.length} / ${lastFindings.length}件`;
  const tried = lastFindings.filter(f => f.status === 'proved' || f.status === 'open');
  const proved = lastFindings.filter(f => f.status === 'proved').length;
  document.getElementById('sortnote').textContent = tried.length
    ? `${tried.length}件を試して ${proved}件はすぐ証明できました。`
      + '「未証明」は偽という意味ではなく、今の定理集合と制限時間では出なかった、というだけです。'
    : '自分の図に関わるものから順に並んでいます(熱ではありません)。'
      + '「証明を試す」で、どれが今の定理集合からすぐ出るか分かります。';
  el.innerHTML = '';
  if (!shown.length) {
    el.className = 'empty';
    el.textContent = '自分の図に関わるものはありませんでした。チェックを外すと全部出ます。';
    return;
  }
  el.className = '';
  for (const f of shown) {
    const div = document.createElement('div');
    div.className = isMine(f) ? 'finding mine' : 'finding';
    const k = document.createElement('div');
    k.className = 'kind';
    k.textContent = KIND_LABEL[f.kind] || f.kind;
    const row = document.createElement('div');
    row.className = 'row';
    const t = document.createElement('div');
    t.className = 'text';
    t.textContent = f.text;
    row.appendChild(t);
    if (f.status === 'proved' || f.status === 'open') {
      const b = document.createElement('span');
      b.className = 'badge ' + f.status;
      b.textContent = f.status === 'proved' ? '証明できた' : '未証明';
      b.title = f.status === 'proved'
        ? '今の定理集合から制限時間内に導けました'
        : '制限時間内には導けませんでした(偽という意味ではありません)';
      row.appendChild(b);
    }
    // この性質に必要な補助作図だけを取り込むボタン。
    const needed = neededAux(f);
    if (needed.length) {
      const take = document.createElement('button');
      take.className = 'take';
      take.textContent = `取り込む (${needed.length})`;
      take.title = 'この性質に出てくる補助作図だけを自分の図にします';
      take.addEventListener('click', (e) => { e.stopPropagation(); adoptAux(needed); });
      row.appendChild(take);
    }
    div.append(k, row);
    div.addEventListener('mouseenter', () => { highlight = new Set(f.ids); draw(); });
    div.addEventListener('mouseleave', () => { highlight.clear(); draw(); });
    el.appendChild(div);
  }
  el.scrollTop = 0;
}

// ============================================================
// 起動
// ============================================================
/// 右の枠の幅をドラッグで変える。作図式がそのまま名前になるので、
/// 配置によっては既定の幅では読みにくい。
function setupSplitter() {
  const sp = document.getElementById('splitter');
  const root = document.documentElement;
  const apply = (px) => {
    const w = Math.min(window.innerWidth - 320, Math.max(260, px));
    root.style.setProperty('--side-w', w + 'px');
    resize();
  };
  let dragging = false;
  sp.addEventListener('pointerdown', (e) => {
    dragging = true; sp.classList.add('active'); sp.setPointerCapture(e.pointerId);
  });
  sp.addEventListener('pointermove', (e) => {
    if (dragging) apply(window.innerWidth - e.clientX);
  });
  const stop = (e) => {
    dragging = false; sp.classList.remove('active');
    try { sp.releasePointerCapture(e.pointerId); } catch (_) {}
  };
  sp.addEventListener('pointerup', stop);
  sp.addEventListener('pointercancel', stop);
  sp.addEventListener('dblclick', () => apply(360));
}

/// この性質を図の上で見るために要る補助作図を、依存関係を辿って集める。
/// 「自分が選んだ性質のみ図に取り込みたい」ため、一覧の各行から
/// その行のぶんだけを取り込めるようにしてある。
function neededAux(f) {
  const byName = new Map(aux.map(o => [o.name, o]));
  const want = new Set();
  const visit = (n) => {
    const o = byName.get(n);
    if (!o || want.has(n)) return;
    want.add(n);
    for (const d of (o.args || [])) visit(d);
    if (o.on) visit(o.on);
  };
  for (const n of f.ids) visit(n);
  // aux の並び(依存順)を保ったまま返す。
  return aux.filter(o => want.has(o.name));
}

/// 補助作図を捨てる。作図を編集したら、それは古い図に対する提案なので残さない。
function dropAux() {
  if (!aux.length) return;
  aux = [];
  updateAuxBar();
}

/// 補助作図をユーザーの作図として取り込む。以後は掴めるし、次に調べるとき
/// エンジンにも送られる。which を渡すとその分だけ取り込む。
function adoptAux(which) {
  const take = which && which.length ? which : aux;
  if (!take.length) return;
  snapshot();
  const taken = new Set(take.map(o => o.name));
  for (const o of aux) {
    if (!taken.has(o.name)) continue;
    delete o.auxiliary;
    objects.push(o);
  }
  aux = aux.filter(o => !taken.has(o.name));
  updateAuxBar();
  // 取り込んだだけで作図の意味は変わらないので、結果は消さずに描き直す。
  updateHint();
  paintFindings();
  draw();
}

function updateAuxBar() {
  const bar = document.getElementById('auxbar');
  bar.hidden = aux.length === 0;
  document.getElementById('auxcount').textContent =
    aux.length ? `補助作図 ${aux.length} 個(破線)` : '';
  draw();
}

function refresh() { updateHint(); draw(); }

function init() {
  const bar = document.getElementById('toolbar');
  for (const t of TOOLS) {
    const b = document.createElement('button');
    b.textContent = t.label;
    b.dataset.tool = t.id;
    b.addEventListener('click', () => selectTool(t.id));
    bar.appendChild(b);
  }
  document.getElementById('discover').addEventListener('click', discover);
  document.getElementById('onlymine').addEventListener('change', paintFindings);
  document.getElementById('hideproved').addEventListener('change', paintFindings);
  document.getElementById('proveall').addEventListener('click', proveAll);
  setupSplitter();
  document.getElementById('adopt').addEventListener('click', () => adoptAux());
  document.getElementById('dropaux').addEventListener('click', () => { dropAux(); draw(); });
  document.getElementById('copy').addEventListener('click', (e) => {
    // summaryの中にあるので、そのままだと折りたたみが開閉してしまう。
    e.preventDefault(); e.stopPropagation();
    navigator.clipboard.writeText(serialize()).catch(() => {});
  });
  document.querySelectorAll('[data-act]').forEach(b => b.addEventListener('click', () => {
    if (b.dataset.act === 'undo') undo();
    if (b.dataset.act === 'clear') { snapshot(); objects = []; pending = []; invalidateFindings(); refresh(); }
  }));
  window.addEventListener('keydown', (e) => {
    if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'z') { e.preventDefault(); undo(); }
    if (e.key === 'Escape') { pending = []; refresh(); }
  });
  window.addEventListener('resize', resize);

  // 最初から空の画板だと何をすればいいか分からないので、三角形を1つ置いておく。
  objects = [
    { name: 'A', kind: 'point', op: 'free', args: [], x: -1.6, y: -1.0 },
    { name: 'B', kind: 'point', op: 'free', args: [], x: 1.8, y: -1.0 },
    { name: 'C', kind: 'point', op: 'free', args: [], x: -0.2, y: 1.5 },
    { name: 'l1', kind: 'line', op: 'through', args: ['A', 'B'] },
    { name: 'l2', kind: 'line', op: 'through', args: ['B', 'C'] },
    { name: 'l3', kind: 'line', op: 'through', args: ['C', 'A'] },
  ];
  selectTool('point');
  resize();
}
init();

(function(){
  const items = Array.from(document.querySelectorAll('details.item'));
  if (!items.length) return;
  const q = document.getElementById('q');
  const count = document.getElementById('count');
  const filters = Array.from(document.querySelectorAll('[data-filter]'));
  let status = 'all';
  function apply(){
    const words = (q && q.value || '').trim().toLowerCase().split(/\s+/).filter(Boolean);
    let shown = 0;
    for (const d of items){
      const okStatus = status === 'all' || d.dataset.status === status;
      const text = d.textContent.toLowerCase();
      const okText = words.every(w => text.includes(w));
      d.hidden = !(okStatus && okText);
      if (!d.hidden) shown++;
      if (words.length && !d.hidden) d.open = true;
    }
    document.querySelectorAll('.group').forEach(g => {
      g.hidden = !g.querySelector('details.item:not([hidden])');
    });
    if (count) count.textContent = shown + ' / ' + items.length;
  }
  if (q) q.addEventListener('input', apply);
  filters.forEach(b => b.addEventListener('click', () => {
    status = b.dataset.filter;
    filters.forEach(x => x.setAttribute('aria-pressed', x === b));
    apply();
  }));
  const setAll = v => items.forEach(d => { if (!d.hidden) d.open = v; });
  const ex = document.getElementById('expand'), co = document.getElementById('collapse');
  if (ex) ex.addEventListener('click', () => setAll(true));
  if (co) co.addEventListener('click', () => setAll(false));
  function openHash(){
    const t = location.hash && document.getElementById(decodeURIComponent(location.hash.slice(1)));
    if (t && t.tagName === 'DETAILS'){ t.open = true; t.scrollIntoView(); }
  }
  window.addEventListener('hashchange', openHash);
  openHash();
  apply();
})();

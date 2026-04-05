let STATE = {
  nodes: [],
  edges: [],
  disrupted: new Set(),
  hovered: null,
  selected: null,
  chartTab: 'flow',
  dark: true,
  baselineTotal: 0,
  current: { totalFlow: 0, edgeFlowMap: new Map() },
  aps: new Set(),
  spofs: new Set(),
  ranking: [],
  tiers: new Map(),
  inFlow: new Map(),
  outFlow: new Map()
};

let NODE_POS = {};
let SVG_HEIGHT = 500;
const SVG_WIDTH = 1040;

const COL = { farm: 120, proc: 320, wh: 520, dist: 720, ret: 920 };

const TYPE_META = {
  farm:        { dark: "#10b981", light: "#059669", darkBg: "#022c22",  lightBg: "#d1fae5" },
  processor:   { dark: "#3b82f6", light: "#2563eb", darkBg: "#0c1a3a",  lightBg: "#dbeafe" },
  warehouse:   { dark: "#f59e0b", light: "#d97706", darkBg: "#2c1700",  lightBg: "#fef3c7" },
  distributor: { dark: "#8b5cf6", light: "#7c3aed", darkBg: "#1e0a30",  lightBg: "#ede9fe" },
  retailer:    { dark: "#ef4444", light: "#dc2626", darkBg: "#2d0808",  lightBg: "#fee2e2" },
};
const TYPE_LABEL = {
  farm: "Farm", processor: "Processor", warehouse: "Warehouse",
  distributor: "Distributor", retailer: "Retailer",
};

const SOURCE_TYPES = new Set(["farm"]);
const NR = 32; // node radius

// ─── Network Generator ────────────────────────────────────────────────────────

function randInt(min, max) { return Math.floor(Math.random() * (max - min + 1)) + min; }

function generateNetwork() {
  const nf = parseInt($('inpFarms').value) || 1;
  const np = parseInt($('inpProcs').value) || 1;
  const nw = parseInt($('inpWhs').value) || 1;
  const nd = parseInt($('inpDists').value) || 1;
  const nr = parseInt($('inpRets').value) || 1;

  STATE.nodes = [];
  STATE.edges = [];
  STATE.disrupted.clear();
  STATE.selected = null;
  NODE_POS = {};

  const layers = [
    { type: 'farm', count: nf, cap: [80, 150], label: "Farm" },
    { type: 'processor', count: np, cap: [100, 200], label: "Processor" },
    { type: 'warehouse', count: nw, cap: [150, 250], label: "Warehouse" },
    { type: 'distributor', count: nd, cap: [100, 180], label: "Distributor" },
    { type: 'retailer', count: nr, cap: [50, 100], label: "Retailer" }
  ];

  const maxNodes = Math.max(nf, np, nw, nd, nr);
  const Y_GAP = 130;
  SVG_HEIGHT = Math.max(500, maxNodes * Y_GAP + 100);

  // Generate Nodes & Coordinates
  const layerIds = [];
  layers.forEach((layer) => {
    let ids = [];
    const startY = (SVG_HEIGHT - (layer.count - 1) * Y_GAP) / 2;
    for (let i=0; i<layer.count; i++) {
        const id = `${layer.type}${i+1}`;
        ids.push(id);
        STATE.nodes.push({ id, label: `${layer.label} ${i+1}`, type: layer.type, capacity: randInt(layer.cap[0], layer.cap[1]) });
        NODE_POS[id] = { x: COL[layer.type === 'processor' ? 'proc' : layer.type === 'warehouse' ? 'wh' : layer.type === 'distributor' ? 'dist' : layer.type === 'retailer' ? 'ret' : 'farm'], y: startY + i * Y_GAP };
    }
    layerIds.push(ids);
  });

  // Generate Edges ensuring full connectivity logic
  for (let l = 0; l < layerIds.length - 1; l++) {
    const fromL = layerIds[l];
    const toL = layerIds[l+1];
    
    // Connect each 'to' to at least one 'from'
    toL.forEach(t => {
       const f = fromL[randInt(0, fromL.length - 1)];
       STATE.edges.push({ from: f, to: t, flow: randInt(20, 80) });
    });
    // Connect each 'from' to at least one 'to'
    fromL.forEach(f => {
       if (!STATE.edges.find(e => e.from === f)) {
           const t = toL[randInt(0, toL.length - 1)];
           STATE.edges.push({ from: f, to: t, flow: randInt(20, 80) });
       }
       // Randomly add another edge sometimes
       if(toL.length > 1 && Math.random() > 0.5) {
           let t = toL[randInt(0, toL.length - 1)];
           if (!STATE.edges.find(e => e.from === f && e.to === t)) {
               STATE.edges.push({ from: f, to: t, flow: randInt(20, 60) });
           }
       }
    });
  }

  const base = runMaxFlow(new Set());
  STATE.baselineTotal = base.totalFlow;
  kahnTiers();
  updateState();
}


// ─── DSA ──────────────────────────────────────────────────────────────────────

class MaxFlowGraph {
  constructor(n) { this.g = Array.from({ length: n }, () => []); }
  addEdge(u, v, cap) {
    this.g[u].push({ to: v, cap, rev: this.g[v].length });
    this.g[v].push({ to: u, cap: 0, rev: this.g[u].length - 1 });
  }
  bfs(s, t, par, pe) {
    const vis = new Uint8Array(this.g.length), q = [s]; vis[s] = 1; par[s] = -1;
    while (q.length) {
      const u = q.shift();
      for (let i = 0; i < this.g[u].length; i++) {
        const e = this.g[u][i];
        if (!vis[e.to] && e.cap > 0) { vis[e.to] = 1; par[e.to] = u; pe[e.to] = i; if (e.to === t) return true; q.push(e.to); }
      }
    }
    return false;
  }
  maxflow(s, t) {
    const init = this.g.map(adj => adj.map(e => e.cap));
    const par = new Array(this.g.length).fill(-1), pe = [...par]; let total = 0;
    while (this.bfs(s, t, par, pe)) {
      let pf = Infinity, cur = t;
      while (cur !== s) { const p = par[cur], i = pe[cur]; pf = Math.min(pf, this.g[p][i].cap); cur = p; }
      cur = t;
      while (cur !== s) { const p = par[cur], i = pe[cur]; this.g[p][i].cap -= pf; this.g[cur][this.g[p][i].rev].cap += pf; cur = p; }
      total += pf;
    }
    const efMap = new Map();
    for (let u = 0; u < this.g.length; u++) {
      for (let i = 0; i < this.g[u].length; i++) {
        const e = this.g[u][i], sent = init[u][i] - e.cap;
        if (sent > 0) efMap.set(`${u}__${e.to}`, (efMap.get(`${u}__${e.to}`) || 0) + sent);
      }
    }
    return { flow: total, efMap };
  }
}

function runMaxFlow(disrupted) {
  const ae = STATE.edges.filter(e => !disrupted.has(e.from) && !disrupted.has(e.to));
  const an = STATE.nodes.filter(n => !disrupted.has(n.id));
  if(an.length === 0) return { totalFlow: 0, edgeFlowMap: new Map() };
  const ni = new Map(); an.forEach((n, i) => ni.set(n.id, i));
  const S = an.length, T = S + 1;
  const g = new MaxFlowGraph(T + 1);
  for (const f of an.filter(n => n.type === "farm")) {
    const cap = ae.filter(e => e.from === f.id).reduce((s, e) => s + e.flow, 0);
    g.addEdge(S, ni.get(f.id), f.capacity); // Use capacity correctly
  }
  for (const r of an.filter(n => n.type === "retailer")) g.addEdge(ni.get(r.id), T, r.capacity);
  for (const e of ae) { const u = ni.get(e.from), v = ni.get(e.to); if (u !== undefined && v !== undefined) g.addEdge(u, v, e.flow); }
  const { flow, efMap } = g.maxflow(S, T);
  const edgeFlowMap = new Map();
  for (const [key, f] of efMap) {
    const [u, v] = key.split("__").map(Number);
    if (u === S || v === T || u === T || v === S) continue;
    const fid = an[u]?.id, tid = an[v]?.id;
    if (fid && tid) edgeFlowMap.set(`${fid}__${tid}`, (edgeFlowMap.get(`${fid}__${tid}`) || 0) + f);
  }
  return { totalFlow: flow, edgeFlowMap };
}

function tarjanAP(disrupted) {
  const active = STATE.nodes.filter(n => !disrupted.has(n.id)).map(n => n.id);
  const idx = new Map(); active.forEach((id, i) => idx.set(id, i));
  const n = active.length, adj = Array.from({ length: n }, () => []);
  for (const e of STATE.edges) { const u = idx.get(e.from), v = idx.get(e.to); if (u !== undefined && v !== undefined) { adj[u].push(v); adj[v].push(u); } }
  const disc = new Array(n).fill(-1), low = new Array(n).fill(0), isAP = new Array(n).fill(false); let t = 0;
  function dfs(u, p) {
    disc[u] = low[u] = t++; let cc = 0;
    for (const v of adj[u]) {
      if (disc[v] === -1) { cc++; dfs(v, u); low[u] = Math.min(low[u], low[v]); if (p === -1 && cc > 1) isAP[u] = true; if (p !== -1 && low[v] >= disc[u]) isAP[u] = true; }
      else if (v !== p) low[u] = Math.min(low[u], disc[v]);
    }
  }
  for (let i = 0; i < n; i++) if (disc[i] === -1) dfs(i, -1);
  const r = new Set(); isAP.forEach((ap, i) => { if (ap) r.add(active[i]); });
  return r;
}

function bfsReach(start, targets, disrupted) {
  if (disrupted.has(start)) return false;
  const adj = new Map();
  for (const e of STATE.edges) if (!disrupted.has(e.from) && !disrupted.has(e.to)) { if (!adj.has(e.from)) adj.set(e.from, []); adj.get(e.from).push(e.to); }
  const vis = new Set(), q = [start];
  while (q.length) { const c = q.shift(); if (targets.has(c)) return true; if (vis.has(c)) continue; vis.add(c); for (const nb of adj.get(c) || []) if (!vis.has(nb)) q.push(nb); }
  return false;
}

function detectSPOFs(disrupted, aps, baseFlow) {
  const rets = new Set(STATE.nodes.filter(n => n.type === "retailer").map(n => n.id));
  const farms = STATE.nodes.filter(n => n.type === "farm").map(n => n.id);
  const r = new Set();
  for (const c of aps) { if (disrupted.has(c)) continue; const td = new Set(disrupted); td.add(c); if (!farms.some(f => bfsReach(f, rets, td)) && baseFlow > 0) r.add(c); }
  return r;
}

function computeRanking(disrupted, baseFlow, spofs, aps) {
  return STATE.nodes.filter(n => !disrupted.has(n.id)).map(node => {
    const td = new Set(disrupted); td.add(node.id);
    const { totalFlow } = runMaxFlow(td);
    return { id: node.id, label: node.label, type: node.type, impactPct: baseFlow > 0 ? Math.round(((baseFlow - totalFlow) / baseFlow) * 100) : 0, isSPOF: spofs.has(node.id), isAP: aps.has(node.id) };
  }).sort((a, b) => b.impactPct - a.impactPct);
}

function kahnTiers() {
  const inDeg = new Map(), adj = new Map();
  for (const n of STATE.nodes) { inDeg.set(n.id, 0); adj.set(n.id, []); }
  for (const e of STATE.edges) { adj.get(e.from)?.push(e.to); inDeg.set(e.to, (inDeg.get(e.to) || 0) + 1); }
  const tier = new Map(), q = [];
  for (const [id, d] of inDeg) if (d === 0) { q.push(id); tier.set(id, 0); }
  while (q.length) { const u = q.shift(); const t = tier.get(u) || 0; for (const v of adj.get(u) || []) { inDeg.set(v, (inDeg.get(v) || 0) - 1); tier.set(v, Math.max(tier.get(v) || 0, t + 1)); if (inDeg.get(v) === 0) q.push(v); } }
  STATE.tiers = tier;
}

// ─── Rendering ────────────────────────────────────────────────────────────────

function scoreCol(s, dark) { return s >= 75 ? (dark ? "#10b981" : "#059669") : s >= 45 ? (dark ? "#f59e0b" : "#d97706") : (dark ? "#ef4444" : "#dc2626"); }
function scoreLabel(s) { return s >= 75 ? "Resilient" : s >= 45 ? "Vulnerable" : "Critical"; }
function curvePath(a, b) { const dx = b.x - a.x; return `M${a.x},${a.y} C${a.x + dx * 0.5},${a.y} ${b.x - dx * 0.5},${b.y} ${b.x},${b.y}`; }

const $ = id => document.getElementById(id);
function setHTML(id, html) { const el = $(id); if (el) el.innerHTML = html; }

function getScore() { return STATE.baselineTotal > 0 ? Math.round((STATE.current.totalFlow / STATE.baselineTotal) * 100) : 0; }

function updateState() {
  STATE.current = runMaxFlow(STATE.disrupted);
  STATE.aps = tarjanAP(STATE.disrupted);
  STATE.spofs = detectSPOFs(STATE.disrupted, STATE.aps, STATE.baselineTotal);
  STATE.ranking = computeRanking(STATE.disrupted, STATE.baselineTotal, STATE.spofs, STATE.aps);
  
  STATE.inFlow.clear(); STATE.outFlow.clear();
  for (const [k, f] of STATE.current.edgeFlowMap) {
    const [from, to] = k.split("__");
    STATE.inFlow.set(to, (STATE.inFlow.get(to) || 0) + f);
    STATE.outFlow.set(from, (STATE.outFlow.get(from) || 0) + f);
  }
  render();
}

function render() {
  $('networkSvg').setAttribute('height', SVG_HEIGHT);
  $('networkSvg').setAttribute('viewBox', `0 0 1040 ${SVG_HEIGHT}`);

  renderSVG();
  renderSidebar();
  renderChart();
  renderHeader();
}

function renderHeader() {
  $('bodyRoot').className = STATE.dark ? 'dark' : 'light';
  $('themeToggleBtn').innerHTML = `<span class="icon">${STATE.dark ? '☀️' : '🌙'}</span> <span class="label">${STATE.dark ? 'Light Mode' : 'Dark Mode'}</span>`;
  
  const score = getScore();
  const sc = scoreCol(score, STATE.dark);
  
  $('headerScoreValue').innerText = `${score}%`;
  $('headerScoreValue').style.color = sc;
  $('headerScoreLabel').innerText = scoreLabel(score);
  $('headerScoreLabel').style.color = sc;
  
  // Legend
  const leg = Object.entries(TYPE_LABEL).map(([t, l]) => {
    const c = STATE.dark ? TYPE_META[t].dark : TYPE_META[t].light;
    return `<div class="legend-item"><div class="legend-dot" style="background:${c}; box-shadow: 0 0 8px ${c}80"></div><div class="legend-text">${l}</div></div>`;
  }).join('');
  
  const disC = STATE.dark ? "#ef4444" : "#dc2626";
  const dis = `<div class="legend-item"><div class="legend-dot" style="border: 2px dashed ${disC}"></div><div class="legend-text">Disrupted</div></div>`;
  const spof = `<div class="legend-item"><div class="legend-dot" style="border: 2px solid #f59e0b"></div><div class="legend-text" style="color:#f59e0b; font-weight:700">SPOF</div></div>`;
  
  setHTML('legendContainer', leg + dis + spof);
}

function renderSVG() {
  const isDark = STATE.dark;
  const T = {
    arrowA: isDark ? "#3b82f6" : "#2563eb",
    arrowI: isDark ? "#475569" : "#cbd5e1",
    arrowD: isDark ? "#7f1d1d" : "#fca5a5",
    gridBorder: isDark ? "rgba(255,255,255,0.05)" : "rgba(0,0,0,0.05)",
    gridText: isDark ? "#475569" : "#94a3b8"
  };

  let defs = `
    <filter id="drop-shadow" x="-30%" y="-30%" width="160%" height="160%">
      <feDropShadow dx="0" dy="6" stdDeviation="8" flood-color="${isDark ? '#000000' : '#1e293b'}" flood-opacity="${isDark ? '0.7' : '0.3'}"/>
    </filter>
    <marker id="arr-a" markerWidth="12" markerHeight="12" refX="10" refY="5" orient="auto" markerUnits="userSpaceOnUse"><path d="M0,0 L0,10 L12,5 z" fill="${T.arrowA}" /></marker>
    <marker id="arr-i" markerWidth="12" markerHeight="12" refX="10" refY="5" orient="auto" markerUnits="userSpaceOnUse"><path d="M0,0 L0,10 L12,5 z" fill="${T.arrowI}" /></marker>
    <marker id="arr-d" markerWidth="12" markerHeight="12" refX="10" refY="5" orient="auto" markerUnits="userSpaceOnUse"><path d="M0,0 L0,10 L12,5 z" fill="${T.arrowD}" /></marker>
  `;
  STATE.nodes.forEach(n => {
    const m = TYPE_META[n.type], c = isDark ? m.dark : m.light, bg = isDark ? m.darkBg : m.lightBg, dis = STATE.disrupted.has(n.id);
    const stop1 = dis ? (isDark ? "#ef4444" : "#fca5a5") : c;
    const stop2 = dis ? (isDark ? "#7f1d1d" : "#f87171") : c;
    const stop3 = dis ? (isDark ? "#1a0505" : "#fee2e2") : bg;
    
    defs += `<radialGradient id="ng-${n.id}" cx="35%" cy="30%" r="70%">
              <stop offset="0%" stop-color="#ffffff" stop-opacity="${dis ? 0.15 : 0.7}" />
              <stop offset="15%" stop-color="${stop1}" stop-opacity="${dis ? 0.6 : 0.9}" />
              <stop offset="55%" stop-color="${stop2}" stop-opacity="${dis ? 0.9 : 1}" />
              <stop offset="100%" stop-color="${stop3}" stop-opacity="1" />
             </radialGradient>`;
  });
  setHTML('svgDefs', defs);

  // Grid
  const cols = [
    { x: COL.farm, l: "FARMS" }, { x: COL.proc, l: "PROCESSORS" }, { x: COL.wh, l: "WAREHOUSES" },
    { x: COL.dist, l: "DISTRIBUTORS" }, { x: COL.ret, l: "RETAILERS" }
  ];
  let grid = '';
  cols.forEach(({x, l}) => {
    grid += `<rect x="${x - 45}" y="26" width="90" height="${SVG_HEIGHT - 52}" rx="16" fill="transparent" stroke="${T.gridBorder}" stroke-width="1" stroke-dasharray="8 8" />`;
    grid += `<text x="${x}" y="17" text-anchor="middle" fill="${T.gridText}" font-size="10" font-weight="700" letter-spacing="1.5" font-family="Outfit,sans-serif">${l}</text>`;
  });
  setHTML('svgGrid', grid);

  // Edges
  let edgeStr = '';
  STATE.edges.forEach(e => {
    const fp = NODE_POS[e.from], tp = NODE_POS[e.to]; if(!fp || !tp) return;
    const key = `${e.from}__${e.to}`;
    const dis = STATE.disrupted.has(e.from) || STATE.disrupted.has(e.to);
    const flow = STATE.current.edgeFlowMap.get(key) || 0;
    const active = flow > 0;
    
    const dx = tp.x - fp.x, dy = tp.y - fp.y, dist = Math.sqrt(dx*dx + dy*dy);
    const ox = (dx/dist)*(NR+1), oy = (dy/dist)*(NR+1);
    const exFrac = (NR+9)/dist;
    const endX = tp.x - dx*exFrac, endY = tp.y - dy*exFrac;
    const pd = curvePath({x: fp.x + ox, y: fp.y + oy}, {x: endX, y: endY});
    const mx = (fp.x + tp.x)/2, my = (fp.y + tp.y)/2 - 10;
    
    const stroke = dis ? (isDark ? "#7f1d1d80" : "#fca5a580") : active ? (isDark ? "#3b82f6" : "#2563eb") : (isDark ? "#334155" : "#cbd5e1");
    const sw = active ? Math.max(1.5, Math.min(5, flow / 15)) : 1;
    const marker = dis ? "url(#arr-d)" : active ? "url(#arr-a)" : "url(#arr-i)";
    const op = dis ? 0.3 : active ? 1 : 0.4;
    
    if (active && !dis) edgeStr += `<path d="${pd}" fill="none" stroke="${isDark ? '#3b82f630' : '#2563eb20'}" stroke-width="${sw + 8}" />`;
    edgeStr += `<path d="${pd}" fill="none" stroke="${stroke}" stroke-width="${sw}" marker-end="${marker}" opacity="${op}" stroke-linecap="round" />`;
    if (active && !dis) {
       edgeStr += `<rect x="${mx-12}" y="${my-8}" width="24" height="12" rx="4" fill="${isDark?'#0f172a':'#ffffff'}" opacity="0.8" />`;
       edgeStr += `<text x="${mx}" y="${my+1}" text-anchor="middle" fill="${isDark ? '#e0e7ff' : '#1e3a8a'}" font-size="10" font-weight="800" font-family="monospace">${flow}</text>`;
    }
  });
  setHTML('svgEdges', edgeStr);

  // Nodes
  let nodeStr = '';
  STATE.nodes.forEach(n => {
    const pos = NODE_POS[n.id]; if(!pos) return;
    const isDis = STATE.disrupted.has(n.id), isSPOF = STATE.spofs.has(n.id), isAP = STATE.aps.has(n.id) && !isDis;
    const isSel = STATE.selected === n.id;
    const col = isDark ? TYPE_META[n.type].dark : TYPE_META[n.type].light;
    const r = NR * (isSel ? 1.08 : 1);
    const strokeC = isDis ? (isDark ? "#ef4444" : "#dc2626") : isSPOF ? "#f59e0b" : isSel ? (isDark ? "#e0e7ff" : "#1e40af") : (isDark ? "rgba(255,255,255,0.1)" : "rgba(0,0,0,0.2)");
    const sw = isDis ? 3 : isSPOF ? 4 : isSel ? 3 : 2;
    
    let inner = '';
    // SVG Glow filter dropshadow simulation
    if (isSPOF) inner += `<circle r="${r+14}" fill="none" stroke="#f59e0b" stroke-width="2" stroke-dasharray="6 4" opacity="0.8" />`;
    if (isAP && !isSPOF) inner += `<circle r="${r+8}" fill="none" stroke="${isDark ? '#f59e0b50' : '#d9770650'}" stroke-width="2" stroke-dasharray="4 4" />`;
    if (isSel && !isDis) inner += `<circle r="${r+10}" fill="${col}20" />`;
    if (!isDis && !isSel) inner += `<circle r="${r+4}" fill="${col}10" />`;
    
    inner += `<circle r="${r}" fill="url(#ng-${n.id})" stroke="${strokeC}" stroke-width="${sw}" filter="url(#drop-shadow)" />`;
    if (!isDis) inner += `<circle r="${r*0.4}" cx="${-r*0.25}" cy="${-r*0.25}" fill="#ffffff20" />`;
    
    if (isDis) {
      inner += `<line x1="-12" y1="-12" x2="12" y2="12" stroke="${isDark ? '#ef4444' : '#dc2626'}" stroke-width="3" stroke-linecap="round" />`;
      inner += `<line x1="12" y1="-12" x2="-12" y2="12" stroke="${isDark ? '#ef4444' : '#dc2626'}" stroke-width="3" stroke-linecap="round" />`;
    }
    
    inner += `<text text-anchor="middle" fill="${isDis ? (isDark ? '#7f1d1d' : '#fca5a5') : '#ffffff'}" font-size="12" font-weight="800" font-family="Outfit,sans-serif" dy="4">${n.capacity}</text>`;
    if (isSPOF) inner += `<text y="${-r-11}" text-anchor="middle" fill="#f59e0b" font-size="10" font-weight="900" letter-spacing="1">SPOF</text>`;
    inner += `<text y="${r+18}" text-anchor="middle" fill="${isDis ? (isDark ? '#ef444466' : '#dc262666') : (isDark?'#94a3b8':'#475569')}" font-size="11" font-weight="${isSel ? '800' : '600'}" font-family="Outfit,sans-serif">${n.label}</text>`;
    
    nodeStr += `<g transform="translate(${pos.x},${pos.y})" data-id="${n.id}" class="node-wrapper"><g class="node-group">${inner}</g></g>`;
  });
  setHTML('svgNodes', nodeStr);
}

function renderSidebar() {
  const isDark = STATE.dark;
  const score = getScore();
  const sc = scoreCol(score, isDark);
  
  let metHtml = `
    <div class="metric-row"><span class="metric-label">Theoretical Max Flow</span><span class="metric-value" style="color:${isDark?'#10b981':'#059669'}">${STATE.baselineTotal} vol</span></div>
    <div class="metric-row"><span class="metric-label">Active Flow</span><span class="metric-value" style="color:${STATE.current.totalFlow < STATE.baselineTotal ? (isDark?'#f59e0b':'#d97706') : (isDark?'#10b981':'#059669')}">${STATE.current.totalFlow} vol</span></div>
    <div class="metric-row"><span class="metric-label">Retention Score</span><span class="metric-value" style="color:${sc}">${score}%</span></div>
    <div class="metric-row"><span class="metric-label">Disrupted Objects</span><span class="metric-value" style="color:${STATE.disrupted.size ? (isDark?'#ef4444':'#dc2626') : (isDark?'#475569':'#94a3b8')}">${STATE.disrupted.size} / ${STATE.nodes.length}</span></div>
    <div class="metric-row"><span class="metric-label">Articulation Nodes</span><span class="metric-value" style="color:${isDark?'#f59e0b':'#d97706'}">${STATE.aps.size}</span></div>
    <div class="metric-row"><span class="metric-label">True SPOFs</span><span class="metric-value" style="color:#f59e0b">${STATE.spofs.size}</span></div>
  `;
  setHTML('metricsList', metHtml);
  
  $('scoreBarFill').style.width = `${score}%`;
  $('scoreBarFill').style.background = sc;
  $('scoreBarFill').style.boxShadow = `0 0 10px ${sc}99`;
  
  let spofHtml = '';
  if (STATE.spofs.size === 0) {
    spofHtml = `<div style="background:${isDark?'#064e3b20':'#d1fae540'}; border:1px solid ${isDark?'#059669':'#34d399'}; border-radius:10px; padding:12px; font-size:13px; color:${isDark?'#34d399':'#059669'}; font-weight:700; text-align:center">✓ Redundant Infrastructure</div>`;
  } else {
    [...STATE.spofs].forEach(id => {
      const node = STATE.nodes.find(n => n.id === id);
      const c = isDark ? TYPE_META[node.type].dark : TYPE_META[node.type].light;
      spofHtml += `
        <div class="spof-card" style="background:${isDark?'rgba(245, 158, 11, 0.05)':'#fffbeb'}; border:1px solid ${isDark?'rgba(245, 158, 11, 0.3)':'#fde68a'}" onclick="STATE.selected='${id}'; updateState(); $('selectedNodeContainer').scrollIntoView({behavior:'smooth'})">
          <div style="width:10px; height:10px; border-radius:50%; background:${c}; box-shadow: 0 0 8px ${c}90; flex-shrink:0;"></div>
          <div style="flex:1">
            <div class="spof-card-label">${node.label}</div>
            <div class="spof-card-desc">Disconnects terminal route entirely</div>
          </div>
          <span class="spof-badge">SPOF</span>
        </div>`;
    });
  }
  setHTML('spofList', spofHtml);
  
  let selHtml = '';
  if (STATE.selected) {
    const selNode = STATE.nodes.find(n => n.id === STATE.selected);
    const selImpact = STATE.ranking.find(r => r.id === STATE.selected);
    const isDis = STATE.disrupted.has(selNode.id);
    const tC = isDark ? TYPE_META[selNode.type].dark : TYPE_META[selNode.type].light;
    const nf = SOURCE_TYPES.has(selNode.type) ? (STATE.outFlow.get(selNode.id)||0) : (STATE.inFlow.get(selNode.id)||0);
    
    let tags = '';
    if (STATE.spofs.has(selNode.id)) tags += `<span style="font-size:9px; padding:2px 6px; border-radius:12px; background:${isDark?'rgba(245, 158, 11, 0.1)':'#fffbeb'}; color:#f59e0b; font-weight:800; border:1px solid #f59e0b80">SPOF</span>`;
    if (STATE.aps.has(selNode.id) && !STATE.spofs.has(selNode.id)) tags += `<span style="font-size:9px; padding:2px 6px; border-radius:12px; background:${isDark?'rgba(245, 158, 11, 0.05)':'#fffbeb'}; color:${isDark?'#f59e0b':'#d97706'}">AP</span>`;
    if (isDis) tags += `<span style="font-size:9px; padding:2px 6px; border-radius:12px; background:${isDark?'rgba(239, 68, 68, 0.1)':'#fee2e2'}; color:${isDark?'#ef4444':'#dc2626'}; font-weight:700; border: 1px solid #ef444460">Disrupted</span>`;
    
    selHtml = `
      <div class="selected-node-details">
        <div class="section-title">Selected Node Details</div>
        <div class="selected-node-header">
          <div style="width:12px; height:12px; border-radius:50%; background:${tC}; box-shadow:0 0 10px ${tC}90"></div>
          <span style="font-weight:900; font-size:16px">${selNode.label}</span>
          ${tags}
        </div>
        <div class="selected-node-grid">
          <div class="selected-node-stat"><div class="selected-node-stat-label">Capacity</div><div class="selected-node-stat-val">${selNode.capacity}</div></div>
          <div class="selected-node-stat"><div class="selected-node-stat-label">${SOURCE_TYPES.has(selNode.type)?'Outgoing Flow':'Incoming Flow'}</div><div class="selected-node-stat-val">${nf}</div></div>
          <div class="selected-node-stat"><div class="selected-node-stat-label">Topo Tier</div><div class="selected-node-stat-val">T${STATE.tiers.get(selNode.id)}</div></div>
          ${selImpact ? `<div class="selected-node-stat"><div class="selected-node-stat-label">Impact Loss</div><div class="selected-node-stat-val" style="color:#ef4444">-${selImpact.impactPct}%</div></div>` : ''}
        </div>
        <button class="toggle-node-btn" style="background:${isDis?(isDark?'rgba(16, 185, 129, 0.1)':'#d1fae5'):(isDark?'rgba(239, 68, 68, 0.1)':'#fee2e2')}; color:${isDis?(isDark?'#10b981':'#059669'):(isDark?'#ef4444':'#dc2626')}; border: 1px solid ${isDis?(isDark?'rgba(16, 185, 129, 0.3)':'#34d399'):(isDark?'rgba(239, 68, 68, 0.3)':'#fca5a5')}" onclick="STATE.disrupted.has('${selNode.id}')?STATE.disrupted.delete('${selNode.id}'):STATE.disrupted.add('${selNode.id}'); updateState();">
          ${isDis ? "✓ Restore Node Integrity" : "✕ Disrupt Infrastructure"}
        </button>
      </div>`;
  }
  setHTML('selectedNodeContainer', selHtml);
  
  let rankHtml = '';
  STATE.ranking.slice(0, 15).forEach((item, idx) => {
    const off = STATE.disrupted.has(item.id);
    const bc = item.impactPct > 50 ? (isDark ? "#ef4444" : "#dc2626") : item.impactPct > 25 ? (isDark ? "#f59e0b" : "#d97706") : (isDark ? "#10b981" : "#059669");
    const nc = isDark ? TYPE_META[item.type].dark : TYPE_META[item.type].light;
    const rankCol = idx === 0 ? "#f59e0b" : idx === 1 ? (isDark?"#94a3b8":"#64748b") : idx === 2 ? (isDark?"#b45309":"#d97706") : (isDark?"#475569":"#94a3b8");
    
    let tags = '';
    if (item.isSPOF && !off) tags += `<span style="font-size:8px; color:#f59e0b; font-weight:900; border:1px solid rgba(245, 158, 11, 0.4); border-radius:4px; padding:1px 4px">SPOF</span>`;
    if (item.isAP && !item.isSPOF && !off) tags += `<span style="font-size:8px; color:${isDark?'#f59e0b':'#d97706'}; border:1px solid rgba(245, 158, 11, 0.3); border-radius:4px; padding:1px 4px">AP</span>`;
    if (off) tags += `<span style="font-size:9px; color:${isDark?'#ef4444':'#dc2626'}; font-weight:700">OFF</span>`;
    
    const isSel = STATE.selected === item.id;
    rankHtml += `
      <div class="rank-item" style="opacity:${off?0.4:1}; border:${item.isSPOF?'1px solid rgba(245, 158, 11, 0.2)':'1px solid transparent'}; background:${isSel?(isDark?'rgba(255,255,255,0.05)':'#eef2ff'):'transparent'}" onclick="STATE.selected=STATE.selected==='${item.id}'?null:'${item.id}'; updateState();">
        <span class="rank-no" style="color:${rankCol}">${idx + 1}</span>
        <div style="width:10px; height:10px; border-radius:50%; background:${nc}; flex-shrink:0;"></div>
        <span class="rank-label" style="font-weight:${item.isSPOF?700:500}">${item.label}</span>
        ${tags}
        <div class="rank-bar-bg"><div class="rank-bar-fill" style="width:${item.impactPct}%; background:${bc}; box-shadow: 0 0 5px ${bc}80"></div></div>
        <span class="rank-impact" style="color:${bc}">-${item.impactPct}%</span>
      </div>`;
  });
  setHTML('rankingList', rankHtml);
}

function renderChart() {
  const tId = STATE.chartTab;
  const isDark = STATE.dark;
  const TBorder = isDark ? "rgba(255, 255, 255, 0.1)" : "rgba(0, 0, 0, 0.1)";
  const TTextFaint = isDark ? "#475569" : "#94a3b8";
  const TTextMid = isDark ? "#94a3b8" : "#475569";
  
  document.querySelectorAll('.tab-btn').forEach(btn => btn.className = btn.getAttribute('data-tab') === tId ? 'tab-btn active' : 'tab-btn');
  const hints = { flow: "Farms = outgoing · Others = incoming · Ghost = capacity", tier: "% = utilisation · solid = flow · outline = capacity", gauge: "Resilience gauge — Critical / Vulnerable / Resilient zones" };
  setHTML('tabHint', hints[tId]);
  
  let html = '';
  if (tId === 'flow') {
    const nodes = STATE.nodes.filter(n => !STATE.disrupted.has(n.id));
    const maxCap = Math.max(...nodes.map(n => n.capacity), 1);
    const BW = 30, GAP = 10, CH = 150, PAD_L = 50, PAD_TOP = 10, PAD_BOT = 60;
    const W = nodes.length * (BW + GAP) + PAD_L + 20, H = CH + PAD_TOP + PAD_BOT;
    
    html = `<div style="overflow-x:auto"><svg width="${W}" height="${H}" viewBox="0 0 ${W} ${H}" style="display:block; min-width:100%">
      <line x1="${PAD_L}" y1="${PAD_TOP}" x2="${PAD_L}" y2="${PAD_TOP + CH}" stroke="${TBorder}" stroke-width="1" />
      <line x1="${PAD_L}" y1="${PAD_TOP + CH}" x2="${maxCap > 0 ? W - 10 : PAD_L+1}" y2="${PAD_TOP + CH}" stroke="${TBorder}" stroke-width="1" />`;
    
    [0, 50, 100, 150, 200, 250].forEach(v => {
      if(v > maxCap * 1.2) return;
      const y = PAD_TOP + CH - (v / maxCap) * CH;
      if (y >= PAD_TOP) {
        html += `<line x1="${PAD_L - 4}" y1="${y}" x2="${PAD_L}" y2="${y}" stroke="${TBorder}" stroke-width="1" />
                 <line x1="${PAD_L}" y1="${y}" x2="${W - 10}" y2="${y}" stroke="${isDark ? 'rgba(255,255,255,0.03)' : 'rgba(0,0,0,0.05)'}" stroke-width="1" stroke-dasharray="4 4" />
                 <text x="${PAD_L - 8}" y="${y + 4}" text-anchor="end" fill="${TTextFaint}" font-size="10" font-family="monospace">${v}</text>`;
      }
    });
    
    nodes.forEach((node, i) => {
      const x = PAD_L + i * (BW + GAP) + GAP / 2;
      const nf = SOURCE_TYPES.has(node.type) ? (STATE.outFlow.get(node.id)||0) : (STATE.inFlow.get(node.id)||0);
      const capH = (node.capacity / maxCap) * CH, flowH = (nf / maxCap) * CH;
      const col = isDark ? TYPE_META[node.type].dark : TYPE_META[node.type].light;
      const capY = PAD_TOP + CH - capH;
      const flowY = PAD_TOP + CH - flowH;
      const sl = node.label.replace("Processor ", "P").replace("Warehouse ", "W").replace("Distributor ", "D").replace("Retailer ", "R");
      
      html += `<rect x="${x}" y="${capY}" width="${BW}" height="${capH}" fill="${col}" opacity="0.1" rx="4" />
               <rect x="${x}" y="${capY}" width="${BW}" height="${capH}" fill="none" stroke="${col}" stroke-width="1" opacity="0.3" rx="4" />`;
      if (flowH > 0) {
        html += `<rect x="${x + 4}" y="${flowY}" width="${BW - 8}" height="${flowH}" fill="${col}" opacity="0.9" rx="3" />
                 <text x="${x + BW / 2}" y="${flowY - 4}" text-anchor="middle" fill="${col}" font-size="10" font-weight="800" font-family="monospace">${nf}</text>`;
      }
      html += `<g transform="translate(${x + BW / 2}, ${PAD_TOP + CH + 14})"><text transform="rotate(-40)" text-anchor="end" fill="${TTextMid}" font-size="11">${sl}</text></g>`;
      if (SOURCE_TYPES.has(node.type) && flowH > 0) html += `<text x="${x + BW / 2}" y="${PAD_TOP + CH + 46}" text-anchor="middle" fill="${col}" font-size="8" opacity="0.7">out</text>`;
    });
    
    html += `<rect x="${PAD_L + 10}" y="${PAD_TOP + 4}" width="12" height="10" fill="${isDark?'#94a3b8':'#64748b'}" opacity="0.2" rx="2" />
             <text x="${PAD_L + 28}" y="${PAD_TOP + 12}" fill="${TTextFaint}" font-size="10">Capacity</text>
             <rect x="${PAD_L + 80}" y="${PAD_TOP + 4}" width="12" height="10" fill="${isDark?'#3b82f6':'#2563eb'}" opacity="0.9" rx="2" />
             <text x="${PAD_L + 98}" y="${PAD_TOP + 12}" fill="${TTextFaint}" font-size="10">Flow</text>
             </svg></div>`;
  } else if (tId === 'tier') {
    const types = ["farm", "processor", "warehouse", "distributor", "retailer"];
    const tcols = isDark ? ["#10b981","#3b82f6","#f59e0b","#8b5cf6","#ef4444"] : ["#059669","#2563eb","#d97706","#7c3aed","#dc2626"];
    const data = types.map((t, i) => {
      const ns = STATE.nodes.filter(n => n.type === t && !STATE.disrupted.has(n.id));
      const cap = ns.reduce((s, n) => s + n.capacity, 0);
      const flow = ns.reduce((s, n) => s + (SOURCE_TYPES.has(n.type) ? (STATE.outFlow.get(n.id)||0) : (STATE.inFlow.get(n.id)||0)), 0);
      return { name: ["Farms","Procs","W.houses","Distrib.","Retailers"][i], cap, flow, col: tcols[i], util: cap > 0 ? Math.round((flow / cap) * 100) : 0 };
    });
    const maxV = Math.max(...data.map(d => d.cap), 1);
    const BW = 60, GAP = 30, CH = 150, PAD_L = 50, PAD_TOP = 20, PAD_BOT = 40;
    const W = data.length * (BW + GAP) + PAD_L + 20, H = CH + PAD_TOP + PAD_BOT;
    
    html = `<svg width="100%" viewBox="0 0 ${W} ${H}" style="display:block">
      <line x1="${PAD_L}" y1="${PAD_TOP}" x2="${PAD_L}" y2="${PAD_TOP + CH}" stroke="${TBorder}" stroke-width="1" />
      <line x1="${PAD_L}" y1="${PAD_TOP + CH}" x2="${W - 10}" y2="${PAD_TOP + CH}" stroke="${TBorder}" stroke-width="1" />`;
    
    [0, 200, 400, 600, 800, 1000].forEach(v => {
      if(v > maxV * 1.2) return;
      const y = PAD_TOP + CH - (v / maxV) * CH;
      if (y >= PAD_TOP) {
        html += `<line x1="${PAD_L - 4}" y1="${y}" x2="${W - 10}" y2="${y}" stroke="${isDark ? 'rgba(255,255,255,0.03)' : 'rgba(0,0,0,0.05)'}" stroke-width="1" stroke-dasharray="4 4" />
                 <text x="${PAD_L - 8}" y="${y + 4}" text-anchor="end" fill="${TTextFaint}" font-size="10" font-family="monospace">${v}</text>`;
      }
    });
    
    data.forEach((d, i) => {
      const x = PAD_L + i * (BW + GAP) + GAP / 2, capH = (d.cap / maxV) * CH, flowH = (d.flow / maxV) * CH;
      html += `<rect x="${x}" y="${PAD_TOP + CH - capH}" width="${BW}" height="${capH}" fill="${d.col}" opacity="0.1" rx="6" />
               <rect x="${x}" y="${PAD_TOP + CH - capH}" width="${BW}" height="${capH}" fill="none" stroke="${d.col}" stroke-width="1.5" opacity="0.3" rx="6" />`;
      if (flowH > 0) {
        html += `<rect x="${x + 6}" y="${PAD_TOP + CH - flowH}" width="${BW - 12}" height="${flowH}" fill="${d.col}" opacity="0.9" rx="4" />`;
      }
      html += `<text x="${x + BW / 2}" y="${PAD_TOP + CH - capH - 6}" text-anchor="middle" fill="${d.col}" font-size="12" font-weight="900" font-family="monospace">${d.util}%</text>
               <text x="${x + BW / 2}" y="${PAD_TOP + CH + 18}" text-anchor="middle" fill="${TTextMid}" font-size="12" font-weight="700">${d.name}</text>
               <text x="${x + BW / 2}" y="${PAD_TOP + CH + 32}" text-anchor="middle" fill="${TTextFaint}" font-size="10" font-family="monospace">${d.flow}/${d.cap}</text>`;
    });
    html += `</svg>`;
  } else if (tId === 'gauge') {
    const score = getScore();
    const CX = 200, CY = 160, R = 120, SW = 24;
    const pct = Math.max(0, Math.min(100, score)) / 100;
    const angle = Math.PI + pct * Math.PI;
    const needleX = CX + (R - 6) * Math.cos(angle), needleY = CY + (R - 6) * Math.sin(angle);
    const arc = (from, to, r) => `M ${CX + r * Math.cos(from)} ${CY + r * Math.sin(from)} A ${r} ${r} 0 0 1 ${CX + r * Math.cos(to)} ${CY + r * Math.sin(to)}`;
    const sc = scoreCol(score, isDark);
    const critEnd = Math.PI + 0.45 * Math.PI, vulnEnd = Math.PI + 0.75 * Math.PI;
    
    html = `<svg viewBox="0 0 400 230" style="display:block; width:100%; max-width:480px; margin: 0 auto">
      <path d="${arc(Math.PI, 2 * Math.PI, R)}" fill="none" stroke="${isDark ? 'rgba(255,255,255,0.05)' : 'rgba(0,0,0,0.05)'}" stroke-width="${SW}" stroke-linecap="round" />
      <path d="${arc(Math.PI, critEnd, R)}" fill="none" stroke="${isDark ? '#ef4444' : '#ef4444'}" stroke-width="${SW}" opacity="0.6" />
      <path d="${arc(critEnd, vulnEnd, R)}" fill="none" stroke="${isDark ? '#f59e0b' : '#f59e0b'}" stroke-width="${SW}" opacity="0.6" />
      <path d="${arc(vulnEnd, 2 * Math.PI, R)}" fill="none" stroke="${isDark ? '#10b981' : '#10b981'}" stroke-width="${SW}" opacity="0.6" />
      <path d="${arc(Math.PI, angle, R)}" fill="none" stroke="${sc}" stroke-width="${SW}" stroke-linecap="round" />
      <path d="${arc(Math.PI, angle, R)}" fill="none" stroke="${sc}" stroke-width="${SW + 14}" stroke-linecap="round" opacity="0.15" />`;
      
    [0, 25, 45, 75, 100].forEach(p => {
      const a = Math.PI + (p / 100) * Math.PI;
      const x1 = CX + (R - SW / 2 - 4) * Math.cos(a), y1 = CY + (R - SW / 2 - 4) * Math.sin(a);
      const x2 = CX + (R + SW / 2 + 4) * Math.cos(a), y2 = CY + (R + SW / 2 + 4) * Math.sin(a);
      const tx = CX + (R + SW / 2 + 18) * Math.cos(a), ty = CY + (R + SW / 2 + 18) * Math.sin(a);
      html += `<line x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}" stroke="${isDark ? '#475569' : '#94a3b8'}" stroke-width="2" />
               <text x="${tx}" y="${ty + 4}" text-anchor="middle" fill="${TTextMid}" font-size="11" font-weight="700" font-family="monospace">${p}</text>`;
    });
    
    html += `<text x="${CX - R - 14}" y="${CY + 30}" fill="${isDark ? '#ef4444' : '#dc2626'}" font-size="13" font-weight="800">Critical</text>
             <text x="${CX - 28}" y="${CY + R + 30}" fill="${isDark ? '#f59e0b' : '#d97706'}" font-size="13" font-weight="800" text-anchor="middle">Vulnerable</text>
             <text x="${CX + R + 14}" y="${CY + 30}" fill="${isDark ? '#10b981' : '#059669'}" font-size="13" font-weight="800" text-anchor="end">Resilient</text>
             <line x1="${CX}" y1="${CY}" x2="${needleX}" y2="${needleY}" stroke="${isDark ? '#f8fafc' : '#0f172a'}" stroke-width="4" stroke-linecap="round" />
             <circle cx="${CX}" cy="${CY}" r="14" fill="${sc}" />
             <circle cx="${CX}" cy="${CY}" r="6" fill="${isDark ? '#030712' : '#ffffff'}" />
             <text x="${CX}" y="${CY - 38}" text-anchor="middle" fill="${sc}" font-size="48" font-weight="900">${score}%</text>
             <text x="${CX}" y="${CY - 12}" text-anchor="middle" fill="${sc}" font-size="16" font-weight="800" letter-spacing="1px" text-transform="uppercase">${scoreLabel(score)}</text>
             </svg>`;
  }
  setHTML('tabContent', html);
}

// ─── Events & Initialization ──────────────────────────────────────────────────

function attachStaticEvents() {
  $('themeToggleBtn').onclick = () => { STATE.dark = !STATE.dark; render(); };
  document.querySelectorAll('.tab-btn').forEach(btn => {
    btn.onclick = () => { STATE.chartTab = btn.getAttribute('data-tab'); renderChart(); };
  });
  $('btnGenerate').onclick = () => { generateNetwork(); };
  
  // Attach delegation event to avoid re-rendering DOM during active clicks
  $('svgNodes').onclick = (e) => {
    const wrapper = e.target.closest('.node-wrapper');
    if(!wrapper) return;
    const id = wrapper.getAttribute('data-id');
    if(STATE.disrupted.has(id)) STATE.disrupted.delete(id); else STATE.disrupted.add(id);
    STATE.selected = id;
    updateState();
  };
}

function init() {
  attachStaticEvents();
  generateNetwork(); // Replaces static fetch('data.json')
}

init();

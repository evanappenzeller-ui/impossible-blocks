// Standalone BFS verifier for Parking Lot Escape levels.
// Mirrors the solver in index.html. Run: node verify-levels.mjs
// Reads levels from a JSON file at ./levels-export.json (write that file from a
// browser console with: copy(JSON.stringify(window.__plg.LEVELS)) -> save to file)
// OR pass levels inline via --inline (read from stdin).
//
// Easier: this script imports the LEVELS array directly from a JS module
// at ./levels-data.mjs (which we keep in sync with the array in index.html).
// For each level it runs BFS and prints {name, diff, minMoves, status}.

import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

const GRID_ROWS = 6;
const GRID_COLS = 6;
const EXIT_ROW = 2;
const MAX_BFS_STATES = 600000;

function in_bounds(r, c) { return r >= 0 && r < GRID_ROWS && c >= 0 && c < GRID_COLS; }

function normalizeBlock(b, idx) {
  return {
    id: b.id ?? `b${idx}`,
    kind: b.kind ?? 'slider',
    dir: b.dir, len: b.len, row: b.row, col: b.col,
    extent: b.extent ?? 1,
    target: !!b.target,
    heavy: b.heavy ?? 0,
    breakable: !!b.breakable,
    keyId: b.keyId ?? null,
    lockId: b.lockId ?? null,
    destroyed: false, unlocked: false,
  };
}
function normalizeTile(t) {
  return { row: t.row, col: t.col, type: t.type, arrowDir: t.arrowDir, pairId: t.pairId };
}
function cellsOf(b) {
  if (b.destroyed) return [];
  const ext = b.extent || 1;
  const dr = b.dir === 'v' ? ext : 0;
  const dc = b.dir === 'h' ? ext : 0;
  const cells = [];
  for (let i = 0; i < b.len; i++) cells.push({ r: b.row + i * dr, c: b.col + i * dc });
  return cells;
}
function sweptCells(b, newDir, newExtent) {
  const pr = b.row, pc = b.col;
  const startBody = [];
  const ext = b.extent || 1;
  const dr0 = b.dir === 'v' ? ext : 0;
  const dc0 = b.dir === 'h' ? ext : 0;
  for (let i = 1; i < b.len; i++) startBody.push({ r: pr + i * dr0, c: pc + i * dc0 });
  const dr1 = newDir === 'v' ? newExtent : 0;
  const dc1 = newDir === 'h' ? newExtent : 0;
  const endBody = [];
  for (let i = 1; i < b.len; i++) endBody.push({ r: pr + i * dr1, c: pc + i * dc1 });
  const all = [{ r: pr, c: pc }, ...startBody, ...endBody];
  let minR = Infinity, maxR = -Infinity, minC = Infinity, maxC = -Infinity;
  all.forEach(({ r, c }) => {
    if (r < minR) minR = r; if (r > maxR) maxR = r;
    if (c < minC) minC = c; if (c > maxC) maxC = c;
  });
  const startSet = new Set(startBody.map(p => `${p.r},${p.c}`));
  const endSet = new Set(endBody.map(p => `${p.r},${p.c}`));
  const swept = [];
  for (let r = minR; r <= maxR; r++) {
    for (let c = minC; c <= maxC; c++) {
      if (r === pr && c === pc) continue;
      if (startSet.has(`${r},${c}`) || endSet.has(`${r},${c}`)) continue;
      swept.push({ r, c });
    }
  }
  return { swept, endBody };
}
const SWIVEL_ORIENTATIONS = [
  { dir: 'h', extent: +1 }, { dir: 'h', extent: -1 },
  { dir: 'v', extent: +1 }, { dir: 'v', extent: -1 },
];
function adjacentRotations(b) {
  return SWIVEL_ORIENTATIONS.filter(o => o.dir !== b.dir);
}
function encodeState(state) {
  return state.map(b => b.destroyed ? 'X'
    : `${b.dir}${b.extent || 1},${b.row},${b.col}${b.unlocked ? 'U' : ''}`
  ).join('|');
}

function bfsSolve(initialBlocks, levelTiles, levelGravity) {
  const wallsLocal = (levelTiles || []).filter(t => t.type === 'wall').map(t => ({ r: t.row, c: t.col }));
  const onewayLocal = {}; const teleportLocal = {};
  (levelTiles || []).forEach(t => {
    if (t.type === 'oneway') onewayLocal[`${t.row},${t.col}`] = t.arrowDir;
    if (t.type === 'teleport') {
      const partner = (levelTiles || []).find(o => o !== t && o.type === 'teleport' && o.pairId === t.pairId);
      if (partner) teleportLocal[`${t.row},${t.col}`] = { r: partner.row, c: partner.col };
    }
  });

  function occOf(state) {
    const g = Array.from({ length: GRID_ROWS }, () => Array(GRID_COLS).fill(-1));
    wallsLocal.forEach(w => { if (in_bounds(w.r, w.c)) g[w.r][w.c] = -2; });
    state.forEach((b, idx) => {
      cellsOf(b).forEach(({ r, c }) => { if (in_bounds(r, c)) g[r][c] = idx; });
    });
    return g;
  }
  function lockUpdateLocal(state) {
    const keysByID = {};
    state.forEach((b, i) => { if (b.keyId && !b.destroyed) (keysByID[b.keyId] ||= []).push(i); });
    state.forEach(b => {
      if (b.lockId && !b.unlocked) {
        const keys = keysByID[b.lockId] || [];
        const lockCells = cellsOf(b);
        let touch = false;
        for (const ki of keys) {
          const kc = cellsOf(state[ki]);
          outer: for (const a of lockCells) for (const c of kc) {
            if (Math.abs(a.r - c.r) + Math.abs(a.c - c.c) === 1) { touch = true; break outer; }
          }
          if (touch) break;
        }
        if (touch) b.unlocked = true;
      }
    });
  }
  function gravitySettleLocal(state) {
    if (!levelGravity) return;
    const dr = levelGravity === 'down' ? +1 : -1;
    let changed = true;
    while (changed) {
      changed = false;
      const order = [...state.keys()].sort((a, b) => {
        const ra = Math.max(...cellsOf(state[a]).map(p => p.r), -Infinity);
        const rb = Math.max(...cellsOf(state[b]).map(p => p.r), -Infinity);
        return levelGravity === 'down' ? rb - ra : ra - rb;
      });
      for (const i of order) {
        const b = state[i];
        if (b.destroyed) continue;
        if (b.kind === 'swivel') continue;
        if (b.lockId && !b.unlocked) continue;
        if (b.keyId) continue;
        const cells = cellsOf(b);
        const occ = occOf(state);
        cells.forEach(({ r, c }) => occ[r][c] = -1);
        let canFall = true;
        for (const { r, c } of cells) {
          const nr = r + dr;
          if (!in_bounds(nr, c)) { canFall = false; break; }
          if (occ[nr][c] !== -1) { canFall = false; break; }
          const okey = `${nr},${c}`;
          if (onewayLocal[okey]) {
            const need = dr > 0 ? 'down' : 'up';
            if (onewayLocal[okey] !== need) { canFall = false; break; }
          }
        }
        if (canFall) { b.row += dr; changed = true; }
      }
    }
  }
  function teleportFn(state, idx) {
    const b = state[idx];
    if (b.destroyed || b.kind === 'swivel') return;
    const cells = cellsOf(b);
    for (let i = 0; i < cells.length; i++) {
      const { r, c } = cells[i];
      const partner = teleportLocal[`${r},${c}`];
      if (!partner) continue;
      const ext = b.extent || 1;
      const dr = b.dir === 'v' ? ext : 0;
      const dc = b.dir === 'h' ? ext : 0;
      const newRow = partner.r - i * dr;
      const newCol = partner.c - i * dc;
      const occ = occOf(state);
      cellsOf(b).forEach(p => occ[p.r][p.c] = -1);
      let ok = true;
      for (let j = 0; j < b.len; j++) {
        const nr = newRow + j * dr;
        const nc = newCol + j * dc;
        if (!in_bounds(nr, nc)) { ok = false; break; }
        if (occ[nr][nc] !== -1) { ok = false; break; }
      }
      if (ok) { b.row = newRow; b.col = newCol; }
      return;
    }
  }
  function settle(state, idx) {
    if (idx != null && idx >= 0) teleportFn(state, idx);
    gravitySettleLocal(state);
    lockUpdateLocal(state);
  }

  function maxSlideLocal(state, idx, delta) {
    const b = state[idx];
    if (!b || b.destroyed || b.kind === 'swivel') return 0;
    if (b.lockId && !b.unlocked) return 0;
    const occ = occOf(state);
    cellsOf(b).forEach(({ r, c }) => occ[r][c] = -1);
    let steps = 0;
    while (true) {
      const next = steps + 1;
      let cr, cc;
      if (delta > 0) {
        cr = b.row + (b.dir === 'v' ? b.len - 1 + next : 0);
        cc = b.col + (b.dir === 'h' ? b.len - 1 + next : 0);
      } else {
        cr = b.row + (b.dir === 'v' ? -next : 0);
        cc = b.col + (b.dir === 'h' ? -next : 0);
      }
      if (!in_bounds(cr, cc)) {
        if (b.target && b.dir === 'h' && delta > 0 && cr === EXIT_ROW) return steps + GRID_COLS;
        break;
      }
      if (occ[cr][cc] !== -1) break;
      const tkey = `${cr},${cc}`;
      if (onewayLocal[tkey]) {
        const moveDir = (b.dir === 'h' ? (delta > 0 ? 'right' : 'left') : (delta > 0 ? 'down' : 'up'));
        if (onewayLocal[tkey] !== moveDir) break;
      }
      steps = next;
    }
    return steps;
  }
  function canRotateLocal(state, idx, newDir, newExtent) {
    const b = state[idx];
    if (b.kind !== 'swivel') return false;
    if (b.dir === newDir) return false;
    const occ = occOf(state);
    cellsOf(b).forEach(({ r, c }) => occ[r][c] = -1);
    const { swept, endBody } = sweptCells(b, newDir, newExtent);
    for (const { r, c } of endBody) {
      if (!in_bounds(r, c)) return false;
      if (occ[r][c] !== -1) return false;
    }
    for (const { r, c } of swept) {
      if (!in_bounds(r, c)) return false;
      if (occ[r][c] !== -1) return false;
    }
    return true;
  }
  function isSolvedLocal(state) {
    const t = state.find(b => b.target && !b.destroyed);
    if (!t) return false;
    return t.col >= GRID_COLS;
  }

  // Use Dijkstra (priority queue) to handle non-uniform edge costs (heavy moves cost > 1).
  // For simplicity, since costs are small ints, use a bucket queue.
  const start = initialBlocks.map(b => ({ ...b }));
  settle(start);
  const startKey = encodeState(start);
  const visited = new Map(); visited.set(startKey, 0);
  // Buckets indexed by depth (cost). Cost is bounded by maybe a few hundred.
  const buckets = [[ { state: start, key: startKey } ]];
  let depth = 0;
  while (depth < buckets.length) {
    const bucket = buckets[depth] || [];
    for (let bi = 0; bi < bucket.length; bi++) {
      if (visited.size >= MAX_BFS_STATES) return { minMoves: -1, exhausted: true };
      const { state, key } = bucket[bi];
      if (visited.get(key) !== depth) continue; // stale (we found a shorter path later)
      if (isSolvedLocal(state)) return { minMoves: depth };
      // Slide
      for (let i = 0; i < state.length; i++) {
        const b = state[i];
        if (!b || b.destroyed || b.kind === 'swivel') continue;
        const isHeavy = b.heavy && b.heavy > 1;
        for (const delta of [-1, +1]) {
          const maxS = Math.min(maxSlideLocal(state, i, delta), GRID_COLS);
          const stepRange = isHeavy ? [1] : Array.from({ length: maxS }, (_, k) => k + 1);
          for (const s of stepRange) {
            if (s > maxS) continue;
            const ns = state.map(x => ({ ...x }));
            if (ns[i].dir === 'h') ns[i].col += delta * s;
            else ns[i].row += delta * s;
            settle(ns, i);
            const cost = isHeavy ? b.heavy : 1;
            const nd = depth + cost;
            const nk = encodeState(ns);
            if (!visited.has(nk) || visited.get(nk) > nd) {
              visited.set(nk, nd);
              (buckets[nd] ||= []).push({ state: ns, key: nk });
            }
          }
          if (b.breakable && maxS > 0) {
            const ns = state.map(x => ({ ...x }));
            const slideS = isHeavy ? 1 : maxS;
            if (ns[i].dir === 'h') ns[i].col += delta * slideS;
            else ns[i].row += delta * slideS;
            ns[i].destroyed = true;
            settle(ns, i);
            const cost = isHeavy ? b.heavy : 1;
            const nd = depth + cost;
            const nk = encodeState(ns);
            if (!visited.has(nk) || visited.get(nk) > nd) {
              visited.set(nk, nd);
              (buckets[nd] ||= []).push({ state: ns, key: nk });
            }
          }
        }
      }
      // Rotate
      for (let i = 0; i < state.length; i++) {
        const b = state[i];
        if (!b || b.destroyed || b.kind !== 'swivel') continue;
        for (const o of adjacentRotations(b)) {
          if (canRotateLocal(state, i, o.dir, o.extent)) {
            const ns = state.map(x => ({ ...x }));
            ns[i].dir = o.dir; ns[i].extent = o.extent;
            settle(ns, i);
            const nd = depth + 1;
            const nk = encodeState(ns);
            if (!visited.has(nk) || visited.get(nk) > nd) {
              visited.set(nk, nd);
              (buckets[nd] ||= []).push({ state: ns, key: nk });
            }
          }
        }
      }
    }
    depth++;
  }
  return { minMoves: -1 };
}

// ===== Load levels =====
// Read levels from index.html by extracting the L.push({...}) calls in the second <script> block.
const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const html = fs.readFileSync(path.join(__dirname, 'index.html'), 'utf8');

// Find the second script block (the LEVELS one).
const scripts = [...html.matchAll(/<script>([\s\S]*?)<\/script>/g)].map(m => m[1]);
const levelsScript = scripts[scripts.length - 1];
if (!levelsScript) { console.error('No levels script found'); process.exit(1); }

// Extract each L.push({...}) call. Use a brace-counting parser to handle nested objects.
function extractLevels(src) {
  const out = [];
  const re = /L\.push\(/g;
  let m;
  while ((m = re.exec(src))) {
    let i = m.index + m[0].length;
    let depth = 1, start = i;
    let inStr = null;
    while (i < src.length && depth > 0) {
      const ch = src[i];
      if (inStr) {
        if (ch === '\\') i++;
        else if (ch === inStr) inStr = null;
      } else {
        if (ch === '"' || ch === "'" || ch === '`') inStr = ch;
        else if (ch === '(') depth++;
        else if (ch === ')') depth--;
      }
      i++;
    }
    const body = src.slice(start, i - 1);
    out.push(body);
  }
  return out;
}
const literals = extractLevels(levelsScript);
const levels = literals.map(lit => {
  // eval each as an object literal (it's our own code; trusted).
  try { return (new Function(`return (${lit});`))(); } catch (e) { return null; }
}).filter(Boolean);

console.log(`Found ${levels.length} levels in index.html\n`);

const results = [];
const start = Date.now();
for (const lvl of levels) {
  const init = (lvl.blocks || lvl.cars || []).map((b, i) => normalizeBlock(b, i));
  const tiles = (lvl.tiles || []).map(normalizeTile);
  const t0 = Date.now();
  const r = bfsSolve(init, tiles, lvl.gravity || null);
  const ms = Date.now() - t0;
  const status = r.minMoves >= 0 ? 'OK' : (r.exhausted ? 'EXHAUSTED' : 'UNSOLVABLE');
  results.push({ level: lvl.name, diff: lvl.diff, minMoves: r.minMoves, ms, status });
  const tag = status === 'OK' ? '[32mOK[0m' : `[31m${status}[0m`;
  console.log(`Level ${String(lvl.name).padStart(3)} [${(lvl.diff||'').padEnd(7)}] minMoves=${String(r.minMoves).padStart(3)}  ${ms.toString().padStart(5)}ms  ${tag}`);
}
const totalMs = Date.now() - start;
const bad = results.filter(r => r.status !== 'OK');
console.log(`\nTotal: ${levels.length} levels, ${totalMs}ms`);
if (bad.length === 0) console.log('[32mAll levels solvable.[0m');
else { console.log(`[31m${bad.length} problem level(s):[0m`); bad.forEach(b => console.log(' ', b)); process.exit(1); }

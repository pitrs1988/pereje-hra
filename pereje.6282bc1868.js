// ── core.js ──
// ═══════════════════════════════════════════════════════════════════════════
//  DETERMINISTIC CORE — course generator, physics, replay codec.
//  Only + − × ÷, Math.sqrt/floor/abs/min/max and integer hashing are used here,
//  so a run replays bit-identically in every browser (needed for fair, verifiable
//  challenges). Never use Math.sin/cos/pow/exp/random in this section.
// ═══════════════════════════════════════════════════════════════════════════
const TICK_RATE = 120;
const DT = 1 / TICK_RATE;
const RIVER_H = 640;          // world units between nominal bank lines
const BANK_MAX = 42;          // max bank intrusion into the corridor
const FIRST_GATE_X = 700;
const PHYS = {
  pull: 1700,                 // cross-current acceleration (u/s²) — the "gravity"
  stroke: 575,                // velocity a paddle stroke sets against the current
  maxDrift: 840,
  tilt: 0.35,                 // how much vertical speed tilts the hull
  hitOff: [18, 0, -18],       // hitbox circles along the hull axis
  hitR: [7.5, 9.5, 7.5],
  starR: 15,
};
const BIOME_GATES = 20;       // gates per biome

// Difficulty levels change both the physics and the course. A run only ever competes with runs
// of the same level (the level travels inside every challenge code).
//   flipW = half-width of the slack water around a current reversal (0 = the level has no flips)
const LEVELS = [
  { id: 0, name: 'Děti', speed: 0.8, pull: 1300, stroke: 500, maxDrift: 680, hit: 0.85, ramp: 120,
    gap: [300, 220], spacing: [380, 330], maxD: [120, 190], logsFrom: 8, boomFrom: -1, bridgeFrom: 14, flipFrom: -1, flipW: 0 },
  { id: 1, name: 'Normální', speed: 1, pull: 1700, stroke: 575, maxDrift: 840, hit: 1, ramp: 70,
    gap: [238, 158], spacing: [340, 292], maxD: [150, 250], logsFrom: 6, boomFrom: 18, bridgeFrom: 12, flipFrom: 26, flipW: 230 },
  { id: 2, name: 'Profi vodák', speed: 1.12, pull: 1850, stroke: 600, maxDrift: 900, hit: 1, ramp: 45,
    gap: [210, 148], spacing: [320, 280], maxD: [170, 270], logsFrom: 3, boomFrom: 8, bridgeFrom: 8, flipFrom: 14, flipW: 140 },
];
const levelOf = id => LEVELS[id === 0 || id === 2 ? id : 1];
const CALM_DAMP = 3;          // 1/s — how fast vertical drift dies in slack water

const clamp = (v, a, b) => (v < a ? a : v > b ? b : v);
const lerp = (a, b, t) => a + (b - a) * t;
const ease = t => t * t * (3 - 2 * t);

function hash32(a, b = 0, c = 0) {
  let h = Math.imul((a ^ 0x9E3779B9) | 0, 0x85EBCA6B);
  h ^= h >>> 13; h = Math.imul(h ^ (b | 0), 0xC2B2AE35);
  h ^= h >>> 16; h = Math.imul(h ^ (c | 0), 0x27D4EB2F);
  h ^= h >>> 15; h = Math.imul(h, 0x165667B1);
  h ^= h >>> 16;
  return h >>> 0;
}
const rnd = (seed, a, b = 0) => hash32(seed, a, b) / 4294967296;

const _te = new TextEncoder();
function strHash(s) {
  let h = 0x811C9DC5;
  for (const ch of _te.encode(String(s))) { h ^= ch; h = Math.imul(h, 0x01000193); }
  return h >>> 0;
}

function vnoise(seed, x) {
  const i = Math.floor(x), f = x - i;
  const a = rnd(seed, i), b = rnd(seed, i + 1);
  return a + (b - a) * (f * f * (3 - 2 * f));
}
const fbm1 = (seed, x) => vnoise(seed, x) * 0.62 + vnoise(seed + 17, x * 2.3) * 0.27 + vnoise(seed + 41, x * 5.1) * 0.11;

// Moving obstacles: smooth ping-pong, polynomial only.
function moveOffset(m, tick) {
  if (!m) return 0;
  let u = tick / m.period + m.phase;
  u -= Math.floor(u);
  const tri = 1 - Math.abs(2 * u - 1);
  return m.amp * (2 * (tri * tri * (3 - 2 * tri)) - 1);
}

function segDist2(px, py, x1, y1, x2, y2) {
  const dx = x2 - x1, dy = y2 - y1;
  const l2 = dx * dx + dy * dy;
  let t = l2 > 0 ? ((px - x1) * dx + (py - y1) * dy) / l2 : 0;
  t = t < 0 ? 0 : t > 1 ? 1 : t;
  const ex = x1 + dx * t - px, ey = y1 + dy * t - py;
  return ex * ex + ey * ey;
}

// ─── Course: lazily generated, fully determined by the seed ────────────────
class Course {
  constructor(seed, level = 1) {
    this.seed = seed >>> 0;
    this.lv = levelOf(level);
    this.level = this.lv.id;
    this.sb1 = hash32(this.seed, 0xB1);
    this.sb2 = hash32(this.seed, 0xB2);
    this.gates = [];
    this.stars = [];
    this.flips = [];          // x positions where the cross-current reverses
    this.biomeEdges = [];     // x positions where the biome advances
    this.n = 0;
    this.lastX = FIRST_GATE_X - 380;
    this.prevOpen = [{ cy: RIVER_H / 2, amp: 0 }];
    this.lastBridge = -99;
    this.lastKind = '';
    this.nextFlip = this.lv.flipFrom >= 0 ? this.lv.flipFrom + Math.floor(this.r(0, 90) * 6) : -1;
    this.genX = 0;
  }
  r(n, k) { return rnd(this.seed, n, k); }
  ensure(x) { while (this.genX < x) this._next(); }

  speedAt(x) { return (232 + 110 * ease(clamp(x / 26000, 0, 1))) * this.lv.speed; }
  difficultyAt(x) { return clamp(x / 26000, 0, 1); }
  bankTop(x) { return 6 + (BANK_MAX - 6) * fbm1(this.sb1, x / 260); }
  bankBot(x) { return RIVER_H - 6 - (BANK_MAX - 6) * fbm1(this.sb2, x / 240); }
  _countLE(arr, x) {
    let lo = 0, hi = arr.length;
    while (lo < hi) { const m = (lo + hi) >> 1; if (arr[m] <= x) lo = m + 1; else hi = m; }
    return lo;
  }
  // Which way the current pulls (+1 toward the lower bank); strokes always push against it.
  currentAt(x) { return (this._countLE(this.flips, x) & 1) ? -1 : 1; }
  // Signed pull strength: ±1 in open water, easing smoothly to 0 at a flip line and back up on the
  // other side (slack water), so a reversal never yanks the boat around.
  flowAt(x) {
    const i = this._countLE(this.flips, x), sign = (i & 1) ? -1 : 1, W = this.lv.flipW;
    if (W > 0) {
      let d = 1e9;
      if (i < this.flips.length) d = this.flips[i] - x;
      if (i > 0 && x - this.flips[i - 1] < d) d = x - this.flips[i - 1];
      if (d < W) { const t = d / W; return sign * t * t * (3 - 2 * t); }
    }
    return sign;
  }
  biomeAt(x) { return this._countLE(this.biomeEdges, x) % 5; }
  // first gate index with gate.x >= x
  gateIndexAt(x) {
    let lo = 0, hi = this.gates.length;
    while (lo < hi) { const m = (lo + hi) >> 1; if (this.gates[m].x < x) lo = m + 1; else hi = m; }
    return lo;
  }
  starIndexAt(x) {
    let lo = 0, hi = this.stars.length;
    while (lo < hi) { const m = (lo + hi) >> 1; if (this.stars[m].x < x) lo = m + 1; else hi = m; }
    return lo;
  }

  _next() {
    const n = this.n;
    const R = k => this.r(n, k);
    const lv = this.lv;
    const t = Math.min(1, n / lv.ramp), e = ease(t);
    let spacing = lerp(lv.spacing[0], lv.spacing[1], e) + (R(1) - 0.5) * 40;
    let gap = lerp(lv.gap[0], lv.gap[1], e) + (R(2) - 0.5) * 16;
    let maxD = lerp(lv.maxD[0], lv.maxD[1], e);
    if (n < 3) gap += 30 - n * 10;

    let kind = 'rocks';
    const kr = R(3);
    if (n >= lv.logsFrom && kr < 0.34) kind = 'logs';
    if (lv.boomFrom >= 0 && n >= lv.boomFrom && kr > 1 - lerp(0.16, 0.34, clamp((n - lv.boomFrom) / 50, 0, 1))) kind = 'boom';
    if (n >= lv.bridgeFrom && n - this.lastBridge >= 9 && R(4) < 0.24) kind = 'bridge';

    const flipHere = n === this.nextFlip;
    if (flipHere) {
      // room for the whole slack-water zone between two gates, the flip line in the middle
      spacing = Math.max(spacing, 2 * lv.flipW + 240);
      if (kind === 'bridge' || kind === 'boom') kind = 'rocks';
      maxD = Math.min(maxD, 120);
      const inFlip = (this.flips.length & 1) === 1;
      this.nextFlip = n + (inFlip ? 14 + Math.floor(R(91) * 10) : 7 + Math.floor(R(92) * 5));
    }
    if (this.lastKind === 'bridge') spacing += 50;
    if (n === 0) spacing = 380;

    const x = this.lastX + spacing;
    if (flipHere) this.flips.push(this.lastX + spacing * 0.5);
    if (n > 0 && n % BIOME_GATES === 0) this.biomeEdges.push(this.lastX + spacing * 0.5);

    const g = { n, x, kind, shapes: [], open: [], move: null, halfW: 0, biome: 0 };
    const amp = kind === 'boom'
      ? lerp(28, 78, clamp((n - lv.boomFrom) / 50, 0, 1)) * (0.7 + 0.3 * R(6)) : 0;

    // Allowed gap-center window so every opening is reachable from every previous opening.
    let lo = -1e9, hi = 1e9;
    for (const o of this.prevOpen) {
      const d = Math.max(60, maxD - o.amp - amp);
      lo = Math.max(lo, o.cy - d); hi = Math.min(hi, o.cy + d);
    }

    if (kind === 'bridge') {
      this.lastBridge = n;
      let m = RIVER_H / 2 + (R(8) - 0.5) * 120;
      m = clamp(m, lo + 40, hi - 40);
      m = clamp(m, 260, 380);
      const pr = 24, ph = 12;
      const gA = Math.min(gap + 6, (m - ph - pr) - (BANK_MAX + 8));
      const gB = Math.min(gap + 6, (RIVER_H - BANK_MAX - 8) - (m + ph + pr));
      const aTop = m - ph - pr - gA, bBot = m + ph + pr + gB;
      g.shapes.push({ t: 1, x1: x, y1: m - ph, x2: x, y2: m + ph, r: pr, v: 0 });
      g.shapes.push({ t: 1, x1: x, y1: -110, x2: x, y2: aTop - pr, r: pr, v: 1 });
      g.shapes.push({ t: 1, x1: x, y1: bBot + pr, x2: x, y2: RIVER_H + 110, r: pr, v: 2 });
      g.open.push({ cy: aTop + gA / 2, gap: gA, amp: 0 }, { cy: bBot - gB / 2, gap: gB, amp: 0 });
      g.mid = m;
    } else {
      const bandLo = BANK_MAX + 24 + gap / 2 + amp, bandHi = RIVER_H - BANK_MAX - 24 - gap / 2 - amp;
      let a = Math.max(lo, bandLo), b = Math.min(hi, bandHi);
      if (a > b) { const c = clamp((lo + hi) / 2, bandLo, bandHi); a = b = c; }
      // favour changes of direction a little — makes rhythms less monotonous
      let u = R(5);
      const prev = this.prevOpen[0].cy;
      if ((n & 3) === 1) u = prev > RIVER_H / 2 ? u * 0.5 : 0.5 + u * 0.5;
      const cy = lerp(a, b, u);
      const top = cy - gap / 2, bot = cy + gap / 2;
      if (kind === 'rocks') {
        this._rockCol(g, x, top, -1, n, 30);
        this._rockCol(g, x, bot, 1, n, 60);
      } else if (kind === 'logs') {
        this._log(g, x, top, -1, n, 30);
        this._log(g, x, bot, 1, n, 50);
      } else { // boom: chained floating logs that slide across the current
        const lr = 15;
        g.shapes.push({ t: 1, x1: x, y1: -150, x2: x, y2: top - lr, r: lr, v: 0 });
        g.shapes.push({ t: 1, x1: x, y1: bot + lr, x2: x, y2: RIVER_H + 150, r: lr, v: 1 });
        g.move = { amp, period: Math.round(lerp(330, 210, clamp((n - lv.boomFrom) / 60, 0, 1)) / lv.speed), phase: R(7) };
      }
      g.open.push({ cy, gap, amp });
    }

    for (const s of g.shapes) {
      const w = s.t === 0 ? Math.abs(s.x - x) + s.r : Math.max(Math.abs(s.x1 - x), Math.abs(s.x2 - x)) + s.r;
      if (w > g.halfW) g.halfW = w;
    }
    // score as soon as the boat clears the part of the gate that is actually in the river
    let px = x;
    for (const s of g.shapes) {
      if (s.t === 0) { if (s.y + s.r > 0 && s.y - s.r < RIVER_H) px = Math.max(px, s.x + s.r); continue; }
      const ya = Math.max(0, Math.min(s.y1, s.y2)), yb = Math.min(RIVER_H, Math.max(s.y1, s.y2));
      if (ya > yb) continue;
      const xAt = y => (s.y2 === s.y1 ? Math.max(s.x1, s.x2) : s.x1 + (s.x2 - s.x1) * (y - s.y1) / (s.y2 - s.y1));
      px = Math.max(px, xAt(ya) + s.r, xAt(yb) + s.r);
    }
    g.passX = px;
    g.biome = this.biomeAt(x);

    // ── stars: arcs between gates and daring ones inside gaps ──
    if (n >= 1 && R(20) < 0.3) {
      const po = this.prevOpen[Math.floor(R(21) * this.prevOpen.length)];
      const no = g.open[Math.floor(R(22) * g.open.length)];
      const yMid = (po.cy + no.cy) / 2 + (R(23) - 0.5) * 110;
      const fr = [0.36, 0.5, 0.64];
      for (let i = 0; i < 3; i++) {
        const f = fr[i];
        const lin = lerp(po.cy, no.cy, f);
        const w = 1 - ((f - 0.5) * (f - 0.5)) * 4;          // 0.92..1 bulge
        const y = clamp(lin + (yMid - (po.cy + no.cy) / 2) * w, BANK_MAX + 40, RIVER_H - BANK_MAX - 40);
        this.stars.push({ id: this.stars.length, x: this.lastX + spacing * f, y });
      }
    }
    if (n >= 2 && !g.move && R(24) < 0.24) {
      const o = g.open[Math.floor(R(25) * g.open.length)];
      const side = R(26) < 0.5 ? -1 : 1;
      this.stars.push({ id: this.stars.length, x, y: o.cy + side * (o.gap / 2 - 30) });
    }

    this.gates.push(g);
    this.prevOpen = g.open;
    this.lastKind = kind;
    this.lastX = x;
    this.genX = x;
    this.n++;
  }

  _rockCol(g, gx, edge, dir, n, k) {
    let i = 0;
    let r = 24 + this.r(n, k) * 10;
    let y = edge + dir * r;
    let x = gx + (this.r(n, k + 1) - 0.5) * 10;
    const far = dir < 0 ? -34 : RIVER_H + 34;
    for (;;) {
      g.shapes.push({ t: 0, x, y, r, v: hash32(this.seed, n, k + i) & 1023 });
      // side boulders for a natural cluster — always kept clear of the gap edge
      if (i >= 1 && this.r(n, k + 40 + i) < 0.7) {
        const rs = 12 + this.r(n, k + 50 + i) * 11;
        const side = this.r(n, k + 60 + i) < 0.5 ? -1 : 1;
        const sx = x + side * (r * 0.8 + rs * 0.6);
        let sy = y + dir * (this.r(n, k + 70 + i) - 0.5) * r;
        if (dir < 0) sy = Math.min(sy, edge - 6 - rs); else sy = Math.max(sy, edge + 6 + rs);
        g.shapes.push({ t: 0, x: sx, y: sy, r: rs, v: hash32(this.seed, n, k + 80 + i) & 1023 });
      }
      if ((dir < 0 && y < far) || (dir > 0 && y > far) || i > 14) break;
      i++;
      const r2 = 21 + this.r(n, k + 2 + i * 3) * 17;
      y += dir * (r + r2) * 0.6;
      x = gx + (this.r(n, k + 3 + i * 3) - 0.5) * 30;
      r = r2;
    }
  }

  _log(g, gx, edge, dir, n, k) {
    const lr = 13 + this.r(n, k) * 4;
    const tipX = gx + (this.r(n, k + 1) - 0.5) * 24;
    const tipY = edge + dir * lr;
    const baseX = gx + (this.r(n, k + 2) - 0.5) * 150;
    const baseY = dir < 0 ? -110 : RIVER_H + 110;
    g.shapes.push({ t: 1, x1: baseX, y1: baseY, x2: tipX, y2: tipY, r: lr, v: hash32(this.seed, n, k) & 1023 });
    if (this.r(n, k + 3) < 0.65) { // a second, shorter log leaning on the first
      const lr2 = 10 + this.r(n, k + 4) * 4;
      const t2Y = edge + dir * (lr2 + 22 + this.r(n, k + 5) * 40);
      const t2X = tipX + (this.r(n, k + 6) - 0.5) * 70;
      g.shapes.push({ t: 1, x1: baseX + (this.r(n, k + 7) - 0.5) * 120, y1: baseY, x2: t2X, y2: t2Y, r: lr2, v: hash32(this.seed, n, k + 9) & 1023 });
    }
  }
}

// ─── Simulation of one boat ────────────────────────────────────────────────
class Sim {
  constructor(course) {
    this.c = course;
    course.ensure(3000);
    this.tick = 0;
    this.x = 0; this.y = RIVER_H / 2; this.vy = 0; this.vx = course.speedAt(0);
    this.px = this.x; this.py = this.y; this.pvy = 0;
    this.alive = true;
    this.score = 0; this.gatesPassed = 0; this.starsGot = 0; this.strokes = 0;
    this.nextGate = 0; this.nextStar = 0;
    this.taken = [];            // star ids collected
    this.cur = 1;
    this.deathTick = -1; this.death = null;
    this.gateClear = 1e9;
    this.events = [];
  }
  clone() {
    const s = Object.create(Sim.prototype);
    Object.assign(s, this);
    s.taken = this.taken.slice();
    s.events = [];
    return s;
  }
  heading() {
    const hx = this.vx, hy = this.vy * PHYS.tilt;
    const l = Math.sqrt(hx * hx + hy * hy) || 1;
    return [hx / l, hy / l];
  }
  step(tap) {
    if (!this.alive) return;
    const c = this.c;
    if (this.x + 3200 > c.genX) c.ensure(this.x + 4200);
    this.px = this.x; this.py = this.y; this.pvy = this.vy;
    const lv = c.lv;
    const cur = c.currentAt(this.x);
    if (cur !== this.cur) { this.cur = cur; this.events.push({ type: 'flip', cur }); }
    // Slack water around a reversal: the pull fades out and back in, strokes are gentler and
    // vertical drift dies away, so the player has time to adjust to the new direction.
    const flow = c.flowAt(this.x);
    const calm = 1 - (flow < 0 ? -flow : flow);
    if (tap) { this.vy = -cur * lv.stroke * (1 - 0.6 * calm); this.strokes++; this.events.push({ type: 'stroke', n: this.strokes }); }
    this.vy += flow * lv.pull * DT;
    if (calm > 0) this.vy -= this.vy * calm * CALM_DAMP * DT;
    if (this.vy > lv.maxDrift) this.vy = lv.maxDrift; else if (this.vy < -lv.maxDrift) this.vy = -lv.maxDrift;
    this.vx = c.speedAt(this.x);
    this.x += this.vx * DT;
    this.y += this.vy * DT;
    this.tick++;
    this._collide();
    if (this.alive) this._progress();
  }
  _die(cause, x, y) {
    this.alive = false; this.deathTick = this.tick;
    this.death = { cause, x, y };
    this.events.push({ type: 'crash', cause, x, y });
  }
  _collide() {
    const c = this.c;
    const [hx, hy] = this.heading();
    for (let i = 0; i < 3; i++) {
      const o = PHYS.hitOff[i], r = PHYS.hitR[i] * c.lv.hit;
      const px = this.x + hx * o, py = this.y + hy * o;
      if (py - r < c.bankTop(px)) return this._die('bank', px, py - r);
      if (py + r > c.bankBot(px)) return this._die('bank', px, py + r);
    }
    const g0 = Math.max(0, this.nextGate - 1), g1 = Math.min(c.gates.length - 1, this.nextGate + 1);
    for (let gi = g0; gi <= g1; gi++) {
      const g = c.gates[gi];
      if (this.x + 40 < g.x - g.halfW || this.x - 40 > g.x + g.halfW) continue;
      const off = g.move ? moveOffset(g.move, this.tick) : 0;
      for (const s of g.shapes) {
        for (let i = 0; i < 3; i++) {
          const o = PHYS.hitOff[i], hr = PHYS.hitR[i] * c.lv.hit;
          const px = this.x + hx * o, py = this.y + hy * o - off;
          const rr = s.r + hr;
          const d2 = s.t === 0
            ? (px - s.x) * (px - s.x) + (py - s.y) * (py - s.y)
            : segDist2(px, py, s.x1, s.y1, s.x2, s.y2);
          if (d2 < rr * rr) return this._die(g.kind, px, py + off);
          if (gi === this.nextGate && d2 < (rr + 14) * (rr + 14)) {
            const cl = Math.sqrt(d2) - rr;
            if (cl < this.gateClear) this.gateClear = cl;
          }
        }
      }
    }
  }
  _progress() {
    const c = this.c;
    while (this.nextGate < c.gates.length && this.x > c.gates[this.nextGate].passX) {
      const g = c.gates[this.nextGate];
      this.nextGate++; this.gatesPassed++; this.score++;
      this.events.push({ type: 'gate', n: g.n, near: this.gateClear < 7 });
      this.gateClear = 1e9;
    }
    const st = c.stars;
    while (this.nextStar < st.length && st[this.nextStar].x < this.x - 40) this.nextStar++;
    for (let i = this.nextStar; i < st.length && st[i].x < this.x + 40; i++) {
      const s = st[i];
      if (this.taken.includes(s.id)) continue;
      const rr = PHYS.starR + PHYS.hitR[1] + 4;
      if ((s.x - this.x) * (s.x - this.x) + (s.y - this.y) * (s.y - this.y) < rr * rr) {
        this.taken.push(s.id); this.starsGot++; this.score++;
        this.events.push({ type: 'star', id: s.id, x: s.x, y: s.y });
      }
    }
  }
}

// Run a replay headlessly. Returns the finished sim.
function runReplay(seed, taps, maxTicks = TICK_RATE * 60 * 45, level = 1) {
  const sim = new Sim(new Course(seed, level));
  let ti = 0;
  while (sim.alive && sim.tick < maxTicks) {
    let tap = false;
    while (ti < taps.length && taps[ti] <= sim.tick) { if (taps[ti] === sim.tick) tap = true; ti++; }
    sim.step(tap);
    sim.events.length = 0;
  }
  return sim;
}

// ─── Challenge codes: seed + run replay, checksummed, base64url ────────────
const CODE_PREFIX = 'PRJ1-';
const MODES = { free: 0, daily: 1, river: 2 };
const _td = new TextDecoder();
function b64uEnc(bytes) {
  let s = '';
  for (let i = 0; i < bytes.length; i++) s += String.fromCharCode(bytes[i]);
  return btoa(s).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}
function b64uDec(str) {
  let s = str.replace(/-/g, '+').replace(/_/g, '/');
  while (s.length % 4) s += '=';
  const bin = atob(s);
  const out = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
  return out;
}
function fnvBytes(bytes, len) {
  let h = 0x811C9DC5;
  for (let i = 0; i < len; i++) { h ^= bytes[i]; h = Math.imul(h, 0x01000193); }
  return h >>> 0;
}
// RULES must be bumped whenever physics, hitboxes or the course generator change:
// codes and saved ghosts from other rule sets are then rejected instead of mis-verifying.
const RULES = 2;
const MAX_RUN_TICKS = TICK_RATE * 60 * 120;   // 2 h — anything longer is not a real run
const cleanText = (s, n) => Array.from(String(s || '').replace(/[\u0000-\u001f\u007f\u200e\u200f\u202a-\u202e\u2066-\u2069]/g, '').normalize('NFC')).slice(0, n).join('');
const Replay = {
  // r: { mode, seed, score, endTick, name, label, taps (strictly increasing), pauses }
  encode(r) {
    const w = [];
    const vu = v => { v = Math.max(0, Math.floor(v)); while (v >= 128) { w.push((v & 127) | 128); v = Math.floor(v / 128); } w.push(v); };
    const str = (s, max) => { const b = _te.encode(cleanText(s, max)); vu(b.length); for (const x of b) w.push(x); };
    w.push(3, RULES, r.mode & 255, levelOf(r.level).id);
    const sd = r.seed >>> 0; w.push(sd & 255, (sd >>> 8) & 255, (sd >>> 16) & 255, sd >>> 24);
    vu(r.score); vu(r.endTick); vu(r.pauses | 0);
    str(r.name, 16); str(r.label, 32);
    vu(r.taps.length);
    let prev = -1;
    for (const t of r.taps) {
      if (!(t > prev)) throw new Error('taps must be strictly increasing');
      vu(t - prev - 1); prev = t;
    }
    const h = fnvBytes(w, w.length);
    w.push(h & 255, (h >>> 8) & 255, (h >>> 16) & 255, h >>> 24);
    return CODE_PREFIX + b64uEnc(w);
  },
  // Accepts a bare code or any text/URL that contains one.
  decode(text) {
    const m = String(text || '').match(/PRJ1-([A-Za-z0-9_-]{8,})/);
    if (!m) throw new Error('Kód výzvy nenalezen (začíná na PRJ1-).');
    let b;
    try { b = b64uDec(m[1]); } catch { throw new Error('Kód je poškozený.'); }
    if (b.length < 14) throw new Error('Kód je příliš krátký.');
    const body = b.length - 4;
    const h = (b[body] | (b[body + 1] << 8) | (b[body + 2] << 16) | (b[body + 3] << 24)) >>> 0;
    if (h !== fnvBytes(b, body)) throw new Error('Kód je neúplný nebo poškozený (kontrolní součet nesedí).');
    let p = 0;
    const bad = () => new Error('Kód je poškozený.');
    const need = k => { if (p + k > body) throw bad(); };
    const u8 = () => { need(1); return b[p++]; };
    const vu = () => { let v = 0, mul = 1; for (let i = 0; i < 6; i++) { const x = u8(); v += (x & 127) * mul; if (!(x & 128)) return v; mul *= 128; } throw bad(); };
    const str = n => { const l = vu(); if (l > 200) throw bad(); need(l); const s = _td.decode(b.subarray(p, p + l)); p += l; return cleanText(s, n); };
    const ver = u8();
    if (ver < 1 || ver > 3) throw new Error('Kód je z novější verze hry.');
    const rules = ver === 1 ? 1 : u8();
    if (rules !== RULES) throw new Error('Kód je ze starší verze pravidel hry — přehrát ho nejde.');
    const mode = u8();
    const level = ver >= 3 ? u8() : 1;
    if (level > 2) throw bad();
    need(4);
    const seed = (b[p] | (b[p + 1] << 8) | (b[p + 2] << 16) | (b[p + 3] << 24)) >>> 0; p += 4;
    const score = vu(), endTick = vu();
    const pauses = ver === 1 ? -1 : vu();
    const name = str(16), label = str(32);
    const n = vu();
    if (endTick < 1 || endTick > MAX_RUN_TICKS || n > endTick) throw bad();
    const taps = new Array(n);
    let prev = -1;
    for (let i = 0; i < n; i++) { prev = prev + 1 + vu(); taps[i] = prev; }
    if (n && taps[n - 1] >= endTick) throw bad();
    return { mode, level, seed, score, endTick, name, label, taps, pauses, rules };
  },
  // A genuine run dies exactly at endTick with exactly the claimed score.
  verify(r) {
    const sim = runReplay(r.seed, r.taps, r.endTick, r.level);
    return { ok: !sim.alive && sim.score === r.score && sim.deathTick === r.endTick, score: sim.score, endTick: sim.deathTick, sim };
  },
};

function utcDayKey(d = new Date()) {
  return d.getUTCFullYear() + '-' + String(d.getUTCMonth() + 1).padStart(2, '0') + '-' + String(d.getUTCDate()).padStart(2, '0');
}
const dailySeed = key => strHash('PEREJE/daily/' + key);
const riverName = name => String(name || '').normalize('NFC').trim().toUpperCase().slice(0, 24);
const riverSeed = name => strHash('PEREJE/river/' + riverName(name));

// Simple look-ahead pilot — drives the attract-mode boat behind the menu.
function pilotTap(sim, skill = 1) {
  const c = sim.c;
  const g = c.gates[sim.nextGate];
  let ty = RIVER_H / 2;
  if (g) {
    const eta = Math.max(0, (g.x - sim.x) / sim.vx);
    const off = g.move ? moveOffset(g.move, sim.tick + eta * TICK_RATE) : 0;
    let best = g.open[0];
    for (const o of g.open) if (Math.abs(o.cy - sim.y) < Math.abs(best.cy - sim.y)) best = o;
    ty = best.cy + off;
    if (eta > 0.9 && sim.nextGate > 0) {
      const pg = c.gates[sim.nextGate - 1];
      const w = clamp((eta - 0.9) / 0.6, 0, 1);
      ty = lerp(ty, pg.open[0].cy, w * 0.3);
    }
  }
  const cur = sim.cur, lv = c.lv;
  const flow = c.flowAt(sim.x), strength = flow < 0 ? -flow : flow;
  const py = sim.y + sim.vy * DT * 2;
  const err = (py - ty) * cur;      // >0 means drifted past the target in current direction
  if (strength < 0.35) return err > 26 * skill && sim.vy * cur >= 0;   // slack water: small corrections
  // stroke at the bottom of the arc so the hop is centred on the target line
  const apex = lv.stroke * lv.stroke / (2 * lv.pull * strength);
  return sim.vy * cur > 0 && err > Math.min(apex, 140) * 0.45 * skill;
}

;
// ── water.js ──
/* =====================================================================
   PEŘEJE — WebGL2 river WATER renderer
   One fullscreen triangle, one fragment pass. Offline, no external deps.
   Top-level declarations: WATER_PALETTES, WATER_CLARITY, createWaterRenderer
   ===================================================================== */

/* Tuned biome palettes (sRGB 0..1). The caller interpolates between them.
   0 forest dawn, 1 red canyon sunset, 2 jungle dusk, 3 moonlit night, 4 glacier */
const WATER_PALETTES = [
  { // 0 forest dawn — clear teal water over granite gravel
    deep:    [0.035, 0.235, 0.270],
    shallow: [0.180, 0.560, 0.520],
    bed:     [0.640, 0.600, 0.500],
    foam:    [0.960, 0.985, 0.975],
    sky:     [0.780, 0.860, 0.900],
    sun:     [1.000, 0.880, 0.700]
  },
  { // 1 red canyon sunset — ochre-jade water, rust sandstone bed
    deep:    [0.075, 0.250, 0.215],
    shallow: [0.420, 0.560, 0.360],
    bed:     [0.800, 0.540, 0.340],
    foam:    [1.000, 0.945, 0.870],
    sky:     [0.980, 0.680, 0.460],
    sun:     [1.000, 0.640, 0.320]
  },
  { // 2 jungle / wetland dusk — murky green, peat bed
    deep:    [0.075, 0.180, 0.095],
    shallow: [0.270, 0.360, 0.160],
    bed:     [0.400, 0.330, 0.200],
    foam:    [0.860, 0.900, 0.780],
    sky:     [0.520, 0.470, 0.580],
    sun:     [1.000, 0.720, 0.480]
  },
  { // 3 moonlit night — authored as "lit" colours; night param darkens them
    deep:    [0.040, 0.170, 0.300],
    shallow: [0.170, 0.400, 0.480],
    bed:     [0.440, 0.420, 0.400],
    foam:    [0.840, 0.910, 1.000],
    sky:     [0.090, 0.140, 0.260],
    sun:     [0.780, 0.870, 1.000]
  },
  { // 4 glacier — milky turquoise meltwater (glacial flour), pale stone bed
    deep:    [0.050, 0.400, 0.520],
    shallow: [0.400, 0.780, 0.800],
    bed:     [0.720, 0.790, 0.810],
    foam:    [0.975, 1.000, 1.000],
    sky:     [0.860, 0.930, 1.000],
    sun:     [1.000, 0.985, 0.950]
  }
];

/* Recommended p.clarity per biome. */
const WATER_CLARITY = [0.92, 0.70, 0.30, 0.62, 0.78];

function createWaterRenderer(canvas) {
  'use strict';

  // World-space period of every x-dependent water/bed pattern (all noise is tileable in x
  // with this period, so large camX / waterOffsetX are reduced in JS double precision).
  const PERIOD = 65536;
  const K_SHEAR = 0.38;       // streamline slope per unit cross-current
  const TIME_WRAP = 3600;     // visual clock wrap (keeps float32 time precise)
  const N_OBS = 96, N_TRAIL = 32, N_RIP = 16;
  const STRIPS = 32, BIN_W = 64;  // per-strip culling lists (must match the shader)

  const CTX_OPTS = {
    alpha: false, antialias: false, premultipliedAlpha: false,
    preserveDrawingBuffer: false, powerPreference: 'high-performance'
  };

  let gl = null;
  try { gl = canvas.getContext('webgl2', CTX_OPTS); } catch (err) { gl = null; }
  if (!gl) { console.warn('[water] WebGL2 is not available'); return null; }

  /* ------------------------------------------------------------------ */
  /* Shaders                                                             */
  /* ------------------------------------------------------------------ */
  const VS = `#version 300 es
void main() {
  vec2 p = vec2(float((gl_VertexID << 1) & 2), float(gl_VertexID & 2));
  gl_Position = vec4(p * 2.0 - 1.0, 0.0, 1.0);
}`;

  const FS = `#version 300 es
precision highp float;
precision highp int;
precision highp sampler2D;

uniform vec2  u_res;       // backing store px
uniform vec2  u_css;       // CSS px
uniform float u_time;      // wrapped visual clock
uniform float u_scale;     // CSS px per world unit
uniform float u_camMod;    // camX mod PERIOD (world-anchored patterns)
uniform float u_offMod;    // waterOffsetX mod PERIOD (advected patterns)
uniform float u_camY;
uniform float u_flow;
uniform float u_shear;
uniform vec3  u_deep, u_shallow, u_bedc, u_foam, u_sky, u_sun;   // linear rgb
uniform float u_night, u_lanternR, u_clarity, u_quality;
uniform vec2  u_boat;
uniform vec4  u_obs[96];
uniform vec4  u_trail[32];
uniform vec4  u_tarc[8];   // trail arc length per point (packed 4 per vec4)
uniform vec4  u_rip[16];   uniform int u_ripCount;
uniform sampler2D u_prof;  // 256x1 RGBA16F: top, bottom, cross, rapids
uniform sampler2D u_der;   // 256x1 R32F: streamline shift S (world units)
uniform sampler2D u_noise; // 256x256 RGBA8: value-noise lattice corners
uniform sampler2D u_rand;  // 256x256 RGBA8: independent random values
uniform highp usampler2D u_bins; // 64 x (2*STRIPS) R8UI: per-strip [count, indices...] obstacles, then trail segs

out vec4 o_col;

const float TAU = 6.28318530718;
const float PERIOD = 65536.0;
const int STRIPS = 32;

float sq(float x) { return x * x; }

// Value noise + analytic derivatives. One texel holds the 4 lattice corners.
// Lattice wraps every 256 cells, so a cell size of 256/m world units tiles PERIOD.
vec3 noiseD(vec2 x) {
  vec2 i = floor(x); vec2 f = x - i;
  vec4 c = texelFetch(u_noise, ivec2(i) & 255, 0);
  vec2 u  = f * f * f * (f * (f * 6.0 - 15.0) + 10.0);
  vec2 du = 30.0 * f * f * (f * (f - 2.0) + 1.0);
  float k1 = c.y - c.x, k2 = c.z - c.x, k3 = c.x - c.y - c.z + c.w;
  return vec3(c.x + k1 * u.x + k2 * u.y + k3 * u.x * u.y,
              du * vec2(k1 + k3 * u.y, k2 + k3 * u.x));
}
float noise(vec2 x) {
  vec2 i = floor(x); vec2 f = x - i;
  vec4 c = texelFetch(u_noise, ivec2(i) & 255, 0);
  vec2 u = f * f * (3.0 - 2.0 * f);
  return mix(mix(c.x, c.y, u.x), mix(c.z, c.w, u.x), u.y);
}

// Animated cellular noise. Returns (F1, F2-F1). Tileable (cells wrap at 256).
vec2 cellular(vec2 x, float t) {
  vec2 ip = floor(x); vec2 fp = x - ip;
  ivec2 ii = ivec2(ip);
  float f1 = 8.0, f2 = 8.0;
  for (int j = -1; j <= 1; j++) {
    for (int i = -1; i <= 1; i++) {
      vec4 h = texelFetch(u_rand, (ii + ivec2(i, j)) & 255, 0);
      vec2 o = 0.5 + 0.42 * sin(t * (0.55 + 0.7 * h.z) + TAU * h.xy);
      vec2 r = vec2(float(i), float(j)) + o - fp;
      float d = dot(r, r);
      if (d < f1) { f2 = f1; f1 = d; } else if (d < f2) { f2 = d; }
    }
  }
  f1 = sqrt(f1);
  return vec2(f1, sqrt(f2) - f1);
}
float cellEdge(vec2 x, float t) { return cellular(x, t).y; }

// Caustic web: rounded cells (F1 ridges) sharpened by the cell borders, domain-warped so the
// filaments curve, two drifting layers interfere. p: advected world coords; cells 256/m -> tiles PERIOD.
float causLayer(vec2 x, float t) {
  vec2 c = cellular(x, t);
  float ridge = smoothstep(0.22, 0.72, c.x);            // bright toward borders/junctions, round dark cells
  float line = exp(-c.y * 7.0);                           // soft glow at the borders
  return ridge * ridge * (0.35 + 0.65 * line);
}
float caustics(vec2 p, float t, bool hq) {
  vec2 w = vec2(noise(p / 32.0 + vec2(t * 0.11, 3.7)), noise(p / 32.0 + vec2(9.1, t * 0.09))) - 0.5;
  float c = causLayer(p / 16.0 + w * 1.6, t * 1.15);
  if (hq) {
    float c2 = causLayer(p / 21.333333 + vec2(5.3, 11.9) - w * 1.2, t * 0.85 + 2.0);
    c = c * 0.55 + c2 * 0.45 + c * c2 * 1.8;
  } else {
    c *= 1.2;
  }
  // focusing varies in soft patches
  return c * (0.4 + 1.2 * noise(p / 64.0 + vec2(t * 0.05, 0.0)));
}

// Riverbed: sand/gravel tint, sand ripples, scattered pebbles. World-anchored, tileable.
vec3 bedTex(vec2 b) {
  float n1 = noise(b / 32.0);
  float n2 = noise(b / 8.0 + vec2(7.3, 2.1));
  vec3 c = u_bedc * (0.70 + 0.45 * n1 + 0.22 * (n2 - 0.5));
  float rp = sin(b.x * (TAU * 2731.0 / PERIOD) + n1 * 6.0 + b.y * 0.05);
  c *= 0.93 + 0.07 * rp;
  vec2 pc = b / 12.8;
  vec2 pi = floor(pc); vec2 pf = pc - pi;
  vec4 h = texelFetch(u_rand, ivec2(pi) & 255, 0);
  vec2 ctr = 0.3 + 0.4 * h.xy;
  float rad = 0.14 + 0.2 * h.z;
  vec2 dv = (pf - ctr) * vec2(1.0, 1.25);
  float pd = length(dv);
  float has = step(0.3, h.w);
  float peb = (1.0 - smoothstep(rad - 0.08, rad, pd)) * has;
  float ao = (smoothstep(rad + 0.16, rad, pd) - peb) * has;
  float lit = 0.88 + 0.3 * clamp(-(dv.x + dv.y) / max(rad, 0.01), -1.0, 1.0);
  vec3 pcol = u_bedc * mix(0.55, 1.3, fract(h.w * 7.13)) * vec3(1.0, 0.97, 0.93);
  c *= 1.0 - 0.28 * ao;
  c = mix(c, pcol * lit, peb);
  return c;
}

float foamNoise(vec2 a, float t) {
  vec2 q = vec2(a.x / 25.6, a.y / 7.0);
  float n1 = noise(q + vec2(t * 0.23, t * 0.17));
  float n2 = noise(q * vec2(2.0, 2.15) + vec2(-t * 0.41, t * 0.31) + vec2(17.0, 3.3));
  float n3 = noise(q * vec2(4.0, 3.9) + vec2(t * 0.7, -t * 0.55) + vec2(41.0, 9.7));
  float lace = 1.0 - abs(2.0 * n2 - 1.0);
  return n1 * 0.5 + lace * 0.33 + n3 * 0.17;
}

float streamShift(float sx) {
  float fi = sx / u_css.x * 256.0 - 0.5;
  float fl = floor(fi);
  int i0 = clamp(int(fl), 0, 255);
  int i1 = clamp(int(fl) + 1, 0, 255);
  float a = texelFetch(u_der, ivec2(i0, 0), 0).x;
  float b = texelFetch(u_der, ivec2(i1, 0), 0).x;
  return mix(a, b, clamp(fi - fl, 0.0, 1.0));
}

vec3 toSRGB(vec3 c) {
  // soft highlight shoulder, then gamma
  vec3 k = max(c - 0.82, 0.0);
  c = c - k + 0.18 * (1.0 - exp(-k / 0.18));
  return pow(max(c, 0.0), vec3(1.0 / 2.2));
}

void main() {
  // ---- pixel in CSS px, y down
  vec2 px = vec2(gl_FragCoord.x, u_res.y - gl_FragCoord.y) * (u_css / u_res);
  float t = u_time;
  float inv = 1.0 / u_scale;
  bool hq = u_quality >= 0.5;
  float dith = (fract(52.9829189 * fract(dot(gl_FragCoord.xy, vec2(0.06711056, 0.00583715)))) - 0.5) / 255.0;

  // ---- river profile at this column
  vec4 prof = texture(u_prof, vec2(px.x / u_css.x, 0.5));
  float crossC = clamp(prof.z, -1.0, 1.0);
  float rapids = clamp(prof.w, 0.0, 1.0);
  float dTop = px.y - prof.x, dBot = prof.y - px.y;
  float e = min(dTop, dBot);                   // px into the water from the nearest bank
  float W = max(prof.y - prof.x, 1.0);

  float bx = u_camMod + px.x * inv;            // world-anchored x (periodic)
  float wy = u_camY + px.y * inv;

  // ---- lighting environment
  float nightK = clamp(u_night, 0.0, 1.0);
  vec3 ambient = mix(vec3(1.0), vec3(0.13, 0.17, 0.27), nightK);
  vec2 lb = px - u_boat;
  float lx = length(lb) / max(u_lanternR, 1.0);
  float latt = nightK * (sq(max(1.0 - lx * lx, 0.0)) + 0.3 * exp(-lx * 2.0));
  vec3 lanternC = vec3(1.0, 0.58, 0.24);
  vec3 light = ambient + lanternC * latt * 2.4;
  vec3 wetSand = u_bedc * 0.4;

  if (e < -8.0) {   // deep inside the bank (covered by the land layer anyway)
    o_col = vec4(toSRGB(wetSand * light) + dith, 1.0);
    return;
  }

  float ax = u_offMod + px.x * inv;            // advected x: water texture flows at flowSpeed
  float S = streamShift(px.x);
  float Y = wy - S;                            // streamline-aligned y (cross-current bends flow)
  float shear = u_shear * crossC;
  vec2 flowDir = normalize(vec2(1.0, shear));
  vec2 latDir = vec2(-flowDir.y, flowDir.x);
  float flowK = clamp(u_flow / 170.0, 0.5, 1.8);

  // ---- feature accumulation (px units)
  float foamAmt = 0.0;   // requested foam coverage
  float rough = 0.0;     // extra small-scale roughness
  vec2  gF = vec2(0.0);  // height slope from features
  float shade = 0.0;     // wet shadow
  float shoal = 0.0;     // local shallowing near obstacles
  float iceGlow = 0.0;

  // obstacles & trail segments are binned per vertical screen strip in JS -> only nearby ones are visited
  int strip = clamp(int(px.x / u_css.x * float(STRIPS)), 0, STRIPS - 1);
  int obsN = int(texelFetch(u_bins, ivec2(0, strip), 0).r);
  for (int k = 0; k < 63; k++) {
    if (k >= obsN) break;
    int i = int(texelFetch(u_bins, ivec2(k + 1, strip), 0).r);
    vec4 o = u_obs[i];
    float r = max(o.z, 1.0);
    vec2 d = px - o.xy;
    float dl = d.y - d.x * shear;
    if (d.x < -2.6 * r - 18.0 || d.x > 7.0 * r + 52.0 || abs(dl) > 2.3 * r + 18.0 + max(d.x, 0.0) * 0.65) continue;
    float len = length(d);
    float dd = len - r;
    vec2 rad = d / max(len, 1e-3);
    int kind = int(o.w + 0.5);

    if (kind == 4) {   // lily pad: gentle pulsing ripple rings + soft shadow, no foam
      float seed = fract((u_camMod + o.x * inv) * (898.0 / PERIOD));   // k/PERIOD: no pop when camMod wraps
      for (int m = 0; m < 2; m++) {
        float ph = fract(t * 0.26 + float(m) * 0.5 + seed);
        float rr = r * 1.04 + ph * r * 1.7;
        float w = 2.2 + ph * 3.5;
        float x = len - rr;
        float env = exp(-x * x / (w * w)) * sq(1.0 - ph) * smoothstep(0.0, 0.12, ph);
        gF += rad * env * (-2.0 * x / (w * w)) * 2.4;
      }
      shade = max(shade, (1.0 - smoothstep(r * 0.7, r * 1.35, length(d - vec2(3.0, 4.0)))) * 0.38);
      continue;
    }

    float kf = kind == 1 ? 0.72 : (kind == 3 ? 1.25 : 1.0);
    float along = dot(d, flowDir);
    float lat = dot(d, latDir);
    float cosUp = clamp(-along / max(len, 1e-3), 0.0, 1.0);

    // foam collar hugging the obstacle (thicker on the upstream face)
    float cw = 3.0 + r * (0.18 + 0.32 * cosUp);
    float collar = (1.0 - smoothstep(0.0, cw, dd)) * smoothstep(-6.0, -1.0, dd);
    // wet shadow ring + directional cast shadow + shallow halo
    float win = 1.0 - smoothstep(r * 0.5 + 6.0, r * 1.25 + 14.0, dd);   // fades to 0 before the cull radius
    shade = max(shade, exp(-max(dd, 0.0) / (r * 0.26 + 4.0)) * 0.55 * win);
    shade = max(shade, (1.0 - smoothstep(r * 0.75, r * 1.3, length(d - vec2(0.22, 0.3) * r))) * 0.42);
    shoal = max(shoal, exp(-max(dd, 0.0) / (r * 0.9 + 6.0)) * win);
    if (kind == 2) iceGlow = max(iceGlow, exp(-max(dd, 0.0) / (r * 0.8 + 8.0)) * win);

    float fa = collar * (0.6 + 0.2 * cosUp);
    float rg = collar * 1.4;

    // downstream wake: turbulent core + diverging V of standing-wave foam
    if (along > -r * 0.3) {
      float a = max(along, 0.0);
      float L = (r * 4.5 + 30.0) * kf;
      float fade = pow(1.0 - smoothstep(0.0, L, a), 0.8);
      float hw = r * 0.8 + a * 0.24;
      // vortex shedding: the turbulent core snakes from side to side, travelling with the current
      float lam = max(r * 5.0, 60.0);
      float seedO = fract((u_camMod + o.x * inv) * (1134.0 / PERIOD) + o.y * 0.011) * TAU;
      // phase reduced with fract() first: sin() of args ~1e4..1e5 rad is imprecise on some mobile GPUs
      float wig = sin(TAU * fract((a - t * u_flow * u_scale * 0.8) / lam) + seedO) * hw * 0.32 * smoothstep(0.0, r * 2.0, a);
      float core = (1.0 - smoothstep(hw * 0.2, hw, abs(lat + wig))) * fade * fade * smoothstep(-r * 0.3, r * 0.5, along);
      float armPos = r * 0.95 + a * 0.46;
      float armW = 1.8 + a * 0.065 + r * 0.05;
      float ad = abs(lat) - armPos;
      float arm = exp(-ad * ad / (armW * armW)) * (1.0 - smoothstep(0.0, L * 1.2, a)) * smoothstep(-r * 0.2, r * 0.6, along);
      fa = max(fa, max(core * 0.8 * kf, arm * 0.55));
      rg += core * 2.4 + arm * 1.6;
      gF += latDir * sign(lat) * arm * (-2.0 * ad / (armW * armW)) * (1.4 + r * 0.06);
    }
    // pressure pillow upstream: smooth dome where water piles against the obstacle
    vec2 pq = vec2(along + r * 0.85, lat * 0.8);
    float ps = r * 0.7 + 5.0;
    float pil = exp(-dot(pq, pq) / (ps * ps));
    gF += (flowDir * pq.x + latDir * pq.y * 0.8) * (-2.0 / (ps * ps)) * pil * (r * 0.5 + 3.0);
    rg += pil * 0.7;

    foamAmt = max(foamAmt, fa);
    rough = max(rough, rg);
  }

  // ---- boat wake (polyline, newest first)
  float wake = 0.0, armBest = 0.0;
  vec2 armG = vec2(0.0);
  int segN = int(texelFetch(u_bins, ivec2(0, strip + STRIPS), 0).r);
  for (int k = 0; k < 31; k++) {
    if (k >= segN) break;
    int i = int(texelFetch(u_bins, ivec2(k + 1, strip + STRIPS), 0).r);
    vec4 A = u_trail[i]; vec4 B = u_trail[i + 1];
    float arcLen = u_tarc[i >> 2][i & 3];      // arc length from the boat to point i (px)
    vec2 ab = B.xy - A.xy;
    float segL = length(ab);
    float reach = 44.0 + 0.38 * (arcLen + segL);
    if (length(px - (A.xy + B.xy) * 0.5) > reach + segL * 0.5) continue;
    float tt = clamp(dot(px - A.xy, ab) / max(dot(ab, ab), 1e-4), 0.0, 1.0);
    vec2 dv = px - (A.xy + ab * tt);
    float dist = length(dv);
    float age = clamp(mix(A.z, B.z, tt), 0.0, 1.0);
    float str = clamp(mix(A.w, B.w, tt), 0.0, 1.0);
    float life = pow(1.0 - age, 1.1) * str;
    float wdt = 6.0 + 24.0 * age;
    float band = 1.0 - smoothstep(wdt * 0.35, wdt, dist);
    float edge = exp(-sq((dist - wdt * 0.82) / (1.6 + 2.6 * age)));
    wake = max(wake, band * life * (0.5 + 0.5 * (1.0 - age)) + edge * life * 0.35);
    rough = max(rough, (band + edge * 0.6) * life * 2.6);
    float s = arcLen + segL * tt;
    float armOff = 8.0 + 0.36 * s;
    float armW = 1.7 + 0.045 * s;
    float arm = exp(-sq((dist - armOff) / armW)) * life * (1.0 - smoothstep(0.55, 1.0, age)) * (1.0 - smoothstep(70.0, 190.0, s));
    if (arm > armBest) {
      armBest = arm;
      armG = (dv / max(dist, 1e-3)) * arm * (-2.0 * (dist - armOff) / (armW * armW));
    }
  }
  foamAmt = max(foamAmt, max(wake * 0.95, armBest * 0.3));
  gF += armG * 0.9;

  // ---- ripples (paddle strokes, splashes, impacts)
  for (int i = 0; i < 16; i++) {
    if (i >= u_ripCount) break;
    vec4 R = u_rip[i];
    float age = clamp(R.z, 0.0, 1.0), st = clamp(R.w, 0.0, 1.5);
    float rr = 2.0 + 80.0 * st * (1.0 - sq(1.0 - age));
    float w = 3.0 + 9.0 * age;
    vec2 dv = px - R.xy;
    float dist = length(dv);
    float x = dist - rr;
    if (abs(x) > 3.0 * w + 4.0) continue;
    float fade = sq(1.0 - age) * st;
    float env = exp(-x * x / (w * w));
    float k = TAU / (4.0 + 7.0 * age);
    float dh = env * (k * cos(x * k) - 2.0 * x / (w * w) * sin(x * k));
    gF += (dv / max(dist, 1e-3)) * dh * fade * 4.5;
    foamAmt = max(foamAmt, env * fade * (1.0 - smoothstep(0.0, 0.4, age)) * 0.75);
    rough = max(rough, env * fade * 1.6);
  }

  // ---- rapids: standing waves anchored to the bed + whitewater
  if (rapids > 0.01) {
    float fr = TAU * 1365.0 / PERIOD;                     // ~48 world-unit wavelength
    float yc = (px.y - 0.5 * (prof.x + prof.y)) / (0.5 * W);   // -1..1 across the river
    float sph = bx * fr + (noise(vec2(bx / 32.0, wy / 21.0)) - 0.5) * 4.0 + yc * yc * 2.2;  // smile-shaped crests
    float sw = sin(sph);
    gF.x += rapids * cos(sph) * fr * inv * 7.0;
    foamAmt = max(foamAmt, rapids * (0.1 + 0.42 * smoothstep(0.6, 1.0, sw)));
    rough = max(rough, rapids * 2.4);
  }

  // ---- shoreline: lapping foam line + a fainter receding line
  float lapPh = t * 1.15 + bx * (TAU * 173.0 / PERIOD) + noise(vec2(bx / 32.0, wy / 40.0)) * 4.0;
  float lap = 3.0 + 2.6 * sin(lapPh);
  float shoreN = noise(vec2(bx / 12.8 + t * 0.15, wy / 6.0));
  float shoreF = 1.0 - smoothstep(lap - 1.5, lap + 4.5, e);
  float lap2 = lap + 9.0 + 3.0 * sin(lapPh * 0.7 - 1.9);
  float line2 = exp(-sq((e - lap2) / 2.2)) * 0.38 * smoothstep(0.3, 0.7, shoreN);
  foamAmt = max(foamAmt, max(shoreF * (0.45 + 0.4 * shoreN), line2));
  rough = max(rough, shoreF * 1.2);

  // ---- flowing surface normal: anisotropic fbm (stretched along the flow) + domain warp
  vec2 q = vec2(ax / 128.0, Y / 34.0);
  float wn = noise(vec2(q.x * 0.5 + t * 0.013, q.y * 0.37 - t * 0.021) + vec2(5.2, 1.3));
  q.y += (wn - 0.5) * 1.6;
  vec2 Gl = vec2(0.0), Gh = vec2(0.0);
  int oct = hq ? 4 : 3;
  vec2 fr2 = vec2(1.0); float amp = 1.0;
  for (int k = 0; k < 4; k++) {
    if (k >= oct) break;
    float fk = float(k);
    vec2 dr = t * flowK * vec2(0.035 * sin(fk * 2.1 + 0.5), 0.06 * cos(fk * 1.7 + 0.3)) * (1.0 + fk * 0.7);
    vec3 n = noiseD(q * fr2 + dr + vec2(fk * 37.0, fk * 17.3));
    vec2 g = n.yz * fr2 * amp;
    if (k < 2) Gl += g; else Gh += g;
    fr2 *= vec2(2.0, 1.72); amp *= 0.55;
  }
  vec2 Gq = Gl * (1.0 + 0.25 * abs(crossC)) + Gh * (0.8 + rough * 1.1);
  vec2 gN = vec2(Gq.x / 128.0 - Gq.y * shear / 34.0, Gq.y / 34.0) * inv;

  // visible flow lines (thin, long, along the streamlines) — stronger with |cross|
  float sl = noise(vec2(ax / 42.666667 + t * 0.04, Y / 3.3));
  float slm = noise(vec2(ax / 128.0 - t * 0.02, Y / 22.0 + 4.0));
  float sl2 = noise(vec2(ax / 64.0 - t * 0.03, Y / 6.5 + 7.7));
  float streakVis = 0.18 + 0.82 * abs(crossC) + rapids * 0.3;
  float streak = smoothstep(0.6, 0.84, sl) * smoothstep(0.35, 0.7, slm) * streakVis * smoothstep(4.0, 26.0, e);
  float darkLine = smoothstep(0.35, 0.1, sl2) * streakVis * 0.6;
  // floating foam flecks carried by the current (they visibly drift sideways in cross-currents)
  float fl = noise(vec2(ax / 10.666667 + t * 0.03, Y / 3.2 + 3.1));
  float flm = noise(vec2(ax / 85.333333, Y / 30.0 + 1.7));       // clusters of flecks
  float fleck = smoothstep(0.87, 0.96, fl) * smoothstep(0.55, 0.85, flm) * (0.2 + 0.8 * abs(crossC)) * smoothstep(8.0, 30.0, e);

  vec2 slope = gN * 7.0 + gF;
  slope.y += (streak - darkLine * 0.5) * 0.05;
  vec3 N = normalize(vec3(-slope, 1.0));

  // ---- foam mask (shared animated noise, thresholded by requested amount)
  float fN = foamNoise(vec2(ax, Y), t * flowK);
  float fAmt = clamp(foamAmt, 0.0, 1.0);
  float foamA = 0.0;
  float foamTex = 1.0;     // brightness variation inside foam (thick = bright, thin = greyer)
  float foamRim = 0.0;     // slight darkening of the water right around foam patches
  if (fAmt > 0.02) {
    // soft blobs where foam is dense ...
    float thr = mix(0.97, 0.25, fAmt);
    float blob = smoothstep(thr - 0.1, thr + 0.05, fN);
    foamTex = 0.8 + 0.28 * smoothstep(thr, thr + 0.28, fN);
    foamRim = smoothstep(thr - 0.24, thr - 0.1, fN) * (1.0 - blob) * smoothstep(0.05, 0.3, fAmt);
    // ... and a bubbly cellular lace network whose filaments thicken with the amount
    float lace = 0.0;
    if (hq && fAmt > 0.22) {
      float ce = cellEdge(vec2(ax / 8.0, Y / 5.2) + (fN - 0.5) * 0.9, t * 1.7 * flowK);
      float lw = 0.04 + 0.3 * fAmt * fAmt;
      lace = (1.0 - smoothstep(lw, lw + 0.12, ce)) * smoothstep(0.22, 0.55, fAmt) * smoothstep(0.3, 0.6, fN);
    }
    foamA = max(blob, lace * (0.4 + 0.4 * fN)) * (0.6 + 0.4 * fAmt);
    foamA = max(foamA, fAmt * (0.1 + 0.18 * fN));     // milky aerated water under the lace
  }
  foamA = max(foamA, max(fleck * 0.45, streak * 0.07));

  // ---- water body: depth, riverbed seen through refraction, caustics
  float ep = max(e, 0.0);
  float shelf = 1.0 - exp(-ep / 16.0);
  float bowl = smoothstep(0.0, 0.5 * W, ep);
  float depth = clamp(0.5 * shelf + 0.5 * bowl, 0.0, 1.0) * (1.0 - 0.55 * shoal);
  vec2 refr = -slope * (4.0 + 26.0 * depth) * inv;
  vec3 bed = bedTex(vec2(bx, wy) + refr);
  float clar = clamp(u_clarity, 0.0, 1.0);
  float od = depth * mix(3.4, 1.45, clar) + (1.0 - clar) * 1.1;
  float bedVis = exp(-od * 1.45);
  float causVis = clar * bedVis * (1.0 - 0.5 * foamA);
  float caus = causVis > 0.015 ? caustics(vec2(ax, Y) + refr * 1.6, t, hq) * (1.0 - 0.6 * depth) : 0.0;
  vec3 scatter = mix(u_shallow, u_deep, smoothstep(0.0, 0.9, depth));
  vec3 filt = mix(vec3(1.0), u_shallow / max(max(u_shallow.r, max(u_shallow.g, u_shallow.b)), 1e-3), 0.55);
  vec3 bedLit = bed * filt * (0.8 + caus * (0.25 + 0.9 * clar));
  vec3 body = mix(scatter, bedLit, bedVis);
  body *= 0.92 + 0.16 * wn;                                    // painterly large-scale variation
  float sss = clamp(-slope.y * 3.0 + slope.x * 0.8, 0.0, 1.0); // light through wave faces toward the viewer
  body += u_shallow * sss * 0.16 * (1.0 - 0.6 * bedVis);
  body *= 1.0 + streak * 0.1 - darkLine * 0.04;
  body += u_shallow * caus * clar * 0.06 * (1.0 - bedVis);     // faint light shafts in deeper water
  body = mix(body, body * vec3(0.38, 0.44, 0.48), shade);
  body += vec3(0.20, 0.55, 0.60) * iceGlow * 0.22;
  body *= 1.0 - (1.0 - smoothstep(0.0, 28.0, dTop)) * 0.2 - (1.0 - smoothstep(0.0, 10.0, dBot)) * 0.06;

  // ---- surface: fresnel sky reflection (incl. far-bank reflection), sun/moon glitter
  vec3 Vf = normalize(vec3((px.x / u_css.x - 0.5) * -0.25, 0.42, 1.0));
  float ndv = clamp(dot(N, Vf), 0.0, 1.0);
  float F = 0.02 + 0.98 * pow(1.0 - ndv, 5.0);
  F = clamp(F * 1.6 + 0.03, 0.0, 0.85);
  vec3 R = reflect(-Vf, N);
  vec3 skyCol = mix(u_sky * 1.15 + u_sun * 0.06, u_sky * 0.72, clamp(R.z, 0.0, 1.0)) * mix(1.0, 0.32, nightK);
  float reach = max(dTop, 0.0) * R.z / max(-R.y, 0.06);
  float bankRef = smoothstep(70.0, 22.0, reach);
  vec3 bankCol = mix(u_bedc * 0.32, u_deep * 0.55, 0.5) * mix(1.0, 0.5, nightK);
  skyCol = mix(skyCol, bankCol, bankRef);

  // glitter: per-pixel view vector from a virtual eye south of the screen, so glints form a
  // path toward the sun/moon instead of a uniform sprinkle
  vec3 eye = vec3(u_css.x * 0.62, u_css.y * 1.55, u_css.y * mix(1.35, 0.75, nightK));
  vec3 Vg = normalize(eye - vec3(px, 0.0));
  vec3 Ls = normalize(vec3(-0.3, -1.0, 0.78));
  vec3 Lm = normalize(vec3(0.0, -1.0, 0.3));
  vec3 L = normalize(mix(Ls, Lm, nightK));
  vec3 Hh = normalize(L + Vg);
  // capillary micro-waves only for glints -> fine twinkling sparkles instead of broad patches
  vec3 Ns = N;
  if (hq) {
    vec3 cap = noiseD(vec2(ax / 10.666667 + t * 0.55, Y / 5.5 - t * 0.45) + vec2(13.0, 7.0));
    Ns = normalize(vec3(-(slope + cap.yz * vec2(0.05, 0.09) * (1.0 + rough * 0.3)), 1.0));
  }
  float ndh = clamp(dot(Ns, Hh), 0.0, 1.0);
  float sr = pow(ndh, mix(500.0, 650.0, nightK));
  float spec = (smoothstep(0.3, 0.85, sr) * 1.6 + sr * 0.4) * mix(1.6, 6.0, nightK);
  // by day, gather the glints into a sun path instead of an even sprinkle over the whole river
  spec *= mix(mix(0.3, 1.0, pow(clamp(Hh.z, 0.0, 1.0), 40.0)), 1.0, nightK);
  float sheen = pow(clamp(dot(N, Hh), 0.0, 1.0), mix(60.0, 110.0, nightK)) * mix(0.035, 0.2, nightK);
  float glitMask = 1.0 - smoothstep(0.0, 4.0, -e);
  vec3 lightC = mix(u_sun, vec3(0.62, 0.74, 1.0), nightK * 0.55);   // moonlight is always cool
  vec3 specC = lightC * (spec + sheen) * glitMask * (1.0 - foamA) * (1.0 - bankRef * 0.8);

  vec3 col = body * light;
  col = mix(col, skyCol, F * (1.0 - foamA));
  col += specC;

  // lantern glints on the water
  if (latt > 0.002) {
    vec3 Ll = normalize(vec3(u_boat - px, 60.0));
    vec3 Hl = normalize(Ll + vec3(0.0, 0.0, 1.0));
    col += lanternC * pow(clamp(dot(N, Hl), 0.0, 1.0), 90.0) * latt * 2.4 * (1.0 - foamA);
  }

  // ---- foam on top (lit, with a hint of volume from the normal)
  float fshade = 0.86 + 0.5 * clamp(dot(N.xy, vec2(0.35, 0.9)), -0.5, 0.5);
  vec3 foamCol = mix(u_foam * mix(vec3(1.0), filt, 0.35), u_foam, smoothstep(0.2, 0.8, fAmt)) * fshade * foamTex;
  col *= 1.0 - foamRim * 0.18;
  col = mix(col, foamCol * light, foamA);

  // ---- wet sand just past the waterline (mostly hidden under the bank layer)
  float landK = smoothstep(0.0, -3.0, e);
  col = mix(col, wetSand * light + u_sky * 0.04 * (1.0 - nightK), landK);

  o_col = vec4(toSRGB(col) + dith, 1.0);
}`;

  /* ------------------------------------------------------------------ */
  /* Static data: noise lattice (corner-packed) + random texture         */
  /* ------------------------------------------------------------------ */
  function makeNoiseData() {
    let s = 0x2F6B4A1D | 0;
    const rnd = () => { s ^= s << 13; s ^= s >>> 17; s ^= s << 5; return (s >>> 0) / 4294967296; };
    const N = 256;
    const base = new Uint8Array(N * N);
    for (let i = 0; i < N * N; i++) base[i] = (rnd() * 256) | 0;
    const corner = new Uint8Array(N * N * 4);
    for (let y = 0; y < N; y++) {
      const y1 = (y + 1) & 255;
      for (let x = 0; x < N; x++) {
        const x1 = (x + 1) & 255, o = (y * N + x) * 4;
        corner[o] = base[y * N + x];
        corner[o + 1] = base[y * N + x1];
        corner[o + 2] = base[y1 * N + x];
        corner[o + 3] = base[y1 * N + x1];
      }
    }
    const rand = new Uint8Array(N * N * 4);
    for (let i = 0; i < rand.length; i++) rand[i] = (rnd() * 256) | 0;
    return { corner, rand };
  }
  const NOISE = makeNoiseData();

  /* ------------------------------------------------------------------ */
  /* GL resources                                                        */
  /* ------------------------------------------------------------------ */
  const UNIFORMS = ['u_res', 'u_css', 'u_time', 'u_scale', 'u_camMod', 'u_offMod', 'u_camY', 'u_flow', 'u_shear',
    'u_deep', 'u_shallow', 'u_bedc', 'u_foam', 'u_sky', 'u_sun', 'u_night', 'u_lanternR', 'u_clarity', 'u_quality',
    'u_boat', 'u_obs', 'u_trail', 'u_tarc', 'u_rip', 'u_ripCount',
    'u_prof', 'u_der', 'u_noise', 'u_rand', 'u_bins'];

  function compile(type, src) {
    const sh = gl.createShader(type);
    gl.shaderSource(sh, src);
    gl.compileShader(sh);
    if (!gl.getShaderParameter(sh, gl.COMPILE_STATUS) && !gl.isContextLost()) {
      console.warn('[water] shader compile failed:\n' + gl.getShaderInfoLog(sh));
      gl.deleteShader(sh);
      return null;
    }
    return sh;
  }

  function makeTex(internal, w, h, format, type, data, filter) {
    const tx = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_2D, tx);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, filter);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, filter);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    gl.texImage2D(gl.TEXTURE_2D, 0, internal, w, h, 0, format, type, data);
    return tx;
  }

  function build() {
    const vs = compile(gl.VERTEX_SHADER, VS);
    const fs = compile(gl.FRAGMENT_SHADER, FS);
    if (!vs || !fs) {
      if (vs) gl.deleteShader(vs);
      if (fs) gl.deleteShader(fs);
      return null;
    }
    const prog = gl.createProgram();
    gl.attachShader(prog, vs);
    gl.attachShader(prog, fs);
    gl.linkProgram(prog);
    gl.deleteShader(vs);
    gl.deleteShader(fs);
    if (!gl.getProgramParameter(prog, gl.LINK_STATUS) && !gl.isContextLost()) {
      console.warn('[water] program link failed:\n' + gl.getProgramInfoLog(prog));
      gl.deleteProgram(prog);
      return null;
    }
    const loc = {};
    for (const n of UNIFORMS) loc[n] = gl.getUniformLocation(prog, n);
    const vao = gl.createVertexArray();

    gl.pixelStorei(gl.UNPACK_ALIGNMENT, 1);
    const texProf = makeTex(gl.RGBA16F, 256, 1, gl.RGBA, gl.FLOAT, new Float32Array(1024), gl.LINEAR);
    const texDer = makeTex(gl.R32F, 256, 1, gl.RED, gl.FLOAT, new Float32Array(256), gl.NEAREST);
    const texNoise = makeTex(gl.RGBA8, 256, 256, gl.RGBA, gl.UNSIGNED_BYTE, NOISE.corner, gl.NEAREST);
    const texRand = makeTex(gl.RGBA8, 256, 256, gl.RGBA, gl.UNSIGNED_BYTE, NOISE.rand, gl.NEAREST);
    const texBins = makeTex(gl.R8UI, BIN_W, STRIPS * 2, gl.RED_INTEGER, gl.UNSIGNED_BYTE, new Uint8Array(BIN_W * STRIPS * 2), gl.NEAREST);

    gl.useProgram(prog);
    gl.uniform1i(loc.u_prof, 0);
    gl.uniform1i(loc.u_der, 1);
    gl.uniform1i(loc.u_noise, 2);
    gl.uniform1i(loc.u_rand, 3);
    gl.uniform1i(loc.u_bins, 4);
    gl.disable(gl.DEPTH_TEST);
    gl.disable(gl.BLEND);
    return { prog, loc, vao, texProf, texDer, texNoise, texRand, texBins };
  }

  let R = build();
  if (!R) return null;

  /* ------------------------------------------------------------------ */
  /* Per-frame scratch                                                   */
  /* ------------------------------------------------------------------ */
  let cssW = Math.max(1, canvas.clientWidth || canvas.width || 1);
  let cssH = Math.max(1, canvas.clientHeight || canvas.height || 1);
  const profBuf = new Float32Array(1024);
  const shift = new Float32Array(256);
  const shiftPrev = new Float64Array(256);
  let shiftValid = false, shiftX0 = 0, shiftDx = 1;
  const obsBuf = new Float32Array(N_OBS * 4);
  const trailBuf = new Float32Array(N_TRAIL * 4);
  const ripBuf = new Float32Array(N_RIP * 4);
  const arcBuf = new Float32Array(N_TRAIL);
  const binBuf = new Uint8Array(BIN_W * STRIPS * 2);
  const lin = new Float32Array(18);

  function binAdd(row, idx) {
    const o = row * BIN_W, c = binBuf[o];
    if (c < BIN_W - 1) { binBuf[o + 1 + c] = idx; binBuf[o] = c + 1; }
  }
  function binRange(x0, x1, rowBase, idx) {
    const sw = cssW / STRIPS;
    const s0 = Math.max(0, Math.floor(x0 / sw)), s1 = Math.min(STRIPS - 1, Math.floor(x1 / sw));
    for (let s = s0; s <= s1; s++) binAdd(rowBase + s, idx);
  }
  // Conservative x-extents of every feature's influence (mirrors the shader's early-outs).
  function buildBins(no, nt) {
    binBuf.fill(0);
    for (let i = 0; i < no; i++) {
      const x = obsBuf[i * 4], r = Math.max(obsBuf[i * 4 + 2], 1);
      binRange(x - 2.6 * r - 20, x + 7.0 * r + 54, 0, i);
    }
    let arc = 0;
    arcBuf.fill(0);
    for (let i = 0; i < nt; i++) {
      arcBuf[i] = arc;
      if (i + 1 >= nt) break;
      const ax = trailBuf[i * 4], ay = trailBuf[i * 4 + 1], bx = trailBuf[i * 4 + 4], by = trailBuf[i * 4 + 5];
      const segL = Math.hypot(bx - ax, by - ay);
      const reach = 44 + 0.38 * (arc + segL) + segL * 0.5 + 2;
      const mx = (ax + bx) * 0.5;
      binRange(mx - reach, mx + reach, STRIPS, i);
      arc += segL;
    }
  }

  const mod = (a, m) => { const r = a % m; return r < 0 ? r + m : r; };
  // finite-number guard: a NaN/Infinity from the caller must never reach a uniform (it would blank the water)
  const num = (v, d) => { if (v == null) return d; v = +v; return Number.isFinite(v) ? v : d; };

  // Streamline shift S(x) = ∫ K·cross dx, integrated in WORLD space and anchored to the previous
  // frame (so patterns don't slide when cross-current zones scroll off the left edge).
  function updateShift(prof, camX, scale) {
    const dx = cssW / 256 / scale;
    const x0 = camX + 0.5 * dx;
    let s0 = 0;
    if (shiftValid) {
      const fi = (x0 - shiftX0) / shiftDx;
      if (fi >= 0 && fi <= 255) {
        const i = Math.floor(fi), f = fi - i, j = Math.min(i + 1, 255);
        s0 = shiftPrev[i] + (shiftPrev[j] - shiftPrev[i]) * f;
      } else if (fi < 0 && fi > -256) {
        s0 = shiftPrev[0] + K_SHEAR * (prof[2] || 0) * (x0 - shiftX0);
      } else if (fi > 255 && fi < 512) {
        s0 = shiftPrev[255] + K_SHEAR * (prof[2] || 0) * (x0 - (shiftX0 + 255 * shiftDx));
      }
      if (!Number.isFinite(s0)) s0 = 0;
    }
    // integrate in double precision (shiftPrev is Float64) so the frame-to-frame anchor never
    // random-walks; only the uploaded copy is rounded to float32
    shiftPrev[0] = s0;
    let cPrev = prof[2] || 0;
    for (let i = 1; i < 256; i++) {
      const c = prof[i * 4 + 2] || 0;
      shiftPrev[i] = shiftPrev[i - 1] + K_SHEAR * 0.5 * (cPrev + c) * dx;
      cPrev = c;
    }
    shift.set(shiftPrev);
    shiftX0 = x0; shiftDx = dx; shiftValid = true;
  }

  function linColor(dst, o, c, fallback) {
    const a = c || fallback;
    for (let k = 0; k < 3; k++) dst[o + k] = Math.pow(Math.min(Math.max(+a[k] || 0, 0), 1.5), 2.2);
  }

  function copyVec4(dst, src, count) {
    dst.fill(0);
    if (!src || count <= 0) return 0;
    const n = Math.min(count, dst.length / 4, Math.floor(src.length / 4));
    for (let i = 0; i < n * 4; i++) { const v = +src[i]; dst[i] = Number.isFinite(v) ? v : 0; }
    return n;
  }

  /* ------------------------------------------------------------------ */
  /* API                                                                 */
  /* ------------------------------------------------------------------ */
  const api = {
    lost: false,

    resize(w, h, pixelRatio) {
      cssW = Math.max(1, +w || 1);
      cssH = Math.max(1, +h || 1);
      const pr = Math.max(0.1, +pixelRatio || 1);
      canvas.width = Math.max(1, Math.round(cssW * pr));
      canvas.height = Math.max(1, Math.round(cssH * pr));
    },

    render(p) {
      if (!p || api.lost || !R || gl.isContextLost()) return;
      const L = R.loc;
      const scale = Math.max(1e-3, num(p.scale, 1) || 1);
      const camX = num(p.camX, 0);
      const time = num(p.time, 0);

      // profile -> RGBA16F texture (sanitised copy: NaN-free and inside half-float range),
      // plus derived stream-shift texture
      const src = p.profile;
      const pn = src ? Math.min(1024, src.length | 0) : 0;
      for (let i = 0; i < pn; i++) {
        const v = +src[i];
        profBuf[i] = Number.isFinite(v) ? Math.min(Math.max(v, -60000), 60000) : 0;
      }
      const prof = profBuf;
      updateShift(prof, camX, scale);

      gl.useProgram(R.prog);
      gl.bindVertexArray(R.vao);
      // the browser may allocate a smaller drawing buffer than canvas.width/height (huge canvases, iOS
      // memory limits): always render into what was actually allocated
      const bw = gl.drawingBufferWidth || canvas.width, bh = gl.drawingBufferHeight || canvas.height;
      gl.viewport(0, 0, bw, bh);

      gl.pixelStorei(gl.UNPACK_ALIGNMENT, 1);
      gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, R.texProf);
      gl.texSubImage2D(gl.TEXTURE_2D, 0, 0, 0, 256, 1, gl.RGBA, gl.FLOAT, prof, 0);
      gl.activeTexture(gl.TEXTURE1); gl.bindTexture(gl.TEXTURE_2D, R.texDer);
      gl.texSubImage2D(gl.TEXTURE_2D, 0, 0, 0, 256, 1, gl.RED, gl.FLOAT, shift, 0);
      gl.activeTexture(gl.TEXTURE2); gl.bindTexture(gl.TEXTURE_2D, R.texNoise);
      gl.activeTexture(gl.TEXTURE3); gl.bindTexture(gl.TEXTURE_2D, R.texRand);

      gl.uniform2f(L.u_res, bw, bh);
      gl.uniform2f(L.u_css, cssW, cssH);
      gl.uniform1f(L.u_time, mod(time, TIME_WRAP));
      gl.uniform1f(L.u_scale, scale);
      gl.uniform1f(L.u_camMod, mod(camX, PERIOD));
      const flow = num(p.flowSpeed, 170);
      const off = num(p.waterOffsetX, camX - flow * time);
      gl.uniform1f(L.u_offMod, mod(off, PERIOD));
      gl.uniform1f(L.u_camY, num(p.camY, 0));
      gl.uniform1f(L.u_flow, flow);
      gl.uniform1f(L.u_shear, K_SHEAR);

      const pal = p.palette || WATER_PALETTES[0];
      const d0 = WATER_PALETTES[0];
      linColor(lin, 0, pal.deep, d0.deep);
      linColor(lin, 3, pal.shallow, d0.shallow);
      linColor(lin, 6, pal.bed, d0.bed);
      linColor(lin, 9, pal.foam, d0.foam);
      linColor(lin, 12, pal.sky, d0.sky);
      linColor(lin, 15, pal.sun, d0.sun);
      gl.uniform3f(L.u_deep, lin[0], lin[1], lin[2]);
      gl.uniform3f(L.u_shallow, lin[3], lin[4], lin[5]);
      gl.uniform3f(L.u_bedc, lin[6], lin[7], lin[8]);
      gl.uniform3f(L.u_foam, lin[9], lin[10], lin[11]);
      gl.uniform3f(L.u_sky, lin[12], lin[13], lin[14]);
      gl.uniform3f(L.u_sun, lin[15], lin[16], lin[17]);

      gl.uniform1f(L.u_night, Math.min(Math.max(num(p.night, 0), 0), 1));
      gl.uniform1f(L.u_lanternR, Math.max(1, num(p.lanternRadius, 150)));
      gl.uniform1f(L.u_clarity, Math.min(Math.max(num(p.clarity, 0.8), 0), 1));
      gl.uniform1f(L.u_quality, num(p.quality, 1));
      const boat = p.boat;
      gl.uniform2f(L.u_boat, boat ? num(boat[0], cssW * 0.3) : cssW * 0.3, boat ? num(boat[1], cssH * 0.5) : cssH * 0.5);

      const no = copyVec4(obsBuf, p.obstacles, p.obstacleCount | 0);
      const nt = copyVec4(trailBuf, p.trail, p.trailCount | 0);
      const nr = copyVec4(ripBuf, p.ripples, p.rippleCount | 0);
      buildBins(no, nt);
      gl.activeTexture(gl.TEXTURE4); gl.bindTexture(gl.TEXTURE_2D, R.texBins);
      gl.texSubImage2D(gl.TEXTURE_2D, 0, 0, 0, BIN_W, STRIPS * 2, gl.RED_INTEGER, gl.UNSIGNED_BYTE, binBuf, 0);
      gl.uniform4fv(L.u_obs, obsBuf);
      gl.uniform4fv(L.u_trail, trailBuf);
      gl.uniform4fv(L.u_tarc, arcBuf);
      gl.uniform4fv(L.u_rip, ripBuf);
      gl.uniform1i(L.u_ripCount, nr);

      gl.drawArrays(gl.TRIANGLES, 0, 3);
    },

    dispose() {
      canvas.removeEventListener('webglcontextlost', onLost, false);
      canvas.removeEventListener('webglcontextrestored', onRestored, false);
      if (R && !gl.isContextLost()) {
        gl.deleteProgram(R.prog);
        gl.deleteVertexArray(R.vao);
        for (const tx of [R.texProf, R.texDer, R.texNoise, R.texRand, R.texBins]) gl.deleteTexture(tx);
      }
      R = null;
    }
  };

  function onLost(ev) {
    ev.preventDefault();          // allow restoration
    api.lost = true;
    R = null;
    shiftValid = false;
  }
  function onRestored() {
    R = build();
    shiftValid = false;
    api.lost = !R;
    if (!R) console.warn('[water] failed to rebuild GL resources after context restore');
  }
  canvas.addEventListener('webglcontextlost', onLost, false);
  canvas.addEventListener('webglcontextrestored', onRestored, false);

  return api;
}

;
// ── audio.js ──
/* =====================================================================
 * PEŘEJE — procedural Web Audio engine
 * Every sound is synthesized at runtime (oscillators, generated noise,
 * biquads, generated-IR convolution reverb). No samples, no files.
 * Usage: const audio = createAudioEngine(); ... audio.unlock() on first gesture.
 * ===================================================================== */
function createAudioEngine(opts) {
  'use strict';
  // opts (optional, for tools/tests): { context: AudioContext|OfflineAudioContext, manualTick: bool }
  opts = (opts && typeof opts === 'object') ? opts : {};

  const METHODS = ['unlock', 'setVolumes', 'setMuted', 'setPaused', 'startAmbience', 'stopAmbience',
    'setScene', 'startMusic', 'stopMusic', 'setMusicState', 'stroke', 'gate', 'star', 'nearMiss',
    'flip', 'crash', 'record', 'ui', 'countdown'];
  const G = (typeof globalThis !== 'undefined') ? globalThis : (typeof window !== 'undefined' ? window : {});
  let AC = null;
  try { AC = G.AudioContext || G.webkitAudioContext || null; } catch (e) { AC = null; }
  if (!AC && !opts.context) { // (old WebKit reports some constructors as typeof 'object'; new AC() is try/caught anyway)
    // No Web Audio: identical surface, all no-ops.
    const o = {};
    for (const m of METHODS) o[m] = function () {};
    o.stats = function () { return { available: false }; };
    o.isUnlocked = function () { return false; };
    return o;
  }

  // ------------------------------------------------------------------
  // Persistent state — valid (and remembered) before unlock()
  // ------------------------------------------------------------------
  const vol = { master: 0.9, sfx: 0.9, music: 0.6, ambience: 0.75 };
  let muted = false, paused = false;
  const scene = { biome: 0, night: 0, intensity: 0, speed: 0.5 };
  let ambWanted = false, musicWanted = false;
  let errors = 0, lastError = null;

  // ------------------------------------------------------------------
  // Audio graph (built lazily in unlock())
  // ------------------------------------------------------------------
  let ctx = null, ready = false, timer = null;
  let masterGain = null, reverbIn = null;
  let buses = null;           // { sfx, music, amb } each { in, send, duck, sduck }
  let musOut = null;          // { in, send } fader in front of the music bus (start/stop fades)
  let noiseW = null, noiseP = null, noiseB = null; // white / pink / brown noise buffers (generated once)
  let canPan = false;
  let unlockAt = -1e9, listening = false; // wall-clock ms of the last unlock(); gesture auto-resume installed?
  const cnt = [0, 0, 0];      // active voices: [sfx, music, ambience]
  const MAX_SFX = 24, MAX_MUSIC = 40, MAX_AMB = 10;
  const LOOKAHEAD = 0.2;      // music scheduler lookahead (s) — music isn't latency critical

  // ------------------------------------------------------------------
  // Small helpers
  // ------------------------------------------------------------------
  const clamp = (v, a, b) => (v < a ? a : v > b ? b : v);
  const num = (v, d) => ((typeof v === 'number' && isFinite(v)) ? v : d);
  const rnd = (a, b) => a + Math.random() * (b - a);
  const pick = (arr) => arr[(Math.random() * arr.length) | 0];
  const mtof = (m) => 440 * Math.pow(2, (m - 69) / 12);
  const curve = (v) => v * v;  // perceptual volume curve for 0..1 sliders

  function safe(fn) {
    return function () {
      try { return fn.apply(null, arguments); } catch (e) { errors++; lastError = e; return undefined; }
    };
  }

  // Freeze a param at its current value at time t (so following ramps never jump).
  function hold(param, t) {
    if (param.cancelAndHoldAtTime) {
      try { param.cancelAndHoldAtTime(t); return; } catch (e) { /* fall through */ }
    }
    const now = ctx.currentTime, v = param.value;
    param.cancelScheduledValues(now);
    param.setValueAtTime(v, now);
  }
  // Smoothly move a param toward value with time-constant tc.
  function glide(param, value, tc, t) {
    t = (t === undefined) ? ctx.currentTime : t;
    hold(param, t);
    param.setTargetAtTime(value, t, Math.max(0.004, tc));
  }
  // Percussive attack/decay on a gain param (silence -> peak -> ~-45 dB after `d`).
  function envAD(p, t, a, peak, d) {
    p.setValueAtTime(0, t);
    p.linearRampToValueAtTime(peak, t + a);
    p.setTargetAtTime(0, t + a, Math.max(0.003, d / 5));
  }

  // One-shot voice bookkeeping: when all its sources ended, disconnect every node.
  function voice(kind, srcs, nodes) {
    let left = srcs.length;
    cnt[kind]++;
    const done = function () {
      if (--left > 0) return;
      cnt[kind]--;
      for (let i = 0; i < nodes.length; i++) { try { nodes[i].disconnect(); } catch (e) { /* ignore */ } }
      for (let i = 0; i < srcs.length; i++) srcs[i].onended = null;
    };
    for (let i = 0; i < srcs.length; i++) srcs[i].onended = done;
  }

  function mkOsc(type, f, nodes) {
    const o = ctx.createOscillator(); o.type = type; o.frequency.value = f; nodes.push(o); return o;
  }
  function mkGain(v, nodes) { const g = ctx.createGain(); g.gain.value = v; nodes.push(g); return g; }
  function mkFilt(type, f, q, nodes) {
    const b = ctx.createBiquadFilter(); b.type = type; b.frequency.value = f; b.Q.value = q; nodes.push(b); return b;
  }
  // Looping noise source started at a random offset (so reused buffers never sound identical).
  function mkNoise(buf, t, dur, nodes, rate) {
    const s = ctx.createBufferSource();
    s.buffer = buf; s.loop = true;
    if (rate) s.playbackRate.value = rate;
    s.start(t, Math.random() * (buf.duration * 0.9));
    if (dur > 0) s.stop(t + dur);
    nodes.push(s);
    return s;
  }
  // node -> (stereo panner) -> out.in   (+ optional reverb send -> out.send)
  function route(node, out, pan, send, nodes) {
    let o = node;
    if (pan && canPan) {
      const p = ctx.createStereoPanner(); p.pan.value = clamp(pan, -1, 1);
      node.connect(p); o = p; nodes.push(p);
    }
    o.connect(out.in);
    if (send > 0) { const s = mkGain(send, nodes); o.connect(s); s.connect(out.send); }
    return o;
  }

  // ------------------------------------------------------------------
  // Buffers: noise (white/pink/brown) and the reverb impulse response
  // ------------------------------------------------------------------
  function makeNoise(seconds, kind) {
    const sr = ctx.sampleRate, len = Math.max(64, Math.floor(sr * seconds));
    const buf = ctx.createBuffer(1, len, sr);
    const d = buf.getChannelData(0);
    let b0 = 0, b1 = 0, b2 = 0, b3 = 0, b4 = 0, b5 = 0, b6 = 0, last = 0;
    for (let i = 0; i < len; i++) {
      const w = Math.random() * 2 - 1;
      if (kind === 0) d[i] = w * 0.9;
      else if (kind === 1) { // pink (Paul Kellet's refined filter)
        b0 = 0.99886 * b0 + w * 0.0555179; b1 = 0.99332 * b1 + w * 0.0750759;
        b2 = 0.969 * b2 + w * 0.153852; b3 = 0.8665 * b3 + w * 0.3104856;
        b4 = 0.55 * b4 + w * 0.5329522; b5 = -0.7616 * b5 - w * 0.016898;
        d[i] = (b0 + b1 + b2 + b3 + b4 + b5 + b6 + w * 0.5362) * 0.11; b6 = w * 0.115926;
      } else { // brown (leaky integrator)
        last = (last + 0.02 * w) / 1.02; d[i] = last * 3.5;
      }
    }
    // remove linear drift so the loop seam has no step (matters for brown noise)
    const drift = d[len - 1] - d[0];
    for (let i = 0; i < len; i++) d[i] -= drift * (i / len);
    return buf;
  }

  function makeIR(seconds, decayPow) {
    const sr = ctx.sampleRate, len = Math.floor(sr * seconds);
    const buf = ctx.createBuffer(2, len, sr);
    const pre = Math.floor(sr * 0.015);
    for (let c = 0; c < 2; c++) {
      const d = buf.getChannelData(c);
      let lp = 0;
      for (let i = 0; i < len; i++) {
        const t = i / len;
        lp += ((Math.random() * 2 - 1) - lp) * (0.8 - 0.65 * t); // tail gets darker over time
        const fadeIn = i < pre ? i / pre : 1;
        d[i] = lp * Math.pow(1 - t, decayPow) * fadeIn;
      }
    }
    return buf;
  }

  // ------------------------------------------------------------------
  // Mixer: buses -> master -> highpass -> compressor -> out -> destination
  // ------------------------------------------------------------------
  function makeBus(level) {
    const b = { in: ctx.createGain(), send: ctx.createGain(), duck: ctx.createGain(), sduck: ctx.createGain() };
    b.in.gain.value = level; b.send.gain.value = level;
    b.in.connect(b.duck); b.duck.connect(masterGain);
    b.send.connect(b.sduck); b.sduck.connect(reverbIn);
    return b;
  }
  function setBusLevel(b, v, tc) {
    const t = ctx.currentTime;
    glide(b.in.gain, v, tc, t); glide(b.send.gain, v, tc, t);
  }
  // Temporary dip of a whole bus (dry + reverb), e.g. music under a crash.
  function duckBus(b, depth, attack, holdTime, release) {
    const t = ctx.currentTime;
    for (const p of [b.duck.gain, b.sduck.gain]) {
      hold(p, t);
      p.setTargetAtTime(depth, t, attack);
      p.setTargetAtTime(1, t + attack * 3 + holdTime, release);
    }
  }
  function applyLevels(tc) {
    if (!ready) return;
    tc = tc || 0.08;
    glide(masterGain.gain, muted ? 0 : curve(vol.master), muted ? 0.12 : tc);
    setBusLevel(buses.sfx, curve(vol.sfx), tc);
    setBusLevel(buses.music, curve(vol.music) * (paused ? 0.1 : 1), paused ? 0.18 : 0.35);
    setBusLevel(buses.amb, curve(vol.ambience) * (paused ? 0.18 : 1), paused ? 0.25 : 0.5);
    syncLayers();
  }
  function syncLayers() {
    if (!ready) return;
    if (musicWanted && vol.music > 0) { if (!mus.on) musicStart(); } else if (mus.on) musicStop();
    if (ambWanted && vol.ambience > 0) { if (!amb.on) ambStart(); } else if (amb.on) ambStop();
  }

  function build() {
    canPan = typeof ctx.createStereoPanner === 'function';
    masterGain = ctx.createGain(); masterGain.gain.value = 0; // fades in via applyLevels
    const hp = ctx.createBiquadFilter(); hp.type = 'highpass'; hp.frequency.value = 28; hp.Q.value = 0.6;
    const comp = ctx.createDynamicsCompressor();
    comp.threshold.value = -12; comp.knee.value = 8; comp.ratio.value = 3;
    comp.attack.value = 0.01; comp.release.value = 0.25;
    const out = ctx.createGain(); out.gain.value = 0.9;
    masterGain.connect(hp); hp.connect(comp); comp.connect(out); out.connect(ctx.destination);

    // shared reverb (generated ~1.8 s IR)
    reverbIn = ctx.createGain(); reverbIn.gain.value = 1;
    const conv = ctx.createConvolver();
    conv.buffer = makeIR(1.8, 2.6);
    const verbHP = ctx.createBiquadFilter(); verbHP.type = 'highpass'; verbHP.frequency.value = 180; verbHP.Q.value = 0.5;
    const verbOut = ctx.createGain(); verbOut.gain.value = 0.5;
    reverbIn.connect(verbHP); verbHP.connect(conv); conv.connect(verbOut); verbOut.connect(masterGain);

    noiseW = makeNoise(2.0, 0);
    noiseP = makeNoise(3.0, 1);
    noiseB = makeNoise(4.0, 2);

    buses = { sfx: makeBus(curve(vol.sfx)), music: makeBus(curve(vol.music)), amb: makeBus(curve(vol.ambience)) };
    musOut = { in: ctx.createGain(), send: ctx.createGain() };
    musOut.in.gain.value = 0; musOut.send.gain.value = 0;
    musOut.in.connect(buses.music.in); musOut.send.connect(buses.music.send);

    // iOS/Safari: playing a tiny silent buffer inside the gesture fully unlocks output
    try {
      const sb = ctx.createBufferSource(); sb.buffer = ctx.createBuffer(1, 1, ctx.sampleRate);
      sb.connect(ctx.destination); sb.start(0); sb.stop(ctx.currentTime + 0.01);
      sb.onended = function () { try { sb.disconnect(); } catch (e) { /* ignore */ } };
    } catch (e) { /* ignore */ }

    ready = true;
    applyLevels(0.15);
    const si = G.setInterval || (typeof setInterval === 'function' ? setInterval : null);
    if (si && !opts.manualTick) timer = si(safe(tick), 25);
    applyScene(true);
    syncLayers();
  }

  const wallNow = () => (G.performance && typeof G.performance.now === 'function' ? G.performance.now() : Date.now());
  function resumeCtx() {
    if (!ctx || (ctx.state !== 'suspended' && ctx.state !== 'interrupted')) return;
    try { const p = ctx.resume(); if (p && p.catch) p.catch(function () {}); } catch (e) { /* ignore */ }
  }
  // Mobile browsers only count pointerup/touchend/click/keydown as user activation (NOT a touch pointerdown),
  // and iOS 'interrupts' the context on calls / app switches. So if the game unlocked from pointerdown, or
  // only once, retry resume() on every later real gesture and when the page becomes visible again.
  function installAutoResume() {
    const doc = G.document;
    if (listening || opts.context || !doc || typeof doc.addEventListener !== 'function') return;
    listening = true;
    const kick = function () { try { resumeCtx(); } catch (e) { /* ignore */ } };
    for (const ev of ['pointerup', 'touchend', 'mousedown', 'keydown', 'click']) {
      try { doc.addEventListener(ev, kick, { capture: true, passive: true }); } catch (e) { /* ignore */ }
    }
    const sleep = function () {
      if (ctx && ctx.state === 'running' && ctx.suspend) { try { const p = ctx.suspend(); if (p && p.catch) p.catch(function () {}); } catch (e) { /* ignore */ } }
    };
    try { doc.addEventListener('visibilitychange', function () { if (doc.hidden) sleep(); else kick(); }); } catch (e) { /* ignore */ }
    try { if (G.addEventListener) G.addEventListener('pagehide', sleep); } catch (e) { /* ignore */ }
  }
  // The context was closed under us (rare: device loss, browser policy): forget the dead graph so the next
  // unlock() rebuilds everything; wanted music/ambience and all settings are re-applied by build().
  function dropGraph() {
    const ci = G.clearInterval || (typeof clearInterval === 'function' ? clearInterval : null);
    if (timer !== null && ci) { try { ci(timer); } catch (e) { /* ignore */ } }
    timer = null; ready = false; ctx = null; buses = null; musOut = null;
    amb.on = false; amb.L = null; amb.base = null;
    mus.on = false; mus.padG = null; mus.tones = null; mus.next = 0; // new context's clock restarts at 0
    cnt[0] = cnt[1] = cnt[2] = 0;
    lastScene = { biome: -1, night: -1, intensity: -1, speed: -1 };
  }

  function unlock() {
    unlockAt = wallNow();
    if (ctx && ctx.state === 'closed' && !opts.context) dropGraph();
    if (!ctx) {
      if (opts.context) ctx = opts.context;
      else try { ctx = new AC({ latencyHint: 'interactive' }); } catch (e) {
        try { ctx = new AC(); } catch (e2) { ctx = null; }
      }
      if (!ctx) return;
      try { build(); } catch (e) { ready = false; errors++; lastError = e; }
      installAutoResume();
    }
    resumeCtx();
  }

  // Central 25 ms tick: music lookahead scheduler + ambience random events.
  function tick() {
    if (!ready || (ctx.state !== 'running' && !opts.context)) return;
    const t = ctx.currentTime;
    if (mus.on) {
      if (mus.next < t - 0.25) mus.next = t + 0.05; // recover after a long stall
      const ahead = LOOKAHEAD;
      let guard = 0;
      while (mus.next < t + ahead && guard++ < 24) {
        const at = mus.next;
        musicStep(at, 60 / mus.bpm / 4);        // (a bar start may retune the tempo)
        mus.next = at + 60 / mus.bpm / 4;
      }
    }
    if (amb.on) ambTick(t);
  }

  // ==================================================================
  // AMBIENCE — continuous river bed + sparse synthesized critters
  // ==================================================================
  // Per-biome character. babble = centre Hz of the mid water layer, bright = rapids/bubble brightness,
  // wind/sparkle/birds/crickets/frogs/owl = layer weights or event rates.
  const BIOME_AMB = [
    { babble: 700, bright: 1.0, rumble: 1.0, wind: 0.04, windF: 700, sparkle: 0, birds: 1.0, bird: 'song', crickets: 0, frogs: 0, owl: 0 },     // forest dawn
    { babble: 620, bright: 0.9, rumble: 1.15, wind: 0.24, windF: 420, sparkle: 0, birds: 0.35, bird: 'hawk', crickets: 0.12, frogs: 0, owl: 0 }, // red canyon
    { babble: 470, bright: 0.65, rumble: 0.9, wind: 0.02, windF: 600, sparkle: 0, birds: 0.5, bird: 'exotic', crickets: 0.8, frogs: 1.0, owl: 0 }, // jungle dusk
    { babble: 560, bright: 0.75, rumble: 0.85, wind: 0.07, windF: 500, sparkle: 0, birds: 0, bird: 'song', crickets: 1.0, frogs: 0.35, owl: 0.7 },  // night
    { babble: 840, bright: 1.25, rumble: 0.8, wind: 0.75, windF: 950, sparkle: 1.0, birds: 0.1, bird: 'song', crickets: 0, frogs: 0, owl: 0 },   // glacier
  ];
  const amb = {
    on: false, L: null, base: null,
    nextMod: 0, nextBubble: 0, nextBird: 0, nextCricket: 0, nextFrog: 0, nextOwl: 0, nextSparkle: 0,
  };
  let lastScene = { biome: -1, night: -1, intensity: -1, speed: -1 };

  function ambStart() {
    if (amb.on) return;
    amb.on = true;
    amb.rates = null;
    const t = ctx.currentTime, n = [];
    const out = mkGain(0, n); out.connect(buses.amb.in);
    out.gain.setTargetAtTime(0.6, t, 0.6); // gentle fade-in (bed sits ~4 dB under the music)
    const L = { out: out, nodes: n, srcs: [] };
    const panTo = (node, p) => {
      if (!canPan) { node.connect(out); return; }
      const pn = ctx.createStereoPanner(); pn.pan.value = p; n.push(pn); node.connect(pn); pn.connect(out);
    };
    // 1) low rumble of the whole river
    const sR = mkNoise(noiseB, t, 0, n); L.rumbleF = mkFilt('lowpass', 190, 0.5, n); L.rumbleG = mkGain(0, n);
    sR.connect(L.rumbleF); L.rumbleF.connect(L.rumbleG); L.rumbleG.connect(out);
    // 2) mid 'babble' — two decorrelated band-passed pink layers, panned apart
    const sBL = mkNoise(noiseP, t, 0, n); L.bLF = mkFilt('bandpass', 700, 0.9, n); L.bLG = mkGain(0, n);
    sBL.connect(L.bLF); L.bLF.connect(L.bLG); panTo(L.bLG, -0.5);
    const sBR = mkNoise(noiseP, t, 0, n, 0.97); L.bRF = mkFilt('bandpass', 1100, 1.1, n); L.bRG = mkGain(0, n);
    sBR.connect(L.bRF); L.bRF.connect(L.bRG); panTo(L.bRG, 0.5);
    // 3) rapids: bright hiss that grows with intensity
    const sH = mkNoise(noiseW, t, 0, n); L.rapF = mkFilt('bandpass', 2400, 0.6, n); L.rapG = mkGain(0, n);
    sH.connect(L.rapF); L.rapF.connect(L.rapG); L.rapG.connect(out);
    // 4) wind (canyon / glacier), slowly gusting
    const sW = mkNoise(noiseW, t, 0, n, 0.5); L.windF = mkFilt('bandpass', 700, 2.2, n); L.windG = mkGain(0, n);
    sW.connect(L.windF); L.windF.connect(L.windG); panTo(L.windG, 0.15);
    L.srcs = [sR, sBL, sBR, sH, sW];
    amb.L = L;
    amb.nextMod = t; amb.nextBubble = t + 0.8; amb.nextBird = t + rnd(1.5, 4);
    amb.nextCricket = t + rnd(0.5, 2); amb.nextFrog = t + rnd(2, 5); amb.nextOwl = t + rnd(6, 14); amb.nextSparkle = t + 1;
    applyScene(true);
  }

  function ambStop() {
    if (!amb.on || !amb.L) { amb.on = false; return; }
    amb.on = false;
    const L = amb.L, t = ctx.currentTime;
    amb.L = null;
    glide(L.out.gain, 0, 0.35, t);
    for (const s of L.srcs) { try { s.stop(t + 2.2); } catch (e) { /* ignore */ } } // ~6 time constants: inaudible cut
    voice(2, L.srcs, L.nodes); // disconnects everything once the loops stopped
  }

  // Blend biome table by fractional distance (biome may be passed as int; night adds critters).
  function sceneMix() {
    const b = BIOME_AMB[clamp(scene.biome | 0, 0, 4)];
    const night = scene.night;
    return {
      b: b,
      birds: b.birds * (1 - night),
      crickets: Math.max(b.crickets, night * 0.85),
      frogs: Math.max(b.frogs, night * 0.3),
      owl: Math.max(b.owl, night * 0.4) * (b.sparkle > 0 ? 0.3 : 1),
    };
  }

  // Ramp the continuous layers to the current scene (only when values change meaningfully).
  function applyScene(force) {
    const changed = force || scene.biome !== lastScene.biome ||
      Math.abs(scene.night - lastScene.night) > 0.03 ||
      Math.abs(scene.intensity - lastScene.intensity) > 0.025 ||
      Math.abs(scene.speed - lastScene.speed) > 0.04;
    if (!changed) return;
    const biomeChanged = scene.biome !== lastScene.biome;
    lastScene = { biome: scene.biome, night: scene.night, intensity: scene.intensity, speed: scene.speed };
    // music follows the biome key at the next phrase boundary
    mus.pendingKey = clamp(scene.biome | 0, 0, 4);
    if (!amb.on || !amb.L) return;
    const L = amb.L, m = sceneMix(), b = m.b, I = scene.intensity, S = scene.speed;
    const tc = biomeChanged ? 2.0 : 0.8, t = ctx.currentTime;
    const quiet = 1 - 0.18 * scene.night;
    const babble = 0.34 * (0.85 + 0.3 * S) * quiet;
    amb.base = { babble: babble, bf: b.babble, wind: 0.32 * b.wind, windF: b.windF };
    glide(L.rumbleG.gain, 0.55 * b.rumble * (0.8 + 0.35 * S) * quiet, tc, t);
    glide(L.rumbleF.frequency, 160 + 90 * I, tc, t);
    glide(L.bLF.frequency, b.babble, tc, t);
    glide(L.bRF.frequency, b.babble * 1.6, tc, t);
    glide(L.rapG.gain, (0.025 + 0.2 * I * (0.6 + 0.4 * S)) * b.bright * quiet, tc, t);
    glide(L.rapF.frequency, (1500 + 2600 * I) * b.bright, tc, t);
    glide(L.windG.gain, amb.base.wind, tc * 1.5, t);
    // Event rates may have risen (e.g. glacier -> forest birds, dusk -> night crickets): a timer drawn at the
    // old, tiny rate could be minutes away, so pull it in to what the new rate would have drawn.
    const pr = amb.rates || {};
    const near = (k, next, maxGap, rate) => (rate > 0.02 && rate > (pr[k] || 0) * 1.2 ? Math.min(next, t + rnd(0.15, 1) * maxGap / rate) : next);
    amb.nextBird = near('b', amb.nextBird, 11, m.birds);
    amb.nextCricket = near('c', amb.nextCricket, 1.7, m.crickets);
    amb.nextFrog = near('f', amb.nextFrog, 8, m.frogs);
    amb.nextOwl = near('o', amb.nextOwl, 26, m.owl);
    amb.nextSparkle = near('s', amb.nextSparkle, 1.4, b.sparkle);
    amb.rates = { b: m.birds, c: m.crickets, f: m.frogs, o: m.owl, s: b.sparkle };
  }

  // Random slow modulation + one-shot critter / bubble events.
  function ambTick(t) {
    const L = amb.L; if (!L || !amb.base) return;
    const m = sceneMix(), b = m.b, base = amb.base;
    if (t >= amb.nextMod) { // babble drift and wind gusts
      amb.nextMod = t + rnd(0.35, 1.2);
      L.bLG.gain.setTargetAtTime(base.babble * rnd(0.55, 1.0), t, rnd(0.25, 0.6));
      L.bRG.gain.setTargetAtTime(base.babble * rnd(0.45, 0.9), t, rnd(0.25, 0.6));
      L.bLF.frequency.setTargetAtTime(base.bf * rnd(0.75, 1.3), t, 0.5);
      L.bRF.frequency.setTargetAtTime(base.bf * 1.6 * rnd(0.75, 1.3), t, 0.5);
      if (base.wind > 0.01) {
        L.windG.gain.setTargetAtTime(base.wind * rnd(0.35, 1.15), t, rnd(0.8, 1.6));
        L.windF.frequency.setTargetAtTime(base.windF * rnd(0.7, 1.7), t, rnd(0.8, 1.6));
      }
    }
    if (cnt[2] >= MAX_AMB) return;
    if (t >= amb.nextBubble) {
      amb.nextBubble = t + rnd(0.7, 3.2) / (0.6 + scene.speed);
      const k = Math.random() < 0.35 ? 2 + ((Math.random() * 2) | 0) : 1;
      for (let i = 0; i < k; i++) bubble(t + 0.02 + i * rnd(0.03, 0.09), b.bright);
    }
    if (m.birds > 0.02 && t >= amb.nextBird) {
      amb.nextBird = t + rnd(4, 11) / m.birds;
      birdCall(t + 0.05, b.bird);
    }
    if (m.crickets > 0.02 && t >= amb.nextCricket) {
      amb.nextCricket = t + rnd(0.45, 1.7) / m.crickets;
      cricket(t + 0.03);
    }
    if (m.frogs > 0.02 && t >= amb.nextFrog) {
      amb.nextFrog = t + rnd(2.5, 8) / m.frogs;
      frog(t + 0.04);
    }
    if (m.owl > 0.05 && t >= amb.nextOwl) {
      amb.nextOwl = t + rnd(12, 26) / m.owl;
      owl(t + 0.05);
    }
    if (b.sparkle > 0 && t >= amb.nextSparkle) {
      amb.nextSparkle = t + rnd(0.25, 1.4) / b.sparkle;
      sparkle(t + 0.02);
    }
  }

  // --- ambience one-shots (very quiet) ---
  function bubble(t, bright) { // classic rising-resonance bubble
    const n = [];
    const f = rnd(260, 900) * bright;
    const o = mkOsc('sine', f, n); const g = mkGain(0, n);
    o.frequency.setValueAtTime(f, t);
    o.frequency.exponentialRampToValueAtTime(f * rnd(1.7, 2.8), t + rnd(0.03, 0.07));
    envAD(g.gain, t, 0.004, rnd(0.015, 0.045), rnd(0.05, 0.09));
    o.connect(g); route(g, buses.amb, rnd(-0.8, 0.8), 0, n);
    o.start(t); o.stop(t + 0.14);
    voice(2, [o], n);
  }

  function birdCall(t, kind) {
    const n = [], o = mkOsc('sine', 3000, n), g = mkGain(0, n);
    const p = o.frequency, gp = g.gain;
    let end = t;
    gp.setValueAtTime(0, t);
    if (kind === 'hawk') { // distant descending 'kee-ah'
      const f = rnd(2300, 2800);
      p.setValueAtTime(f, t); p.linearRampToValueAtTime(f * 1.08, t + 0.08); p.exponentialRampToValueAtTime(f * 0.62, t + 0.6);
      gp.linearRampToValueAtTime(0.022, t + 0.05); gp.setTargetAtTime(0, t + 0.45, 0.06);
      end = t + 0.75;
    } else if (kind === 'exotic') { // jungle warble with fast vibrato
      const lfo = mkOsc('sine', rnd(18, 30), n), lg = mkGain(rnd(150, 380), n);
      lfo.connect(lg); lg.connect(p);
      const f = rnd(1500, 2400);
      p.setValueAtTime(f, t); p.linearRampToValueAtTime(f * rnd(1.15, 1.5), t + 0.35);
      gp.linearRampToValueAtTime(0.02, t + 0.06); gp.setTargetAtTime(0, t + 0.3, 0.05);
      end = t + 0.55;
      lfo.start(t); lfo.stop(end);
      o.connect(g); route(g, buses.amb, rnd(-0.85, 0.85), 0.35, n);
      o.start(t); o.stop(end);
      voice(2, [o, lfo], n);
      return;
    } else { // song bird: 2-6 quick chirps
      const notes = 2 + ((Math.random() * 5) | 0), f = rnd(2600, 4300), up = Math.random() < 0.6;
      const gap = rnd(0.08, 0.14);
      for (let i = 0; i < notes; i++) {
        const tt = t + i * gap, len = rnd(0.04, 0.075), ff = f * rnd(0.92, 1.1);
        p.setValueAtTime(ff, tt);
        p.exponentialRampToValueAtTime(up ? ff * rnd(1.2, 1.5) : ff * rnd(0.65, 0.8), tt + len);
        gp.setValueAtTime(0, tt); gp.linearRampToValueAtTime(rnd(0.012, 0.022), tt + 0.008);
        gp.linearRampToValueAtTime(0, tt + len);
      }
      end = t + notes * gap + 0.05;
    }
    o.connect(g); route(g, buses.amb, rnd(-0.85, 0.85), 0.3, n);
    o.start(t); o.stop(end);
    voice(2, [o], n);
  }

  function cricket(t) { // amplitude-pulsed high sine trill
    const n = [], f = rnd(4200, 5300), o = mkOsc('sine', f, n), g = mkGain(0, n);
    const pulses = 3 + ((Math.random() * 4) | 0), peak = rnd(0.008, 0.016);
    for (let i = 0; i < pulses; i++) {
      const tt = t + i * 0.042;
      g.gain.setValueAtTime(0, tt); g.gain.linearRampToValueAtTime(peak, tt + 0.006);
      g.gain.linearRampToValueAtTime(0, tt + 0.024);
    }
    o.connect(g); route(g, buses.amb, rnd(-0.9, 0.9), 0, n);
    o.start(t); o.stop(t + pulses * 0.042 + 0.04);
    voice(2, [o], n);
  }

  function frog(t) { // band-passed saw croak, 2-3 pulses, slightly falling pitch
    const n = [], f = rnd(110, 190), o = mkOsc('sawtooth', f, n);
    const bp = mkFilt('bandpass', rnd(600, 1000), 4, n), g = mkGain(0, n);
    const k = 2 + ((Math.random() * 2) | 0), peak = rnd(0.035, 0.06);
    for (let i = 0; i < k; i++) {
      const tt = t + i * 0.12;
      o.frequency.setValueAtTime(f * (1 - i * 0.03), tt);
      o.frequency.linearRampToValueAtTime(f * (0.9 - i * 0.03), tt + 0.07);
      g.gain.setValueAtTime(0, tt); g.gain.linearRampToValueAtTime(peak, tt + 0.012);
      g.gain.linearRampToValueAtTime(0, tt + 0.075);
    }
    o.connect(bp); bp.connect(g); route(g, buses.amb, rnd(-0.8, 0.8), 0.2, n);
    o.start(t); o.stop(t + k * 0.12 + 0.05);
    voice(2, [o], n);
  }

  function owl(t) { // soft 'hoo — hoo-hoo'
    const n = [], f = rnd(360, 420), o = mkOsc('sine', f, n), g = mkGain(0, n);
    const hoots = [[0, 0.32], [0.55, 0.16], [0.78, 0.36]];
    for (const h of hoots) {
      const tt = t + h[0];
      o.frequency.setValueAtTime(f * 1.04, tt); o.frequency.linearRampToValueAtTime(f * 0.96, tt + h[1]);
      g.gain.setValueAtTime(0, tt); g.gain.linearRampToValueAtTime(0.03, tt + 0.06);
      g.gain.linearRampToValueAtTime(0, tt + h[1]);
    }
    o.connect(g); route(g, buses.amb, rnd(-0.7, 0.7), 0.5, n);
    o.start(t); o.stop(t + 1.25);
    voice(2, [o], n);
  }

  function sparkle(t) { // icy tinkle
    const n = [], f = rnd(3000, 7200), o = mkOsc('sine', f, n), g = mkGain(0, n);
    envAD(g.gain, t, 0.003, rnd(0.006, 0.016), rnd(0.18, 0.35));
    o.connect(g); route(g, buses.amb, rnd(-0.9, 0.9), 0.6, n);
    o.start(t); o.stop(t + 0.4);
    voice(2, [o], n);
  }

  // ==================================================================
  // INSTRUMENTS (shared by music and sfx). kind: 0 = sfx voice, 1 = music voice
  // ==================================================================
  // FM pluck / kalimba: modulation index decays fast -> bright attack, round tail.
  function fmPluck(kind, out, f, t, vel, pan, send, dur, ratio, index) {
    const n = [], c = mkOsc('sine', f, n), m = mkOsc('sine', f * ratio, n);
    const mg = mkGain(0, n), g = mkGain(0, n);
    mg.gain.setValueAtTime(f * index, t);
    mg.gain.setTargetAtTime(f * index * 0.06, t, Math.max(0.01, dur * 0.16));
    m.connect(mg); mg.connect(c.frequency); c.connect(g);
    envAD(g.gain, t, 0.004, vel, dur);
    route(g, out, pan, send, n);
    const end = t + dur * 1.15 + 0.03;
    c.start(t); m.start(t); c.stop(end); m.stop(end);
    voice(kind, [c, m], n);
  }

  // Marimba: fundamental + fast-decaying 4th partial (+ optional mallet click partial).
  function marimba(kind, out, f, t, vel, pan, send, dur, click) {
    const n = [], mix = mkGain(1, n), srcs = [];
    const parts = click ? [[1, 1, 1], [3.94, 0.42, 0.11], [9.8, 0.16, 0.025]] : [[1, 1, 1], [3.94, 0.38, 0.1]];
    for (const p of parts) {
      const o = mkOsc('sine', f * p[0], n), g = mkGain(0, n);
      envAD(g.gain, t, 0.003, vel * p[1], dur * p[2]);
      o.connect(g); g.connect(mix);
      o.start(t); o.stop(t + dur * p[2] * 1.15 + 0.03); srcs.push(o);
    }
    route(mix, out, pan, send, n);
    voice(kind, srcs, n);
  }

  // Bell: inharmonic partials with individual decays.
  function bell(kind, out, f, t, vel, pan, send, dur) {
    const n = [], mix = mkGain(1, n), srcs = [];
    const parts = [[1, 1, 1], [2.0, 0.32, 0.6], [2.76, 0.28, 0.4], [5.4, 0.12, 0.18]];
    for (const p of parts) {
      const o = mkOsc('sine', f * p[0], n), g = mkGain(0, n);
      envAD(g.gain, t, 0.002, vel * p[1], dur * p[2]);
      o.connect(g); g.connect(mix);
      o.start(t); o.stop(t + dur * p[2] * 1.15 + 0.03); srcs.push(o);
    }
    route(mix, out, pan, send, n);
    voice(kind, srcs, n);
  }

  // Wood block / tok.
  function wood(kind, out, t, vel, pan, f) {
    const n = [], o = mkOsc('sine', f, n), o2 = mkOsc('triangle', f * 0.505, n), g = mkGain(0, n);
    o.frequency.setValueAtTime(f * 1.25, t); o.frequency.exponentialRampToValueAtTime(f, t + 0.012);
    envAD(g.gain, t, 0.001, vel, 0.06);
    o.connect(g); o2.connect(g); route(g, out, pan, 0.12, n);
    o.start(t); o2.start(t); o.stop(t + 0.09); o2.stop(t + 0.09);
    voice(kind, [o, o2], n);
  }

  function bassNote(f, t, dur, vel) {
    const n = [], o = mkOsc('triangle', f, n), s = mkOsc('sine', f, n);
    const lp = mkFilt('lowpass', 1200, 1.2, n), g = mkGain(0, n);
    lp.frequency.setValueAtTime(1300, t); lp.frequency.setTargetAtTime(420, t, 0.07);
    g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(vel, t + 0.008);
    g.gain.setTargetAtTime(vel * 0.55, t + 0.01, 0.12);
    g.gain.setTargetAtTime(0, t + dur, 0.06);
    o.connect(lp); s.connect(lp); lp.connect(g); route(g, musOut, 0, 0, n);
    const end = t + dur + 0.4; o.start(t); s.start(t); o.stop(end); s.stop(end);
    voice(1, [o, s], n);
  }

  function shaker(t, vel) {
    const n = [], s = mkNoise(noiseW, t, 0.14, n, rnd(0.9, 1.15)), hp = mkFilt('highpass', 6500, 0.8, n), g = mkGain(0, n);
    g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(vel, t + 0.012);
    g.gain.setTargetAtTime(0, t + 0.014, 0.024);
    s.connect(hp); hp.connect(g); route(g, musOut, rnd(0.15, 0.45), 0.08, n);
    voice(1, [s], n);
  }

  function kick(t, vel) {
    const n = [], o = mkOsc('sine', 130, n), g = mkGain(0, n);
    o.frequency.setValueAtTime(130, t); o.frequency.exponentialRampToValueAtTime(46, t + 0.11);
    envAD(g.gain, t, 0.003, vel, 0.34);
    o.connect(g); route(g, musOut, 0, 0.04, n);
    o.start(t); o.stop(t + 0.42);
    voice(1, [o], n);
  }

  function handDrum(t, f, vel, pan) {
    const n = [], o = mkOsc('sine', f * 1.5, n), g = mkGain(0, n);
    o.frequency.setValueAtTime(f * 1.5, t); o.frequency.exponentialRampToValueAtTime(f, t + 0.025);
    envAD(g.gain, t, 0.002, vel, 0.2);
    o.connect(g); route(g, musOut, pan, 0.15, n);
    o.start(t); o.stop(t + 0.26);
    voice(1, [o], n);
  }

  // ==================================================================
  // MUSIC — generative, adaptive, lookahead-scheduled
  // ==================================================================
  const MODES = {
    ionian: [0, 2, 4, 5, 7, 9, 11], lydian: [0, 2, 4, 6, 7, 9, 11],
    dorian: [0, 2, 3, 5, 7, 9, 10], aeolian: [0, 2, 3, 5, 7, 8, 10],
  };
  // root: tonic MIDI note; pent: melody scale (semitones); progs: chord progressions as 0-based mode degrees
  const KEYS = [
    { root: 50, mode: 'ionian', pent: [0, 2, 4, 7, 9], mel: 'marimba', pad: 'sawtooth', progs: [[0, 4, 5, 3], [0, 3, 0, 4], [5, 3, 0, 4], [0, 5, 3, 4], [3, 4, 2, 5]] },  // D major — forest dawn
    { root: 45, mode: 'dorian', pent: [0, 3, 5, 7, 10], mel: 'pluck', pad: 'sawtooth', progs: [[0, 3, 0, 6], [0, 6, 3, 0], [0, 4, 6, 3], [5, 6, 0, 0], [0, 2, 3, 6]] }, // A dorian — canyon
    { root: 52, mode: 'aeolian', pent: [0, 3, 5, 7, 10], mel: 'marimba', pad: 'sawtooth', progs: [[0, 5, 6, 4], [0, 3, 5, 6], [0, 6, 5, 6], [5, 3, 6, 0], [0, 4, 5, 6]] }, // E minor — jungle
    { root: 47, mode: 'aeolian', pent: [0, 3, 5, 7, 10], mel: 'bell', pad: 'triangle', progs: [[0, 5, 2, 6], [0, 3, 0, 5], [5, 6, 0, 0], [0, 6, 5, 3]] },                      // B minor — night
    { root: 53, mode: 'lydian', pent: [0, 2, 4, 7, 9], mel: 'bell', pad: 'triangle', progs: [[0, 1, 0, 1], [0, 4, 1, 5], [0, 5, 1, 4], [3, 1, 0, 0]] },                      // F lydian — glacier
  ];
  const BASS_PATS = [[0, 10], [0, 6, 8, 14], [0, 3, 8, 11], [0, 8, 11], [0, 7, 10, 12]];
  const ARP_PATS = [[0, 1, 2, 3], [0, 1, 2, 3, 2, 1], [0, 2, 1, 3], [3, 2, 1, 0, 1, 2], [0, 1, 0, 2, 0, 3]];
  const HAND_PATS = [[3, 6, 11, 14], [6, 7, 14], [2, 6, 10, 11, 14], [3, 10, 14]];

  const mus = {
    on: false, state: 'menu', idle: false, next: 0, step: 0, bar: 0, pb: 0, bpm: 86,
    keyIdx: 0, pendingKey: 0, key: KEYS[0], mel: null,
    prog: null, progIdx: 0, lastProg: -1, chordBars: 0, tones: null, padG: null,
    sec: 'A', secBars: 8, secCount: 0, energy: 0.6,
    motif: null, motifAge: 0, phraseOn: true, melBase: 6,
    bassPat: null, arpPat: null, handPat: null, arpRest: 0.1,
  };

  function chordTones(key, deg, count) { // stacked thirds within the mode (semitones from key root)
    const m = MODES[key.mode], out = [];
    for (let i = 0; i < count; i++) { const d = deg + i * 2; out.push(m[d % 7] + 12 * Math.floor(d / 7)); }
    return out;
  }
  function melNotes(key) { const a = []; for (let o = 0; o < 3; o++) for (const p of key.pent) a.push(key.root + 12 + o * 12 + p); return a; }
  function wrapRange(m, lo, hi) { while (m < lo) m += 12; while (m > hi) m -= 12; return m; }
  function currentKey() { return mus.on ? mus.key : KEYS[clamp(scene.biome | 0, 0, 4)]; }

  function setKey(k) {
    mus.keyIdx = k; mus.key = KEYS[k]; mus.mel = melNotes(mus.key);
    mus.prog = null; mus.chordBars = 0; mus.motif = null;
  }

  function newMotif(menu) { // 2-bar rhythmic/contour cell (pentatonic index space)
    const map = new Array(32).fill(null);
    const lens = menu ? [4, 4, 6, 8, 8] : [2, 2, 4, 4, 4, 6, 8];
    let s = 0, rel = 0, last = null;
    while (s < 30) {
      const len = pick(lens);
      if (s === 0 || Math.random() > 0.22) {
        if (s > 0) rel = clamp(rel + pick([-2, -1, -1, 0, 1, 1, 2, 3, -3]), -4, 4);
        last = map[s] = { rel: rel, len: Math.min(len, 32 - s), acc: (s % 4 === 0) ? 1 : 0.8, last: false };
      }
      s += len;
    }
    if (last) last.last = true;
    return { map: map, vshift: pick([1, 2, -1, 2, 3]) };
  }

  function snapToChord(idx, rootFirst) {
    const key = mus.key, mel = mus.mel, tones = mus.tones;
    const sets = [[0, 1, 2]]; if (rootFirst) sets.unshift([0]);
    for (const set of sets) {
      const pcs = set.map((i) => (key.root + tones[i]) % 12);
      for (let d = 0; d <= 3; d++) {
        for (const j of [idx - d, idx + d]) if (j >= 0 && j < mel.length && pcs.indexOf(mel[j] % 12) >= 0) return j;
      }
    }
    return idx;
  }

  function padChord(t, dur, I, soft) {
    if (cnt[1] >= MAX_MUSIC) return;
    const key = mus.key, n = [], srcs = [];
    const base = wrapRange(key.root + 12, 55, 66);
    const tn = mus.tones, voicing = [tn[0], tn[1], tn[2], tn[4]]; // 1 3 5 9
    const tri = key.pad === 'triangle';
    const lp = mkFilt('lowpass', 700, 0.6, n), g = mkGain(0, n);
    const lvl = (tri ? 0.05 : 0.034) * (soft ? (tri ? 1.4 : 1.9) : 1);
    const att = soft ? 1.2 : 0.7, end = t + dur;
    const fc = (tri ? 1400 : 900) + 900 * I;
    lp.frequency.setValueAtTime(fc * 0.6, t); lp.frequency.linearRampToValueAtTime(fc, t + dur * 0.5);
    lp.frequency.linearRampToValueAtTime(fc * 0.75, end);
    g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(lvl, t + att);
    g.gain.setTargetAtTime(lvl * 0.75, t + att, 1.5);
    g.gain.setTargetAtTime(0, end, 0.45);
    for (let i = 0; i < voicing.length; i++) {
      const m = wrapRange(base + voicing[i], base, base + 16);
      const o = mkOsc(key.pad, mtof(m), n); o.detune.value = (i % 2) ? 7 : -7;
      o.connect(lp); srcs.push(o);
    }
    const sub = mkOsc('sine', mtof(base + tn[0] - 12), n), sg = mkGain(tri ? 0.5 : 0.9, n);
    sub.connect(sg); sg.connect(lp); srcs.push(sub);
    lp.connect(g); route(g, musOut, 0, 0.55, n);
    for (const o of srcs) { o.start(t); o.stop(end + 2.4); }
    voice(1, srcs, n);
    mus.padG = g;
  }

  function nextChord(time, I, menu) {
    const key = mus.key;
    if (!mus.prog || mus.progIdx >= mus.prog.length) {
      let i = 0, guard = 0;
      do { i = (Math.random() * key.progs.length) | 0; } while (i === mus.lastProg && guard++ < 8);
      mus.lastProg = i; mus.prog = key.progs[i]; mus.progIdx = 0;
    }
    const deg = mus.prog[mus.progIdx++];
    mus.tones = chordTones(key, deg, 5);
    mus.chordBars = (!menu && I > 0.65 && Math.random() < 0.35) ? 1 : 2;
    if (mus.padG) { const p = mus.padG.gain; hold(p, time); p.setTargetAtTime(0, time, 0.35); }
    padChord(time, mus.chordBars * 240 / mus.bpm, I, menu);
  }

  function barStart(time) {
    const menu = mus.state === 'menu';
    const I = menu ? 0 : scene.intensity;
    const target = menu ? 84 : 92 + 32 * I;          // tempo follows intensity, eased per bar
    mus.bpm += clamp(target - mus.bpm, -4, 4);
    if (mus.pendingKey !== mus.keyIdx && (mus.bar % 4 === 0)) setKey(mus.pendingKey);
    if (--mus.secBars <= 0) {                        // arrangement sections keep long sessions fresh
      mus.secCount++;
      if (mus.sec !== 'break' && mus.secCount > 2 && Math.random() < 0.45) { mus.sec = 'break'; mus.secBars = 4; mus.secCount = 0; }
      else { mus.sec = (mus.sec === 'A' && Math.random() < 0.6) ? 'B' : 'A'; mus.secBars = 8; }
      mus.energy = rnd(0.35, 1);
    }
    if (mus.bar % 4 === 0 || !mus.bassPat) {
      mus.bassPat = pick(BASS_PATS); mus.arpPat = pick(ARP_PATS); mus.handPat = pick(HAND_PATS);
      mus.arpRest = rnd(0.05, 0.25);
    }
    if (--mus.chordBars <= 0) nextChord(time, I, menu);
    mus.pb = mus.bar % 8;
    if (mus.pb === 0) {                               // new 8-bar melodic phrase
      if (!mus.motif || (++mus.motifAge >= 2 && Math.random() < 0.6)) { mus.motif = newMotif(menu); mus.motifAge = 0; }
      const r = Math.random();
      mus.phraseOn = menu ? r < 0.7 : mus.sec === 'A' ? r < 0.9 : mus.sec === 'break' ? r < 0.6 : r < 0.35;
      mus.melBase = 5 + ((Math.random() * 3) | 0);
    }
    mus.bar++;
  }

  function melodyStep(ts, s, menu, I, sx) {
    const half = mus.pb >> 1;                         // phrase form A A' B A''
    if (mus.sec === 'B' && half === 2) return;        // breathing room
    const pos = (mus.pb & 1) * 16 + s, note = mus.motif.map[pos];
    if (!note) return;
    if (menu && Math.random() < 0.4) return;
    if (half === 1 && Math.random() < 0.12) return;
    let idx = mus.melBase + (half === 2 ? -note.rel : note.rel) + (half === 1 ? mus.motif.vshift : 0);
    idx = clamp(idx, 0, mus.mel.length - 1);
    const cadence = half === 3 && note.last;
    if (pos % 16 === 0 || cadence) idx = snapToChord(idx, cadence);
    const f = mtof(mus.mel[idx]);
    const dur = Math.min(1.6, note.len * sx * 1.6 + 0.25) * (cadence ? 1.5 : 1);
    const vel = (menu ? 0.12 : 0.09 + 0.035 * I) * note.acc * rnd(0.9, 1.05);
    const pan = rnd(-0.15, 0.15), type = mus.key.mel;
    if (type === 'bell') bell(1, musOut, f, ts, vel * 0.8, pan, 0.5, dur * 1.4);
    else if (type === 'pluck') fmPluck(1, musOut, f, ts, vel, pan, 0.4, dur, 1, 1.6);
    else marimba(1, musOut, f, ts, vel * 1.15, pan, 0.4, dur, false);
  }

  function musicStep(time, sx) {
    const s = mus.step & 15;
    if (s === 0 && !mus.idle) barStart(time);
    mus.step++;
    if (mus.idle || !mus.tones) return;
    const menu = mus.state === 'menu';
    const I = menu ? 0 : scene.intensity;
    const ts = (s & 1) ? time + sx * 0.14 : time;    // gentle swing on off-16ths
    const brk = mus.sec === 'break', key = mus.key, tones = mus.tones;
    if (mus.phraseOn && mus.motif) melodyStep(ts, s, menu, I, sx);
    if (cnt[1] >= MAX_MUSIC) return;
    // --- arpeggio (FM kalimba) ---
    if (menu) {
      if ((s & 3) === 2 && Math.random() < 0.2) {
        fmPluck(1, musOut, mtof(key.root + 24 + tones[(Math.random() * 3) | 0]), ts, 0.065, rnd(-0.4, 0.4), 0.5, 0.9, 2, 1.4);
      }
      return;
    }
    if (I > 0.12) {
      const rate = (I > 0.72 && !brk) ? 1 : 2;
      if (s % rate === 0 && Math.random() > mus.arpRest) {
        const pat = mus.arpPat, i = pat[((s / rate) | 0) % pat.length];
        const arpTones = [tones[0], tones[1], tones[2], tones[0] + 12];
        const m = wrapRange(key.root + 12, 55, 66) + arpTones[i];
        const accent = (s & 3) === 0 ? 1 : 0.7;
        const vel = (0.04 + 0.04 * I) * accent * rnd(0.85, 1.05) * (mus.sec === 'B' ? 1.2 : 1) * (brk ? 0.6 : 1);
        fmPluck(1, musOut, mtof(m), ts, vel, (s & 2) ? 0.3 : -0.3, 0.3, 0.3 + 0.12 * (1 - I), key.mel === 'bell' ? 3 : 2, 1.1 + 1.6 * I);
      }
    }
    // --- bass ---
    if (I > 0.2 && !brk && mus.bassPat.indexOf(s) >= 0) {
      let m = wrapRange(key.root - 12 + tones[0], 36, 50);
      if (s >= 8 && Math.random() < 0.25) m = wrapRange(m + 7, 36, 52);
      bassNote(mtof(m), ts, sx * (s === 0 ? 4 : 2.5), (0.05 + 0.02 * I) * clamp((I - 0.2) / 0.15, 0, 1));
    }
    // --- light hand percussion ---
    if (I > 0.28) {
      const dense = I > 0.7 && !brk;
      if ((s & 1) === 0 || dense) {
        const v = (s & 1) ? 0.016 : ((s & 3) === 2 ? 0.042 : 0.028);
        shaker(ts, v * (0.8 + 0.4 * I) * rnd(0.8, 1.1));
      }
    }
    if (brk) return;
    const e = mus.energy;
    if (I > 0.45 && (s === 0 || s === 8 || (I > 0.7 && e > 0.6 && s === 10))) kick(time, 0.2 + 0.1 * I);
    if (I > 0.6 && mus.handPat.indexOf(s) >= 0) handDrum(ts, (s % 8 === 6) ? 190 : 255, 0.07 + 0.05 * I, (s & 4) ? 0.35 : -0.35);
    if (I > 0.82 && e > 0.5) {
      const clave = (mus.bar & 1) ? [4, 8] : [0, 6, 12];
      if (clave.indexOf(s) >= 0) wood(1, musOut, ts, 0.035, 0.5, 1650);
    }
  }

  // Restart arrangement at a fresh bar (on start / state change).
  function restartPhrase(t) {
    // never before steps already queued by the lookahead (would double-trigger / flam the first beat)
    mus.idle = false; mus.step = 0; mus.bar = 0; mus.next = Math.max(t + 0.06, mus.next);
    mus.chordBars = 0; mus.prog = null; mus.motif = null; mus.secBars = 8; mus.sec = 'A'; mus.secCount = 0;
    if (mus.state === 'play') mus.bpm = 92 + 32 * scene.intensity; else mus.bpm = 84;
    if (mus.pendingKey !== mus.keyIdx || !mus.mel) setKey(mus.pendingKey);
  }

  function musicStart() {
    if (mus.on) return;
    mus.on = true;
    const t = ctx.currentTime;
    mus.next = 0; // fresh start: nothing of ours is queued
    mus.pendingKey = clamp(scene.biome | 0, 0, 4);
    setKey(mus.pendingKey);
    restartPhrase(t);
    if (mus.state === 'over') mus.idle = true;
    glide(musOut.in.gain, 1, 0.04, t); glide(musOut.send.gain, 1, 0.04, t);
  }

  function musicStop() {
    mus.on = false;
    const t = ctx.currentTime;
    glide(musOut.in.gain, 0, 0.25, t); glide(musOut.send.gain, 0, 0.45, t);
    if (mus.padG) { hold(mus.padG.gain, t); mus.padG.gain.setTargetAtTime(0, t, 0.3); mus.padG = null; }
  }

  // 'over': gentle resolving tonic chord + falling bell figure, then near silence.
  function musicOver() {
    mus.idle = true;
    const t = ctx.currentTime + 0.05, key = mus.key;
    if (mus.padG) { hold(mus.padG.gain, t); mus.padG.gain.setTargetAtTime(0, t, 0.25); }
    mus.tones = chordTones(key, 0, 5);
    padChord(t, 2.6, 0.15, true);
    mus.padG = null;
    const top = key.root + 24, tn = mus.tones;
    const fig = [tn[4], tn[2], tn[1], tn[0]];
    for (let i = 0; i < fig.length; i++) {
      bell(1, musOut, mtof(top + fig[i]), t + 0.15 + i * 0.26, 0.055 * (1 - i * 0.12), (i % 2 ? 0.25 : -0.25), 0.6, i === 3 ? 3.2 : 1.6);
    }
    bassNote(mtof(wrapRange(key.root - 12, 36, 50)), t + 0.9, 2.2, 0.04);
  }

  function setMusicState(st) {
    if (st !== 'menu' && st !== 'play' && st !== 'over') return;
    if (st === mus.state) return;
    mus.state = st;
    if (!ready || !mus.on) return;
    if (st === 'over') musicOver();
    else restartPhrase(ctx.currentTime);
  }

  // ==================================================================
  // SOUND EFFECTS — all start at ctx.currentTime (no scheduling delay)
  // ==================================================================
  const getMel = (key) => key._mel || (key._mel = melNotes(key));
  const SFX = () => buses.sfx;

  // Paddle stroke: band-passed noise with a falling resonance + low 'thwump' + tiny drips.
  function sfxStroke(pan, strength) {
    if (cnt[0] >= MAX_SFX + 6) return; // the core control feedback gets priority headroom over decorative sfx
    const t = ctx.currentTime, s = clamp(strength, 0, 1), n = [], srcs = [];
    const v = (0.22 + 0.4 * s) * 1.6;
    const mix = mkGain(1, n);
    // 1) the splash 'sploosh'
    const n1 = mkNoise(noiseW, t, 0.34, n, rnd(0.9, 1.12));
    const bp = mkFilt('bandpass', 1600, rnd(2.5, 4.5), n), g1 = mkGain(0, n);
    const f0 = rnd(1250, 2000) * (0.9 + 0.25 * s);
    bp.frequency.setValueAtTime(f0, t);
    bp.frequency.exponentialRampToValueAtTime(rnd(300, 470), t + rnd(0.1, 0.16));
    g1.gain.setValueAtTime(0, t); g1.gain.linearRampToValueAtTime(v, t + 0.006);
    g1.gain.setTargetAtTime(0, t + 0.014, rnd(0.045, 0.07));
    n1.connect(bp); bp.connect(g1); g1.connect(mix); srcs.push(n1);
    // 2) displaced-water body
    const n2 = mkNoise(noiseP, t, 0.22, n), lp = mkFilt('lowpass', rnd(380, 520), 1.4, n), g2 = mkGain(0, n);
    envAD(g2.gain, t, 0.008, v * 1.3, rnd(0.09, 0.14));
    n2.connect(lp); lp.connect(g2); g2.connect(mix); srcs.push(n2);
    // 3) drip tail (1-2 tiny bubbles)
    const drips = Math.random() < 0.55 ? 2 : 1;
    for (let i = 0; i < drips; i++) {
      const tb = t + rnd(0.1, 0.26), fb = rnd(700, 1500);
      const o = mkOsc('sine', fb, n), gb = mkGain(0, n);
      o.frequency.setValueAtTime(fb, tb); o.frequency.exponentialRampToValueAtTime(fb * rnd(1.6, 2.4), tb + 0.045);
      envAD(gb.gain, tb, 0.003, v * rnd(0.08, 0.14), 0.06);
      o.connect(gb); gb.connect(mix); o.start(tb); o.stop(tb + 0.1); srcs.push(o);
    }
    route(mix, SFX(), clamp(pan, -1, 1) * 0.7, 0.12, n);
    voice(0, srcs, n);
  }

  // Gate passed: marimba 'tok' climbing a pentatonic ladder with the streak.
  function sfxGate(streak) {
    if (cnt[0] >= MAX_SFX + 6) return; // scoring feedback: priority headroom too
    const key = currentKey(), mel = getMel(key), t = ctx.currentTime;
    const k = Math.max(0, streak | 0), step = k % 10, lap = Math.floor(k / 10);
    const idx = Math.min(3 + step, mel.length - 1);
    const f = mtof(mel[idx]), pan = rnd(-0.2, 0.2);
    marimba(0, SFX(), f, t, 0.4, pan, 0.25, 0.75, true);
    if (step % 5 === 4) marimba(0, SFX(), mtof(mel[Math.min(idx + 2, mel.length - 1)]), t + 0.07, 0.2, -pan, 0.3, 0.6, false);
    if (lap > 0 || step === 9) bell(0, SFX(), f * 2, t + 0.035, 0.07 + 0.02 * Math.min(lap, 3), -pan, 0.45, 0.9);
  }

  function ping(t, f, vel, pan) { // tiny sine glint
    const n = [], o = mkOsc('sine', f, n), g = mkGain(0, n);
    envAD(g.gain, t, 0.002, vel, rnd(0.12, 0.25));
    o.connect(g); route(g, SFX(), pan, 0.5, n);
    o.start(t); o.stop(t + 0.3);
    voice(0, [o], n);
  }

  // Star: three quick rising bell notes + shimmer.
  function sfxStar() {
    if (cnt[0] >= MAX_SFX + 4) return;
    const key = currentKey(), mel = getMel(key), t = ctx.currentTime;
    const b = 5 + ((Math.random() * 2) | 0);
    for (let i = 0; i < 3; i++) {
      const m = mel[Math.min(b + i * 2, mel.length - 1)] + 12;
      bell(0, SFX(), mtof(m), t + i * 0.055, 0.15, -0.3 + i * 0.3, 0.35, 0.55);
    }
    for (let i = 0; i < 5; i++) ping(t + 0.12 + i * rnd(0.035, 0.07), rnd(4000, 8000), rnd(0.025, 0.05), rnd(-0.8, 0.8));
    const n = [], s = mkNoise(noiseW, t + 0.05, 0.6, n), hp = mkFilt('highpass', 7500, 0.7, n), g = mkGain(0, n);
    g.gain.setValueAtTime(0, t + 0.05); g.gain.linearRampToValueAtTime(0.06, t + 0.12);
    g.gain.setTargetAtTime(0, t + 0.14, 0.1);
    s.connect(hp); hp.connect(g); route(g, SFX(), 0, 0.4, n);
    voice(0, [s], n);
  }

  // Panned noise sweep helper (whoosh). Returns nothing; registers its own voice.
  function whoosh(t, dur, f0, fPeak, f1, peakAt, vel, q, panFrom, panTo, send) {
    const n = [], s = mkNoise(noiseW, t, dur + 0.05, n), bp = mkFilt('bandpass', f0, q, n), g = mkGain(0, n);
    bp.frequency.setValueAtTime(f0, t);
    bp.frequency.exponentialRampToValueAtTime(fPeak, t + peakAt);
    if (f1) bp.frequency.exponentialRampToValueAtTime(f1, t + dur);
    g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(vel, t + peakAt);
    g.gain.setTargetAtTime(0, t + peakAt + 0.01, Math.max(0.02, (dur - peakAt) / 4));
    s.connect(bp); bp.connect(g);
    if (canPan) {
      const p = ctx.createStereoPanner(); n.push(p);
      p.pan.setValueAtTime(panFrom, t); p.pan.linearRampToValueAtTime(panTo, t + dur);
      g.connect(p); p.connect(SFX().in);
      if (send > 0) { const sg = mkGain(send, n); p.connect(sg); sg.connect(SFX().send); }
    } else route(g, SFX(), 0, send, n);
    voice(0, [s], n);
  }

  function sfxNearMiss() {
    if (cnt[0] >= MAX_SFX) return;
    const d = Math.random() < 0.5 ? -1 : 1;
    whoosh(ctx.currentTime, 0.32, 600, rnd(2400, 3200), 900, 0.09, 1.0, 1.8, -0.7 * d, 0.7 * d, 0.15);
  }

  // Current reversal: rising whoosh sweeping across the stereo field + sub swell + soft landing thump.
  function sfxFlip() {
    const t = ctx.currentTime, d = Math.random() < 0.5 ? -1 : 1;
    whoosh(t, 0.8, 220, 4800, 0, 0.7, 0.9, 1.3, -0.85 * d, 0.85 * d, 0.4);
    const n = [], o = mkOsc('sine', 46, n), o2 = mkOsc('triangle', 92, n), g = mkGain(0, n), g2 = mkGain(0.25, n);
    o.frequency.setValueAtTime(46, t); o.frequency.exponentialRampToValueAtTime(74, t + 0.7);
    o2.frequency.setValueAtTime(92, t); o2.frequency.exponentialRampToValueAtTime(148, t + 0.7);
    g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(0.2, t + 0.62);
    g.gain.setTargetAtTime(0, t + 0.7, 0.08);
    o.connect(g); o2.connect(g2); g2.connect(g); route(g, SFX(), 0, 0.2, n);
    o.start(t); o2.start(t); o.stop(t + 1.2); o2.stop(t + 1.2);
    // thump at the turn
    const th = mkOsc('sine', 95, n), tg = mkGain(0, n), tt = t + 0.72;
    th.frequency.setValueAtTime(95, tt); th.frequency.exponentialRampToValueAtTime(40, tt + 0.16);
    envAD(tg.gain, tt, 0.004, 0.3, 0.3);
    th.connect(tg); route(tg, SFX(), 0, 0.3, n);
    th.start(tt); th.stop(tt + 0.4);
    voice(0, [o, o2, th], n);
  }

  // Collision: wooden crack + hull thud + big wide splash + low boom; music ducks.
  function sfxCrash() {
    const t = ctx.currentTime;
    duckBus(buses.music, 0.22, 0.02, 0.5, 0.9);
    const n = [], srcs = [], out = mkGain(1, n);
    route(out, SFX(), 0, 0.28, n);
    // 1) crack: three tight band-passed noise snaps
    for (let i = 0; i < 3; i++) {
      const tt = t + i * rnd(0.012, 0.03);
      const s = mkNoise(noiseW, tt, 0.09, n), bp = mkFilt('bandpass', rnd(1300, 2700), rnd(2, 5), n), g = mkGain(0, n);
      envAD(g.gain, tt, 0.001, 0.55 - i * 0.13, 0.06);
      s.connect(bp); bp.connect(g); g.connect(out); srcs.push(s);
    }
    // 2) hollow hull thud
    const th = mkOsc('sine', 160, n), th2 = mkOsc('triangle', 95, n), tg = mkGain(0, n);
    th.frequency.setValueAtTime(160, t); th.frequency.exponentialRampToValueAtTime(52, t + 0.18);
    th2.frequency.setValueAtTime(95, t); th2.frequency.exponentialRampToValueAtTime(45, t + 0.2);
    envAD(tg.gain, t, 0.004, 0.5, 0.36);
    th.connect(tg); th2.connect(tg); tg.connect(out);
    th.start(t); th2.start(t); th.stop(t + 0.45); th2.stop(t + 0.45); srcs.push(th, th2);
    // 3) big splash, two decorrelated layers panned wide, lowpass sweeping down
    for (const side of [-0.55, 0.55]) {
      const s = mkNoise(noiseW, t, 1.5, n, rnd(0.9, 1.1)), lp = mkFilt('lowpass', 7000, 0.7, n), g = mkGain(0, n);
      lp.frequency.setValueAtTime(rnd(6000, 8000), t + 0.01); lp.frequency.exponentialRampToValueAtTime(rnd(600, 800), t + 1.0);
      g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(0.3, t + 0.02);
      g.gain.setTargetAtTime(0, t + 0.06, 0.28);
      s.connect(lp); lp.connect(g); route(g, SFX(), side, 0.3, n); srcs.push(s);
    }
    // 4) low boom + rumble
    const bo = mkOsc('sine', 62, n), bg = mkGain(0, n);
    bo.frequency.setValueAtTime(62, t); bo.frequency.exponentialRampToValueAtTime(34, t + 1.0);
    envAD(bg.gain, t, 0.01, 0.5, 1.3);
    bo.connect(bg); bg.connect(out); bo.start(t); bo.stop(t + 1.5); srcs.push(bo);
    const rb = mkNoise(noiseB, t, 1.2, n), rl = mkFilt('lowpass', 170, 0.7, n), rg = mkGain(0, n);
    envAD(rg.gain, t, 0.01, 0.6, 0.9);
    rb.connect(rl); rl.connect(rg); rg.connect(out); srcs.push(rb);
    // 5) droplets falling back
    for (let i = 0; i < 4; i++) {
      const tb = t + rnd(0.35, 1.1), fb = rnd(600, 1400), o = mkOsc('sine', fb, n), gb = mkGain(0, n);
      o.frequency.setValueAtTime(fb, tb); o.frequency.exponentialRampToValueAtTime(fb * rnd(1.6, 2.4), tb + 0.05);
      envAD(gb.gain, tb, 0.003, rnd(0.03, 0.06), 0.07);
      o.connect(gb); route(gb, SFX(), rnd(-0.8, 0.8), 0.2, n);
      o.start(tb); o.stop(tb + 0.12); srcs.push(o);
    }
    voice(0, srcs, n);
  }

  function brass(m, t, vel, dur, pan) { // filtered detuned saws, for the fanfare
    const n = [], f = mtof(m), o1 = mkOsc('sawtooth', f, n), o2 = mkOsc('sawtooth', f, n);
    o1.detune.value = -6; o2.detune.value = 8;
    const lp = mkFilt('lowpass', 500, 1.5, n), g = mkGain(0, n);
    lp.frequency.setValueAtTime(400, t); lp.frequency.linearRampToValueAtTime(3000, t + 0.06);
    lp.frequency.setTargetAtTime(1400, t + 0.06, 0.2);
    g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(vel, t + 0.025);
    g.gain.setTargetAtTime(vel * 0.7, t + 0.03, 0.15); g.gain.setTargetAtTime(0, t + dur, 0.12);
    o1.connect(lp); o2.connect(lp); lp.connect(g); route(g, SFX(), pan, 0.35, n);
    const end = t + dur + 0.7; o1.start(t); o2.start(t); o1.stop(end); o2.stop(end);
    voice(0, [o1, o2], n);
  }

  // New personal best: triplet pickup into a sustained tonic chord + sparkles (in the current key).
  function sfxRecord() {
    const t = ctx.currentTime, key = currentKey(), tn = chordTones(key, 0, 3);
    const base = wrapRange(key.root + 12, 57, 68);
    duckBus(buses.music, 0.3, 0.03, 1.3, 0.7);
    for (let i = 0; i < 3; i++) brass(base + tn[i], t + i * 0.1, 0.12, 0.1, -0.2 + i * 0.2);
    const tc = t + 0.32, chord = [tn[0], tn[1], tn[2], tn[0] + 12];
    for (let i = 0; i < chord.length; i++) brass(base + chord[i], tc, 0.085, 1.1, -0.3 + i * 0.2);
    marimba(0, SFX(), mtof(base + tn[0] + 12), tc, 0.2, 0, 0.3, 1.0, true);
    for (let i = 0; i < 4; i++) bell(0, SFX(), mtof(base + chord[i] + 24), tc + 0.06 + i * 0.07, 0.06, rnd(-0.5, 0.5), 0.5, 0.8);
  }

  function sfxUi(kind) {
    if (cnt[0] >= MAX_SFX) return;
    const t = ctx.currentTime, mel = getMel(currentKey());
    if (kind === 'back') {
      marimba(0, SFX(), mtof(mel[7]), t, 0.16, 0, 0.1, 0.22, false);
      marimba(0, SFX(), mtof(mel[5]), t + 0.07, 0.14, 0, 0.1, 0.3, false);
    } else if (kind === 'open') {
      marimba(0, SFX(), mtof(mel[5]), t, 0.14, 0, 0.12, 0.22, false);
      marimba(0, SFX(), mtof(mel[7]), t + 0.06, 0.16, 0, 0.15, 0.35, false);
    } else if (kind === 'toggle') {
      wood(0, SFX(), t, 0.28, 0, 1900);
    } else if (kind === 'error') {
      const n = [], srcs = [], lp = mkFilt('lowpass', 900, 0.7, n), g = mkGain(0, n);
      for (let i = 0; i < 2; i++) {
        const tt = t + i * 0.12, o = mkOsc('triangle', 196, n), o2 = mkOsc('triangle', 207, n);
        o.connect(lp); o2.connect(lp); o.start(tt); o2.start(tt); o.stop(tt + 0.1); o2.stop(tt + 0.1); srcs.push(o, o2);
        g.gain.setValueAtTime(0, tt); g.gain.linearRampToValueAtTime(0.13, tt + 0.006);
        g.gain.setTargetAtTime(0, tt + 0.06, 0.012);
      }
      lp.connect(g); route(g, SFX(), 0, 0, n);
      voice(0, srcs, n);
    } else { // 'click'
      const n = [], o = mkOsc('sine', 1250, n), g = mkGain(0, n);
      o.frequency.setValueAtTime(1250, t); o.frequency.exponentialRampToValueAtTime(900, t + 0.03);
      envAD(g.gain, t, 0.002, 0.22, 0.05);
      o.connect(g); route(g, SFX(), 0, 0, n);
      o.start(t); o.stop(t + 0.08);
      voice(0, [o], n);
    }
  }

  function sfxCountdown(k) {
    const t = ctx.currentTime, mel = getMel(currentKey());
    if (k > 0) bell(0, SFX(), mtof(mel[5]), t, 0.2, 0, 0.2, 0.5);
    else {
      bell(0, SFX(), mtof(mel[10]), t, 0.18, 0, 0.35, 1.1);
      marimba(0, SFX(), mtof(mel[5]), t, 0.25, 0, 0.25, 0.9, true);
      marimba(0, SFX(), mtof(mel[8]), t + 0.01, 0.14, 0.2, 0.25, 0.8, false);
    }
  }

  // ==================================================================
  // PUBLIC API — every method is exception-safe and a no-op before unlock()
  // ==================================================================
  const live = () => ready && ctx.state !== 'closed';
  // One-shots: a fresh context reports 'suspended' until its audio thread starts (async), so sounds triggered by
  // the unlocking gesture itself are allowed for a moment. But while the context is really suspended/interrupted
  // its clock is frozen: everything triggered would pile up at one instant and blast out together on resume.
  const canPlay = () => {
    if (!live()) return false;
    if (ctx.state === 'running' || opts.context) return true;
    return wallNow() - unlockAt < 1500 && cnt[0] < 6;
  };
  const api = {
    unlock: safe(unlock),
    setVolumes: safe(function (o) {
      if (!o || typeof o !== 'object') return;
      for (const k of ['master', 'sfx', 'music', 'ambience']) {
        if (typeof o[k] === 'number' && isFinite(o[k])) vol[k] = clamp(o[k], 0, 1);
      }
      if (live()) applyLevels(0.06);
    }),
    setMuted: safe(function (m) { muted = !!m; if (live()) applyLevels(0.08); }),
    setPaused: safe(function (p) { p = !!p; if (p === paused) return; paused = p; if (live()) applyLevels(); }),
    startAmbience: safe(function () { ambWanted = true; if (live()) syncLayers(); }),
    stopAmbience: safe(function () { ambWanted = false; if (live()) ambStop(); }),
    setScene: safe(function (sc) {
      if (!sc || typeof sc !== 'object') return;
      const b = Math.round(num(sc.biome, scene.biome));
      scene.biome = ((b % 5) + 5) % 5;
      scene.night = clamp(num(sc.night, scene.night), 0, 1);
      scene.intensity = clamp(num(sc.intensity, scene.intensity), 0, 1);
      scene.speed = clamp(num(sc.speed, scene.speed), 0, 1);
      if (live()) applyScene(false);
    }),
    startMusic: safe(function () { musicWanted = true; if (live()) syncLayers(); }),
    stopMusic: safe(function () { musicWanted = false; if (live()) musicStop(); }),
    setMusicState: safe(function (st) { setMusicState(String(st)); }),
    stroke: safe(function (pan, strength) { if (canPlay()) sfxStroke(num(pan, 0), num(strength, 0.7)); }),
    gate: safe(function (streak) { if (canPlay()) sfxGate(num(streak, 0)); }),
    star: safe(function () { if (canPlay()) sfxStar(); }),
    nearMiss: safe(function () { if (canPlay()) sfxNearMiss(); }),
    flip: safe(function () { if (canPlay() && cnt[0] < MAX_SFX + 8) sfxFlip(); }),
    crash: safe(function () { if (canPlay() && cnt[0] < MAX_SFX + 8) sfxCrash(); }),
    record: safe(function () { if (canPlay() && cnt[0] < MAX_SFX + 8) sfxRecord(); }),
    ui: safe(function (kind) { if (canPlay()) sfxUi(String(kind || 'click')); }),
    countdown: safe(function (k) { if (canPlay() && cnt[0] < MAX_SFX + 4) sfxCountdown(num(k, 0)); }),
    isUnlocked: function () { return !!(ready && ctx && ctx.state === 'running'); },
    stats: function () {
      return {
        available: true, unlocked: ready, state: ctx ? ctx.state : 'none',
        voices: { sfx: cnt[0], music: cnt[1], ambience: cnt[2] },
        music: { on: mus.on, state: mus.state, bpm: Math.round(mus.bpm), key: mus.keyIdx, section: mus.sec },
        ambience: amb.on, errors: errors, lastError: lastError ? String(lastError && lastError.stack || lastError) : null,
      };
    },
  };
  if (opts.manualTick) api.tick = safe(tick); // offline rendering / tests drive the scheduler
  return api;
}

;
// ── game.js ──
// ═══════════════════════════════════════════════════════════════════════════
//  GAME — rendering, input, UI, challenges. Everything visual lives here;
//  nothing in this section can influence the deterministic simulation.
// ═══════════════════════════════════════════════════════════════════════════
(() => {
'use strict';

const REVEAL = 600;            // world units visible ahead of the boat — identical on every screen
const CW = 512;                // land chunk width (world units)
const TICK_MS = 1000 / TICK_RATE;
const TAU = Math.PI * 2;
const $ = id => document.getElementById(id);
const sm = t => { t = clamp(t, 0, 1); return t * t * (3 - 2 * t); };
const hexRgb = h => [parseInt(h.slice(1, 3), 16), parseInt(h.slice(3, 5), 16), parseInt(h.slice(5, 7), 16)];
const rgba = (h, a) => { const c = hexRgb(h); return `rgba(${c[0]},${c[1]},${c[2]},${a})`; };
const mixHex = (a, b, t) => {
  const x = hexRgb(a), y = hexRgb(b);
  const c = i => Math.round(x[i] + (y[i] - x[i]) * t).toString(16).padStart(2, '0');
  return '#' + c(0) + c(1) + c(2);
};
const fmtNum = n => String(n);

// ─── Storage ───────────────────────────────────────────────────────────────
// ─── Native (Capacitor) bridge — every call is optional; the browser build simply skips it ───
const Cap = window.Capacitor;
// Public web version: anyone can open a challenge link without installing anything.
const WEB_URL = 'https://pitrs1988.github.io/pereje-hra/';
const isNative = !!(Cap && typeof Cap.isNativePlatform === 'function' && Cap.isNativePlatform());
const NP = isNative ? (Cap.Plugins || {}) : {};
const nativeCall = (plugin, method, arg) => {
  try { const p = NP[plugin]; if (p && typeof p[method] === 'function') { const r = p[method](arg); if (r && r.catch) r.catch(() => {}); return r; } } catch { /* ignore */ }
  return null;
};
const Native = {
  haptic(kind) {
    if (!S.haptics) return;
    if (isNative) {
      if (kind === 'record') nativeCall('Haptics', 'notification', { type: 'SUCCESS' });
      else nativeCall('Haptics', 'impact', { style: kind === 'crash' ? 'HEAVY' : kind === 'flip' ? 'MEDIUM' : 'LIGHT' });
    } else if (navigator.vibrate) {
      try { navigator.vibrate(kind === 'crash' ? [40, 30, 80] : kind === 'record' ? [20, 40, 20] : kind === 'flip' ? 18 : 6); } catch { /* ignore */ }
    }
  },
  canShare: () => isNative ? !!NP.Share : !!navigator.share,
  share(text) {
    if (isNative) return nativeCall('Share', 'share', { title: 'PEŘEJE — výzva', text, dialogTitle: 'Vyzvat kamarády' });
    return navigator.share ? navigator.share({ title: 'PEŘEJE — výzva', text }).catch(() => {}) : null;
  },
  copy(text) { return isNative && NP.Clipboard ? NP.Clipboard.write({ string: text }) : null; },
  paste() { return isNative && NP.Clipboard ? NP.Clipboard.read().then(r => (r && r.value) || '') : null; },
  persist(key, json) { if (isNative) nativeCall('Preferences', 'set', { key: 'pereje.v1.' + key, value: json }); },
};

const Store = {
  get(k, d) { try { const v = localStorage.getItem('pereje.v1.' + k); return v ? JSON.parse(v) : d; } catch { return d; } },
  set(k, v) {
    const json = JSON.stringify(v);
    try { localStorage.setItem('pereje.v1.' + k, json); } catch { /* private mode */ }
    Native.persist(k, json);   // iOS may purge WebView storage; the native copy survives
  },
};
const reducedMotion = (() => { try { return matchMedia('(prefers-reduced-motion: reduce)').matches; } catch { return false; } })();
const DEFAULTS = { name: '', sfx: 0.8, music: 0.5, amb: 0.7, ghosts: true, shake: !reducedMotion, haptics: true, hitbox: false, quality: 'auto', tutorial: true, level: 1 };
const S = Object.assign({}, DEFAULTS, Store.get('settings', {}));
const saveSettings = () => Store.set('settings', S);
// Records are kept per difficulty level: a kids' score never competes with a pro's.
const blankLevelRec = () => ({ free: { best: 0 }, seeds: {}, daily: {}, rivers: {} });
const REC = Object.assign({ L: [], challenges: [], stats: { runs: 0, gates: 0, stars: 0, strokes: 0, dist: 0, time: 0 } }, Store.get('records2', {}));
for (let i = 0; i < 3; i++) REC.L[i] = Object.assign(blankLevelRec(), REC.L[i] || {});
// Old (rules v1) records cannot be verified under the new physics; only the lifetime stats carry over.
if (!Store.get('records2', null)) { const old = Store.get('records', null); if (old && old.stats) Object.assign(REC.stats, old.stats); }
const LR = lv => REC.L[lv === 0 || lv === 2 ? lv : 1];
const levelName = lv => levelOf(lv).name;
const seedHex = s => (s >>> 0).toString(16).padStart(8, '0');
const saveRecords = () => {
  // Keep storage bounded, but never evict a best run that another table points to.
  if (REC.challenges.length > 40) REC.challenges.length = 40;
  REC.L.forEach((T, lv) => {
    const keep = new Set([
      ...Object.keys(T.rivers).map(n => seedHex(riverSeed(n))),
      ...Object.keys(T.daily).sort().slice(-14).map(k => seedHex(dailySeed(k))),
      ...REC.challenges.filter(h => (h.level ?? 1) === lv).map(h => h.seed),
    ]);
    const ev = Object.keys(T.seeds).filter(k => !keep.has(k));
    if (ev.length > 60) ev.sort((a, b) => (T.seeds[a].at || 0) - (T.seeds[b].at || 0)).slice(0, ev.length - 60).forEach(k => delete T.seeds[k]);
  });
  Store.set('records2', REC);
};
const playerName = () => (S.name || '').trim() || 'Anonym';

// ─── Audio (defensive wrapper) ─────────────────────────────────────────────
const A = (() => {
  let raw = null;
  try { raw = typeof createAudioEngine === 'function' ? createAudioEngine() : null; } catch (e) { console.warn('audio', e); }
  return new Proxy({}, { get: (_, k) => (...a) => { try { return raw && typeof raw[k] === 'function' ? raw[k](...a) : undefined; } catch (e) { /* never break the game for audio */ } } });
})();
let audioReady = false;
function unlockAudio() {
  if (audioReady) return;
  audioReady = true;
  A.unlock();
  applyVolumes();
  A.startAmbience();
  A.startMusic();
  A.setMusicState(G.state === 'play' ? 'play' : 'menu');
}
function applyVolumes() { A.setVolumes({ master: 1, sfx: S.sfx, music: S.music, ambience: S.amb }); }

// ─── Biomes (land art direction) ───────────────────────────────────────────
const BIOMES = [
  { name: 'Lesní potok', sub: 'svítání', ground: '#58863b', ground2: '#76a54b', dark: '#2f5527', shore: '#cdb98c', wet: '#6c5a41',
    grass: ['#86b553', '#4c7a2e', '#9cc862'], flowers: ['#fff6dc', '#ffd34d', '#f7a1c4', '#b9a7ff'],
    canopy: ['#3f7a31', '#56913a', '#2d5d27', '#6aa646'], trees: [['tree', .5], ['pine', .2], ['bush', .3]], density: .55,
    rock: { base: '#8f949a', light: '#d3d7da', dark: '#4b5057', moss: '#6e9440', mossAmt: .55 },
    wood: { bark: '#6e4b2c', dark: '#3d2915', light: '#9a7550', end: '#d6b27c', ring: '#a9834f' },
    deck: '#8b5e36', grade: '#ffc49b', gradeA: .2, dim: 0, night: 0, rays: 1, amb: 'leaves', mist: '#e9f2ee', leaf: ['#d9a33c', '#c96f2d', '#9cbf4a'] },
  { name: 'Rudý kaňon', sub: 'západ slunce', ground: '#b75a31', ground2: '#d27c46', dark: '#7a3119', shore: '#e3ab78', wet: '#7a4529',
    grass: ['#9a913f', '#77702d', '#b0a64f'], flowers: ['#ffd36b', '#ff9a52'],
    canopy: ['#5f6b2c', '#7a8236', '#4a5524', '#8d9440'], trees: [['shrub', .55], ['tree', .15], ['boulder', .3]], density: .35,
    rock: { base: '#b0582f', light: '#eb9a68', dark: '#5f2612', moss: null, mossAmt: 0 },
    wood: { bark: '#7a5432', dark: '#432c18', light: '#a77e55', end: '#deb985', ring: '#b08a58' },
    deck: '#7d5434', grade: '#ff8a45', gradeA: .26, dim: .05, night: 0.08, rays: 0, amb: 'dust', mist: '#f6c8a0', strata: 1, leaf: ['#c9a25a'] },
  { name: 'Džungle', sub: 'soumrak', ground: '#2c5a2b', ground2: '#3d7737', dark: '#14321a', shore: '#6d5a3a', wet: '#3e3020',
    grass: ['#52a03f', '#2f6f2c', '#72c04f'], flowers: ['#ff4fa3', '#ffb13d', '#ffffff'],
    canopy: ['#23602c', '#2f7a35', '#1a4a22', '#3f9442'], trees: [['palm', .45], ['tree', .4], ['bush', .15]], density: .8,
    rock: { base: '#646f5c', light: '#9aab8e', dark: '#2d3a2a', moss: '#4fa03c', mossAmt: .95 },
    wood: { bark: '#5d4128', dark: '#2f2012', light: '#87623f', end: '#c49c66', ring: '#93703f' },
    deck: '#6f4b2c', grade: '#c77dff', gradeA: .16, dim: .26, night: 0.35, rays: 0, amb: 'fireflies', mist: '#bcd9c9', lily: 1, leaf: ['#4f9a3a', '#7bbf4a'] },
  { name: 'Noční les', sub: 'úplněk', ground: '#20402e', ground2: '#2b5439', dark: '#0d2116', shore: '#717886', wet: '#373d48',
    grass: ['#2f6a44', '#1f4a31', '#3f7d55'], flowers: ['#cfe3ff', '#9fc0ff'],
    canopy: ['#1c4a33', '#24603f', '#143a28', '#2e6e4a'], trees: [['pine', .75], ['tree', .1], ['bush', .15]], density: .7,
    rock: { base: '#5d6573', light: '#9aa6b8', dark: '#2a303b', moss: '#3f6a55', mossAmt: .4 },
    wood: { bark: '#5a4636', dark: '#2c2119', light: '#7d6450', end: '#b59b7b', ring: '#8a7258' },
    deck: '#5e4632', grade: '#6f8cff', gradeA: .2, dim: .5, night: 1, rays: 0, amb: 'fireflies', mist: '#93a8cf', fires: 1, leaf: ['#3f6a55'] },
  { name: 'Ledovec', sub: 'mrazivé ráno', ground: '#e3eef6', ground2: '#ffffff', dark: '#a4bfd6', shore: '#cdf0f8', wet: '#7fb4c8',
    grass: ['#c8d9e7', '#a9c1d4', '#ffffff'], flowers: [],
    canopy: ['#2f5a4c', '#3d6e5c', '#24483d', '#4a7f6b'], trees: [['snowpine', .8], ['boulder', .2]], density: .45,
    rock: { base: '#bfe7f4', light: '#ffffff', dark: '#5fa6c4', ice: 1 },
    wood: { bark: '#6b5440', dark: '#3a2c20', light: '#8f765e', end: '#cdb391', ring: '#a08668' },
    deck: '#7a6048', grade: '#bfe4ff', gradeA: .14, dim: 0, night: 0, rays: 1, amb: 'snow', mist: '#f2f9ff', snow: 1, leaf: ['#ffffff'] },
];
const FALLBACK_WATER = [
  { deep: [0.05, 0.32, 0.36], shallow: [0.30, 0.62, 0.58], bed: [0.55, 0.50, 0.36], foam: [0.95, 0.98, 0.97], sky: [0.80, 0.85, 0.92], sun: [1.0, 0.86, 0.70] },
  { deep: [0.12, 0.30, 0.28], shallow: [0.42, 0.55, 0.40], bed: [0.62, 0.42, 0.26], foam: [1.0, 0.94, 0.86], sky: [1.0, 0.70, 0.50], sun: [1.0, 0.62, 0.32] },
  { deep: [0.06, 0.20, 0.14], shallow: [0.22, 0.38, 0.22], bed: [0.30, 0.28, 0.16], foam: [0.88, 0.94, 0.86], sky: [0.62, 0.50, 0.70], sun: [1.0, 0.70, 0.55] },
  { deep: [0.02, 0.06, 0.14], shallow: [0.08, 0.16, 0.26], bed: [0.16, 0.18, 0.22], foam: [0.70, 0.80, 0.92], sky: [0.20, 0.26, 0.42], sun: [0.80, 0.88, 1.0] },
  { deep: [0.04, 0.38, 0.50], shallow: [0.40, 0.80, 0.86], bed: [0.70, 0.80, 0.86], foam: [1.0, 1.0, 1.0], sky: [0.86, 0.93, 1.0], sun: [1.0, 0.97, 0.92] },
];
const WPAL = (typeof WATER_PALETTES !== 'undefined' && Array.isArray(WATER_PALETTES) && WATER_PALETTES.length >= 5) ? WATER_PALETTES : FALLBACK_WATER;
const WCLAR = (typeof WATER_CLARITY !== 'undefined' && Array.isArray(WATER_CLARITY) && WATER_CLARITY.length >= 5) ? WATER_CLARITY : [0.9, 0.6, 0.3, 0.55, 1.0];

// Smooth biome blend around biome edges (visual only)
function biomeMix(course, x) {
  const e = course.biomeEdges;
  const i = course._countLE(e, x);
  const W = 320;
  // distance to nearest edge
  let a = i % 5, b = a, t = 0;
  if (i < e.length && e[i] - x < W) { b = (i + 1) % 5; t = 0.5 - (e[i] - x) / (2 * W); }
  else if (i > 0 && x - e[i - 1] < W) { a = (i - 1) % 5; b = i % 5; t = 0.5 + (x - e[i - 1]) / (2 * W); }
  return { a, b, t: sm(t) };
}

// ─── Canvases & view ───────────────────────────────────────────────────────
const cvW = $('cvWater'), cv = $('cvScene');
const ctx = cv.getContext('2d');
let water = null;
try { water = typeof createWaterRenderer === 'function' ? createWaterRenderer(cvW) : null; } catch (e) { console.warn('water renderer failed', e); water = null; }
// The water canvas is composited into the scene canvas every frame, so it stays invisible itself.
cvW.style.visibility = 'hidden';
const lightCv = document.createElement('canvas'), lctx = lightCv.getContext('2d');
const vigCv = document.createElement('canvas');
const V = { w: 1, h: 1, dpr: 1, s: 1, visW: 1, visH: 1, boatOff: 140, camX: 0, camY: 0, q: 2, sx: 0, sy: 0 };
let qualityLevel = S.quality === 'low' ? 0 : S.quality === 'medium' ? 1 : 2;

let layoutKey = '', viewKey = '';
function layout(force) {
  const w = Math.max(1, window.innerWidth), h = Math.max(1, window.innerHeight);
  const maxDpr = qualityLevel === 2 ? 2 : qualityLevel === 1 ? 1.5 : 1;
  // Pixel budget: a big or high-DPI fullscreen window renders at a capped internal resolution and the
  // browser scales it up, so frame time stops growing with the monitor (about 1080p worth of pixels at most).
  const BUDGET = [0.9e6, 1.5e6, 2.1e6][qualityLevel];
  let dpr = Math.min(window.devicePixelRatio || 1, maxDpr);
  if (w * h * dpr * dpr > BUDGET) dpr = Math.sqrt(BUDGET / (w * h));
  const key = [w, h, dpr.toFixed(3), qualityLevel].join('|');
  if (key === layoutKey && !force) return;
  layoutKey = key;
  V.w = w; V.h = h; V.dpr = dpr;
  V.s = Math.min(h / 700, w / 740);
  V.visW = w / V.s; V.visH = h / V.s;
  V.boatOff = clamp(V.visW - REVEAL, 140, Math.max(140, V.visW * 0.42));
  V.camY = RIVER_H / 2 - V.visH / 2;
  cv.width = Math.round(w * V.dpr); cv.height = Math.round(h * V.dpr);
  cv.style.width = w + 'px'; cv.style.height = h + 'px';
  if (water) {
    cvW.style.width = w + 'px'; cvW.style.height = h + 'px';
    const wr = Math.min(Math.min(window.devicePixelRatio || 1, 1.5) * (qualityLevel === 2 ? 1 : qualityLevel === 1 ? 0.75 : 0.55), Math.sqrt(BUDGET * 0.6 / (w * h)));
    water.resize(w, h, wr);
  }
  const lq = Math.min(0.5, Math.sqrt(BUDGET * 0.2 / (w * h)));
  lightCv.width = Math.max(1, Math.round(w * lq)); lightCv.height = Math.max(1, Math.round(h * lq));
  vigCv.width = Math.max(1, Math.round(w / 3)); vigCv.height = Math.max(1, Math.round(h / 3));
  const vc = vigCv.getContext('2d');
  const g = vc.createRadialGradient(vigCv.width / 2, vigCv.height / 2, Math.min(vigCv.width, vigCv.height) * 0.3, vigCv.width / 2, vigCv.height / 2, Math.hypot(vigCv.width, vigCv.height) * 0.62);
  g.addColorStop(0, 'rgba(0,0,0,0)'); g.addColorStop(1, 'rgba(0,10,20,0.42)');
  vc.fillStyle = g; vc.fillRect(0, 0, vigCv.width, vigCv.height);
  // cached art only depends on scale, pixel density and the vertical framing
  const vk = [V.s.toFixed(4), Math.min(V.dpr, 1.5), V.dpr, V.camY.toFixed(2)].join('|');
  if (vk !== viewKey) { viewKey = vk; chunks.clear(); bodies.clear(); }
}

// ─── Game state ────────────────────────────────────────────────────────────
const G = {
  state: 'menu', prevState: 'menu',
  mode: 'free', seed: 0, label: '', course: null, sim: null,
  ghosts: [], taps: [], inputQ: [], t0: 0, pauseAt: 0,
  challenge: null, deadAt: 0, overAt: 0, death: null, newBest: false, bestBefore: 0,
  attract: null, attractDeadAt: 0, flowAcc: 0, curBiome: -1, lastScoreShown: -1, streak: 0,
  flipWarned: -1, recordFlag: false, runStats: null, lastRun: null,
};
let VT = 0;        // visual clock (s)
let lastNow = performance.now();
let trauma = 0, flash = 0, flashColor = '255,255,255';

function viewCourse() { return G.state === 'menu' ? (G.attract && G.attract.course) : G.course; }

// ─── Sprites & land chunks ─────────────────────────────────────────────────
const sprites = new Map();
const chunks = new Map();
let chunkCourse = null;

function seededR(seed) { let i = 0; return () => rnd(seed, i++); }

function rockPath(c, vr, v, ice) {
  const R = seededR(hash32(v, 77));
  const n = ice ? 8 + (v % 3) : 11 + (v % 5);
  const pts = [];
  for (let i = 0; i < n; i++) {
    const a = i / n * TAU + (R() - 0.5) * (ice ? 0.22 : 0.35);
    const rr = vr * (ice ? 1.0 + R() * 0.12 : 0.95 + R() * 0.12);
    pts.push([Math.cos(a) * rr, Math.sin(a) * rr]);
  }
  c.beginPath();
  if (ice) { pts.forEach((p, i) => i ? c.lineTo(p[0], p[1]) : c.moveTo(p[0], p[1])); c.closePath(); }
  else {
    const mid = (p, q) => [(p[0] + q[0]) / 2, (p[1] + q[1]) / 2];
    let m = mid(pts[n - 1], pts[0]);
    c.moveTo(m[0], m[1]);
    for (let i = 0; i < n; i++) { const p = pts[i], q = pts[(i + 1) % n], mm = mid(p, q); c.quadraticCurveTo(p[0], p[1], mm[0], mm[1]); }
    c.closePath();
  }
  return pts;
}

function paintRock(c, vr, v, B, withShadow = true) {
  const rk = B.rock, ice = !!rk.ice;
  const R = seededR(hash32(v, 991));
  if (withShadow) {
    const g = c.createRadialGradient(vr * 0.22, vr * 0.3, vr * 0.2, vr * 0.22, vr * 0.3, vr * 1.25);
    g.addColorStop(0, 'rgba(0,12,20,0.38)'); g.addColorStop(1, 'rgba(0,12,20,0)');
    c.fillStyle = g; c.beginPath(); c.arc(vr * 0.22, vr * 0.3, vr * 1.25, 0, TAU); c.fill();
  }
  const pts = rockPath(c, vr, v, ice);
  const g = c.createRadialGradient(-vr * 0.42, -vr * 0.46, vr * 0.08, -vr * 0.1, -vr * 0.1, vr * 1.25);
  g.addColorStop(0, rk.light); g.addColorStop(0.45, rk.base); g.addColorStop(1, rk.dark);
  c.fillStyle = g; c.fill();
  c.save(); c.clip();
  // facets
  const n = pts.length;
  for (let k = 0; k < 4; k++) {
    const i = Math.floor(R() * n), j = (i + 1 + Math.floor(R() * 2)) % n;
    const cx = (R() - 0.5) * vr * 0.5, cy = (R() - 0.5) * vr * 0.5;
    c.beginPath(); c.moveTo(cx, cy); c.lineTo(pts[i][0], pts[i][1]); c.lineTo(pts[j][0], pts[j][1]); c.closePath();
    const lightSide = (pts[i][0] + pts[i][1]) < 0;
    c.fillStyle = lightSide ? `rgba(255,255,255,${ice ? 0.22 : 0.09})` : `rgba(0,0,0,${ice ? 0.08 : 0.12})`;
    c.fill();
  }
  if (ice) {
    c.strokeStyle = 'rgba(255,255,255,0.75)'; c.lineWidth = vr * 0.06;
    c.beginPath(); c.moveTo(pts[n - 1][0] * 0.82, pts[n - 1][1] * 0.82);
    for (let i = 0; i < Math.ceil(n / 2); i++) c.lineTo(pts[i][0] * 0.82, pts[i][1] * 0.82);
    c.stroke();
    const ig = c.createRadialGradient(vr * 0.1, vr * 0.15, 0, vr * 0.1, vr * 0.15, vr * 0.7);
    ig.addColorStop(0, 'rgba(120,220,255,0.35)'); ig.addColorStop(1, 'rgba(120,220,255,0)');
    c.fillStyle = ig; c.fillRect(-vr, -vr, vr * 2, vr * 2);
  } else {
    // cracks
    c.strokeStyle = 'rgba(20,16,12,0.32)'; c.lineWidth = Math.max(0.6, vr * 0.035); c.lineCap = 'round';
    for (let k = 0; k < 2; k++) {
      let x = (R() - 0.5) * vr * 0.8, y = (R() - 0.5) * vr * 0.8;
      c.beginPath(); c.moveTo(x, y);
      for (let s = 0; s < 3; s++) { x += (R() - 0.5) * vr * 0.5; y += (R() - 0.5) * vr * 0.5; c.lineTo(x, y); }
      c.stroke();
    }
    // speckles
    for (let k = 0; k < 14; k++) {
      c.fillStyle = R() < 0.5 ? 'rgba(255,255,255,0.12)' : 'rgba(0,0,0,0.12)';
      c.beginPath(); c.arc((R() - 0.5) * vr * 1.6, (R() - 0.5) * vr * 1.6, vr * (0.03 + R() * 0.05), 0, TAU); c.fill();
    }
    if (rk.moss && R() < rk.mossAmt + 0.2) {
      const mc = rk.moss;
      for (let k = 0; k < 5; k++) {
        const mx = -vr * 0.35 + (R() - 0.5) * vr * 0.8, my = -vr * 0.4 + (R() - 0.5) * vr * 0.6, mr = vr * (0.18 + R() * 0.22);
        const mg = c.createRadialGradient(mx, my, 0, mx, my, mr);
        mg.addColorStop(0, rgba(mc, 0.85)); mg.addColorStop(1, rgba(mc, 0));
        c.fillStyle = mg; c.beginPath(); c.arc(mx, my, mr, 0, TAU); c.fill();
      }
    }
  }
  // wet waterline rim (bottom-right)
  const wg = c.createLinearGradient(-vr, -vr, vr, vr);
  wg.addColorStop(0.45, 'rgba(0,20,30,0)'); wg.addColorStop(1, 'rgba(0,20,30,0.45)');
  c.restore();
  rockPath(c, vr, v, ice);
  c.strokeStyle = wg; c.lineWidth = vr * 0.16; c.stroke();
  c.strokeStyle = ice ? 'rgba(40,110,150,0.55)' : 'rgba(10,10,10,0.35)'; c.lineWidth = Math.max(0.8, vr * 0.03); c.stroke();
}

// Body sprites (rocks, logs) live in a small LRU so long sessions don't hoard canvas memory.
const bodies = new Map();
function lruGet(key) { const sp = bodies.get(key); if (sp) { bodies.delete(key); bodies.set(key, sp); } return sp; }
function lruPut(key, sp) { bodies.set(key, sp); while (bodies.size > 220) bodies.delete(bodies.keys().next().value); return sp; }

function rockSprite(vr, v, biome) {
  const px = V.s * V.dpr;
  const vq = Math.max(6, Math.round(vr / 3) * 3);          // radius buckets: 3 world units
  const key = 'r' + biome + '|' + (v % 24) + '|' + vq;
  const hit = lruGet(key);
  if (hit) return hit;
  const pad = vq * 1.6;
  const size = Math.ceil(pad * 2 * px) + 2;
  const c = document.createElement('canvas');
  c.width = c.height = size;
  const x = c.getContext('2d');
  x.setTransform(px, 0, 0, px, size / 2, size / 2);
  paintRock(x, vq, v % 24, BIOMES[biome]);
  return lruPut(key, { c, half: size / 2 / px, vq });
}

function glowSprite(color, key) {
  let sp = sprites.get('g' + key);
  if (sp) return sp;
  const c = document.createElement('canvas'); c.width = c.height = 128;
  const x = c.getContext('2d');
  const g = x.createRadialGradient(64, 64, 0, 64, 64, 64);
  g.addColorStop(0, color); g.addColorStop(0.25, color.replace(/[\d.]+\)$/, '0.45)')); g.addColorStop(1, color.replace(/[\d.]+\)$/, '0)'));
  x.fillStyle = g; x.fillRect(0, 0, 128, 128);
  sp = { c };
  sprites.set('g' + key, sp);
  return sp;
}

// ── decor placement (deterministic per seed, visual only) ──
const CELL = 58;
function decorItem(course, cx, cy) {
  const sd = hash32(course.seed, 0xDEC0);
  const h = hash32(sd, cx, cy);
  const r = k => rnd(h, k);
  const x = (cx + 0.15 + r(1) * 0.7) * CELL, y = (cy + 0.15 + r(2) * 0.7) * CELL;
  const top = course.bankTop(x), bot = course.bankBot(x);
  const onTop = y < top, onBot = y > bot;
  if (!onTop && !onBot) return null;
  const dist = onTop ? top - y : y - bot;
  const m = biomeMix(course, x);
  const bi = r(3) < m.t ? m.b : m.a;
  const B = BIOMES[bi];
  if (r(4) > B.density) return null;
  let u = r(5), type = B.trees[0][0];
  for (const [t, p] of B.trees) { if (u < p) { type = t; break; } u -= p; }
  let size = type === 'bush' || type === 'shrub' ? 9 + r(6) * 8 : type === 'boulder' ? 8 + r(6) * 12 : 20 + r(6) * 22;
  if (dist < size * 0.55 + 6) size = Math.max(7, (dist - 6) / 0.55);
  if (size < 7) return null;
  return { x, y, type, size, bi, v: h & 1023, side: onTop ? -1 : 1 };
}

function forDecor(course, x0, x1, y0, y1, fn) {
  for (let cx = Math.floor(x0 / CELL) - 1; cx <= Math.floor(x1 / CELL) + 1; cx++)
    for (let cy = Math.floor(y0 / CELL) - 1; cy <= Math.floor(y1 / CELL) + 1; cy++) {
      if (cy * CELL > BANK_MAX + 10 && (cy + 1) * CELL < RIVER_H - BANK_MAX - 10) continue;
      const it = decorItem(course, cx, cy);
      if (it) fn(it);
    }
}

function edgePath(c, course, x0, x1, top, yFar) {
  c.beginPath();
  const xs = Math.floor(x0 / 6) * 6;   // global sample grid → identical edges in neighbouring chunks
  c.moveTo(xs, yFar);
  for (let x = xs; x <= x1 + 6; x += 6) c.lineTo(x, top ? course.bankTop(x) : course.bankBot(x));
  c.lineTo(x1 + 6, yFar);
  c.closePath();
}
function edgeLine(c, course, x0, x1, top, off) {
  c.beginPath();
  const xs = Math.floor(x0 / 6) * 6;
  for (let x = xs; x <= x1 + 6; x += 6) {
    const y = top ? course.bankTop(x) - off : course.bankBot(x) + off;
    x === xs ? c.moveTo(x, y) : c.lineTo(x, y);
  }
}

function buildChunk(course, k) {
  const pxs = V.s * Math.min(V.dpr, 1.5);
  const PAD = 4;
  const x0 = k * CW - PAD, x1 = (k + 1) * CW + PAD;
  const PADY = 4 + 16 / V.s;            // covers the maximum screen-shake offset
  const y0 = V.camY - PADY, y1 = V.camY + V.visH + PADY;
  const W = Math.ceil((x1 - x0) * pxs), H = Math.ceil((y1 - y0) * pxs);
  const mk = () => { const c = document.createElement('canvas'); c.width = W; c.height = H; const x = c.getContext('2d'); x.setTransform(pxs, 0, 0, pxs, -x0 * pxs, -y0 * pxs); return [c, x]; };
  const [gc, g] = mk();
  const [cc, cn] = mk();
  const chunk = { k, x0, x1, y0, y1, ground: gc, canopy: cc, lights: [], hasCanopy: false };
  const sd = hash32(course.seed, 0xC4A, k);
  const R = seededR(sd);
  const bm = x => biomeMix(course, x);

  // ground gradient across the chunk (blends biomes smoothly)
  const grad = (key) => {
    const gr = g.createLinearGradient(x0, 0, x1, 0);
    for (let i = 0; i <= 8; i++) {
      const x = x0 + (x1 - x0) * i / 8, m = bm(x);
      gr.addColorStop(i / 8, mixHex(BIOMES[m.a][key], BIOMES[m.b][key], m.t));
    }
    return gr;
  };
  const yTopFar = Math.min(y0, -10) - 10, yBotFar = Math.max(y1, RIVER_H + 10) + 10;
  for (const top of [true, false]) {
    edgePath(g, course, x0, x1, top, top ? yTopFar : yBotFar);
    g.fillStyle = grad('ground'); g.fill();
  }
  // soft colour variation patches
  g.save();
  for (const top of [true, false]) { edgePath(g, course, x0, x1, top, top ? yTopFar : yBotFar); }
  g.clip();
  const landY = (top) => top ? y0 + R() * (BANK_MAX + 20 - y0) : RIVER_H - BANK_MAX - 20 + R() * (y1 - (RIVER_H - BANK_MAX - 20));
  // patches are placed in world space so neighbouring chunks paint identical overlaps (no seams)
  for (let cx = Math.floor((x0 - 110) / 96); cx <= Math.floor((x1 + 110) / 96); cx++) {
    for (let j = 0; j < 10; j++) {
      const h = hash32(course.seed, 0x9A7C, cx * 16 + j), r = q => rnd(h, q);
      const top = j < 5, x = (cx + r(1)) * 96;
      const y = top ? BANK_MAX + 20 - r(2) * 640 : RIVER_H - BANK_MAX - 20 + r(2) * 640;
      const rr = 26 + r(3) * 70;
      if (y + rr < y0 || y - rr > y1) continue;
      const m = bm(x), B = BIOMES[r(4) < m.t ? m.b : m.a];
      const col = r(5) < 0.55 ? B.ground2 : B.dark;
      const pg = g.createRadialGradient(x, y, 0, x, y, rr);
      pg.addColorStop(0, rgba(col, 0.32)); pg.addColorStop(1, rgba(col, 0));
      g.fillStyle = pg; g.fillRect(x - rr, y - rr, rr * 2, rr * 2);
    }
  }
  // canyon strata / glacier drifts follow the shoreline (per-seed offsets, opacity per 64-unit segment)
  for (const top of [true, false]) {
    for (let i = 1; i <= 7; i++) {
      const off = 14 + i * i * 6 + rnd(course.seed, 0x57A7, i) * 6;
      const lw = rnd(course.seed, 0x57A8, i);
      for (let sx = Math.floor(x0 / 64) * 64; sx < x1; sx += 64) {
        const m = bm(sx + 32);
        const st = (BIOMES[m.a].strata ? 1 - m.t : 0) + (BIOMES[m.b].strata ? m.t : 0);
        const sn = (BIOMES[m.a].snow ? 1 - m.t : 0) + (BIOMES[m.b].snow ? m.t : 0);
        if (st < 0.02 && sn < 0.02) continue;
        edgeLine(g, course, sx, sx + 64, top, off);
        if (st > 0.02) { g.strokeStyle = i % 2 ? `rgba(90,30,10,${0.32 * st})` : `rgba(255,200,150,${0.22 * st})`; g.lineWidth = 2 + lw * 4; g.stroke(); }
        if (sn > 0.02) { g.strokeStyle = `rgba(150,185,215,${0.28 * sn})`; g.lineWidth = 3 + lw * 6; g.stroke(); }
      }
    }
  }
  // grass tufts (batched)
  for (let col = 0; col < 3; col++) {
    g.beginPath();
    for (let i = 0; i < 170; i++) {
      const x = x0 + R() * (x1 - x0), top = R() < 0.5, y = landY(top);
      const edge = top ? course.bankTop(x) : course.bankBot(x);
      if (top ? y > edge - 12 : y < edge + 12) continue;
      const h = 3 + R() * 5;
      g.moveTo(x - 2, y + 1); g.lineTo(x - 3, y - h);
      g.moveTo(x, y + 1); g.lineTo(x + 0.5, y - h * 1.2);
      g.moveTo(x + 2, y + 1); g.lineTo(x + 3.5, y - h * 0.9);
    }
    const m = bm((x0 + x1) / 2);
    g.strokeStyle = rgba(mixHex(BIOMES[m.a].grass[col], BIOMES[m.b].grass[col], m.t), 0.75);
    g.lineWidth = 1.1; g.lineCap = 'round'; g.stroke();
  }
  // flowers
  for (let i = 0; i < 70; i++) {
    const x = x0 + R() * (x1 - x0), top = R() < 0.5, y = landY(top);
    const edge = top ? course.bankTop(x) : course.bankBot(x);
    if (top ? y > edge - 14 : y < edge + 14) continue;
    const m = bm(x), B = BIOMES[R() < m.t ? m.b : m.a];
    if (!B.flowers.length) continue;
    g.fillStyle = B.flowers[Math.floor(R() * B.flowers.length)];
    const fx = x, fy = y, fr = 1.2 + R() * 1.6;
    for (let p = 0; p < 4; p++) { g.beginPath(); g.arc(fx + Math.cos(p * 1.57) * fr, fy + Math.sin(p * 1.57) * fr, fr * 0.8, 0, TAU); g.fill(); }
    g.fillStyle = '#ffe680'; g.beginPath(); g.arc(fx, fy, fr * 0.55, 0, TAU); g.fill();
  }
  g.restore();

  // shoreline: sand / gravel band, wet line, pebbles
  for (const top of [true, false]) {
    const m = bm((x0 + x1) / 2);
    const shore = mixHex(BIOMES[m.a].shore, BIOMES[m.b].shore, m.t), wet = mixHex(BIOMES[m.a].wet, BIOMES[m.b].wet, m.t);
    edgeLine(g, course, x0, x1, top, 7);
    g.strokeStyle = rgba(shore, 0.95); g.lineWidth = 14; g.lineJoin = 'round'; g.stroke();
    edgeLine(g, course, x0, x1, top, 15);
    g.strokeStyle = rgba(shore, 0.35); g.lineWidth = 8; g.stroke();
    edgeLine(g, course, x0, x1, top, 2.2);
    g.strokeStyle = rgba(wet, 0.9); g.lineWidth = 4.5; g.stroke();
    edgeLine(g, course, x0, x1, top, 0.2);
    g.strokeStyle = 'rgba(255,255,255,0.35)'; g.lineWidth = 1.2; g.stroke();
    for (let i = 0; i < 60; i++) {
      const x = x0 + R() * (x1 - x0);
      const y = top ? course.bankTop(x) - 2 - R() * 13 : course.bankBot(x) + 2 + R() * 13;
      const pr = 0.8 + R() * 2.2;
      g.fillStyle = R() < 0.5 ? rgba(wet, 0.55) : 'rgba(255,255,255,0.28)';
      g.beginPath(); g.ellipse(x, y, pr * 1.3, pr, R() * 3, 0, TAU); g.fill();
    }
  }
  // reeds / lily pads near the water (visual only, never inside the corridor's gaps)
  for (let x = x0 + 4; x < x1; x += 14) {
    const h = hash32(course.seed, 0x7EED, Math.floor(x / 14));
    const r = q => rnd(h, q);
    const m = bm(x), bi = r(1) < m.t ? m.b : m.a, B = BIOMES[bi];
    for (const top of [true, false]) {
      const rr = r(top ? 2 : 3);
      if ((bi === 0 || bi === 2) && rr < 0.16) {
        const y = top ? course.bankTop(x) - 3 : course.bankBot(x) + 3;
        g.strokeStyle = bi === 2 ? 'rgba(70,120,50,0.9)' : 'rgba(110,140,60,0.9)'; g.lineWidth = 1.2;
        g.beginPath();
        for (let s = 0; s < 6; s++) { const a = -Math.PI / 2 + (r(10 + s) - 0.5) * 1.4; const L = 8 + r(20 + s) * 10; g.moveTo(x, y); g.lineTo(x + Math.cos(a) * L, y + Math.sin(a) * L * (top ? 1 : -1)); }
        g.stroke();
        g.fillStyle = '#5a3a1e';
        for (let s = 0; s < 2; s++) { g.beginPath(); g.ellipse(x + (r(30 + s) - 0.5) * 10, y + (top ? -1 : 1) * (8 + r(32 + s) * 6), 1.3, 3.2, 0, 0, TAU); g.fill(); }
      }
      if (B.lily && rr > 0.86) {
        const nearGate = course.gates.some(gt => Math.abs(gt.x - x) < 120);
        if (!nearGate) {
          const y = top ? course.bankTop(x) + 10 + r(4) * 22 : course.bankBot(x) - 10 - r(4) * 22;
          const lr = 6 + r(5) * 6, la = r(6) * TAU;
          g.fillStyle = 'rgba(0,30,10,0.25)'; g.beginPath(); g.arc(x + 1.5, y + 2, lr, 0, TAU); g.fill();
          g.fillStyle = '#3f8a3a'; g.beginPath(); g.moveTo(x, y); g.arc(x, y, lr, la + 0.35, la + TAU - 0.05); g.closePath(); g.fill();
          g.strokeStyle = 'rgba(160,220,120,0.5)'; g.lineWidth = 0.6; g.stroke();
          if (r(7) < 0.35) { g.fillStyle = '#ff8fc8'; for (let p = 0; p < 6; p++) { g.beginPath(); g.ellipse(x + Math.cos(p) * 2.2, y + Math.sin(p) * 2.2, 2.6, 1.2, p, 0, TAU); g.fill(); } g.fillStyle = '#ffe680'; g.beginPath(); g.arc(x, y, 1.2, 0, TAU); g.fill(); }
        }
      }
    }
  }

  // trees, bushes, boulders: shadows on ground, canopies on top layer
  const items = [];
  forDecor(course, x0 - 60, x1 + 60, y0 - 60, y1 + 60, it => items.push(it));
  items.sort((a, b) => a.y - b.y);
  for (const it of items) {
    if (it.type === 'boulder') continue;
    const s = it.size;
    g.fillStyle = 'rgba(5,20,10,0.28)';
    g.beginPath(); g.ellipse(it.x + s * 0.35, it.y + s * 0.42, s * 1.02, s * 0.88, 0.3, 0, TAU); g.fill();
  }
  for (const it of items) {
    const B = BIOMES[it.bi];
    if (it.type === 'boulder') { g.save(); g.translate(it.x, it.y); paintRock(g, it.size, it.v, B); g.restore(); continue; }
    paintTree(cn, it, B);
    chunk.hasCanopy = true;
  }
  // campfires (night) — live lights
  for (let i = 0; i < 2; i++) {
    const x = x0 + 60 + R() * (x1 - x0 - 120);
    const m = bm(x);
    const B = BIOMES[R() < m.t ? m.b : m.a];
    if (!B.fires || R() < 0.35) continue;
    const top = R() < 0.5;
    const y = top ? course.bankTop(x) - 26 - R() * 18 : course.bankBot(x) + 26 + R() * 18;
    g.fillStyle = '#3a3a40';
    for (let s = 0; s < 8; s++) { g.beginPath(); g.arc(x + Math.cos(s / 8 * TAU) * 6, y + Math.sin(s / 8 * TAU) * 6, 1.9, 0, TAU); g.fill(); }
    g.fillStyle = '#2b1a10'; g.fillRect(x - 4, y - 1, 8, 2); g.fillRect(x - 1, y - 4, 2, 8);
    chunk.lights.push({ x, y, kind: 'fire' });
  }
  return chunk;
}

function paintTree(c, it, B) {
  const R = seededR(hash32(it.v, 4242));
  const { x, y, size: s } = it;
  const col = B.canopy;
  if (it.type === 'pine' || it.type === 'snowpine') {
    const layers = 3;
    for (let L = 0; L < layers; L++) {
      const rr = s * (1 - L * 0.26), pts = 9, rot = R() * TAU;
      c.beginPath();
      for (let i = 0; i <= pts * 2; i++) {
        const a = rot + i / (pts * 2) * TAU, r = i % 2 ? rr * 0.62 : rr;
        const px = x + Math.cos(a) * r - L * s * 0.06, py = y + Math.sin(a) * r - L * s * 0.07;
        i ? c.lineTo(px, py) : c.moveTo(px, py);
      }
      c.closePath();
      const g = c.createRadialGradient(x - rr * 0.4, y - rr * 0.4, rr * 0.05, x, y, rr * 1.1);
      g.addColorStop(0, col[3]); g.addColorStop(0.55, col[L % 2 ? 1 : 0]); g.addColorStop(1, col[2]);
      c.fillStyle = g; c.fill();
      c.strokeStyle = 'rgba(0,0,0,0.18)'; c.lineWidth = 0.8; c.stroke();
      if (it.type === 'snowpine') {
        c.save(); c.clip();
        const sg = c.createRadialGradient(x - rr * 0.5, y - rr * 0.5, 0, x - rr * 0.3, y - rr * 0.3, rr * 0.95);
        sg.addColorStop(0, 'rgba(255,255,255,0.95)'); sg.addColorStop(0.6, 'rgba(235,245,255,0.7)'); sg.addColorStop(1, 'rgba(235,245,255,0)');
        c.fillStyle = sg; c.fillRect(x - rr, y - rr, rr * 2, rr * 2);
        c.restore();
      }
    }
    c.fillStyle = it.type === 'snowpine' ? '#ffffff' : col[3];
    c.beginPath(); c.arc(x - s * 0.18, y - s * 0.2, s * 0.08, 0, TAU); c.fill();
    return;
  }
  if (it.type === 'palm') {
    const n = 7 + Math.floor(R() * 3), rot = R() * TAU;
    for (let i = 0; i < n; i++) {
      const a = rot + i / n * TAU + (R() - 0.5) * 0.3, L = s * (0.85 + R() * 0.3), w = s * 0.2;
      const ex = x + Math.cos(a) * L, ey = y + Math.sin(a) * L;
      const nx = -Math.sin(a), ny = Math.cos(a);
      const bend = 0.25 * L;
      c.beginPath();
      c.moveTo(x, y);
      c.quadraticCurveTo(x + Math.cos(a) * L * 0.5 + nx * (w + bend * 0.3), y + Math.sin(a) * L * 0.5 + ny * (w + bend * 0.3), ex + nx * bend * 0.2, ey + ny * bend * 0.2);
      c.quadraticCurveTo(x + Math.cos(a) * L * 0.5 - nx * w * 0.6, y + Math.sin(a) * L * 0.5 - ny * w * 0.6, x, y);
      const g = c.createLinearGradient(x, y, ex, ey);
      g.addColorStop(0, col[0]); g.addColorStop(0.6, col[3]); g.addColorStop(1, col[1]);
      c.fillStyle = g; c.fill();
      c.strokeStyle = 'rgba(10,40,10,0.45)'; c.lineWidth = 0.7;
      c.beginPath(); c.moveTo(x, y); c.lineTo(ex + nx * bend * 0.2, ey + ny * bend * 0.2); c.stroke();
    }
    c.fillStyle = '#6b4a22';
    for (let i = 0; i < 4; i++) { c.beginPath(); c.arc(x + (R() - 0.5) * s * 0.18, y + (R() - 0.5) * s * 0.18, s * 0.07, 0, TAU); c.fill(); }
    return;
  }
  // round deciduous canopy / bush / dry shrub
  const blobs = it.type === 'tree' ? 7 : 4;
  const base = it.type === 'shrub' ? [B.canopy[0], B.canopy[1], B.canopy[2], B.canopy[3]] : col;
  for (let i = 0; i < blobs; i++) {
    const a = R() * TAU, d = i === 0 ? 0 : s * (0.3 + R() * 0.3);
    const bx = x + Math.cos(a) * d, by = y + Math.sin(a) * d, br = s * (i === 0 ? 0.7 : 0.42 + R() * 0.2);
    const g = c.createRadialGradient(bx - br * 0.45, by - br * 0.5, br * 0.05, bx, by, br);
    g.addColorStop(0, base[3]); g.addColorStop(0.6, base[i % 2]); g.addColorStop(1, base[2]);
    c.fillStyle = g; c.beginPath(); c.arc(bx, by, br, 0, TAU); c.fill();
  }
  // leaf highlights
  c.fillStyle = 'rgba(255,255,220,0.16)';
  for (let i = 0; i < blobs * 3; i++) { c.beginPath(); c.arc(x - s * 0.25 + (R() - 0.6) * s, y - s * 0.25 + (R() - 0.6) * s, s * 0.07, 0, TAU); c.fill(); }
  if (it.type === 'tree' && B === BIOMES[0] && R() < 0.3) { // a few blossoms
    c.fillStyle = 'rgba(255,220,235,0.85)';
    for (let i = 0; i < 6; i++) { c.beginPath(); c.arc(x + (R() - 0.5) * s * 1.2, y + (R() - 0.5) * s * 1.2, s * 0.05, 0, TAU); c.fill(); }
  }
}

let idleBuild = 0;
function ensureChunks(course) {
  if (chunkCourse !== course) { chunks.clear(); chunkCourse = course; }
  const k0 = Math.floor((V.camX - 10) / CW), k1 = Math.floor((V.camX + V.visW + 10) / CW);
  for (const [k] of chunks) if (k < k0 - 1 || k > k1 + 2) chunks.delete(k);
  for (let k = k0; k <= k1; k++) if (!chunks.has(k)) chunks.set(k, buildChunk(course, k));
  // build the next chunk ahead of time, in idle time when the browser offers it
  const ahead = k1 + 1;
  if (!chunks.has(ahead) && !idleBuild) {
    const run = () => { idleBuild = 0; if (chunkCourse === course && !chunks.has(ahead)) chunks.set(ahead, buildChunk(course, ahead)); };
    idleBuild = window.requestIdleCallback ? requestIdleCallback(run, { timeout: 300 }) : setTimeout(run, 16);
  }
  return [k0, k1];
}

// ─── Particles ─────────────────────────────────────────────────────────────
const parts = [];
const MAXP = 900;
function spawn(p) {
  if (parts.length >= MAXP * (qualityLevel === 0 ? 0.5 : 1)) return;
  p.age = 0; p.life = p.life || 1;
  parts.push(p);
}
const ripples = [];
function addRipple(x, y, str = 1, dur = 1.1) { ripples.push({ x, y, t: VT, dur, str }); if (ripples.length > 16) ripples.shift(); }
const trail = [];
const ghostTrails = new Map();

function updateParticles(dt, course) {
  const flow = course ? course.speedAt(V.camX) * 0.6 : 140;
  for (let i = parts.length - 1; i >= 0; i--) {
    const p = parts[i];
    p.age += dt;
    if (p.age >= p.life) { parts[i] = parts[parts.length - 1]; parts.pop(); continue; }
    switch (p.k) {
      case 'drop': p.vz -= 900 * dt; p.z += p.vz * dt; p.x += p.vx * dt; p.y += p.vy * dt; if (p.z < 0) { p.age = p.life; } break;
      case 'foam': p.x += (flow + (p.vx || 0)) * dt; p.y += (p.vy || 0) * dt; p.vx = (p.vx || 0) * 0.96; p.vy = (p.vy || 0) * 0.96; break;
      case 'splinter': p.x += p.vx * dt; p.y += p.vy * dt; p.vx *= 0.985; p.vy *= 0.985; p.x += flow * 0.6 * dt; p.rot += p.vr * dt; p.vr *= 0.98; break;
      case 'spark': p.x += p.vx * dt; p.y += p.vy * dt; p.vx *= 0.93; p.vy *= 0.93; break;
      case 'leaf':
        if (p.z > 0) { p.z -= 22 * dt; p.x += p.vx * dt + Math.sin(VT * 2 + p.ph) * 14 * dt; p.y += p.vy * dt; p.rot += p.vr * dt; }
        else { p.z = 0; p.x += flow * dt; p.rot += p.vr * 0.1 * dt; }
        break;
      case 'snow': p.x += (p.vx + Math.sin(VT * 1.3 + p.ph) * 10) * dt; p.y += p.vy * dt; break;
      case 'fly': p.ph += dt; p.x += Math.sin(p.ph * 0.9 + p.s) * 16 * dt; p.y += Math.cos(p.ph * 1.3 + p.s * 2) * 12 * dt; break;
      case 'mote': p.x += p.vx * dt; p.y += p.vy * dt; break;
      case 'bubble': p.y -= 6 * dt; p.x += flow * 0.3 * dt; break;
      case 'text': p.y -= 26 * dt; break;
    }
  }
}

function ambient(dt, course) {
  if (!course || qualityLevel === 0 && Math.random() < 0.5) return;
  const m = biomeMix(course, V.camX + V.visW / 2);
  const w = (name) => (BIOMES[m.a].amb === name ? 1 - m.t : 0) + (BIOMES[m.b].amb === name ? m.t : 0);
  const x0 = V.camX, x1 = V.camX + V.visW + 200, y0 = V.camY, y1 = V.camY + V.visH;
  const rate = (r) => Math.random() < r * dt;
  const leafCols = BIOMES[m.t > 0.5 ? m.b : m.a].leaf;
  if (rate(2.2 * w('leaves'))) spawn({ k: 'leaf', x: x0 + Math.random() * (x1 - x0), y: y0 + Math.random() * (y1 - y0), z: 60 + Math.random() * 60, vx: 20 + Math.random() * 20, vy: 10 + Math.random() * 15, rot: Math.random() * 6, vr: (Math.random() - 0.5) * 4, ph: Math.random() * 6, life: 9, col: leafCols[Math.floor(Math.random() * leafCols.length)] });
  if (rate(4 * w('leaves'))) spawn({ k: 'mote', x: x0 + Math.random() * (x1 - x0), y: y0 + Math.random() * (y1 - y0), vx: 6, vy: -4, life: 4, s: 1 + Math.random() * 1.5 });
  if (rate(10 * w('dust'))) spawn({ k: 'mote', x: x0 + Math.random() * (x1 - x0), y: y0 + Math.random() * (y1 - y0), vx: 40 + Math.random() * 30, vy: -6, life: 3, s: 1 + Math.random() * 2, dust: 1 });
  const flies = w('fireflies');
  if (flies > 0.05) {
    let n = 0; for (const p of parts) if (p.k === 'fly') n++;
    if (n < 34 * flies) spawn({ k: 'fly', x: x0 + Math.random() * (x1 - x0), y: Math.random() < 0.5 ? y0 + Math.random() * (BANK_MAX + 60 - y0) : RIVER_H - BANK_MAX - 60 + Math.random() * (y1 - RIVER_H + BANK_MAX + 60), ph: 0, s: Math.random() * 10, life: 5 + Math.random() * 5 });
  }
  const sn = w('snow');
  if (sn > 0.05) for (let i = 0; i < 3; i++) if (rate(26 * sn)) spawn({ k: 'snow', x: x0 + Math.random() * (x1 - x0), y: y0 - 10 + Math.random() * (y1 - y0), vx: 18, vy: 24 + Math.random() * 20, ph: Math.random() * 6, life: 6, s: 0.8 + Math.random() * 1.8 });
}

// ─── Boat drawing ──────────────────────────────────────────────────────────
const HULL = { player: ['#ff7a45', '#e4572e', '#a5321a'], ghost: ['#9fe8ff', '#4cc3f0', '#1d7fa8'], pb: ['#e3c8ff', '#b18cf0', '#7552b8'] };
function drawBoat(c, x, y, ang, pad, style, alpha = 1, night = 0) {
  const [hl, hb, hd] = HULL[style] || HULL.player;
  c.save();
  c.translate(x, y);
  c.globalAlpha = alpha;
  // shadow
  c.save();
  c.translate(5, 8); c.rotate(ang);
  c.fillStyle = 'rgba(0,15,25,0.28)';
  c.beginPath(); c.moveTo(31, 0); c.bezierCurveTo(21, -12.8, -21, -12.8, -30, 0); c.bezierCurveTo(-21, 12.8, 21, 12.8, 31, 0); c.fill();
  c.restore();
  c.rotate(ang);
  // bow wave
  c.strokeStyle = 'rgba(255,255,255,0.55)'; c.lineWidth = 1.6;
  c.beginPath(); c.moveTo(22, -7); c.quadraticCurveTo(33, 0, 22, 7); c.stroke();
  // hull
  c.beginPath(); c.moveTo(31, 0); c.bezierCurveTo(21, -12.2, -21, -12.2, -30, 0); c.bezierCurveTo(-21, 12.2, 21, 12.2, 31, 0); c.closePath();
  const g = c.createLinearGradient(0, -9, 0, 9);
  g.addColorStop(0, hl); g.addColorStop(0.5, hb); g.addColorStop(1, hd);
  c.fillStyle = g; c.fill();
  c.strokeStyle = 'rgba(40,10,0,0.45)'; c.lineWidth = 0.9; c.stroke();
  // deck ridge + stripe
  c.strokeStyle = 'rgba(255,255,255,0.35)'; c.lineWidth = 1.1;
  c.beginPath(); c.moveTo(28, 0); c.lineTo(10, 0); c.moveTo(-14, 0); c.lineTo(-27, 0); c.stroke();
  c.strokeStyle = 'rgba(255,240,200,0.7)'; c.lineWidth = 0.8;
  c.beginPath(); c.moveTo(26, -1.8); c.bezierCurveTo(12, -8.5, -12, -8.5, -26, -1.8); c.stroke();
  // cockpit
  c.fillStyle = '#20150e'; c.beginPath(); c.ellipse(-2, 0, 10, 6.4, 0, 0, TAU); c.fill();
  c.strokeStyle = style === 'player' ? '#2a3b52' : 'rgba(255,255,255,0.6)'; c.lineWidth = 1.4; c.stroke();
  // paddle (behind arms)
  const beta = pad.beta;
  const dx = Math.cos(beta), dy = Math.sin(beta), L = 24;
  c.strokeStyle = '#3b2a1c'; c.lineWidth = 1.6; c.lineCap = 'round';
  c.beginPath(); c.moveTo(-1 - dx * L, -dy * L); c.lineTo(-1 + dx * L, dy * L); c.stroke();
  for (const sgn of [1, -1]) {
    const bx = -1 + dx * L * sgn, by = dy * L * sgn;
    const dip = pad.dipSide === sgn ? pad.dip : 0;
    c.save(); c.translate(bx, by); c.rotate(beta);
    c.fillStyle = style === 'player' ? (dip > 0.1 ? '#e7d9a6' : '#fff1c4') : 'rgba(255,255,255,0.9)';
    c.beginPath(); c.ellipse(sgn * 3, 0, 6.2, 3.2 * (1 - dip * 0.35), 0, 0, TAU); c.fill();
    c.strokeStyle = 'rgba(0,0,0,0.3)'; c.lineWidth = 0.6; c.stroke();
    c.restore();
  }
  // paddler: vest, arms, head
  c.fillStyle = style === 'player' ? '#ffc23d' : style === 'pb' ? '#efe0ff' : '#dff7ff';
  c.beginPath(); c.ellipse(-3, 0, 5.8, 7.4, 0, 0, TAU); c.fill();
  c.strokeStyle = 'rgba(0,0,0,0.25)'; c.lineWidth = 0.7; c.stroke();
  c.strokeStyle = style === 'player' ? '#e0a46a' : 'rgba(255,255,255,0.8)'; c.lineWidth = 2.2;
  c.beginPath(); c.moveTo(-2, -5); c.lineTo(-1 + dx * 9, dy * 9); c.moveTo(-2, 5); c.lineTo(-1 - dx * 9, -dy * 9); c.stroke();
  c.fillStyle = style === 'player' ? '#2f7fd6' : style === 'pb' ? '#8f6cd8' : '#2aa6d6';
  c.beginPath(); c.arc(-1.5, 0, 4.4, 0, TAU); c.fill();
  c.fillStyle = 'rgba(255,255,255,0.45)'; c.beginPath(); c.arc(-2.6, -1.3, 1.6, 0, TAU); c.fill();
  // bow lantern at night
  if (night > 0.05) {
    c.fillStyle = `rgba(255,214,120,${0.9 * night})`; c.beginPath(); c.arc(21, 0, 2.3, 0, TAU); c.fill();
  }
  c.restore();
}

function paddlePose(st, now) {
  // st: { side, t } last stroke
  const d = 0.3;
  const p = st && now - st.t < d ? (now - st.t) / d : 1;
  if (p < 1) {
    const e = 1 - (1 - p) * (1 - p);
    const sweep = -0.85 + 1.7 * e;
    return { beta: Math.PI / 2 + st.side * sweep, dipSide: st.side, dip: Math.sin(p * Math.PI) };
  }
  return { beta: Math.PI / 2 + Math.sin(now * 1.7) * 0.1, dipSide: 0, dip: 0 };
}

function boatAngle(vx, vy) { return Math.atan2(vy * PHYS.tilt, vx); }

// ─── Obstacles drawing ─────────────────────────────────────────────────────
// Fade keyed to a single x (a gate's gap line) so every gate kind is revealed identically.
function revealAlpha(x, revealX) { return clamp((revealX - x) / 90, 0, 1); }

function capsulePath(c, len, r) {
  c.beginPath();
  c.moveTo(0, -r); c.lineTo(len, -r); c.arc(len, 0, r, -Math.PI / 2, Math.PI / 2); c.lineTo(0, r); c.arc(0, 0, r, Math.PI / 2, Math.PI * 1.5); c.closePath();
}

// Paints a log lying along +x from its bank end (0,0) to its cut tip (L,0).
function paintLog(c, L, r, v, B, boom) {
  const W = B.wood;
  const R = seededR(hash32(v, 515));
  capsulePath(c, L, r);
  const g = c.createLinearGradient(0, -r, 0, r);
  g.addColorStop(0, W.light); g.addColorStop(0.35, W.bark); g.addColorStop(1, W.dark);
  c.fillStyle = g; c.fill();
  c.save(); c.clip();
  c.strokeStyle = rgba(W.dark, 0.55); c.lineWidth = 1.1;
  for (let i = 0; i < 14; i++) {
    const yy = (R() - 0.5) * r * 1.7, xs = R() * L, xl = 20 + R() * 60;
    c.beginPath(); c.moveTo(xs, yy); c.quadraticCurveTo(xs + xl / 2, yy + (R() - 0.5) * 3, xs + xl, yy); c.stroke();
  }
  for (let i = 0; i < 3; i++) { c.fillStyle = rgba(W.dark, 0.6); c.beginPath(); c.ellipse(R() * L, (R() - 0.5) * r, 3, 1.8, 0, 0, TAU); c.fill(); }
  if (B.rock.moss && B.rock.mossAmt > 0.8) { c.fillStyle = 'rgba(80,160,60,0.45)'; for (let i = 0; i < 6; i++) { c.beginPath(); c.ellipse(R() * L, -r * 0.5, 8 + R() * 10, r * 0.35, 0, 0, TAU); c.fill(); } }
  if (B.snow) { c.fillStyle = 'rgba(255,255,255,0.88)'; c.beginPath(); c.ellipse(L / 2, -r * 0.62, L / 2, r * 0.42, 0, 0, TAU); c.fill(); }
  const wl = c.createLinearGradient(0, r * 0.2, 0, r);
  wl.addColorStop(0, 'rgba(0,25,35,0)'); wl.addColorStop(1, 'rgba(0,25,35,0.4)');
  c.fillStyle = wl; c.fillRect(-r, 0, L + 2 * r, r);
  if (boom) { c.fillStyle = 'rgba(60,60,66,0.9)'; for (let bx = L - 40; bx > -r; bx -= 70) c.fillRect(bx, -r, 4, r * 2); }
  c.restore();
  // cut end with rings
  c.fillStyle = W.end; c.beginPath(); c.ellipse(L, 0, r * 0.5, r * 0.95, 0, 0, TAU); c.fill();
  c.strokeStyle = rgba(W.ring, 0.9); c.lineWidth = 0.8;
  for (let i = 1; i <= 3; i++) { c.beginPath(); c.ellipse(L, 0, r * 0.5 * i / 4, r * 0.95 * i / 4, 0, 0, TAU); c.stroke(); }
  c.strokeStyle = rgba(W.dark, 0.8); c.lineWidth = 1.2; c.beginPath(); c.ellipse(L, 0, r * 0.5, r * 0.95, 0, 0, TAU); c.stroke();
  if (boom) { // red/white buoy at the tip — marks moving obstacles
    const br = r * 0.95, bx = L + r * 0.9;
    c.fillStyle = '#f2f2f2'; c.beginPath(); c.arc(bx, 0, br, 0, TAU); c.fill();
    c.fillStyle = '#e8352b';
    c.beginPath(); c.arc(bx, 0, br, -Math.PI / 4, Math.PI / 4); c.lineTo(bx, 0); c.fill();
    c.beginPath(); c.arc(bx, 0, br, Math.PI * 0.75, Math.PI * 1.25); c.lineTo(bx, 0); c.fill();
    c.strokeStyle = 'rgba(0,0,0,0.35)'; c.lineWidth = 0.8; c.beginPath(); c.arc(bx, 0, br, 0, TAU); c.stroke();
    c.fillStyle = 'rgba(255,255,255,0.7)'; c.beginPath(); c.arc(L + r * 0.6, -br * 0.4, br * 0.25, 0, TAU); c.fill();
  }
}

function drawLog(c, s, off, biome, boom) {
  let x1 = s.x1, y1 = s.y1 + off, x2 = s.x2, y2 = s.y2 + off;
  // the decorated tip (cut end / buoy) always faces the river, never the bank
  if (Math.abs(y1 - off - RIVER_H / 2) < Math.abs(y2 - off - RIVER_H / 2)) { [x1, x2] = [x2, x1]; [y1, y2] = [y2, y1]; }
  const r = s.r / 0.92;
  const L = Math.hypot(x2 - x1, y2 - y1), a = Math.atan2(y2 - y1, x2 - x1);
  // shadow (world-space offset, so drawn live)
  c.save(); c.translate(x1 + 6, y1 + 9); c.rotate(a);
  c.fillStyle = 'rgba(0,15,25,0.26)'; capsulePath(c, L, r * 1.05); c.fill();
  c.restore();
  const px = V.s * V.dpr, Lq = Math.round(L / 4) * 4;
  const key = 'L' + biome + '|' + s.v + '|' + Lq + '|' + Math.round(r * 2) + '|' + (boom ? 1 : 0);
  let sp = lruGet(key);
  if (!sp) {
    const left = r + 2, right = Lq + r * 2 + 3, half = r + 2;
    const cvs = document.createElement('canvas');
    cvs.width = Math.ceil((left + right) * px); cvs.height = Math.ceil(half * 2 * px);
    const x = cvs.getContext('2d');
    x.setTransform(px, 0, 0, px, left * px, half * px);
    paintLog(x, Lq, r, s.v, BIOMES[biome], boom);
    sp = lruPut(key, { c: cvs, left, w: left + right, half, Lq });
  }
  const k = L / (sp.Lq || 1);
  c.save(); c.translate(x1, y1); c.rotate(a); c.scale(k, 1);
  c.drawImage(sp.c, -sp.left, -sp.half, sp.w, sp.half * 2);
  c.restore();
}

function drawPillar(c, s, B) {
  const r = s.r / 0.92;
  const top = s.y1 - r, bot = s.y2 + r, x = s.x1;
  c.fillStyle = 'rgba(0,15,25,0.3)';
  roundRect(c, x - r + 7, top + 9, r * 2, bot - top, r * 0.75); c.fill();
  const stone = B.snow ? ['#f2f6fa', '#c3d0dc', '#7d8c9b'] : B.strata ? ['#f0b88a', '#c27a50', '#6e3a20'] : ['#d6d0c4', '#a59f94', '#5d5852'];
  const g = c.createLinearGradient(x - r, 0, x + r, 0);
  g.addColorStop(0, stone[0]); g.addColorStop(0.5, stone[1]); g.addColorStop(1, stone[2]);
  roundRect(c, x - r, top, r * 2, bot - top, r * 0.75); c.fillStyle = g; c.fill();
  c.save(); c.clip();
  c.strokeStyle = 'rgba(0,0,0,0.25)'; c.lineWidth = 1;
  c.beginPath();
  for (let y = top + 10, row = 0; y < bot; y += 12, row++) {
    c.moveTo(x - r, y); c.lineTo(x + r, y);
    const jx = x + (row % 2 ? -r * 0.3 : r * 0.35);
    c.moveTo(jx, y - 12); c.lineTo(jx, y);
  }
  c.stroke();
  if (B.rock.moss) { c.fillStyle = rgba(B.rock.moss, 0.35); c.fillRect(x - r, top, r * 0.6, bot - top); }
  // lit top-left edge so pillars read clearly under the deck at any time of day
  const hl = c.createLinearGradient(x - r, 0, x - r + 7, 0);
  hl.addColorStop(0, 'rgba(255,255,255,0.45)'); hl.addColorStop(1, 'rgba(255,255,255,0)');
  c.fillStyle = hl; c.fillRect(x - r, top, 7, bot - top);
  c.restore();
  c.strokeStyle = 'rgba(0,0,0,0.45)'; c.lineWidth = 1.4; roundRect(c, x - r, top, r * 2, bot - top, r * 0.75); c.stroke();
  if (!water || water.lost) { // the WebGL water draws a real foam collar; the 2D fallback needs a hint of one
    c.strokeStyle = `rgba(255,255,255,${0.3 + 0.12 * Math.sin(VT * 6 + x)})`; c.lineWidth = 2;
    roundRect(c, x - r - 3, top - 3, r * 2 + 6, bot - top + 6, r * 0.85); c.stroke();
  }
}

function roundRect(c, x, y, w, h, r) {
  r = Math.min(r, w / 2, h / 2);
  c.beginPath();
  c.moveTo(x + r, y); c.arcTo(x + w, y, x + w, y + h, r); c.arcTo(x + w, y + h, x, y + h, r); c.arcTo(x, y + h, x, y, r); c.arcTo(x, y, x + w, y, r); c.closePath();
}

function drawDeck(c, g, B, alpha) {
  const x = g.x, hw = 9;
  const y0 = V.camY - 20, y1 = V.camY + V.visH + 20;
  c.save(); c.globalAlpha = alpha;
  c.fillStyle = 'rgba(0,15,25,0.25)'; c.fillRect(x - hw + 14, y0, hw * 2, y1 - y0);
  const deck = B.snow ? '#9a8068' : B.deck;
  c.fillStyle = deck; c.fillRect(x - hw, y0, hw * 2, y1 - y0);
  // planks
  c.strokeStyle = 'rgba(30,15,5,0.45)'; c.lineWidth = 1;
  c.beginPath();
  for (let y = Math.floor(y0 / 6) * 6; y < y1; y += 6) { c.moveTo(x - hw, y); c.lineTo(x + hw, y); }
  c.stroke();
  const shade = c.createLinearGradient(x - hw, 0, x + hw, 0);
  shade.addColorStop(0, 'rgba(255,230,190,0.25)'); shade.addColorStop(0.5, 'rgba(0,0,0,0)'); shade.addColorStop(1, 'rgba(0,0,0,0.25)');
  c.fillStyle = shade; c.fillRect(x - hw, y0, hw * 2, y1 - y0);
  if (B.snow) { c.fillStyle = 'rgba(255,255,255,0.75)'; c.fillRect(x - hw + 3, y0, hw * 2 - 9, y1 - y0); }
  // rails + posts
  c.fillStyle = '#3d2814';
  c.fillRect(x - hw - 1, y0, 2, y1 - y0); c.fillRect(x + hw - 1, y0, 2, y1 - y0);
  for (let y = Math.floor(y0 / 46) * 46; y < y1; y += 46) { c.fillRect(x - hw - 2.5, y - 2.5, 5, 5); c.fillRect(x + hw - 2.5, y - 2.5, 5, 5); }
  c.restore();
}

function drawStar(c, s, t, a) {
  const bob = Math.sin(t * 3 + s.id) * 1.5;
  c.save(); c.translate(s.x, s.y + bob); c.globalAlpha = a;
  const gl = glowSprite('rgba(255,214,90,0.9)', 'star');
  c.globalCompositeOperation = 'lighter';
  c.globalAlpha = a * 0.55;
  c.drawImage(gl.c, -30, -30, 60, 60);
  c.globalCompositeOperation = 'source-over';
  c.globalAlpha = a;
  c.rotate(Math.sin(t * 1.4 + s.id) * 0.35);
  const sc = 1 + Math.sin(t * 5 + s.id * 2) * 0.06;
  c.scale(sc, sc);
  c.beginPath();
  for (let i = 0; i < 10; i++) { const ang = -Math.PI / 2 + i * Math.PI / 5, r = i % 2 ? 6.2 : 14; c.lineTo(Math.cos(ang) * r, Math.sin(ang) * r); }
  c.closePath();
  const g = c.createLinearGradient(-10, -12, 10, 12);
  g.addColorStop(0, '#fff6c2'); g.addColorStop(0.45, '#ffcf3d'); g.addColorStop(1, '#e08a12');
  c.fillStyle = g; c.fill();
  c.strokeStyle = '#a85a06'; c.lineWidth = 1.2; c.stroke();
  c.fillStyle = 'rgba(255,255,255,0.8)'; c.beginPath(); c.ellipse(-3, -5, 2.4, 1.4, -0.6, 0, TAU); c.fill();
  c.restore();
}

// ─── Main render ───────────────────────────────────────────────────────────
const N_OBS = 96;
const profile = new Float32Array(256 * 4);
const obsArr = new Float32Array(N_OBS * 4), trailArr = new Float32Array(32 * 4), ripArr = new Float32Array(16 * 4);
let lastFrameMs = 8;
const TRAIL_LIFE = 0.95;
const ghostCv = document.createElement('canvas'), gctx = ghostCv.getContext('2d');
let holeSprite = null;

function boatRenderState(sim, alpha) {
  if (!sim) return { x: 0, y: RIVER_H / 2, vy: 0, vx: 232 };
  if (!sim.alive) return { x: sim.x, y: sim.y, vy: sim.vy, vx: sim.vx };
  return { x: sim.px + (sim.x - sim.px) * alpha, y: sim.py + (sim.y - sim.py) * alpha, vy: sim.pvy + (sim.vy - sim.pvy) * alpha, vx: sim.vx };
}

function renderAlpha(now) {
  if (G.state === 'menu') return G.attract && G.attract.sim.alive ? clamp(G.attract.acc / DT, 0, 1) : 1;
  if (G.state === 'paused') return G.pauseAlpha;
  if (G.state !== 'play' || !G.sim) return 1;
  const e = (now - G.t0) / TICK_MS;
  return clamp(e - (G.sim.tick - 1), 0, 1);
}

// Fractional simulation tick used to place moving obstacles between sim steps.
function visualTick(sim, alpha) {
  if (!sim) return 0;
  return sim.alive ? sim.tick - 1 + alpha : sim.tick;
}

function sternPoint(x, y, vx, vy) {
  const a = boatAngle(vx, vy);
  return { x: x - Math.cos(a) * 25, y: y - Math.sin(a) * 25 };
}

function render(now, dt) {
  const course = viewCourse();
  if (!course) return;
  const alpha = renderAlpha(now);
  const sim = G.state === 'menu' ? G.attract.sim : G.sim;
  const bs = boatRenderState(sim, alpha);
  if (G.state === 'ready' || (G.state === 'paused' && G.prevState === 'ready')) { bs.x = 0; bs.y = RIVER_H / 2 + Math.sin(VT * 2.2) * 4; bs.vy = Math.cos(VT * 2.2) * 9; }
  let camBoatX = bs.x;
  if ((G.state === 'dead' || G.state === 'over') && G.death) camBoatX = G.death.camX;
  // shake
  trauma = Math.max(0, trauma - dt * 1.6);
  const sh = S.shake ? trauma * trauma * 14 : 0;
  V.sx = sh ? (Math.sin(VT * 61) + Math.sin(VT * 37.3)) * 0.5 * sh : 0;
  V.sy = sh ? (Math.sin(VT * 53.7) + Math.cos(VT * 41.1)) * 0.5 * sh : 0;
  V.camX = camBoatX - V.boatOff;
  const revealX = camBoatX + REVEAL;     // nothing past this line is ever drawn — same on every screen
  course.ensure(V.camX + V.visW + 800);
  const tick = visualTick(sim, alpha);
  const s = V.s;

  const mid = V.camX + V.visW * 0.5;
  const bm = biomeMix(course, mid);
  const Ba = BIOMES[bm.a], Bb = BIOMES[bm.b];
  const lerpB = k => Ba[k] + (Bb[k] - Ba[k]) * bm.t;
  const night = lerpB('night');
  const flow = course.speedAt(V.camX) * 0.6;
  if (G.state !== 'paused') G.flowAcc += flow * dt;
  const hasWater = !!(water && !water.lost);

  // trail bookkeeping (world points at the stern)
  if (sim && sim.alive && (G.state === 'play' || G.state === 'menu')) trail.push(Object.assign(sternPoint(bs.x, bs.y, bs.vx, bs.vy), { t: VT }));
  while (trail.length && VT - trail[0].t > TRAIL_LIFE) trail.shift();

  // ── WATER (WebGL) ──
  if (hasWater) {
    for (let i = 0; i < 256; i++) {
      const sx = (i + 0.5) / 256 * V.w, wx = V.camX + (sx - V.sx) / s;
      profile[i * 4] = (course.bankTop(wx) - V.camY) * s + V.sy;
      profile[i * 4 + 1] = (course.bankBot(wx) - V.camY) * s + V.sy;
      // current & rapids carry gameplay information: never sample them past the reveal line
      const wc = Math.min(wx, revealX);
      profile[i * 4 + 2] = course.flowAt(wc) * (course._countLE(course.flips, wc) > 0 ? 1 : 0.55);
      const gi = course.gateIndexAt(wc - 220);
      let near = 0;
      for (let q = gi; q <= gi + 1 && q < course.gates.length; q++) near = Math.max(near, clamp(1 - Math.abs(course.gates[q].x - wc) / 220, 0, 1));
      profile[i * 4 + 3] = clamp(course.difficultyAt(wc) * 0.45 + near * 0.35, 0, 1);
    }
    let on = 0;
    const pushO = (x, y, r, kind) => {
      if (on >= N_OBS || x > revealX) return;
      const sx = (x - V.camX) * s + V.sx;
      if (sx < -(7 * r * s + 56) || sx > V.w + 2.6 * r * s + 20) return;
      if (y < course.bankTop(x) - r * 0.5 || y > course.bankBot(x) + r * 0.5) return;
      obsArr[on * 4] = sx; obsArr[on * 4 + 1] = (y - V.camY) * s + V.sy; obsArr[on * 4 + 2] = r * s; obsArr[on * 4 + 3] = kind; on++;
    };
    const pushGate = g => {
      const off = moveOffset(g.move, tick);
      const kind = g.kind === 'bridge' ? 3 : g.kind === 'rocks' ? (BIOMES[g.biome].rock.ice ? 2 : 0) : 1;
      for (const sh2 of g.shapes) {
        if (sh2.t === 0) { pushO(sh2.x, sh2.y + off, sh2.r, kind); continue; }
        const L = Math.hypot(sh2.x2 - sh2.x1, sh2.y2 - sh2.y1), n = Math.max(1, Math.ceil(L / (sh2.r * 2.4)));
        // water end first, so the visible part of a log always gets its foam
        const tipFirst = Math.abs(sh2.y2 - RIVER_H / 2) < Math.abs(sh2.y1 - RIVER_H / 2);
        for (let k = 0; k <= n; k++) { const t = tipFirst ? 1 - k / n : k / n; pushO(sh2.x1 + (sh2.x2 - sh2.x1) * t, sh2.y1 + (sh2.y2 - sh2.y1) * t + off, sh2.r, kind); }
      }
    };
    // gates ahead of the boat get priority; passed gates only fill what is left
    const gB = course.gateIndexAt(camBoatX - 60);
    for (let gi = gB; gi < course.gates.length && course.gates[gi].x - course.gates[gi].halfW < Math.min(V.camX + V.visW + 100, revealX); gi++) pushGate(course.gates[gi]);
    for (let gi = gB - 1; gi >= 0 && course.gates[gi].x + course.gates[gi].halfW > V.camX - 400; gi--) pushGate(course.gates[gi]);
    // trail: resampled by age so the wake has the same length at any refresh rate
    let tn = 0;
    for (let q = 0, j = trail.length - 1; q < 32 && j >= 0; q++) {
      const want = VT - (q / 31) * TRAIL_LIFE;
      while (j > 0 && trail[j].t > want) j--;
      const p = trail[j], age = (VT - p.t) / TRAIL_LIFE;
      trailArr[tn * 4] = (p.x + flow * (VT - p.t) - V.camX) * s + V.sx; trailArr[tn * 4 + 1] = (p.y - V.camY) * s + V.sy;
      trailArr[tn * 4 + 2] = clamp(age, 0, 1); trailArr[tn * 4 + 3] = 1; tn++;
      if (p.t > want) break;          // ran out of history
    }
    let rn = 0;
    for (const r of ripples) {
      const age = (VT - r.t) / r.dur;
      if (age >= 1 || rn >= 16) continue;
      ripArr[rn * 4] = (r.x + flow * (VT - r.t) - V.camX) * s + V.sx; ripArr[rn * 4 + 1] = (r.y - V.camY) * s + V.sy;
      ripArr[rn * 4 + 2] = age; ripArr[rn * 4 + 3] = r.str; rn++;
    }
    const pa = WPAL[bm.a], pb = WPAL[bm.b];
    const mixA = (a, b) => [a[0] + (b[0] - a[0]) * bm.t, a[1] + (b[1] - a[1]) * bm.t, a[2] + (b[2] - a[2]) * bm.t];
    const pal = { deep: mixA(pa.deep, pb.deep), shallow: mixA(pa.shallow, pb.shallow), bed: mixA(pa.bed, pb.bed), foam: mixA(pa.foam, pb.foam), sky: mixA(pa.sky, pb.sky), sun: mixA(pa.sun, pb.sun) };
    try {
      water.render({
        time: VT, camX: V.camX - V.sx / s, camY: V.camY - V.sy / s, scale: s, waterOffsetX: V.camX - V.sx / s - G.flowAcc, flowSpeed: flow,
        profile, obstacles: obsArr, obstacleCount: on, trail: trailArr, trailCount: tn, ripples: ripArr, rippleCount: rn,
        boat: [(bs.x - V.camX) * s + V.sx, (bs.y - V.camY) * s + V.sy], palette: pal, night, lanternRadius: 150 * s,
        clarity: WCLAR[bm.a] + (WCLAR[bm.b] - WCLAR[bm.a]) * bm.t, quality: qualityLevel === 2 ? 1 : 0.35,
      });
    } catch (e) { console.warn('water render failed, falling back', e); water = null; }
  }

  // ── SCENE (2D) ── the water is composited first so blend modes see real pixels
  const c = ctx;
  c.setTransform(1, 0, 0, 1, 0, 0);
  c.globalAlpha = 1; c.globalCompositeOperation = 'source-over';
  if (water && !water.lost) c.drawImage(cvW, 0, 0, cv.width, cv.height);
  else c.clearRect(0, 0, cv.width, cv.height);
  const k = s * V.dpr;
  c.setTransform(k, 0, 0, k, (-V.camX * s + V.sx) * V.dpr, (-V.camY * s + V.sy) * V.dpr);

  if (!water || water.lost) drawWaterFallback(c, course, bm, flow);

  // 2D wake lines (subtle accent over the shader wake; the whole wake without WebGL)
  const wakeK = water ? 0.35 : 1;
  drawWake(c, trail, flow, '255,255,255', wakeK);
  if (S.ghosts) for (const gh of G.ghosts) { const tr = ghostTrails.get(gh); if (tr) drawWake(c, tr, flow, '190,240,255', wakeK * 0.5); }

  // foam particles (water level)
  for (const p of parts) if (p.k === 'foam' || (p.k === 'leaf' && p.z <= 0) || p.k === 'bubble') drawParticle(c, p);

  // land chunks
  const [k0, k1] = ensureChunks(course);
  for (let kk = k0; kk <= k1; kk++) { const ch = chunks.get(kk); if (ch) c.drawImage(ch.ground, ch.x0, ch.y0, ch.x1 - ch.x0, ch.y1 - ch.y0); }
  drawStartLine(c, course);

  // ── everything that carries gameplay information is clipped to the reveal line ──
  c.save();
  c.beginPath(); c.rect(V.camX - 400, V.camY - 400, revealX - V.camX + 400, V.visH + 800); c.clip();
  drawFlipMarkers(c, course, revealX);
  const decks = [];
  for (let gi = course.gateIndexAt(V.camX - 160); gi < course.gates.length; gi++) {
    const g = course.gates[gi];
    if (g.x - g.halfW > revealX || g.x - g.halfW > V.camX + V.visW + 40) break;
    const a = revealAlpha(g.x, revealX);
    if (a <= 0) continue;
    const B = BIOMES[g.biome];
    const off = moveOffset(g.move, tick);
    c.globalAlpha = a;
    if (g.kind === 'rocks') {
      for (const s2 of g.shapes) {
        const vr = s2.r / 0.92, sp = rockSprite(vr, s2.v, g.biome), h = sp.half * vr / sp.vq;
        c.drawImage(sp.c, s2.x - h, s2.y + off - h, h * 2, h * 2);
      }
    } else if (g.kind === 'logs' || g.kind === 'boom') {
      for (const s2 of g.shapes) drawLog(c, s2, off, g.biome, g.kind === 'boom');
    } else if (g.kind === 'bridge') {
      for (const s2 of g.shapes) drawPillar(c, s2, B);
      decks.push(g);
    }
    c.globalAlpha = 1;
  }
  const taken = sim ? sim.taken : [];
  const visStars = [];
  for (let si = course.starIndexAt(V.camX - 40); si < course.stars.length; si++) {
    const st = course.stars[si];
    if (st.x > Math.min(revealX, V.camX + V.visW + 40)) break;
    if (!taken.includes(st.id)) { visStars.push(st); drawStar(c, st, VT, revealAlpha(st.x, revealX)); }
  }

  // ghosts (each drawn opaque into a sprite, then blended once → no see-through layers)
  const labels = [];
  if (S.ghosts && G.state !== 'menu') {
    for (const gh of G.ghosts) {
      const gs = gh.sim;
      let gx, gy, gvy;
      if (G.state === 'ready' || (G.state === 'paused' && G.prevState === 'ready')) { gx = 0; gy = RIVER_H / 2 + Math.sin(VT * 2.2 + 1) * 4; gvy = 0; }
      else { const r = boatRenderState(gs, alpha); gx = r.x; gy = r.y; gvy = r.vy; }
      let ga = 0.55;
      if (!gs.alive) ga = Math.max(0, 0.55 - (G.sim.tick - gs.deathTick) / 120 * 0.55);
      if (ga <= 0.01) continue;
      drawGhost(c, gx, gy, boatAngle(gs.vx, gvy), paddlePose(gh.pad, VT), gh.style, ga, night);
      labels.push({ x: gx, y: gy - 24, text: gh.name, col: gh.style === 'pb' ? '#efe0ff' : '#dff7ff', a: Math.min(1, ga * 1.8) });
    }
  }

  // player / attract boat
  const deathPose = (G.state === 'dead' || G.state === 'over') ? G.death : (G.state === 'menu' && !G.attract.sim.alive) ? G.attract.death : null;
  if (deathPose) {
    const d = deathPose, p = clamp((VT - d.t) / 1.4, 0, 1);
    if (p < 1) {
      c.save(); c.translate(d.x + flow * 0.25 * (VT - d.t), d.y); c.scale(1 - p * 0.35, 1 - p * 0.35);
      drawBoat(c, 0, 0, d.ang + d.spin * (1 - Math.pow(1 - p, 2)) * 2.4, paddlePose(null, VT), 'player', 1 - p * p, night);
      c.restore();
    }
  } else if (sim) {
    const st = G.state === 'menu' ? G.attract.pad : G.pad;
    drawBoat(c, bs.x, bs.y, boatAngle(bs.vx, bs.vy), paddlePose(st, VT), 'player', 1, night);
  }

  // flying particles
  for (const p of parts) if (p.k !== 'foam' && !(p.k === 'leaf' && p.z <= 0) && p.k !== 'bubble' && p.k !== 'fly' && p.k !== 'text') drawParticle(c, p);

  // bridge decks (above boats); stars in a bridge gap are re-drawn on top so the bonus is never hidden
  for (const g of decks) {
    const under = Math.abs(bs.x - g.x) < 40;
    drawDeck(c, g, BIOMES[g.biome], (under ? 0.5 : 1) * revealAlpha(g.x, revealX));
    for (const st of visStars) if (Math.abs(st.x - g.x) < 30) drawStar(c, st, VT, revealAlpha(st.x, revealX));
  }
  if (S.hitbox && sim) drawHitboxes(c, course, sim, tick, revealX);
  c.restore();

  // canopies
  for (let kk = k0; kk <= k1; kk++) { const ch = chunks.get(kk); if (ch && ch.hasCanopy) c.drawImage(ch.canopy, ch.x0, ch.y0, ch.x1 - ch.x0, ch.y1 - ch.y0); }

  // birds gliding high above (day only) + drifting cloud shadows
  const day = 1 - night - lerpB('dim');
  if (day > 0.4 && qualityLevel > 0) drawBirds(c, day);
  if (day > 0.3 && qualityLevel > 0) {
    const cs = glowSprite('rgba(0,18,30,0.9)', 'cloud');
    c.globalAlpha = 0.13 * day;
    const SP = 1500; // world-anchored, slowly drifting downstream
    for (let i = 0; i < 3; i++) {
      const base = i * 517 + VT * 22, r = 260 + (i % 2) * 130;
      const cy = RIVER_H * (0.1 + 0.4 * i) + Math.sin(VT * 0.05 + i) * 40;
      for (let cx = base + Math.floor((V.camX - r - base) / SP + 1) * SP; cx < V.camX + V.visW + r; cx += SP)
        c.drawImage(cs.c, cx - r, cy - r * 0.6, r * 2, r * 1.2);
    }
    c.globalAlpha = 1;
  }

  // fireflies (additive)
  c.globalCompositeOperation = 'lighter';
  const fg = glowSprite('rgba(220,255,140,0.9)', 'fly');
  for (const p of parts) if (p.k === 'fly') {
    const a = Math.min(1, p.age, p.life - p.age) * (0.5 + 0.5 * Math.sin(p.ph * 4 + p.s));
    c.globalAlpha = a * 0.8; c.drawImage(fg.c, p.x - 6, p.y - 6, 12, 12);
  }
  c.globalAlpha = 1; c.globalCompositeOperation = 'source-over';

  // ── the fog wall: fully opaque from the reveal line on, with soft world-anchored billows ──
  const mistC = mixHex(Ba.mist, Bb.mist, bm.t);
  const fogC = mixHex(mistC, '#0b1626', night * 0.72);
  const fogEnd = V.camX + V.visW + 60;
  if (revealX - 140 < fogEnd) {
    const mg = c.createLinearGradient(revealX - 120, 0, revealX, 0);
    mg.addColorStop(0, rgba(fogC, 0)); mg.addColorStop(0.65, rgba(fogC, 0.7)); mg.addColorStop(1, rgba(fogC, 1));
    c.fillStyle = mg; c.fillRect(revealX - 120, V.camY - 40, 120, V.visH + 80);
    c.fillStyle = fogC; c.fillRect(revealX - 0.5, V.camY - 40, Math.max(0, fogEnd - revealX + 0.5), V.visH + 80);
    for (let i = -3; i <= 11; i++) {
      const y = i * 72 + Math.sin(VT * 0.35 + i * 1.9) * 22;
      if (y < V.camY - 140 || y > V.camY + V.visH + 140) continue;
      const x = revealX - 40 + Math.sin(VT * 0.27 + i * 2.3) * 18, r = 70 + 22 * Math.sin(i * 2.7 + VT * 0.21);
      const pg = c.createRadialGradient(x, y, 0, x, y, r);
      pg.addColorStop(0, rgba(fogC, 0.5)); pg.addColorStop(1, rgba(fogC, 0));
      c.fillStyle = pg; c.fillRect(x - r, y - r, r * 2, r * 2);
    }
  }

  // ── screen-space post: lighting, grade, rays, labels, vignette, flash ──
  c.setTransform(V.dpr, 0, 0, V.dpr, 0, 0);
  const toSX = wx => (wx - V.camX) * s + V.sx, toSY = wy => (wy - V.camY) * s + V.sy;
  const darkness = lerpB('dim');
  const lightsIn = [];
  for (let kk = k0; kk <= k1; kk++) { const ch = chunks.get(kk); if (ch) for (const L of ch.lights) if (L.x < revealX - 30) lightsIn.push(L); }
  if (darkness > 0.01) {
    const lw = lightCv.width, lh = lightCv.height, q = lw / V.w;
    if (!holeSprite) {
      holeSprite = document.createElement('canvas'); holeSprite.width = holeSprite.height = 64;
      const hx = holeSprite.getContext('2d'), hg = hx.createRadialGradient(32, 32, 0, 32, 32, 32);
      hg.addColorStop(0, 'rgba(0,0,0,1)'); hg.addColorStop(0.5, 'rgba(0,0,0,0.6)'); hg.addColorStop(1, 'rgba(0,0,0,0)');
      hx.fillStyle = hg; hx.fillRect(0, 0, 64, 64);
    }
    lctx.globalCompositeOperation = 'source-over'; lctx.globalAlpha = 1;
    lctx.clearRect(0, 0, lw, lh);
    lctx.fillStyle = night > 0.5 ? `rgba(4,8,26,${darkness})` : `rgba(22,18,46,${darkness})`;
    lctx.fillRect(0, 0, lw, lh);
    lctx.globalCompositeOperation = 'destination-out';
    const hole = (wx, wy, r, str) => {
      const x = toSX(wx) * q, y = toSY(wy) * q, rr = r * s * q;
      lctx.globalAlpha = str; lctx.drawImage(holeSprite, x - rr, y - rr, rr * 2, rr * 2);
    };
    if (sim && G.state !== 'over' && G.state !== 'dead') hole(bs.x + 10, bs.y, 175, 0.95);
    else if (G.death) hole(G.death.x, G.death.y, 140 * (1 - clamp((VT - G.death.t) / 2, 0, 0.7)), 0.9);
    if (S.ghosts && G.state !== 'menu') for (const gh of G.ghosts) if (gh.sim.alive) hole(G.state === 'ready' ? 0 : gh.sim.x, gh.sim.y, 70, 0.6);
    for (const L of lightsIn) hole(L.x, L.y, 95 + Math.sin(VT * 13 + L.x) * 6, 0.85);
    for (const st of visStars) if (st.x < revealX - 20) hole(st.x, st.y, 46, 0.7);
    for (const p of parts) if (p.k === 'fly') hole(p.x, p.y, 22, 0.5);
    lctx.globalAlpha = 1; lctx.globalCompositeOperation = 'source-over';
    c.drawImage(lightCv, 0, 0, V.w, V.h);
    // warm lantern & fire glow (truly additive now that the canvas is opaque)
    c.globalCompositeOperation = 'lighter';
    const lg = glowSprite('rgba(255,170,70,0.5)', 'lantern');
    const glowAt = (wx, wy, r, a) => { const x = toSX(wx), y = toSY(wy), rr = r * s; c.globalAlpha = a; c.drawImage(lg.c, x - rr, y - rr, rr * 2, rr * 2); };
    if (sim && G.state !== 'over' && G.state !== 'dead') glowAt(bs.x + 14, bs.y, 120, 0.4 * night + 0.06);
    for (const L of lightsIn) glowAt(L.x, L.y, 60 + Math.sin(VT * 11 + L.x) * 5, 0.6);
    c.globalAlpha = 1; c.globalCompositeOperation = 'source-over';
    for (const L of lightsIn) drawFlame(c, toSX(L.x), toSY(L.y), s);
  }
  // colour grade (soft-light on real pixels)
  const gradeC = mixHex(Ba.grade, Bb.grade, bm.t), gradeA = lerpB('gradeA');
  c.globalCompositeOperation = 'soft-light';
  c.fillStyle = rgba(gradeC, gradeA * 0.8);
  c.fillRect(0, 0, V.w, V.h);
  c.globalCompositeOperation = 'source-over';
  const rays = lerpB('rays');
  if (rays > 0.02 && qualityLevel > 0) drawRays(c, rays);
  // the current-direction hint sits above lighting and grade so it never washes out
  if (sim && sim.alive && (G.state === 'play' || G.state === 'ready' || G.state === 'paused')) {
    c.setTransform(k, 0, 0, k, (-V.camX * s + V.sx) * V.dpr, (-V.camY * s + V.sy) * V.dpr);
    drawCurrentHint(c, bs, course);
    c.setTransform(V.dpr, 0, 0, V.dpr, 0, 0);
  }
  // labels & floating texts in screen space so they stay legible on phones
  const fs = Math.max(11, 11 * s * 1.15);
  c.textAlign = 'center';
  for (const L of labels) {
    if (L.x > revealX) continue;
    c.globalAlpha = L.a;
    c.font = `600 ${fs}px system-ui, sans-serif`;
    c.fillStyle = 'rgba(0,0,0,0.5)'; c.fillText(L.text, toSX(L.x) + 1, toSY(L.y) + 1);
    c.fillStyle = L.col; c.fillText(L.text, toSX(L.x), toSY(L.y));
  }
  c.globalAlpha = 1;
  for (const p of parts) if (p.k === 'text') drawFloatText(c, p, toSX(p.x), toSY(p.y));
  c.drawImage(vigCv, 0, 0, V.w, V.h);
  if (flash > 0.01) { c.fillStyle = `rgba(${flashColor},${flash})`; c.fillRect(0, 0, V.w, V.h); flash *= Math.pow(0.02, dt); }
}

function drawGhost(c, x, y, ang, pad, style, alpha, night) {
  const px = V.s * V.dpr, size = Math.ceil(80 * px);
  if (ghostCv.width !== size) { ghostCv.width = ghostCv.height = size; }
  gctx.setTransform(1, 0, 0, 1, 0, 0);
  gctx.clearRect(0, 0, size, size);
  gctx.setTransform(px, 0, 0, px, size / 2, size / 2);
  drawBoat(gctx, 0, 0, ang, pad, style, 1, night);
  c.globalAlpha = alpha;
  c.drawImage(ghostCv, x - 40, y - 40, 80, 80);
  c.globalAlpha = 1;
}

function drawFloatText(c, p, x, y) {
  const t = p.age / p.life;
  const size = Math.max(13, (p.size || 15) * V.s * 1.1);
  c.globalAlpha = 1 - t * t;
  c.font = `800 ${size}px "Bahnschrift", "Segoe UI", system-ui, sans-serif`;
  c.textAlign = 'center';
  c.lineWidth = 3.5; c.strokeStyle = 'rgba(0,30,40,0.6)'; c.strokeText(p.text, x, y);
  c.fillStyle = p.col || '#fff'; c.fillText(p.text, x, y);
  c.globalAlpha = 1;
}

function drawFlame(c, x, y, s) {
  c.save(); c.translate(x, y); c.scale(s, s);
  c.globalCompositeOperation = 'lighter';
  for (let i = 0; i < 3; i++) {
    const f = Math.sin(VT * 17 + i * 2.1) * 1.5, h = 8 + Math.sin(VT * 9 + i) * 2;
    c.fillStyle = i === 0 ? 'rgba(255,90,20,0.7)' : i === 1 ? 'rgba(255,170,40,0.7)' : 'rgba(255,240,170,0.8)';
    c.beginPath(); c.moveTo(-4 + i, 0); c.quadraticCurveTo(f, -h * (1 - i * 0.25), 4 - i, 0); c.fill();
  }
  c.restore();
}

function drawRays(c, a) {
  const t = VT * 0.15;
  c.save();
  c.globalCompositeOperation = 'screen';
  for (let i = 0; i < 4; i++) {
    const x = V.w * (0.1 + i * 0.27) + Math.sin(t + i * 1.7) * 40;
    const w = V.w * (0.06 + 0.04 * Math.sin(t * 1.3 + i));
    const g = c.createLinearGradient(x, 0, x + V.h * 0.5, V.h);
    g.addColorStop(0, `rgba(255,236,200,${0.06 * a})`); g.addColorStop(1, 'rgba(255,236,200,0)');
    c.fillStyle = g;
    c.beginPath(); c.moveTo(x, -10); c.lineTo(x + w, -10); c.lineTo(x + w + V.h * 0.55, V.h + 10); c.lineTo(x + V.h * 0.55, V.h + 10); c.closePath(); c.fill();
  }
  c.restore();
}

// Wake lines batched into a few alpha buckets: one stroke per bucket instead of per segment.
function drawWake(c, tr, flow, rgb, k = 1) {
  if (tr.length < 3) return;
  const BUCKETS = 6;
  c.lineCap = 'round';
  for (let b = 0; b < BUCKETS; b++) {
    const a0 = b / BUCKETS, a1 = (b + 1) / BUCKETS, am = (a0 + a1) / 2;
    c.beginPath();
    let any = false;
    for (let i = tr.length - 1; i > 0; i--) {
      const p = tr[i], q = tr[i - 1];
      const ap = VT - p.t, aq = VT - q.t, age = ap / TRAIL_LIFE;
      if (age >= 1) break;
      if (age < a0 || age >= a1) continue;
      const px = p.x + flow * ap, py = p.y, qx = q.x + flow * aq, qy = q.y;
      let dx = px - qx, dy = py - qy;
      const l = Math.hypot(dx, dy) || 1; dx /= l; dy /= l;
      const nx = -dy, ny = dx, op = 6 + age * 26, oq = 6 + (aq / TRAIL_LIFE) * 26;
      c.moveTo(px + nx * op, py + ny * op); c.lineTo(qx + nx * oq, qy + ny * oq);
      c.moveTo(px - nx * op, py - ny * op); c.lineTo(qx - nx * oq, qy - ny * oq);
      any = true;
    }
    if (!any) continue;
    c.strokeStyle = `rgba(${rgb},${(0.42 * (1 - am) * k).toFixed(3)})`;
    c.lineWidth = 2.6 * (1 - am) + 0.4;
    c.stroke();
  }
}

// Particles use globalAlpha with fixed colours (no per-particle colour strings).
function drawParticle(c, p) {
  const t = clamp(p.age / p.life, 0, 1);
  switch (p.k) {
    case 'drop': c.globalAlpha = 0.85 * (1 - t); c.fillStyle = '#e6f8ff'; c.beginPath(); c.arc(p.x, p.y - p.z * 0.4, p.s, 0, TAU); c.fill(); break;
    case 'foam': c.globalAlpha = 0.55 * (1 - t); c.fillStyle = '#ffffff'; c.beginPath(); c.arc(p.x, p.y, p.s * (1 + t * 1.5), 0, TAU); c.fill(); break;
    case 'bubble': c.globalAlpha = 0.6 * (1 - t); c.strokeStyle = '#e6faff'; c.lineWidth = 0.8; c.beginPath(); c.arc(p.x, p.y, p.s, 0, TAU); c.stroke(); break;
    case 'splinter': c.save(); c.translate(p.x, p.y); c.rotate(p.rot); c.globalAlpha = 1 - t * t; c.fillStyle = p.col; c.fillRect(-p.s, -p.s * 0.3, p.s * 2, p.s * 0.6); c.restore(); break;
    case 'spark':
      c.globalCompositeOperation = 'lighter'; c.globalAlpha = 1 - t;
      c.fillStyle = t < 0.5 ? '#fff4c0' : '#ffc878';
      c.beginPath(); c.arc(p.x, p.y, p.s * (1 - t * 0.5), 0, TAU); c.fill();
      c.globalCompositeOperation = 'source-over'; break;
    case 'leaf': c.save(); c.translate(p.x + p.z * 0.4, p.y + p.z * 0.6); c.rotate(p.rot); c.globalAlpha = Math.min(1, (p.life - p.age) * 0.8); c.fillStyle = p.col; c.beginPath(); c.ellipse(0, 0, 4, 2, 0, 0, TAU); c.fill(); c.restore(); break;
    case 'snow': c.globalAlpha = 0.85 * Math.min(1, p.life - p.age); c.fillStyle = '#ffffff'; c.beginPath(); c.arc(p.x, p.y, p.s, 0, TAU); c.fill(); break;
    case 'mote': c.globalAlpha = (p.dust ? 0.35 : 0.6) * Math.sin(t * Math.PI); c.fillStyle = p.dust ? '#ffd2a0' : '#fffadc'; c.beginPath(); c.arc(p.x, p.y, p.s, 0, TAU); c.fill(); break;
  }
  c.globalAlpha = 1;
}

function drawCurrentHint(c, bs, course) {
  const cur = course.currentAt(bs.x), fl = Math.abs(course.flowAt(bs.x));
  const t = (VT * 1.6) % 1;
  const since = VT - (G.flipAt || -99), k = since < 2.5 ? 1.6 - 0.24 * since : 1;   // louder right after a flip
  c.save();
  c.lineCap = 'round'; c.lineJoin = 'round';
  for (let i = 0; i < 2; i++) {
    const ph = (t + i * 0.5) % 1, d = 36 + ph * 22, y = bs.y + cur * d, w = 9 * k, h = 5.5 * k;
    c.globalAlpha = (1 - ph) * 0.9 * (0.3 + 0.7 * fl);
    c.beginPath(); c.moveTo(bs.x - w, y - cur * h); c.lineTo(bs.x, y); c.lineTo(bs.x + w, y - cur * h);
    c.strokeStyle = 'rgba(0,20,30,0.55)'; c.lineWidth = 4.6; c.stroke();
    c.strokeStyle = cur > 0 ? '#bfefff' : '#ffb35c'; c.lineWidth = 2.4; c.stroke();
  }
  c.restore();
}

function drawFlipMarkers(c, course, revealX) {
  for (const fx of course.flips) {
    const fw = course.lv.flipW || 0;
    if (fx + fw < V.camX - 60 || fx - fw > Math.min(revealX, V.camX + V.visW + 60)) continue;
    const after = course.currentAt(fx + 1);
    c.save();
    c.globalAlpha = revealAlpha(fx, revealX);
    const top = course.bankTop(fx), bot = course.bankBot(fx), W = course.lv.flipW || 26;
    const col = after > 0 ? '120,220,255' : '255,170,80';
    // slack-water band: calm, glassy water where the current fades out and turns
    const calm = c.createLinearGradient(fx - W, 0, fx + W, 0);
    calm.addColorStop(0, 'rgba(225,245,255,0)'); calm.addColorStop(0.3, 'rgba(225,245,255,0.13)'); calm.addColorStop(0.5, 'rgba(225,245,255,0.2)');
    calm.addColorStop(0.7, 'rgba(225,245,255,0.13)'); calm.addColorStop(1, 'rgba(225,245,255,0)');
    c.fillStyle = calm; c.fillRect(fx - W, top, W * 2, bot - top);
    if (W > 40) { // soft wavy eddy lines where the calm water starts and ends
      c.strokeStyle = 'rgba(235,250,255,0.32)'; c.lineWidth = 2; c.setLineDash([14, 12]); c.lineDashOffset = -VT * 18;
      for (const ex of [fx - W * 0.82, fx + W * 0.82]) {
        c.beginPath();
        for (let y = top + 8; y <= bot - 8; y += 12) { const xx = ex + Math.sin(y * 0.045 + VT * 1.6 + ex) * 5; if (y === top + 8) c.moveTo(xx, y); else c.lineTo(xx, y); }
        c.stroke();
      }
      c.setLineDash([]);
    }
    const g = c.createLinearGradient(fx - 26, 0, fx + 26, 0);
    g.addColorStop(0, `rgba(${col},0)`); g.addColorStop(0.5, `rgba(${col},0.28)`); g.addColorStop(1, `rgba(${col},0)`);
    c.fillStyle = g; c.fillRect(fx - 26, top, 52, bot - top);
    c.strokeStyle = `rgba(${col},0.9)`; c.lineWidth = 3; c.lineCap = 'round'; c.lineJoin = 'round';
    const ph = (VT * 60) % 40;
    c.beginPath();
    for (let y = top + 20 + (after > 0 ? ph : 40 - ph); y < bot - 10; y += 40) { c.moveTo(fx - 9, y - after * 6); c.lineTo(fx, y + after * 3); c.lineTo(fx + 9, y - after * 6); }
    c.stroke();
    c.restore();
  }
}

// A flock crosses the view every ~18 s (purely cosmetic, uses the visual clock)
function drawBirds(c, a) {
  const period = 18, ph = VT / period, k = Math.floor(ph), t = ph - k;
  if (t > 0.55) return;
  const seed = hash32(k, 0xB1D);
  const n = 3 + (seed % 4);
  const dir = (seed >> 3) & 1 ? 1 : -1;
  const y0 = V.camY + V.visH * (0.15 + rnd(seed, 1) * 0.7);
  const span = V.visW + 400;
  const x0 = dir > 0 ? V.camX - 200 + t / 0.55 * span : V.camX + V.visW + 200 - t / 0.55 * span;
  const silhouette = (bx, by, flap, col) => {
    c.fillStyle = col;
    c.beginPath(); c.ellipse(bx, by, 5, 1.8, 0, 0, TAU); c.fill();                 // body
    c.beginPath(); c.arc(bx + dir * 5, by, 1.6, 0, TAU); c.fill();                  // head
    for (const sd of [-1, 1]) {                                                       // wings
      const tip = by + sd * (9 + flap * 3);
      c.beginPath(); c.moveTo(bx + dir * 2, by);
      c.quadraticCurveTo(bx - dir * 1, tip, bx - dir * 6, tip + sd * 1.5);
      c.quadraticCurveTo(bx - dir * 3, by + sd * 3, bx - dir * 3, by); c.closePath(); c.fill();
    }
  };
  for (let i = 0; i < n; i++) {
    const row = Math.ceil(i / 2), side = i % 2 ? 1 : -1;
    const bx = x0 - dir * row * 26, by = y0 + side * row * 18 + Math.sin(VT * 1.3 + i) * 3;
    const flap = Math.sin(VT * 8 + i * 1.7);
    silhouette(bx + 60, by + 90, flap, `rgba(0,20,30,${0.16 * a})`);              // shadow far below
    silhouette(bx, by, flap, `rgba(38,44,58,${0.75 * a})`);
  }
}

function drawStartLine(c, course) {
  const x = 64;
  if (x < V.camX - 60 || x > V.camX + V.visW + 60) return;
  const top = course.bankTop(x), bot = course.bankBot(x);
  for (let y = top + 22, i = 0; y < bot - 12; y += 34, i++) {
    const bob = Math.sin(VT * 2.4 + i * 1.3) * 1.2;
    c.fillStyle = 'rgba(0,15,25,0.25)'; c.beginPath(); c.arc(x + 2, y + 3 + bob, 5, 0, TAU); c.fill();
    c.fillStyle = i % 2 ? '#f4f4f4' : '#ff5a36'; c.beginPath(); c.arc(x, y + bob, 4.6, 0, TAU); c.fill();
    c.fillStyle = 'rgba(255,255,255,0.7)'; c.beginPath(); c.arc(x - 1.5, y - 1.5 + bob, 1.4, 0, TAU); c.fill();
  }
  for (const [py, dir] of [[top - 12, -1], [bot + 12, 1]]) {
    c.fillStyle = 'rgba(0,15,25,0.3)'; c.fillRect(x + 1, py + 2, 3, 3);
    c.fillStyle = '#5b3d22'; c.beginPath(); c.arc(x, py, 2.4, 0, TAU); c.fill();
    const wave = Math.sin(VT * 5) * 1.5;
    for (let i = 0; i < 4; i++) for (let j = 0; j < 3; j++) {
      c.fillStyle = (i + j) % 2 ? '#111' : '#fafafa';
      c.fillRect(x + 2 + i * 4, py + dir * 2 + (dir < 0 ? -(j + 1) * 4 : j * 4) + wave * (i / 4), 4, 4);
    }
  }
}

function drawHitboxes(c, course, sim, tick, revealX) {
  c.save(); c.lineWidth = 1.2; c.strokeStyle = 'rgba(255,0,80,0.9)';
  const [hx, hy] = sim.heading();
  for (let i = 0; i < 3; i++) { c.beginPath(); c.arc(sim.x + hx * PHYS.hitOff[i], sim.y + hy * PHYS.hitOff[i], PHYS.hitR[i], 0, TAU); c.stroke(); }
  c.strokeStyle = 'rgba(255,230,0,0.8)';
  for (let gi = course.gateIndexAt(V.camX - 140); gi < course.gates.length && course.gates[gi].x - course.gates[gi].halfW < revealX; gi++) {
    const g = course.gates[gi], off = moveOffset(g.move, tick);
    for (const s of g.shapes) {
      c.beginPath();
      if (s.t === 0) c.arc(s.x, s.y + off, s.r, 0, TAU);
      else { const a = Math.atan2(s.y2 - s.y1, s.x2 - s.x1); c.arc(s.x1, s.y1 + off, s.r, a + Math.PI / 2, a - Math.PI / 2); c.arc(s.x2, s.y2 + off, s.r, a - Math.PI / 2, a + Math.PI / 2); c.closePath(); }
      c.stroke();
    }
  }
  edgeLine(c, course, V.camX, revealX, true, 0); c.stroke();
  edgeLine(c, course, V.camX, revealX, false, 0); c.stroke();
  c.restore();
}

// 2D fallback water when WebGL2 is unavailable
let fbWaterTile = null;
function drawWaterFallback(c, course, bm, flow) {
  const pa = WPAL[bm.a], pb = WPAL[bm.b];
  const col = (k, f) => { const a = pa[k], b = pb[k]; return `rgb(${[0, 1, 2].map(i => Math.round((a[i] + (b[i] - a[i]) * bm.t) * 255 * f)).join(',')})`; };
  const g = c.createLinearGradient(0, 0, 0, RIVER_H);
  g.addColorStop(0, col('shallow', 1)); g.addColorStop(0.18, col('deep', 1.05)); g.addColorStop(0.5, col('deep', 0.9)); g.addColorStop(0.82, col('deep', 1.05)); g.addColorStop(1, col('shallow', 1));
  c.fillStyle = g; c.fillRect(V.camX - 10, V.camY - 10, V.visW + 20, V.visH + 20);
  if (!fbWaterTile) {
    fbWaterTile = document.createElement('canvas'); fbWaterTile.width = 256; fbWaterTile.height = 256;
    const x = fbWaterTile.getContext('2d');
    x.strokeStyle = 'rgba(255,255,255,0.10)'; x.lineCap = 'round';
    for (let i = 0; i < 140; i++) { const px = Math.random() * 256, py = Math.random() * 256, l = 10 + Math.random() * 40; x.lineWidth = 0.6 + Math.random() * 1.6; x.beginPath(); x.moveTo(px, py); x.quadraticCurveTo(px + l / 2, py + (Math.random() - 0.5) * 6, px + l, py); x.stroke(); }
  }
  const pat = c.createPattern(fbWaterTile, 'repeat');
  const off = (V.camX - G.flowAcc) % 256;
  c.save(); c.translate(V.camX - off - 256, V.camY - 256);
  c.fillStyle = pat; c.fillRect(0, 0, V.visW + 768, V.visH + 512);
  c.restore();
  // foam rings around rocks
  c.strokeStyle = 'rgba(255,255,255,0.35)'; c.lineWidth = 3;
  for (const r of ripples) { const age = (VT - r.t) / r.dur; if (age < 1) { c.globalAlpha = 1 - age; c.beginPath(); c.arc(r.x + flow * (VT - r.t), r.y, 8 + age * 60 * r.str, 0, TAU); c.stroke(); } }
  c.globalAlpha = 1;
}

// ─── Simulation driving ────────────────────────────────────────────────────
function newRandomSeed() {
  try { const a = new Uint32Array(1); crypto.getRandomValues(a); return a[0]; } catch { return (Math.random() * 4294967296) >>> 0; }
}

function startAttract() {
  const course = new Course(newRandomSeed(), S.level);
  G.attract = { course, sim: new Sim(course), acc: 0, pad: null, deadAt: 0 };
  if (G.state === 'menu') { trail.length = 0; parts.length = 0; ripples.length = 0; }
}

function updateAttract(dt) {
  const at = G.attract;
  if (!at.sim.alive) {
    if (VT - at.deadAt > 2.2) { fadeSwap(() => { if (G.state === 'menu') startAttract(); }); at.deadAt = VT + 99; }
    return;
  }
  at.acc += dt;
  let n = 0;
  while (at.acc >= DT && n < 30) {
    at.acc -= DT; n++;
    const tap = pilotTap(at.sim, 0.95 + 0.1 * Math.sin(at.sim.tick * 0.013));
    at.sim.step(tap);
    for (const ev of at.sim.events) handleEvent(ev, at.sim, true);
    at.sim.events.length = 0;
    if (!at.sim.alive) { at.deadAt = VT; break; }
  }
  if (n >= 30) at.acc = 0;
}

let fading = false;
function fadeSwap(fn) {
  if (fading) return;
  fading = true;
  const f = $('fade');
  f.classList.add('on');
  setTimeout(() => { fn(); requestAnimationFrame(() => { f.classList.remove('on'); fading = false; }); }, 380);
}

function bladePos(sim, side) {
  const a = boatAngle(sim.vx, sim.vy);
  const lx = 6, ly = side * 26;
  return [sim.x + Math.cos(a) * lx - Math.sin(a) * ly, sim.y + Math.sin(a) * lx + Math.cos(a) * ly];
}

function handleEvent(ev, sim, quiet) {
  const isPlayer = !quiet;
  switch (ev.type) {
    case 'stroke': {
      const holder = quiet ? G.attract : G;
      const side = holder.pad && holder.pad.side ? -holder.pad.side : 1;
      holder.pad = { side, t: VT };
      const [bx, by] = bladePos(sim, side);
      addRipple(bx, by, 0.6, 0.9);
      for (let i = 0; i < 7; i++) spawn({ k: 'drop', x: bx, y: by, z: 2, vx: (Math.random() - 0.7) * 120, vy: side * (20 + Math.random() * 60), vz: 120 + Math.random() * 120, s: 0.9 + Math.random() * 1.3, life: 0.6 });
      for (let i = 0; i < 3; i++) spawn({ k: 'foam', x: bx + (Math.random() - 0.5) * 6, y: by + (Math.random() - 0.5) * 6, s: 2 + Math.random() * 2, life: 0.9, vx: -40, vy: side * 10 });
      if (isPlayer) { A.stroke(side * 0.6, 1); Native.haptic('stroke'); }
      break;
    }
    case 'gate':
      if (isPlayer) {
        G.streak++;
        A.gate(G.streak);
        if (G.sim.gatesPassed >= 1) $('tapHint').classList.add('hidden');
        if (S.tutorial && G.sim.gatesPassed >= 3) { S.tutorial = false; saveSettings(); }
        bumpScore();
        if (ev.near) { spawn({ k: 'text', text: 'Těsně!', x: sim.x + 10, y: sim.y - 30, life: 0.9, col: '#ffe08a', size: 14 }); A.nearMiss(); }
        if (G.sim.score > G.bestBefore && G.bestBefore > 0 && !G.recordFlag) { G.recordFlag = true; showBanner('Nový rekord!', 'Pokračuj, každý bod se počítá', 1600); }
        const sc = G.sim.score;
        if (sc === 10 || sc === 25 || sc === 50 || sc === 75 || sc === 100 || (sc > 100 && sc % 50 === 0)) showBanner(String(sc), sc >= 50 ? 'Legendární jízda!' : 'Skvělé tempo!', 1100);
      }
      break;
    case 'star': {
      for (let i = 0; i < 16; i++) { const a = Math.random() * TAU, v = 60 + Math.random() * 160; spawn({ k: 'spark', x: ev.x, y: ev.y, vx: Math.cos(a) * v, vy: Math.sin(a) * v, s: 1.5 + Math.random() * 2, life: 0.5 + Math.random() * 0.3 }); }
      addRipple(ev.x, ev.y, 0.8, 1);
      if (isPlayer) { spawn({ k: 'text', text: '+1', x: ev.x, y: ev.y - 16, life: 0.8, col: '#ffd34d', size: 17 }); A.star(); bumpScore(); }
      break;
    }
    case 'flip':
      if (isPlayer) {
        A.flip(); Native.haptic('flip'); trauma = Math.min(1, trauma + 0.35); G.flipAt = VT;
        showBanner(ev.cur < 0 ? 'Protiproud!' : 'Proud se vrací', ev.cur < 0 ? 'Proud teď táhne NAHORU — záběr tě pošle dolů' : 'Proud opět táhne dolů', 1700, 2);
      }
      break;
    case 'crash': {
      const [hx, hy] = sim.heading();
      for (let i = 0; i < 26; i++) { const a = Math.random() * TAU, v = 60 + Math.random() * 220; spawn({ k: 'drop', x: ev.x, y: ev.y, z: 2, vx: Math.cos(a) * v, vy: Math.sin(a) * v, vz: 150 + Math.random() * 220, s: 1 + Math.random() * 2, life: 0.9 }); }
      for (let i = 0; i < 16; i++) { const a = Math.random() * TAU, v = 40 + Math.random() * 160; spawn({ k: 'splinter', x: ev.x, y: ev.y, vx: Math.cos(a) * v + hx * 60, vy: Math.sin(a) * v + hy * 60, rot: Math.random() * 6, vr: (Math.random() - 0.5) * 18, s: 2 + Math.random() * 4, life: 1.6, col: Math.random() < 0.5 ? '#e4572e' : '#8a5a33' }); }
      for (let i = 0; i < 12; i++) spawn({ k: 'foam', x: ev.x + (Math.random() - 0.5) * 30, y: ev.y + (Math.random() - 0.5) * 30, s: 3 + Math.random() * 5, life: 1.5, vx: (Math.random() - 0.5) * 60, vy: (Math.random() - 0.5) * 60 });
      for (let i = 0; i < 10; i++) spawn({ k: 'bubble', x: sim.x + (Math.random() - 0.5) * 24, y: sim.y + (Math.random() - 0.5) * 14, s: 1 + Math.random() * 2.5, life: 1 + Math.random() * 1.2 });
      addRipple(ev.x, ev.y, 1.6, 1.6);
      if (quiet) { G.attract.deadAt = VT; G.attract.death = { x: sim.x, y: sim.y, ang: boatAngle(sim.vx, sim.vy), spin: Math.random() < 0.5 ? -1 : 1, t: VT }; break; }
      onPlayerCrash(sim, ev);
      break;
    }
  }
}

function bumpScore() {
  const el = $('hudScore');
  el.textContent = fmtNum(G.sim.score);
  el.classList.remove('pop'); void el.offsetWidth; el.classList.add('pop');
  updateRaceHud();
}

// ─── Czech text helpers ────────────────────────────────────────────────────
const pl = (n, one, few, many) => (n === 1 ? one : n >= 2 && n <= 4 ? few : many);
const bodu = n => `${n} ${pl(n, 'bod', 'body', 'bodů')}`;
const secs = t => t.toFixed(1).replace('.', ',') + ' s';

// ─── Run lifecycle ─────────────────────────────────────────────────────────
function modeLabel(mode, extra) {
  if (mode === 'daily') { const [y, m, d] = extra.split('-'); return `Denní výzva ${+d}. ${+m}. ${y}`; }
  if (mode === 'river') return 'Řeka ' + extra;
  return 'Volná plavba';
}

function prepareRun(opt) {
  // opt: { mode, seed, label, challenge, level }
  G.mode = opt.mode; G.seed = opt.seed >>> 0; G.label = opt.label; G.challenge = opt.challenge || null;
  G.level = levelOf(G.challenge ? G.challenge.level : opt.level ?? S.level).id;
  G.course = new Course(G.seed, G.level);
  G.sim = new Sim(G.course);
  G.taps = []; G.inputQ = []; G.pad = null; G.streak = 0; G.death = null; G.recordFlag = false;
  G.flipWarned = -1; G.pauses = 0; G.resumeAt = 0; G.pauseAlpha = 1;
  G.ghosts = [];
  ghostTrails.clear();
  const own = LR(G.level).seeds[seedHex(G.seed)];
  if (G.challenge) G.ghosts.push(makeGhost(G.challenge.name || 'Soupeř', G.challenge.taps, 'ghost', G.challenge.score));
  if (own && own.code) { try { const r = Replay.decode(own.code); if (r.seed === G.seed && r.level === G.level) G.ghosts.push(makeGhost('Tvůj rekord', r.taps, 'pb', r.score)); } catch { /* other rules version */ } }
  G.bestBefore = bestFor(G.mode, G.seed);
  trail.length = 0; parts.length = 0; ripples.length = 0;
  G.curBiome = 0;
  G.state = 'ready';
  clearTimeout(bannerTimer); bannerPrioUntil = 0; $('banner').classList.remove('show');
  $('fade').classList.remove('on');
  $('hudScore').textContent = '0';
  $('hudMode').textContent = `${G.label} · ${levelName(G.level)}`;
  $('hudBest').textContent = G.bestBefore ? 'Rekord ' + G.bestBefore : '';
  updateRaceHud();
  showScreen(null);
  setHud(true);
  $('tapHint').classList.remove('hidden', 'playing');
  $('tapHint').classList.toggle('first', !!S.tutorial);
  A.setPaused(false);
  A.setMusicState('play');
  blurActive();
}

function makeGhost(name, taps, style, finalScore) {
  return { name, taps, ti: 0, sim: new Sim(G.course), style, pad: null, finalScore };
}

function bestFor(mode, seed) {
  const T = LR(G.level);
  if (mode === 'free' && !G.challenge) return Math.max(T.free.best || 0, 0);
  const r = T.seeds[seedHex(seed)];
  let best = r ? r.best : 0;
  if (mode === 'river' && G.riverName && riverSeed(G.riverName) === seed) best = Math.max(best, T.rivers[G.riverName] || 0);
  if (mode === 'daily' && G.dayKey && dailySeed(G.dayKey) === seed) best = Math.max(best, T.daily[G.dayKey] || 0);
  return best;
}

function beginPlay(ts) {
  G.state = 'play';
  G.t0 = ts;
  if (S.tutorial) $('tapHint').classList.add('playing'); else $('tapHint').classList.add('hidden');
  queueTap(ts);
}

function queueTap(ts) {
  let tick = Math.ceil((ts - G.t0) / TICK_MS - 1e-6);
  if (tick < G.sim.tick) tick = G.sim.tick;
  if (G.inputQ.length && G.inputQ[G.inputQ.length - 1] >= tick) return; // one stroke per tick
  G.inputQ.push(tick);
}

function updatePlay(now) {
  const sim = G.sim;
  let target = Math.floor((now - G.t0) / TICK_MS) + 1;
  // After a hitch, slow time instead of teleporting. Queued strokes move with the clock,
  // so nothing the player did during the hitch is delayed or dropped.
  if (target - sim.tick > 18) {
    const shift = target - sim.tick - 18;
    G.t0 += shift * TICK_MS; target = sim.tick + 18;
    let last = -1;
    G.inputQ = G.inputQ.map(t => Math.max(sim.tick, t - shift)).filter(t => (t > last ? ((last = t), true) : false));
  }
  while (sim.alive && sim.tick < target) {
    let tap = false;
    while (G.inputQ.length && G.inputQ[0] <= sim.tick) { G.inputQ.shift(); tap = true; }
    if (tap) G.taps.push(sim.tick);
    const tickNow = sim.tick;
    for (const gh of G.ghosts) {
      if (!gh.sim.alive) continue;
      let gt = false;
      while (gh.ti < gh.taps.length && gh.taps[gh.ti] <= tickNow) { if (gh.taps[gh.ti] === tickNow) gt = true; gh.ti++; }
      gh.sim.step(gt);
      for (const ev of gh.sim.events) if (ev.type === 'stroke') gh.pad = { side: gh.pad && gh.pad.side ? -gh.pad.side : 1, t: VT };
      gh.sim.events.length = 0;
    }
    sim.step(tap);
    for (const ev of sim.events) handleEvent(ev, sim, false);
    sim.events.length = 0;
  }
  // ghost wakes (from the stern)
  if (S.ghosts) for (const gh of G.ghosts) {
    if (!gh.sim.alive) continue;
    let tr = ghostTrails.get(gh); if (!tr) { tr = []; ghostTrails.set(gh, tr); }
    tr.push(Object.assign(sternPoint(gh.sim.x, gh.sim.y, gh.sim.vx, gh.sim.vy), { t: VT }));
    while (tr.length && VT - tr[0].t > TRAIL_LIFE) tr.shift();
  }
  // biome banner & flip warning
  const b = G.course.biomeAt(sim.x);
  if (b !== G.curBiome) { G.curBiome = b; A.setScene({ biome: b }); if (sim.x > 200) showBanner(BIOMES[b].name, BIOMES[b].sub, 1800); }
  const nextFlip = G.course.flips.find(fx => fx > sim.x);
  if (nextFlip !== undefined && nextFlip - sim.x < 520 && G.flipWarned !== nextFlip) {
    G.flipWarned = nextFlip;
    const willBe = G.course.currentAt(nextFlip + 1);
    showBanner('⚠ Klidná voda, pak protiproud', willBe < 0 ? 'Za klidnou vodou tě proud potáhne nahoru' : 'Za klidnou vodou se proud vrací dolů', 1600, 2);
  }
  updateRaceHud();
}

function updateRaceHud() {
  const el = $('hudRace');
  if (!G.sim || !G.ghosts.length || !S.ghosts) { if (el.innerHTML) el.innerHTML = ''; return; }
  let html = '';
  for (const gh of G.ghosts) {
    const target = gh.finalScore;
    const mine = G.sim.score;
    const cls = mine > target ? 'ahead' : mine === target ? 'even' : 'behind';
    html += `<div class="race ${gh.style} ${cls}"><span class="dot"></span><b>${escapeHtml(gh.name)}</b><span>${mine > target ? '✓ překonáno' : 'cíl ' + target}</span></div>`;
  }
  if (el.innerHTML !== html) el.innerHTML = html;
}

function onPlayerCrash(sim, ev) {
  G.state = 'dead';
  G.deadAt = performance.now();
  const ang = boatAngle(sim.vx, sim.vy);
  G.death = { x: sim.x, y: sim.y, ang, spin: Math.random() < 0.5 ? -1 : 1, t: VT, camX: sim.x };
  trauma = Math.min(1, trauma + 0.9);
  flash = S.shake && !reducedMotion ? 0.55 : 0.18; flashColor = '255,255,255';
  A.crash();
  A.setMusicState('over');
  Native.haptic('crash');
  finishRun();
  setTimeout(() => { if (G.state === 'dead') showOver(); }, 1050);
}

function encodeRun(run) {
  try { return Replay.encode({ mode: typeof run.mode === 'string' ? (MODES[run.mode] || 0) : run.mode, level: run.level, seed: run.seed, score: run.score, endTick: run.endTick, name: run.name, label: run.label, taps: run.taps, pauses: run.pauses }); }
  catch (e) { console.warn(e); return ''; }
}

function finishRun() {
  const sim = G.sim;
  const run = { mode: G.mode, level: G.level, seed: G.seed, score: sim.score, endTick: sim.deathTick, name: playerName(), label: G.label, taps: G.taps.slice(), pauses: G.pauses | 0 };
  const code = encodeRun(run);
  run.code = code;
  G.lastRun = run;
  const hex = seedHex(G.seed), T = LR(G.level);
  const prev = T.seeds[hex];
  G.newBest = false;
  // random free rivers are only worth remembering when something was achieved on them
  if ((!prev || sim.score > prev.best) && (G.mode !== 'free' || sim.score > 0 || G.challenge)) T.seeds[hex] = { best: sim.score, code, label: G.label, at: Date.now(), rules: RULES };
  else if (prev) prev.at = Date.now();
  if (G.mode === 'free' && !G.challenge && sim.score > (T.free.best || 0)) { T.free = { best: sim.score, code, at: Date.now() }; G.newBest = sim.score > 0; }
  if ((G.mode !== 'free' || G.challenge) && sim.score > G.bestBefore && sim.score > 0) G.newBest = true;
  if (G.mode === 'daily' && G.dayKey && dailySeed(G.dayKey) === G.seed) T.daily[G.dayKey] = Math.max(T.daily[G.dayKey] || 0, sim.score);
  if (G.mode === 'river' && G.riverName && riverSeed(G.riverName) === G.seed) T.rivers[G.riverName] = Math.max(T.rivers[G.riverName] || 0, sim.score);
  const st = REC.stats;
  st.runs++; st.gates += sim.gatesPassed; st.stars += sim.starsGot; st.strokes += sim.strokes; st.dist += Math.round(sim.x / 10); st.time += sim.deathTick / TICK_RATE;
  if (G.challenge) {
    const ch = G.challenge;
    const key = ch.code;
    let h = REC.challenges.find(x => x.code === key);
    if (!h) { h = { from: ch.name, label: ch.label, level: G.level, their: ch.score, mine: 0, verified: ch.verified, code: key, seed: hex, at: Date.now(), tries: 0 }; REC.challenges.unshift(h); }
    h.tries++; h.mine = Math.max(h.mine, sim.score); h.at = Date.now();
  }
  saveRecords();
  if (G.newBest) { A.record(); setTimeout(() => Native.haptic('record'), 350); }
}

const OVER_LOCK = 650;   // ms the game-over card ignores input (players often keep tapping as they crash)
function showOver() {
  G.state = 'over';
  G.overAt = performance.now();
  setHud(false);
  const sim = G.sim;
  $('ovTitle').textContent = G.newBest ? 'Nový rekord!' : pickCrashTitle(sim.death && sim.death.cause);
  $('ovTitle').classList.toggle('gold', G.newBest);
  $('ovScore').textContent = sim.score;
  $('ovLabel').textContent = `${G.label} · ${levelName(G.level)}`;
  $('ovGates').textContent = sim.gatesPassed;
  $('ovStars').textContent = sim.starsGot;
  $('ovDist').textContent = Math.round(sim.x / 10) + ' m';
  $('ovTime').textContent = secs(sim.deathTick / TICK_RATE);
  const best = Math.max(bestFor(G.mode, G.seed), sim.score);
  const pz = G.pauses ? ` · pauzy: ${G.pauses}` : '';
  $('ovBest').textContent = (G.mode === 'free' && !G.challenge ? `Nejlepší volná plavba: ${best}` : `Tvůj rekord na této řece: ${best}`) + pz;
  const res = $('ovChallenge');
  if (G.challenge) {
    const ch = G.challenge, t = ch.score, m = sim.score, n = escapeHtml(ch.name || 'Soupeř');
    const note = ch.verified ? '' : '<span>Pozor: soupeřův záznam nešel ověřit — počítá se skóre, které jeho jízda opravdu dala.</span>';
    res.className = 'result ' + (m > t ? 'win' : m === t ? 'draw' : 'lose');
    res.innerHTML = (m > t ? `<b>Výhra ${m} : ${t}</b><span>Výzva splněna — ${n} má co dohánět. Pošli odvetu!</span>`
      : m === t ? `<b>Remíza ${m} : ${t}</b><span>Přesně stejně jako ${n}. Ještě jeden pokus?</span>`
      : `<b>Prohra ${m} : ${t}</b><span>${n} vede o ${bodu(t - m)}. Duch ukazuje cestu — zkus to znovu.</span>`) + note;
    res.hidden = false;
  } else { res.hidden = true; }
  const freshRiver = G.mode === 'free' && !G.challenge;
  $('btnSame').hidden = !freshRiver;
  $('btnRetry').style.gridColumn = freshRiver ? '' : '1 / -1';
  $('btnRetry').querySelector('span').textContent = freshRiver ? 'Nová řeka' : 'Znovu';
  $('ovHint').textContent = (freshRiver ? 'Mezerník = nová řeka' : 'Mezerník = znovu') + ' · Každá jízda je uložená jako ověřitelný záznam.';
  const scr = $('scrOver');
  scr.classList.add('locked');
  setTimeout(() => scr.classList.remove('locked'), OVER_LOCK);
  showScreen('scrOver');
}

function pickCrashTitle(cause) {
  const t = { rocks: ['Na skále!', 'Kámen nepovolil', 'Rozbitá špice'], logs: ['Uvíznutí v kládách', 'Dřevo vyhrálo'], boom: ['Plovoucí zátaras!', 'Srážka s bójí'], bridge: ['Pilíř mostu!', 'Most stojí, loďka ne'], bank: ['Na mělčině!', 'Břeh tě zastavil'] }[cause] || ['Ztroskotání!'];
  return t[Math.floor(Math.random() * t.length)];
}

function restart(sameSeed) {
  if (G.mode === 'free' && !sameSeed && !G.challenge) prepareRun({ mode: 'free', seed: newRandomSeed(), label: 'Volná plavba', level: G.level });
  else prepareRun({ mode: G.mode, seed: G.seed, label: G.label, challenge: G.challenge, level: G.level });
}

function pause() {
  if (G.state !== 'play' && G.state !== 'ready') return;
  G.pauseAlpha = renderAlpha(performance.now());
  G.prevState = G.state;
  if (G.state === 'play') G.pauses = (G.pauses | 0) + 1;
  G.state = 'paused';
  G.pauseAt = performance.now();
  G.resumeAt = 0;
  A.setPaused(true);
  showScreen('scrPause');
}
// Resuming a live run goes through a short 3-2-1 so the player can re-orient; the sim stays frozen meanwhile.
function resume() {
  if (G.state !== 'paused' || G.resumeAt) return;
  showScreen(null);
  blurActive();
  if (G.prevState !== 'play') { finishResume(); return; }
  G.resumeAt = performance.now() + 900;
  G.lastCount = 3;
  A.countdown(3);
  showBanner('3', 'připrav se', 320);
}
function tickResume(now) {
  if (G.state !== 'paused' || !G.resumeAt) return;
  const left = G.resumeAt - now;
  if (left <= 0) { finishResume(); return; }
  const n = left > 600 ? 3 : left > 300 ? 2 : 1;
  if (n !== G.lastCount) { G.lastCount = n; A.countdown(n); showBanner(String(n), 'připrav se', 320); }
}
function finishResume() {
  const wasCounting = !!G.resumeAt;
  G.resumeAt = 0; G.lastCount = 0;
  G.state = G.prevState;
  if (G.state === 'play') G.t0 += performance.now() - G.pauseAt;
  if (wasCounting) A.countdown(0);
  A.setPaused(false);
}
function cancelResume() {
  if (G.state === 'paused' && G.resumeAt) { G.resumeAt = 0; G.lastCount = 0; showScreen('scrPause'); }
}

function goMenu() {
  setHud(false);
  $('tapHint').classList.add('hidden');
  G.state = 'menu';
  G.challenge = null;
  G.resumeAt = 0;
  clearHash();
  fadeSwap(() => { if (G.state === 'menu') startAttract(); });
  A.setPaused(false);
  A.setMusicState('menu');
  refreshMenu();
  showScreen('scrMenu');
}
function clearHash() { if (location.hash) { try { history.replaceState(null, '', location.pathname + location.search); } catch { /* file:// in some browsers */ } } }

// ─── Input ─────────────────────────────────────────────────────────────────
function press(ts) {
  const now = performance.now();
  if (!(ts > 0) || Math.abs(ts - now) > 1000) ts = now;   // old WebViews report epoch timestamps
  unlockAudio();
  if (G.state === 'ready') { beginPlay(ts); return; }
  if (G.state === 'play') queueTap(ts);
}
cv.addEventListener('pointerdown', e => {
  if (e.button !== undefined && e.button > 0) return;
  e.preventDefault();
  press(e.timeStamp);
}, { passive: false });
$('tapLayer').addEventListener('pointerdown', e => { if (e.button > 0) return; e.preventDefault(); press(e.timeStamp); }, { passive: false });
document.addEventListener('contextmenu', e => { if (G.state === 'play' || G.state === 'ready') e.preventDefault(); });
const TAP_KEYS = new Set(['Space', 'ArrowUp', 'KeyW', 'KeyJ', 'KeyK']);
const overLocked = () => performance.now() - G.overAt < OVER_LOCK;
window.addEventListener('keydown', e => {
  const tag = (e.target && e.target.tagName) || '';
  const typing = tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT';
  if (typing) { if (e.code === 'Escape') e.target.blur(); return; }
  if (e.code === 'Escape' || e.code === 'KeyP') {
    e.preventDefault();
    if (e.repeat) return;
    if (G.state === 'play' || G.state === 'ready') pause();
    else if (G.state === 'paused' && G.resumeAt) cancelResume();
    else if (G.state === 'paused' && currentScreen && currentScreen !== 'scrPause') { if (e.code === 'Escape') backFrom(currentScreen); }
    else if (G.state === 'paused') resume();
    else if (e.code === 'Escape' && currentScreen && currentScreen !== 'scrMenu' && currentScreen !== 'scrOver') backFrom(currentScreen);
    return;
  }
  if (G.state === 'over' && currentScreen === 'scrOver' && (TAP_KEYS.has(e.code) || e.code === 'Enter' || e.code === 'KeyR')) {
    if (e.repeat || overLocked()) { e.preventDefault(); return; }
    if (e.code === 'Space' || e.code === 'KeyR' || (e.code === 'Enter' && document.activeElement === document.body)) { e.preventDefault(); unlockAudio(); restart(false); return; }
  }
  if (TAP_KEYS.has(e.code) && (G.state === 'play' || G.state === 'ready')) { e.preventDefault(); if (!e.repeat) press(e.timeStamp); return; }
  if (TAP_KEYS.has(e.code) && G.state === 'paused' && G.resumeAt) { e.preventDefault(); return; }  // countdown running
  if (e.code === 'KeyH' && e.shiftKey) { S.hitbox = !S.hitbox; saveSettings(); }
});
window.addEventListener('blur', () => { if (G.state === 'play') pause(); else cancelResume(); });
document.addEventListener('visibilitychange', () => {
  if (document.hidden && (G.state === 'play' || G.state === 'ready')) pause();
  else { if (document.hidden) cancelResume(); A.setPaused(document.hidden || G.state === 'paused'); }
});

const padPrev = new Map();
function pollGamepads() {
  if (!navigator.getGamepads) return;
  let pads;
  try { pads = navigator.getGamepads(); } catch { return; }
  for (const gp of pads) {
    if (!gp) continue;
    const prev = padPrev.get(gp.index) || [];
    const cur = gp.buttons.map(b => b.pressed);
    padPrev.set(gp.index, cur);
    const edge = i => cur[i] && !prev[i];
    const now = performance.now();
    const ts = gp.timestamp > 0 && gp.timestamp <= now && now - gp.timestamp < 50 ? gp.timestamp : now;
    if ([0, 2, 3, 5, 7].some(edge)) {
      if (G.state === 'play' || G.state === 'ready') press(ts);
      else if (G.state === 'over' && currentScreen === 'scrOver' && !overLocked()) restart(false);
      else if (G.state === 'paused' && currentScreen === 'scrPause') resume();
      else if (G.state === 'menu' && currentScreen === 'scrMenu' && edge(0)) prepareRun({ mode: 'free', seed: newRandomSeed(), label: 'Volná plavba' });
    }
    if (edge(1)) { // B = stroke while playing, otherwise back
      if (G.state === 'play' || G.state === 'ready') press(ts);
      else if (G.state === 'paused' && currentScreen === 'scrPause') resume();
      else if (currentScreen && !['scrMenu', 'scrOver', 'scrPause'].includes(currentScreen)) backFrom(currentScreen);
    }
    if (edge(9)) { if (G.state === 'paused' && currentScreen === 'scrPause') resume(); else if (G.state === 'play' || G.state === 'ready') pause(); }
    if (edge(8) && G.state === 'over' && currentScreen === 'scrOver' && !overLocked()) goMenu();
  }
}

// ─── UI ────────────────────────────────────────────────────────────────────
let currentScreen = 'scrMenu';
const coarse = (() => { try { return matchMedia('(pointer: coarse)').matches; } catch { return false; } })();
function showScreen(id) {
  document.querySelectorAll('.screen').forEach(s => { const on = s.id === id; s.classList.toggle('show', on); s.setAttribute('aria-hidden', on ? 'false' : 'true'); });
  currentScreen = id;
  $('hud').inert = !!id;
  if (id && !coarse) setTimeout(() => {
    if (currentScreen !== id) return;
    const f = document.querySelector(`#${id} [data-autofocus]`) || document.querySelector(`#${id} .titlebar .iconbtn`);
    if (f) f.focus({ preventScroll: true });
  }, id === 'scrOver' ? OVER_LOCK : 60);
}
function setHud(on) { $('hud').classList.toggle('hidden', !on); $('tapLayer').classList.toggle('hidden', !on); document.body.classList.toggle('playing', on); }
function blurActive() { if (document.activeElement && document.activeElement !== document.body) document.activeElement.blur(); }
let bannerTimer = 0, bannerPrioUntil = 0;
function showBanner(title, sub, ms, prio = 0) {
  const now = performance.now();
  if (prio < 2 && now < bannerPrioUntil) return;          // never cover a current-flip message
  if (prio >= 2) bannerPrioUntil = now + (ms || 1400);
  const b = $('banner');
  b.querySelector('b').textContent = title;
  b.querySelector('span').textContent = sub || '';
  b.classList.remove('show'); void b.offsetWidth; b.classList.add('show');
  clearTimeout(bannerTimer);
  bannerTimer = setTimeout(() => b.classList.remove('show'), ms || 1400);
}
let toastTimer = 0;
function toast(msg) {
  const t = $('toast'); t.textContent = msg; t.classList.add('show');
  clearTimeout(toastTimer); toastTimer = setTimeout(() => t.classList.remove('show'), 2400);
}
function escapeHtml(s) { return String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c])); }

const LEVEL_INFO = ['Klidnější voda, bez protiproudu, větší mezery', 'Peřeje s protiproudem a pohyblivými zátarasy', 'Rychlá a těsná divoká voda, protiproud brzy'];
function syncLevelButtons() {
  document.querySelectorAll('[data-action="set-level"]').forEach(b => {
    const on = +b.dataset.level === S.level;
    b.classList.toggle('on', on); b.setAttribute('aria-checked', on ? 'true' : 'false');
  });
  document.querySelectorAll('.level-info').forEach(el => { el.textContent = LEVEL_INFO[S.level]; });
}
function refreshMenu() {
  const T = LR(S.level);
  $('menuBestFree').textContent = T.free.best ? 'rekord ' + T.free.best : 'nová řeka pokaždé';
  const dk = utcDayKey();
  $('menuBestDaily').textContent = T.daily[dk] ? 'dnes ' + T.daily[dk] : 'stejná řeka pro všechny';
  $('nameInput').value = S.name;
  syncLevelButtons();
}

function startDaily() {
  const dk = utcDayKey();
  G.dayKey = dk;
  prepareRun({ mode: 'daily', seed: dailySeed(dk), label: modeLabel('daily', dk) });
}
function startRiver(name) {
  name = riverName(name);
  if (!name) { toast('Zadej název řeky'); return; }
  G.riverName = name;
  prepareRun({ mode: 'river', seed: riverSeed(name), label: modeLabel('river', name) });
}

// What a code claims about its river is only shown when the seed proves it.
function describeSeed(r) {
  if (r.mode === 1) {
    const m = (r.label || '').match(/(\d{1,2})\. (\d{1,2})\. (\d{4})/);
    const dk = m && `${m[3]}-${m[2].padStart(2, '0')}-${m[1].padStart(2, '0')}`;
    if (dk && dailySeed(dk) === r.seed) return { mode: 'daily', label: modeLabel('daily', dk), dayKey: dk, tag: dk === utcDayKey() ? '✓ dnešní denní výzva' : '✓ denní výzva ' + m[0] + ' (starší)' };
    return { mode: 'free', label: 'Výzva', tag: '⚠ tvrdí, že je to denní výzva, ale řeka nesedí' };
  }
  if (r.mode === 2) {
    const nm = riverName((r.label || '').replace(/^Řeka\s+/, ''));
    if (nm && riverSeed(nm) === r.seed) return { mode: 'river', label: modeLabel('river', nm), riverName: nm, tag: '✓ ' + modeLabel('river', nm) };
    return { mode: 'free', label: 'Výzva', tag: '⚠ název řeky neodpovídá trati' };
  }
  return { mode: 'free', label: 'Volná plavba', tag: '' };
}

let pendingChallenge = null, challengeReturn = null, loadTimer = 0;
function clearChallengePreview() { pendingChallenge = null; $('btnAccept').disabled = true; $('chPreview').hidden = true; }
function loadChallenge(text) {
  const box = $('chPreview');
  try {
    const r = Replay.decode(text);
    const v = Replay.verify(r);
    r.verified = v.ok;
    if (!v.ok) { r.claimed = r.score; r.score = v.score; }   // compete against what the run really scored
    r.code = Replay.encode(Object.assign({}, r, { score: r.claimed !== undefined ? r.claimed : r.score }));
    const info = describeSeed(r);
    r.info = info;
    pendingChallenge = r;
    const mine = LR(r.level).seeds[seedHex(r.seed)];
    const pz = r.pauses > 0 ? ` · pauzy: ${r.pauses}` : r.pauses === 0 ? ' · bez pauzy' : '';
    box.innerHTML = `
      <div class="ch-head"><span class="avatar">${escapeHtml((r.name || '?').slice(0, 1).toUpperCase())}</span>
      <div><b>${escapeHtml(r.name || 'Anonym')}</b><small>${escapeHtml(info.label)} · ${levelName(r.level)}</small></div>
      <div class="ch-score">${r.score}<small>${pl(r.score, 'bod', 'body', 'bodů')}</small></div></div>
      <div class="ch-meta">${v.ok ? '<span class="ok">✓ Skóre ověřeno přehráním záznamu</span>' : `<span class="bad">⚠ Záznam dává ${bodu(v.score)}, ne ${r.claimed}. Hraje se proti skutečnému výsledku.</span>`}
      ${info.tag ? `<span class="${info.tag[0] === '✓' ? 'ok' : 'bad'}">${escapeHtml(info.tag)}</span>` : ''}
      <span>Délka jízdy ${secs(r.endTick / TICK_RATE)} · ${r.taps.length} ${pl(r.taps.length, 'záběr', 'záběry', 'záběrů')}${pz}${mine ? ' · tvůj rekord zde: ' + mine.best : ''}</span></div>`;
    box.hidden = false;
    $('btnAccept').disabled = false;
    return true;
  } catch (e) {
    pendingChallenge = null;
    box.innerHTML = `<div class="ch-meta"><span class="bad">${escapeHtml(e.message || 'Neplatný kód')}</span></div>`;
    box.hidden = false;
    $('btnAccept').disabled = true;
    A.ui('error');
    return false;
  }
}
function acceptChallenge() {
  const r = pendingChallenge;
  if (!r) return;
  const info = r.info || describeSeed(r);
  G.dayKey = info.dayKey || utcDayKey();
  G.riverName = info.riverName || '';
  challengeReturn = null;
  clearHash();
  prepareRun({ mode: info.mode, seed: r.seed, label: info.label, challenge: r, level: r.level });
}
function openChallengeScreen(code, from) {
  challengeReturn = from || null;
  $('chInput').value = code || '';
  if (code) loadChallenge(code); else clearChallengePreview();
  showScreen('scrChallenge');
}

function openShare(run) {
  run = run || G.lastRun;
  if (!run || !run.code) { toast('Žádná jízda ke sdílení'); return; }
  // a run made before the player entered a name can be re-signed (the name is not part of verification)
  if ((!run.name || run.name === 'Anonym') && (S.name || '').trim()) {
    run = Object.assign({}, run, { name: playerName() });
    run.code = encodeRun(run) || run.code;
  }
  shareRun = run;
  // The link opens the challenge right in the browser; the app reads the code out of the pasted message.
  const hosted = !isNative && /^https?:/.test(location.protocol) && !/^(localhost|127\.0\.0\.1)$/.test(location.hostname);
  const link = `${hosted ? location.origin + location.pathname : WEB_URL}#${run.code}`;
  const msg = `🛶 PEŘEJE — ${run.label} (${levelName(run.level)}): ${bodu(run.score)}. Překonáš mě?\nHraj tady: ${link}\n(V aplikaci PEŘEJE stačí celou zprávu vložit do Výzev.)`;
  $('shareText').value = msg;
  $('shareCode').textContent = run.code;
  $('shareSummary').textContent = `${run.name} · ${run.label} · ${levelName(run.level)} · ${bodu(run.score)}`;
  $('shareName').value = S.name;
  $('btnNativeShare').hidden = !Native.canShare();
  if (currentScreen !== 'scrShare') shareReturn = currentScreen;
  showScreen('scrShare');
}
let shareReturn = 'scrOver', shareRun = null;

async function copyText(text) {
  try { const n = Native.copy(text); if (n) { await n; toast('Zkopírováno do schránky'); return; } } catch { /* fall back */ }
  try { await navigator.clipboard.writeText(text); toast('Zkopírováno do schránky'); return; } catch { /* fall back */ }
  const ta = document.createElement('textarea');
  ta.value = text; ta.readOnly = true; ta.style.position = 'fixed'; ta.style.opacity = '0'; ta.style.top = '0';
  document.body.appendChild(ta);
  ta.focus(); ta.select(); ta.setSelectionRange(0, text.length);
  let ok = false; try { ok = document.execCommand('copy'); } catch { /* ignore */ }
  ta.remove();
  if (ok) { toast('Zkopírováno do schránky'); return; }
  const st = $('shareText'); st.focus(); st.select();
  toast('Schránka není dostupná — text je označený, zkopíruj ho ručně');
}

function renderRecords() {
  const dk = utcDayKey();
  const st = REC.stats, T = LR(S.level);
  const rows = [];
  const dailyHex = seedHex(dailySeed(dk));
  rows.push(`<div class="levels" role="radiogroup" aria-label="Obtížnost">${[0, 1, 2].map(i => `<button class="lvl${i === S.level ? ' on' : ''}" role="radio" aria-checked="${i === S.level}" data-action="set-level" data-level="${i}">${levelName(i)}</button>`).join('')}</div>`);
  rows.push(`<div class="rec-grid">
    <div><small>Volná plavba</small><b>${T.free.best || 0}</b>${T.free.code ? `<button class="mini" data-action="share-code" data-code="${T.free.code}">Vyzvat</button>` : ''}</div>
    <div><small>Dnešní denní výzva</small><b>${T.daily[dk] || 0}</b>${T.seeds[dailyHex] && T.seeds[dailyHex].code ? `<button class="mini" data-action="share-seed" data-seed="${dailyHex}">Vyzvat</button>` : ''}</div>
    <div><small>Jízd celkem</small><b>${st.runs}</b></div>
    <div><small>Branek / hvězd</small><b>${st.gates} / ${st.stars}</b></div>
  </div>`);
  const days = Object.keys(T.daily).sort().reverse().slice(0, 7);
  if (days.length) rows.push(`<h3>Denní výzvy</h3><ul class="rec-list">${days.map(d => `<li><span>${d.split('-').reverse().map(Number).join('. ')}</span><b>${T.daily[d]}</b></li>`).join('')}</ul>`);
  const rivers = Object.keys(T.rivers).slice(0, 12);
  if (rivers.length) rows.push(`<h3>Vlastní řeky</h3><ul class="rec-list">${rivers.map(n => `<li><span>${escapeHtml(n)}</span><b>${T.rivers[n]}</b>${T.seeds[seedHex(riverSeed(n))] ? `<button class="mini" data-action="share-seed" data-seed="${seedHex(riverSeed(n))}">Vyzvat</button>` : ''}</li>`).join('')}</ul>`);
  if (REC.challenges.length) rows.push(`<h3>Výzvy od kamarádů</h3><ul class="rec-list">${REC.challenges.slice(0, 15).map(h => `<li class="${h.mine > h.their ? 'win' : h.mine === h.their ? 'draw' : 'lose'}"><span>${escapeHtml(h.from)} <small>${escapeHtml(h.label || '')} · ${levelName(h.level ?? 1)}${h.verified ? '' : ' · neověřeno'}</small></span><b>${h.mine} : ${h.their}</b><button class="mini" data-action="replay-challenge" data-code="${h.code}">Hrát</button></li>`).join('')}</ul>`);
  if (!days.length && !rivers.length && !REC.challenges.length && !st.runs) rows.push('<p class="muted">Zatím žádné jízdy. Hurá na vodu!</p>');
  $('recBody').innerHTML = rows.join('');
}

function backFrom(id) {
  A.ui('back');
  if (id === 'scrShare') { showScreen(shareReturn || 'scrOver'); return; }
  if (id === 'scrChallenge') {
    clearHash();
    if (challengeReturn) { const r = challengeReturn; challengeReturn = null; if (r === 'scrRecords') renderRecords(); showScreen(r); return; }
  }
  if (G.state === 'paused') { showScreen('scrPause'); return; }
  if (G.state === 'over') { showScreen('scrOver'); return; }
  showScreen('scrMenu');
}

document.addEventListener('click', e => {
  const btn = e.target.closest('[data-action]');
  if (!btn || btn.disabled) return;
  if (currentScreen === 'scrOver' && G.state === 'over' && overLocked() && btn.closest('#scrOver')) return;
  unlockAudio();
  const act = btn.dataset.action;
  if (act !== 'back') A.ui('click');
  switch (act) {
    case 'play-free': prepareRun({ mode: 'free', seed: newRandomSeed(), label: 'Volná plavba' }); break;
    case 'set-level': S.level = levelOf(+btn.dataset.level).id; saveSettings(); refreshMenu(); if (currentScreen === 'scrRecords') renderRecords(); break;
    case 'play-daily': startDaily(); break;
    case 'open-challenge': openChallengeScreen('', currentScreen === 'scrMenu' ? null : currentScreen); break;
    case 'open-records': renderRecords(); showScreen('scrRecords'); break;
    case 'open-settings': syncSettingsUI(); showScreen('scrSettings'); break;
    case 'open-help': showScreen('scrHelp'); break;
    case 'back': backFrom(currentScreen); break;
    case 'retry': restart(false); break;
    case 'retry-same': restart(true); break;
    case 'retry-pause': restart(true); break;
    case 'share': openShare(); break;
    case 'menu': goMenu(); break;
    case 'resume': resume(); break;
    case 'pause': pause(); break;
    case 'load-code': loadChallenge($('chInput').value); break;
    case 'paste-code':
      if (isNative && NP.Clipboard) { Native.paste().then(t => { $('chInput').value = t; loadChallenge(t); }).catch(() => toast('Schránka není dostupná')); break; }
      if (navigator.clipboard && navigator.clipboard.readText) navigator.clipboard.readText().then(t => { $('chInput').value = t; loadChallenge(t); }).catch(() => { toast('Schránka není dostupná — vlož kód do pole ručně'); $('chInput').focus(); });
      else { toast('Schránka není dostupná — vlož kód do pole ručně'); $('chInput').focus(); }
      break;
    case 'accept-challenge': acceptChallenge(); break;
    case 'play-river': startRiver($('riverInput').value); break;
    case 'copy-msg': copyText($('shareText').value); break;
    case 'copy-code': copyText($('shareCode').textContent); break;
    case 'native-share': Native.share($('shareText').value); break;
    case 'share-code': { try { const r = Replay.decode(btn.dataset.code); openShare(Object.assign(r, { code: btn.dataset.code })); } catch (err) { toast(err.message || 'Záznam je poškozený'); } break; }
    case 'share-seed': { const rec = LR(S.level).seeds[btn.dataset.seed]; if (rec && rec.code) { try { const r = Replay.decode(rec.code); openShare(Object.assign(r, { code: rec.code })); } catch (err) { toast(err.message || 'Záznam je poškozený'); } } else toast('Na této řece zatím nemáš jízdu'); break; }
    case 'replay-challenge': openChallengeScreen(btn.dataset.code, 'scrRecords'); break;
    case 'reset-records':
      if (confirm('Opravdu smazat všechny rekordy a historii výzev?')) { for (const k of Object.keys(REC)) delete REC[k]; Object.assign(REC, { L: [blankLevelRec(), blankLevelRec(), blankLevelRec()], challenges: [], stats: { runs: 0, gates: 0, stars: 0, strokes: 0, dist: 0, time: 0 } }); saveRecords(); renderRecords(); toast('Rekordy smazány'); }
      break;
  }
});
$('nameInput').addEventListener('input', e => { S.name = e.target.value.slice(0, 16); saveSettings(); });
$('shareName').addEventListener('change', e => {
  S.name = e.target.value.slice(0, 16); saveSettings(); $('nameInput').value = S.name;
  if (shareRun) { const r = Object.assign({}, shareRun, { name: playerName() }); r.code = encodeRun(r) || r.code; openShare(r); }
});
$('chInput').addEventListener('input', e => {
  clearTimeout(loadTimer);
  const v = e.target.value;
  if (/PRJ1-[A-Za-z0-9_-]{8,}/.test(v)) loadTimer = setTimeout(() => loadChallenge(v), 250);
  else clearChallengePreview();
});
$('riverInput').addEventListener('keydown', e => { if (e.key === 'Enter') { e.preventDefault(); unlockAudio(); startRiver(e.target.value); } });
// a challenge link opened into an already-open game tab only changes the hash
window.addEventListener('hashchange', () => {
  const m = (location.hash || '').match(/PRJ1-[A-Za-z0-9_-]+/);
  if (!m || G.state === 'dead') return;
  if (G.state === 'play' || G.state === 'ready') pause();
  openChallengeScreen(m[0], currentScreen);
});

function syncSettingsUI() {
  $('setSfx').value = S.sfx; $('setMusic').value = S.music; $('setAmb').value = S.amb;
  $('setGhosts').checked = S.ghosts; $('setShake').checked = S.shake; $('setHaptics').checked = S.haptics; $('setHitbox').checked = S.hitbox;
  $('setQuality').value = S.quality; $('setName').value = S.name;
}
['setSfx', 'setMusic', 'setAmb'].forEach(id => $(id).addEventListener('input', e => {
  const k = { setSfx: 'sfx', setMusic: 'music', setAmb: 'amb' }[id];
  S[k] = +e.target.value; saveSettings(); applyVolumes();
}));
$('setGhosts').addEventListener('change', e => { S.ghosts = e.target.checked; saveSettings(); A.ui('toggle'); });
$('setShake').addEventListener('change', e => { S.shake = e.target.checked; saveSettings(); A.ui('toggle'); });
$('setHaptics').addEventListener('change', e => { S.haptics = e.target.checked; saveSettings(); A.ui('toggle'); Native.haptic('stroke'); });
$('setHitbox').addEventListener('change', e => { S.hitbox = e.target.checked; saveSettings(); A.ui('toggle'); });
$('setQuality').addEventListener('change', e => {
  S.quality = e.target.value; saveSettings();
  qualityLevel = S.quality === 'low' ? 0 : S.quality === 'medium' ? 1 : 2; perf.locked = S.quality !== 'auto';
  layout();
});
$('setName').addEventListener('input', e => { S.name = e.target.value.slice(0, 16); saveSettings(); $('nameInput').value = S.name; });

// ─── Performance governor ─────────────────────────────────────────────────
// Judges frame time against the display's own refresh interval (a 30 Hz-capped phone is not "slow"),
// steps quality down after sustained trouble and tries one step back up after a long calm period.
const perf = { ema: 16, base: 0, slowFor: 0, calmFor: 0, locked: S.quality !== 'auto' };
function perfMonitor(dtMs) {
  perf.base = perf.base ? Math.min(dtMs, perf.base * 1.0015 + 0.0005) : dtMs;
  perf.ema = perf.ema * 0.95 + dtMs * 0.05;
  if (perf.locked || document.hidden || G.state === 'paused') return;
  const slow = perf.ema > Math.max(19, perf.base * 1.5);
  if (slow && qualityLevel > 0) {
    perf.slowFor += dtMs; perf.calmFor = 0;
    if (perf.slowFor > 3000) { qualityLevel--; perf.slowFor = 0; perf.ema = perf.base; layout(); }
  } else {
    perf.slowFor = Math.max(0, perf.slowFor - dtMs * 0.5);
    if (qualityLevel < 2 && perf.ema < perf.base * 1.12) { perf.calmFor += dtMs; if (perf.calmFor > 25000) { qualityLevel++; perf.calmFor = -60000; layout(); } }
  }
}

// ─── Main loop ─────────────────────────────────────────────────────────────
function frame(now) {
  requestAnimationFrame(frame);
  tickFrame(now);
}
function tickFrame(now) {
  const rawMs = now - lastNow;
  lastNow = now;
  const dt = clamp(rawMs, 0, 100) / 1000;
  const t0 = performance.now();
  pollGamepads();
  tickResume(now);
  const paused = G.state === 'paused';
  if (!paused) VT += dt;
  if (G.state === 'menu') updateAttract(dt);
  else if (G.state === 'play') updatePlay(now);
  const course = viewCourse();
  if (!paused) { updateParticles(dt, course); ambient(dt, course); }
  if (course) {
    const b = biomeMix(course, V.camX + V.visW / 2);
    const night = BIOMES[b.a].night + (BIOMES[b.b].night - BIOMES[b.a].night) * b.t;
    const sim = G.state === 'menu' ? G.attract.sim : G.sim;
    A.setScene({ biome: b.t > 0.5 ? b.b : b.a, night, intensity: sim ? course.difficultyAt(sim.x) : 0, speed: sim ? clamp((sim.vx - 232) / 110, 0, 1) : 0 });
  }
  render(now, paused ? 0 : dt);
  lastFrameMs = performance.now() - t0;
  if (rawMs < 250) perfMonitor(rawMs);
}

// ─── Boot ──────────────────────────────────────────────────────────────────
window.addEventListener('resize', () => layout());
if (window.visualViewport) window.visualViewport.addEventListener('resize', () => layout());
startAttract();
layout();
refreshMenu();
showScreen('scrMenu');
if (!water) document.body.classList.add('no-webgl');
// challenge link?
const hashCode = (location.hash || '').match(/PRJ1-[A-Za-z0-9_-]+/);
if (hashCode) openChallengeScreen(hashCode[0], null);
requestAnimationFrame(t => { lastNow = t; frame(t); });
if (isNative) initNative();

function initNative() {
  document.body.classList.add('native');
  const App = NP.App;
  const openLink = url => {
    const m = String(url || '').match(/PRJ1-[A-Za-z0-9_-]+/);
    if (!m || G.state === 'dead') return;
    if (G.state === 'play' || G.state === 'ready') pause();
    openChallengeScreen(m[0], currentScreen);
  };
  if (App) {
    // pereje://vyzva/PRJ1-… opens a challenge directly (also on a cold start)
    try { App.addListener('appUrlOpen', e => openLink(e && e.url)); } catch { /* ignore */ }
    try { const r = App.getLaunchUrl(); if (r && r.then) r.then(v => v && v.url && openLink(v.url)).catch(() => {}); } catch { /* ignore */ }
    // Android back button: pause → back out of overlays → leave the app from the menu
    try {
      App.addListener('backButton', () => {
        if (G.state === 'play' || G.state === 'ready') { pause(); return; }
        if (G.state === 'paused') { if (G.resumeAt) cancelResume(); else if (currentScreen && currentScreen !== 'scrPause') backFrom(currentScreen); else resume(); return; }
        if (G.state === 'dead') return;
        if (currentScreen && currentScreen !== 'scrMenu' && currentScreen !== 'scrOver') { backFrom(currentScreen); return; }
        if (G.state === 'over') { goMenu(); return; }
        nativeCall('App', 'exitApp');
      });
    } catch { /* ignore */ }
    try { App.addListener('appStateChange', st => { if (st && !st.isActive) { if (G.state === 'play' || G.state === 'ready') pause(); else cancelResume(); } }); } catch { /* ignore */ }
  }
  // If the OS purged WebView storage, bring records & settings back from the native copy (once).
  if (NP.Preferences) {
    const keys = ['settings', 'records2'];
    Promise.all(keys.map(k => NP.Preferences.get({ key: 'pereje.v1.' + k }).catch(() => null))).then(vals => {
      let restored = false;
      keys.forEach((k, i) => {
        const v = vals[i] && vals[i].value;
        let has = true; try { has = !!localStorage.getItem('pereje.v1.' + k); } catch { /* ignore */ }
        if (v && !has) { try { localStorage.setItem('pereje.v1.' + k, v); restored = true; } catch { /* ignore */ } }
        if (!v && has) { try { Native.persist(k, localStorage.getItem('pereje.v1.' + k)); } catch { /* ignore */ } }
      });
      if (restored && G.state === 'menu') location.reload();
    }).catch(() => {});
  }
}

// test hooks (harmless)
window.__pereje = { G, V, S, REC, BIOMES, get water() { return water; }, layout, prepareRun, loadChallenge, showOver, Replay, tickFrame, perf };
})();

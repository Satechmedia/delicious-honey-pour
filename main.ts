// Honey pouring over a stack of pancakes: a deterministic SDF ray marcher
// with its own PNG encoder. Node standard library only.
import { mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { deflateSync } from "node:zlib";

const W = 1024;
const H = 1024;
const MAX_BYTES = 1_048_576;

// ---------------------------------------------------------------- helpers
const clamp = (x: number, a: number, b: number) => (x < a ? a : x > b ? b : x);
const mix = (a: number, b: number, t: number) => a + (b - a) * t;
function ss(a: number, b: number, x: number) {
  const t = clamp((x - a) / (b - a), 0, 1);
  return t * t * (3 - 2 * t);
}
function smin(a: number, b: number, k: number) {
  const h = Math.max(k - Math.abs(a - b), 0) / k;
  return Math.min(a, b) - h * h * k * 0.25;
}
function smax(a: number, b: number, k: number) {
  const h = Math.max(k - Math.abs(a - b), 0) / k;
  return Math.max(a, b) + h * h * k * 0.25;
}

// Seeded PRNG (mulberry32) and value noise.
let seed = 0x48f1a7c3;
function rnd() {
  seed = (seed + 0x6d2b79f5) | 0;
  let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
  return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
}
const PERM = new Uint8Array(512);
const VALS = new Float64Array(256);
{
  const p = new Uint8Array(256);
  for (let i = 0; i < 256; i++) {
    p[i] = i;
    VALS[i] = rnd();
  }
  for (let i = 255; i > 0; i--) {
    const j = Math.floor(rnd() * (i + 1));
    const t = p[i];
    p[i] = p[j];
    p[j] = t;
  }
  for (let i = 0; i < 512; i++) PERM[i] = p[i & 255];
}
function noise(x: number, y: number, z: number) {
  const fx = Math.floor(x), fy = Math.floor(y), fz = Math.floor(z);
  const a = x - fx, b = y - fy, c = z - fz;
  const u = a * a * a * (a * (a * 6 - 15) + 10);
  const v = b * b * b * (b * (b * 6 - 15) + 10);
  const w = c * c * c * (c * (c * 6 - 15) + 10);
  const X = fx & 255, Y = fy & 255, Z = fz & 255;
  const A = PERM[X] + Y, B = PERM[X + 1] + Y;
  const AA = PERM[A & 511] + Z, AB = PERM[(A + 1) & 511] + Z;
  const BA = PERM[B & 511] + Z, BB = PERM[(B + 1) & 511] + Z;
  const l0 = mix(VALS[PERM[AA & 511]], VALS[PERM[BA & 511]], u);
  const l1 = mix(VALS[PERM[AB & 511]], VALS[PERM[BB & 511]], u);
  const l2 = mix(VALS[PERM[(AA + 1) & 511]], VALS[PERM[(BA + 1) & 511]], u);
  const l3 = mix(VALS[PERM[(AB + 1) & 511]], VALS[PERM[(BB + 1) & 511]], u);
  return mix(mix(l0, l1, v), mix(l2, l3, v), w);
}
function fbm(x: number, y: number, z: number, oct: number) {
  let s = 0, a = 0.5, n = 0;
  for (let i = 0; i < oct; i++) {
    s += a * noise(x, y, z);
    n += a;
    a *= 0.5;
    x = x * 2.03 + 11.1;
    y = y * 2.03 + 3.7;
    z = z * 2.03 + 7.3;
  }
  return s / n;
}

// ---------------------------------------------------------------- scene
const COUNT = 5;
const PH = 0.222;
const PLATE_Y = 0.05;
const CX = [0.03, -0.06, 0.07, -0.04, 0.02];
const CZ = [-0.02, 0.04, 0.0, -0.05, 0.02];
const PR = [1.68, 1.64, 1.6, 1.56, 1.5];
const CY = CX.map((_, i) => PLATE_Y + PH + i * PH * 1.84);
const TOP = CY[COUNT - 1] + PH - 0.012;
const WOB = CX.map((_, i) => {
  const a2 = 1.3 + i * 2.1, a3 = 0.4 + i * 1.7, a5 = 2.2 + i * 0.9;
  return [
    0.026 * Math.cos(a2), 0.026 * Math.sin(a2),
    0.018 * Math.cos(a3), 0.018 * Math.sin(a3),
    0.010 * Math.cos(a5), 0.010 * Math.sin(a5),
  ];
});

const DRIPS: number[][] = [
  // angle, tip (path length from the axis), half width
  [-1.26, 2.62, 0.1],
  [-0.9, 3.12, 0.125],
  [-0.56, 2.28, 0.088],
  [-0.2, 3.62, 0.15],
  [0.16, 2.5, 0.098],
  [0.5, 3.02, 0.13],
  [0.86, 2.2, 0.09],
  [1.22, 2.78, 0.112],
  [1.9, 2.4, 0.1],
  [2.6, 2.7, 0.11],
  [-2.1, 2.5, 0.1],
  [-2.8, 2.3, 0.09],
];

const STREAM_X = 0.5, STREAM_Z = -0.08;
const BUTTER_X = -0.34, BUTTER_Z = 0.34, BUTTER_Y = TOP + 0.13;
const BA = 0.52, BC = Math.cos(BA), BS = Math.sin(BA);
const POOL_X = -0.4, POOL_Z = 1.9;

let gI = 0, gHard = 0, gSoft = 0, gM = 0;
function stack(x: number, y: number, z: number, all = false) {
  let hard = 1e9, soft = 1e9, idx = 0;
  for (let i = 0; i < COUNT; i++) {
    const dy = y - CY[i];
    if (!all && Math.abs(dy) > PH + 0.3 + Math.min(hard, 0.6)) continue;
    const dx = x - CX[i], dz = z - CZ[i];
    const r = Math.sqrt(dx * dx + dz * dz) + 1e-9;
    const c = dz / r, s = dx / r;
    const c2 = c * c - s * s, s2 = 2 * s * c;
    const c3 = c * c2 - s * s2, s3 = s * c2 + c * s2;
    const c5 = c2 * c3 - s2 * s3, s5 = s2 * c3 + c2 * s3;
    const w = WOB[i];
    const R = PR[i] * (1 + w[0] * c2 + w[1] * s2 + w[2] * c3 + w[3] * s3 + w[4] * c5 + w[5] * s5);
    const rr = PH * 0.8;
    const e = r / R;
    const qx = r - (R - rr), qy = Math.abs(dy + 0.055 * e * e) - (PH - rr);
    const mx = qx > 0 ? qx : 0, my = qy > 0 ? qy : 0;
    const d = Math.min(Math.max(qx, qy), 0) + Math.sqrt(mx * mx + my * my) - rr;
    if (d < hard) {
      hard = d;
      idx = i;
    }
    soft = soft > 1e8 ? d : smin(soft, d, 0.11);
  }
  gI = idx;
  gHard = hard;
  gSoft = soft;
}

function honeyShell(x: number, y: number, z: number, soft: number) {
  if (soft > 0.34) return soft - 0.14;
  const r = Math.sqrt(x * x + z * z);
  const th = Math.atan2(x, z);
  const s = r + Math.max(0, TOP - y);
  const edge = 1.3 + 0.08 * Math.cos(2 * th + 0.7) + 0.06 * Math.cos(3 * th + 2.1) + 0.035 * Math.cos(7 * th + 0.3) +
    0.045 * Math.cos(11 * th + 1.7);
  let mask = s - edge, bulb = 0;
  if (s > 0.85) {
    for (let k = 0; k < DRIPS.length; k++) {
      const dr = DRIPS[k];
      let da = th - dr[0];
      if (da > Math.PI) da -= 2 * Math.PI;
      else if (da < -Math.PI) da += 2 * Math.PI;
      const du = da * 1.6;
      if (Math.abs(du) > 0.5) continue;
      const tip = dr[1];
      const ds = s - clamp(s, 1.0, tip - dr[2]);
      const near = ss(tip - 0.42, tip - 0.06, s);
      const hw = dr[2] * (0.66 + 0.42 * near);
      const d = Math.sqrt(du * du + ds * ds) - hw;
      mask = smin(mask, d, 0.13);
      if (d < 0.05) bulb = Math.max(bulb, near);
    }
  }
  return smax(soft - (0.05 + 0.05 * bulb), mask, 0.05);
}

function plateD(x: number, y: number, z: number) {
  const r = Math.sqrt(x * x + z * z);
  // Plate cross-section: flat well, then a raised rim.
  const px = r, py = y;
  const ax = 2.25, ay = 0.0, bx = 2.92, by = 0.19;
  const d1 = Math.sqrt(Math.max(px - ax, 0) ** 2 + (py - ay) ** 2);
  const ex = bx - ax, ey = by - ay;
  const h = clamp(((px - ax) * ex + (py - ay) * ey) / (ex * ex + ey * ey), 0, 1);
  const d2 = Math.hypot(px - ax - ex * h, py - ay - ey * h);
  return smin(d1, d2, 0.1) - 0.05;
}

// The falling ribbon of honey and the soft mound where it lands.
function streamD(x: number, y: number, z: number) {
  const f = y - TOP;
  const sx = STREAM_X + 0.03 * Math.sin(f * 1.3) * f * 0.28;
  const sz = STREAM_Z + 0.022 * Math.sin(f * 0.9 + 1.1) * f * 0.24;
  const rad = 0.036 + 0.016 * Math.min(1, f / 3.4) + 0.05 * Math.exp(-Math.max(f, 0) * 7);
  const ddx = x - sx, ddz = z - sz;
  const ds = Math.sqrt(ddx * ddx + ddz * ddz) - rad;
  const mx = x - STREAM_X, mz = z - STREAM_Z, my = (y - TOP - 0.03) * 2.1;
  const mound = (Math.sqrt(mx * mx + my * my + mz * mz) - 0.24) / 2.1;
  return smin(ds * 0.92, mound, 0.08);
}

// A butter pat softening at the corners, on a thin skirt of its own melt.
function butterD(x: number, y: number, z: number) {
  const bx = x - BUTTER_X, bz = z - BUTTER_Z;
  const lx = BC * bx - BS * bz, lz = BS * bx + BC * bz;
  const ly = y - BUTTER_Y + 0.035 * lx + 0.02 * lz;
  const taper = 0.08 * clamp((ly + 0.075) / 0.15, 0, 1);
  const wob = 0.016 * Math.sin(lx * 7 + 1) + 0.013 * Math.sin(lz * 9 + 2);
  const qbx = Math.abs(lx) - (0.37 - taper + wob), qby = Math.abs(ly) - 0.055, qbz = Math.abs(lz) - (0.33 - taper - wob);
  const mbx = qbx > 0 ? qbx : 0, mby = qby > 0 ? qby : 0, mbz = qbz > 0 ? qbz : 0;
  const box = Math.sqrt(mbx * mbx + mby * mby + mbz * mbz) + Math.min(Math.max(qbx, qby, qbz), 0) - 0.095;
  const edge = 0.03 * Math.sin(lx * 5.3 + 0.6) + 0.026 * Math.sin(lz * 6.1 + 2.2);
  const qsx = Math.abs(lx) - (0.43 + edge), qsy = Math.abs(y - TOP - 0.055) - 0.004, qsz = Math.abs(lz) - (0.39 - edge);
  const msx = qsx > 0 ? qsx : 0, msy = qsy > 0 ? qsy : 0, msz = qsz > 0 ? qsz : 0;
  const skirt = Math.sqrt(msx * msx + msy * msy + msz * msz) + Math.min(Math.max(qsx, qsy, qsz), 0) - 0.06;
  return smin(box, skirt, 0.07);
}

// Round crumb bubbles: cellular noise, below 1 inside a bubble.
function pores(x: number, y: number, z: number) {
  const fx = Math.floor(x), fy = Math.floor(y), fz = Math.floor(z);
  const ax = x - fx, ay = y - fy, az = z - fz;
  let best = 9;
  for (let k = -1; k <= 1; k++) {
    for (let j = -1; j <= 1; j++) {
      for (let i = -1; i <= 1; i++) {
        const h = PERM[(PERM[(PERM[(fx + i) & 255] + ((fy + j) & 255)) & 511] + ((fz + k) & 255)) & 511];
        if (h % 3 === 0) continue;
        const qx = i + VALS[h] - ax;
        const qy = j + VALS[PERM[(h + 37) & 511]] - ay;
        const qz = k + VALS[PERM[(h + 101) & 511]] - az;
        const d = Math.sqrt(qx * qx + qy * qy + qz * qz) / (0.2 + 0.3 * VALS[(h + 59) & 255]);
        if (d < best) best = d;
      }
    }
  }
  return best;
}

function map(x: number, y: number, z: number) {
  let best = 1e9, mat = 0;

  const pd = plateD(x, y, z);
  best = pd;
  mat = 4;

  // Honey stream falling from above onto the top pancake.
  if (y > TOP - 0.1) {
    const st = streamD(x, y, z);
    if (st < best) {
      best = st;
      mat = 2;
    }
  }

  const rad2 = x * x + z * z;
  if (rad2 < 2.85 * 2.85 && y < TOP + 0.75) {
    stack(x, y, z);
    if (gHard < best) {
      best = gHard;
      mat = 1;
    }
    let hd = honeyShell(x, y, z, gSoft) * 0.82;
    // Honey collected on the plate in front of the stack.
    const qx = x - POOL_X, qz = z - POOL_Z;
    const pr = Math.sqrt(qx * qx + qz * qz) + 1e-9;
    if (pr < 1.2) {
      const co = qz / pr, si = qx / pr;
      const lobes = 0.45 + 0.07 * (co * co - si * si) + 0.06 * (2 * si * co) + 0.045 * (4 * co * co * co - 3 * co);
      const qr = clamp(pr / lobes, 0, 1);
      const fx = pr - lobes, fy = Math.abs(y - PLATE_Y - 0.012 - 0.034 * (1 - qr * qr)) - 0.018;
      const mxp = fx > 0 ? fx : 0, myp = fy > 0 ? fy : 0;
      const pool = Math.min(Math.max(fx, fy), 0) + Math.sqrt(mxp * mxp + myp * myp) - 0.026;
      hd = smin(hd, pool, 0.09);
    }
    if (hd < best) {
      best = hd;
      mat = 2;
    }
    const bd = butterD(x, y, z);
    if (bd < best) {
      best = bd;
      mat = 3;
    }
  } else {
    const bound = Math.max(Math.sqrt(rad2) - 2.78, y - TOP - 0.6);
    if (bound < best) {
      best = Math.max(bound, 0.02);
      mat = 0;
    }
  }
  gM = mat;
  return best;
}

// ---------------------------------------------------------------- lighting
const KEY = norm3(-0.56, 0.74, 0.5);
const RIM = norm3(0.78, 0.36, -0.62);
function norm3(x: number, y: number, z: number): [number, number, number] {
  const l = Math.hypot(x, y, z);
  return [x / l, y / l, z / l];
}

let eR = 0, eG = 0, eB = 0, paneGain = 1;
// A warm studio: gradient room, large softbox and a strip light.
function env(dx: number, dy: number, dz: number, px: number, py: number, pz: number) {
  const up = clamp(dy * 0.5 + 0.5, 0, 1);
  eR = mix(0.2, 0.92, up);
  eG = mix(0.095, 0.62, up);
  eB = mix(0.035, 0.34, up);
  if (dy > 0.04) {
    const t = (7 - py) / dy;
    const hx = px + dx * t, hz = pz + dz * t;
    const sb = ss(-7.6, -6.6, hx) * ss(0.3, -0.7, hx) * ss(-3.0, -2.0, hz) * ss(4.8, 3.8, hz);
    eR += sb * 30;
    eG += sb * 26.5;
    eB += sb * 21;
    const st = ss(3.2, 3.5, hx) * ss(4.4, 4.1, hx) * ss(-5.5, -4.5, hz) * ss(1.5, 0.5, hz);
    eR += st * 7;
    eG += st * 5.2;
    eB += st * 3.3;
  }
  // A tall window behind the dish gives flat honey its long wet sheen.
  if (dz < -0.1) {
    const t = (-9 - pz) / dz;
    const wx = px + dx * t, wy = py + dy * t;
    const win = ss(-4.6, -2.8, wx) * ss(3.8, 1.6, wx) * ss(1.0, 3.2, wy) * ss(6.8, 5.0, wy);
    eR += win * 1.05;
    eG += win * 0.74;
    eB += win * 0.3;
    // A narrow pane inside it: the bright streak that says "wet".
    const pane = ss(-2.5, -2.1, wx) * ss(-0.5, -0.9, wx) * ss(3.0, 3.5, wy) * ss(6.6, 6.1, wy);
    eR += pane * 5.2 * paneGain;
    eG += pane * 4.4 * paneGain;
    eB += pane * 3.1 * paneGain;
  }
}

// Continuous distance to every occluder. It has no early-outs, because a
// jump in the field would print contour lines into the soft shadows.
function occluder(x: number, y: number, z: number) {
  stack(x, y, z, true);
  let d = gSoft;
  const b = butterD(x, y, z);
  if (b < d) d = b;
  if (y > TOP - 0.1) {
    const st = streamD(x, y, z);
    if (st < d) d = st;
  }
  return d;
}

function shadow(x: number, y: number, z: number, lx: number, ly: number, lz: number, k: number) {
  let res = 1, t = 0.05, prev = 1e9;
  for (let i = 0; i < 26; i++) {
    const h = occluder(x + lx * t, y + ly * t, z + lz * t);
    if (h < 0.0005) return 0;
    // Improved penumbra estimate: uses the previous step to avoid banding.
    const q = (h * h) / (2 * prev);
    const dd = Math.sqrt(Math.max(h * h - q * q, 0));
    const v = (k * dd) / Math.max(t - q, 1e-4);
    if (v < res) res = v;
    if (res < 0.005) return 0;
    prev = h;
    t += clamp(h * 0.8, 0.025, 0.3);
    if (t > 5.5) break;
  }
  res = clamp(res, 0, 1);
  return res * res * (3 - 2 * res);
}

function ao(x: number, y: number, z: number, nx: number, ny: number, nz: number) {
  let occ = 0, w = 1;
  for (let i = 1; i <= 5; i++) {
    const h = 0.02 + 0.075 * i;
    const qx = x + nx * h, qy = y + ny * h, qz = z + nz * h;
    const d = Math.min(occluder(qx, qy, qz), plateD(qx, qy, qz));
    occ += (h - d) * w;
    w *= 0.62;
  }
  return clamp(1 - 2.1 * occ, 0, 1);
}

let nX = 0, nY = 0, nZ = 0;
function normal(x: number, y: number, z: number) {
  const e = 0.0016;
  const a = map(x + e, y - e, z - e);
  const b = map(x - e, y - e, z + e);
  const c = map(x - e, y + e, z - e);
  const d = map(x + e, y + e, z + e);
  const nx = a - b - c + d, ny = -a - b + c + d, nz = -a + b - c + d;
  const l = Math.sqrt(nx * nx + ny * ny + nz * nz) + 1e-12;
  nX = nx / l;
  nY = ny / l;
  nZ = nz / l;
}

// ---------------------------------------------------------------- camera
const TX = 0, TY = 0.98, TZ = 0.1;
const EL = 0.36, AZ = 0.08, DIST = 11.2;
const RO = [TX + DIST * Math.cos(EL) * Math.sin(AZ), TY + DIST * Math.sin(EL), TZ + DIST * Math.cos(EL) * Math.cos(AZ)];
const FW = norm3(TX - RO[0], TY - RO[1], TZ - RO[2]);
const RT = norm3(FW[2] * -1, 0, FW[0]);
const UP: [number, number, number] = [
  RT[1] * FW[2] - RT[2] * FW[1],
  RT[2] * FW[0] - RT[0] * FW[2],
  RT[0] * FW[1] - RT[1] * FW[0],
];
const FOCAL = 4.55;

let cR = 0, cG = 0, cB = 0, cId = 0, cDepth = 0;

function background(dx: number, dy: number, dz: number, sx: number, sy: number) {
  // Table plane; soft by construction so it reads as depth of field.
  let r = 0.05, g = 0.024, b = 0.012;
  if (dy < -0.001) {
    const t = (-0.05 - RO[1]) / dy;
    const px = RO[0] + dx * t, pz = RO[2] + dz * t;
    const grain = fbm(px * 0.42 + 3, 0.2, pz * 1.7, 3);
    const wood = 0.72 + 0.55 * grain;
    r = 0.082 * wood;
    g = 0.04 * wood;
    b = 0.02 * wood;
    const pr = Math.hypot(px + 0.42, pz + 0.3);
    const sh = 1 - 0.8 * Math.exp(-Math.max(pr - 2.75, 0) * 1.5);
    r *= sh;
    g *= sh;
    b *= sh;
    const glow = Math.exp(-Math.max(pr - 2.2, 0) * 0.8) * 0.035;
    r += glow * 0.6;
    g += glow * 0.3;
    b += glow * 0.1;
    const far = ss(-3.2, -8.5, pz);
    r = mix(r, 0.062, far);
    g = mix(g, 0.028, far);
    b = mix(b, 0.012, far);
  }
  // Warm bokeh lights behind the dish.
  const hor = ss(0.1, 0.62, sy);
  for (let i = 0; i < BOKEH.length; i++) {
    const k = BOKEH[i];
    const ddx = sx - k[0], ddy = sy - k[1];
    const d = Math.sqrt(ddx * ddx + ddy * ddy);
    if (d < k[2] + 0.01) {
      const a = ss(k[2] + 0.006, k[2] - 0.006, d) * (0.62 + 0.38 * ss(k[2] * 0.3, k[2], d));
      r += a * k[3] * 1.0 * hor;
      g += a * k[3] * 0.56 * hor;
      b += a * k[3] * 0.2 * hor;
    }
  }
  cR = r;
  cG = g;
  cB = b;
}

const BOKEH: number[][] = [];
for (let i = 0; i < 26; i++) {
  BOKEH.push([rnd() * 2.2 - 1.1, 0.25 + rnd() * 0.85, 0.05 + rnd() * 0.075, 0.006 + rnd() * 0.026]);
}

function shade(x: number, y: number, z: number, dx: number, dy: number, dz: number, mat: number) {
  normal(x, y, z);
  let nx = nX, ny = nY, nz = nZ;
  const vx = -dx, vy = -dy, vz = -dz;
  const nv0 = nx * vx + ny * vy + nz * vz;
  if (nv0 < 0) {
    nx = -nx;
    ny = -ny;
    nz = -nz;
  }
  const px = x + nx * 0.006, py = y + ny * 0.006, pz = z + nz * 0.006;
  const occ = ao(px, py, pz, nx, ny, nz);
  const sKey = shadow(px, py, pz, KEY[0], KEY[1], KEY[2], 8.5);
  const ndl = nx * KEY[0] + ny * KEY[1] + nz * KEY[2];
  const rimL = clamp(nx * RIM[0] + ny * RIM[1] + nz * RIM[2], 0, 1);
  const nv = clamp(nx * vx + ny * vy + nz * vz, 0, 1);
  const fres = Math.pow(1 - nv, 5);

  if (mat === 1) {
    stack(x, y, z);
    const i = gI;
    const ddx = x - CX[i], ddz = z - CZ[i];
    const r = Math.sqrt(ddx * ddx + ddz * ddz);
    const e = r / PR[i];
    const v = (y - CY[i] + 0.055 * e * e) / PH;
    // Griddled brown faces with the pale, fluffy crumb showing at the waist.
    const face = ss(0.05, 0.56, Math.abs(v) + 0.16 * (fbm(x * 3.1, y * 3.1 + i, z * 3.1, 2) - 0.5));
    const n1 = fbm(x * 2.7 + i * 3.17, y * 2.7 + i, z * 2.7, 4);
    const n2 = fbm(x * 9.5, y * 9.5 + i, z * 9.5, 3);
    const lace = ss(0.36, 0.66, n1 * 0.52 + n2 * 0.48);
    const cr = mix(0.27, 0.64, lace), cg = mix(0.082, 0.25, lace), cb = mix(0.012, 0.045, lace);
    // Rotated lookups hide the axis-aligned lattice of the value noise.
    const ux = 0.8 * x + 0.6 * z, uz = -0.6 * x + 0.8 * z;
    const crumb = fbm(ux * 10 + y * 3, y * 15 - ux * 2, uz * 10, 4);
    // Pores gather in clusters, as they do in a real griddle batter.
    const cluster = ss(0.36, 0.6, fbm(ux * 4.2 + 9, y * 6.5, uz * 4.2, 2));
    const bubble = ss(1.0, 0.62, pores(ux * 21, y * 15, uz * 21)) * (1 - face) * cluster;
    const k = ss(0.34, 0.66, crumb);
    let ar = mix(0.92, 1.0, k) * (1 - bubble * 0.22);
    let ag = mix(0.56, 0.7, k) * (1 - bubble * 0.36);
    let ab = mix(0.19, 0.3, k) * (1 - bubble * 0.52);
    ar = mix(ar, cr, face);
    ag = mix(ag, cg, face);
    ab = mix(ab, cb, face);
    // Fine crumb relief on the sides.
    const bs = 0.055 * (1 - face * 0.7);
    const e2 = 0.012;
    const wx = ux * 17 + y * 5, wy = y * 21 - ux * 4, wz = uz * 17;
    const f0 = noise(wx, wy, wz);
    const gx = (noise(wx + e2 * 17, wy, wz) - f0) / e2;
    const gy = (noise(wx, wy + e2 * 21, wz) - f0) / e2;
    const gz = (noise(wx, wy, wz + e2 * 17) - f0) / e2;
    let bx = nx - bs * 0.05 * (0.8 * gx - 0.6 * gz), by = ny - bs * 0.05 * gy, bz = nz - bs * 0.05 * (0.6 * gx + 0.8 * gz);
    const bl = Math.sqrt(bx * bx + by * by + bz * bz);
    bx /= bl;
    by /= bl;
    bz /= bl;
    const nl = bx * KEY[0] + by * KEY[1] + bz * KEY[2];
    const wrap = clamp((nl + 0.42) / 1.42, 0, 1);
    const sh = mix(0.2, 1, sKey);
    const bounce = 0.42 + 0.3 * by;
    const crev = occ * occ;
    let lr = 3.05 * wrap * sh + 0.86 * bounce * crev + 1.55 * rimL * rimL * occ;
    let lg = 2.62 * wrap * sh + 0.56 * bounce * crev + 1.0 * rimL * rimL * occ;
    let lb = 2.05 * wrap * sh + 0.34 * bounce * crev + 0.55 * rimL * rimL * occ;
    // Scattering warms the shadow terminator of the soft crumb.
    const scat = ss(-0.45, 0.2, nl) * (1 - ss(0.15, 0.8, nl));
    lr += scat * 0.72;
    lg += scat * 0.3;
    lb += scat * 0.08;
    cR = ar * lr * 0.5;
    cG = ag * lg * 0.5;
    cB = ab * lb * 0.5;
    const hx0 = KEY[0] + vx, hy0 = KEY[1] + vy, hz0 = KEY[2] + vz;
    const hl = Math.sqrt(hx0 * hx0 + hy0 * hy0 + hz0 * hz0);
    const nh = clamp((bx * hx0 + by * hy0 + bz * hz0) / hl, 0, 1);
    const sp = Math.pow(nh, 26) * 0.17 * sKey * face;
    cR += sp * 1.1;
    cG += sp * 0.9;
    cB += sp * 0.65;
    return;
  }

  // Rings spreading from where the pour lands.
  if (mat === 2 && y > TOP - 0.05 && y < TOP + 0.3) {
    const rx0 = x - STREAM_X, rz0 = z - STREAM_Z;
    const rd0 = Math.sqrt(rx0 * rx0 + rz0 * rz0) + 1e-6;
    const amp = 0.16 * Math.exp(-rd0 * 2.0) * Math.sin(rd0 * 25 - 0.8) * ss(0.07, 0.2, rd0);
    nx += (amp * rx0) / rd0;
    nz += (amp * rz0) / rd0;
    const nl0 = Math.sqrt(nx * nx + ny * ny + nz * nz);
    nx /= nl0;
    ny /= nl0;
    nz /= nl0;
  }

  // Reflection used by every glossy material.
  const rd = dx * nx + dy * ny + dz * nz;
  const rx = dx - 2 * rd * nx, ry = dy - 2 * rd * ny, rz = dz - 2 * rd * nz;
  paneGain = mat === 2 ? 1 : 0;
  env(rx, ry, rz, x, y, z);
  const hx = KEY[0] + vx, hy = KEY[1] + vy, hz = KEY[2] + vz;
  const hl = Math.sqrt(hx * hx + hy * hy + hz * hz);
  const nh = clamp((nx * hx + ny * hy + nz * hz) / hl, 0, 1);

  if (mat === 2) {
    stack(x, y, z);
    const onPlate = y < 0.17;
    const poolQ = clamp(Math.hypot(x - POOL_X, z - POOL_Z) / 0.5, 0, 1);
    const thick = onPlate ? mix(0.1, 0.022, poolQ * poolQ) : clamp(gSoft * 1.25, 0.016, 0.16);
    const isStream = y > TOP + 0.09;
    const path = isStream ? 0.2 : (thick * 2.8) / Math.max(nv, 0.42);
    const tR = Math.exp(-0.6 * path), tG = Math.exp(-3.1 * path), tB = Math.exp(-21 * path);
    const lit = clamp((ndl + 0.5) / 1.5, 0, 1) * mix(0.3, 1, sKey);
    const under = 0.36 + 1.02 * lit;
    let hr = 0.96 * tR * under + 0.045;
    let hg = 0.47 * tG * under + 0.012;
    let hb = 0.04 * tB * under + 0.001;
    // Inner glow where light passes through thin honey.
    const glow = Math.exp(-path * 7) * (0.3 + 0.7 * lit);
    hr += glow * 0.3;
    hg += glow * 0.105;
    hb += glow * 0.006;
    if (isStream) {
      const core = Math.pow(1 - nv, 1.4);
      hr = mix(0.92, 0.36, core);
      hg = mix(0.31, 0.065, core);
      hb = mix(0.02, 0.003, core);
    }
    // Melted butter clouds the honey around the pat.
    const bdx = x - BUTTER_X, bdz = z - BUTTER_Z;
    const near = Math.exp(-(bdx * bdx + bdz * bdz) * 4.2) * ss(TOP - 0.2, TOP, y);
    hr = mix(hr, 1.05, near * 0.26);
    hg = mix(hg, 0.56, near * 0.26);
    hb = mix(hb, 0.09, near * 0.26);
    const dark = mix(0.55, 1, occ);
    const F = 0.04 + 0.96 * fres;
    cR = hr * dark * (1 - F) + eR * F * 1.15;
    cG = hg * dark * (1 - F) + eG * F * 1.15;
    cB = hb * dark * (1 - F) + eB * F * 1.15;
    const sp = Math.pow(nh, 340) * 16 * sKey + Math.pow(nh, 46) * 0.42 * sKey;
    cR += sp;
    cG += sp * 0.9;
    cB += sp * 0.7;
    return;
  }

  if (mat === 3) {
    const lit = clamp((ndl + 0.55) / 1.55, 0, 1) * mix(0.42, 1, sKey);
    const lift = 0.48 + 0.25 * ny;
    const bl = 1.5 * lit + lift * occ;
    // The base has already turned to deeper, glossy liquid butter.
    const melt = ss(BUTTER_Y - 0.03, BUTTER_Y - 0.11, y);
    cR = 1.0 * bl + 0.07;
    cG = mix(0.7, 0.54, melt) * bl + 0.035;
    cB = mix(0.17, 0.07, melt) * bl + 0.006;
    const F = 0.035 + mix(0.5, 0.95, melt) * fres;
    cR = cR * (1 - F) + eR * F;
    cG = cG * (1 - F) + eG * F;
    cB = cB * (1 - F) + eB * F;
    const sp = Math.pow(nh, 90) * 1.9 * sKey;
    cR += sp;
    cG += sp * 0.93;
    cB += sp * 0.78;
    return;
  }

  // Plate: deep ink-blue glazed stoneware, the complement of the honey.
  const speck = ss(0.68, 0.86, fbm(x * 9, 1.3, z * 9, 3));
  const pa = 1 - speck * 0.12;
  const lit = clamp(ndl, 0, 1) * mix(0.12, 1, sKey);
  const amb = (0.28 + 0.2 * ny) * occ;
  const r2 = Math.sqrt(x * x + z * z);
  const warm = Math.exp(-Math.max(r2 - 1.65, 0) * 2.2) * 0.3 * occ;
  cR = pa * (0.011 * (2.3 * lit + amb * 1.1) + warm * 0.24);
  cG = pa * (0.023 * (2.2 * lit + amb * 1.1) + warm * 0.1);
  cB = pa * (0.039 * (2.0 * lit + amb * 1.1) + warm * 0.025);
  const F = 0.03 + 0.34 * fres;
  const mirror = mix(0.3, 1, occ) * 0.55;
  cR = cR * (1 - F) + eR * F * mirror;
  cG = cG * (1 - F) + eG * F * mirror;
  cB = cB * (1 - F) + eB * F * mirror;
}

function sample(sx: number, sy: number) {
  let dx = FW[0] * FOCAL + RT[0] * sx + UP[0] * sy;
  let dy = FW[1] * FOCAL + RT[1] * sx + UP[1] * sy;
  let dz = FW[2] * FOCAL + RT[2] * sx + UP[2] * sy;
  const l = Math.sqrt(dx * dx + dy * dy + dz * dz);
  dx /= l;
  dy /= l;
  dz /= l;

  // Bounding cylinder for the plate, stack and pour.
  const R = 3.05;
  const a = dx * dx + dz * dz;
  const b = RO[0] * dx + RO[2] * dz;
  const c = RO[0] * RO[0] + RO[2] * RO[2] - R * R;
  const disc = b * b - a * c;
  cId = 0;
  cDepth = 1000;
  if (disc > 0) {
    const q = Math.sqrt(disc);
    let t = Math.max((-b - q) / a, 0.1);
    const tEnd = (-b + q) / a;
    if (dy < 0) t = Math.max(t, (TOP + 7 - RO[1]) / dy > 0 ? 0.1 : 0.1);
    for (let i = 0; i < 120 && t < tEnd; i++) {
      const x = RO[0] + dx * t, y = RO[1] + dy * t, z = RO[2] + dz * t;
      if (y < -0.12) break;
      const d = map(x, y, z);
      if (d < 0.0009 * t * 0.25 + 0.0007) {
        const mat = gM === 0 ? 2 : gM;
        shade(x, y, z, dx, dy, dz, mat);
        cId = mat;
        cDepth = t;
        return;
      }
      t += d * 0.9;
    }
  }
  background(dx, dy, dz, sx, sy);
}

// ---------------------------------------------------------------- render
const hdr = new Float32Array(W * H * 3);
const ids = new Uint8Array(W * H);
const depth = new Float32Array(W * H);
for (let j = 0; j < H; j++) {
  for (let i = 0; i < W; i++) {
    const sx = ((i + 0.5) / W) * 2 - 1;
    const sy = 1 - ((j + 0.5) / H) * 2;
    sample(sx, sy);
    const o = (j * W + i) * 3;
    hdr[o] = cR;
    hdr[o + 1] = cG;
    hdr[o + 2] = cB;
    ids[j * W + i] = cId;
    depth[j * W + i] = cDepth;
  }
}

// Anti-alias only silhouettes: pixels whose material or depth jumps.
const OFFS = [[-0.125, -0.375], [0.375, -0.125], [0.125, 0.375], [-0.375, 0.125]];
const redo = new Uint8Array(W * H);
for (let j = 1; j < H - 1; j++) {
  for (let i = 1; i < W - 1; i++) {
    const p = j * W + i;
    const id = ids[p], de = depth[p];
    if (ids[p - 1] !== id || ids[p + 1] !== id || ids[p - W] !== id || ids[p + W] !== id ||
      Math.abs(depth[p - 1] - de) > 0.05 || Math.abs(depth[p + 1] - de) > 0.05 ||
      Math.abs(depth[p - W] - de) > 0.05 || Math.abs(depth[p + W] - de) > 0.05) {
      redo[p] = 1;
    }
  }
}
for (let j = 0; j < H; j++) {
  for (let i = 0; i < W; i++) {
    const p = j * W + i;
    if (!redo[p]) continue;
    let r = 0, g = 0, b = 0;
    for (const off of OFFS) {
      sample(((i + 0.5 + off[0]) / W) * 2 - 1, 1 - ((j + 0.5 + off[1]) / H) * 2);
      r += Math.min(cR, 6);
      g += Math.min(cG, 6);
      b += Math.min(cB, 6);
    }
    hdr[p * 3] = r / 4;
    hdr[p * 3 + 1] = g / 4;
    hdr[p * 3 + 2] = b / 4;
  }
}

// Faint steam rising off the warm stack, only over the dark backdrop.
const WISPS = [[-0.34, 0.48, 1.7], [0.04, 0.6, 4.1], [0.33, 0.5, 2.6]];
for (let j = 0; j < H; j++) {
  const sy = 1 - ((j + 0.5) / H) * 2;
  if (sy < 0.42) break;
  for (let i = 0; i < W; i++) {
    const p = j * W + i;
    if (ids[p] !== 0) continue;
    const sx = ((i + 0.5) / W) * 2 - 1;
    let a = 0;
    for (const w of WISPS) {
      const h = sy - w[1];
      if (h < 0) continue;
      const c = w[0] + 0.07 * Math.sin(h * 6 + w[2]) + 0.035 * Math.sin(h * 13 + w[2] * 2);
      const e = (sx - c) / (0.035 + 0.12 * h);
      a += Math.exp(-e * e) * ss(0, 0.12, h) * ss(0.62, 0.08, h);
    }
    if (a > 0.003) {
      const v = a * ss(0.3, 0.72, fbm(sx * 5, sy * 3.2, 1.7, 3)) * 0.07;
      hdr[p * 3] += v;
      hdr[p * 3 + 1] += v * 0.86;
      hdr[p * 3 + 2] += v * 0.7;
    }
  }
}

// Bloom: a soft glow on the brightest honey highlights.
const BW = W >> 2, BH = H >> 2;
let bloom = new Float32Array(BW * BH * 3);
for (let j = 0; j < H; j++) {
  for (let i = 0; i < W; i++) {
    const o = (j * W + i) * 3;
    const lum = hdr[o] * 0.3 + hdr[o + 1] * 0.6 + hdr[o + 2] * 0.1;
    const f = ss(1.1, 2.6, lum) / 16;
    const q = ((j >> 2) * BW + (i >> 2)) * 3;
    bloom[q] += Math.min(hdr[o], 8) * f;
    bloom[q + 1] += Math.min(hdr[o + 1], 8) * f;
    bloom[q + 2] += Math.min(hdr[o + 2], 8) * f;
  }
}
for (let pass = 0; pass < 3; pass++) {
  for (let axis = 0; axis < 2; axis++) {
    const next = new Float32Array(bloom.length);
    const rad = 7;
    const n = axis === 0 ? BW : BH, m = axis === 0 ? BH : BW;
    for (let b = 0; b < m; b++) {
      for (let ch = 0; ch < 3; ch++) {
        let acc = 0;
        const at = (k: number) => {
          const c = clamp(k, 0, n - 1);
          return (axis === 0 ? b * BW + c : c * BW + b) * 3 + ch;
        };
        for (let k = -rad; k <= rad; k++) acc += bloom[at(k)];
        for (let k = 0; k < n; k++) {
          next[at(k)] = acc / (2 * rad + 1);
          acc += bloom[at(k + rad + 1)] - bloom[at(k - rad)];
        }
      }
    }
    bloom = next;
  }
}

const aces = (x: number) => clamp((x * (2.51 * x + 0.03)) / (x * (2.43 * x + 0.59) + 0.14), 0, 1);
const srgb = (x: number) => (x <= 0.0031308 ? 12.92 * x : 1.055 * Math.pow(x, 1 / 2.4) - 0.055);

const rgb = new Uint8Array(W * H * 3);
for (let j = 0; j < H; j++) {
  for (let i = 0; i < W; i++) {
    const o = (j * W + i) * 3;
    const fx = (i / W) * BW - 0.5, fy = (j / H) * BH - 0.5;
    const x0 = clamp(Math.floor(fx), 0, BW - 1), y0 = clamp(Math.floor(fy), 0, BH - 1);
    const x1 = Math.min(x0 + 1, BW - 1), y1 = Math.min(y0 + 1, BH - 1);
    const u = clamp(fx - x0, 0, 1), v = clamp(fy - y0, 0, 1);
    const vx = i / W - 0.5, vy = j / H - 0.5;
    const vig = 1 - 0.62 * ss(0.3, 0.82, Math.sqrt(vx * vx + vy * vy));
    const luma = hdr[o] * 0.2126 + hdr[o + 1] * 0.7152 + hdr[o + 2] * 0.0722;
    for (let c = 0; c < 3; c++) {
      const a = mix(bloom[(y0 * BW + x0) * 3 + c], bloom[(y0 * BW + x1) * 3 + c], u);
      const b = mix(bloom[(y1 * BW + x0) * 3 + c], bloom[(y1 * BW + x1) * 3 + c], u);
      // A small saturation lift keeps the golds rich through the tone curve.
      const graded = Math.max(0, mix(luma, hdr[o + c], 1.06));
      const val = (graded + mix(a, b, v) * 0.5) * vig * 0.92;
      rgb[o + c] = Math.round(clamp(srgb(aces(val)), 0, 1) * 255);
    }
  }
}

// ---------------------------------------------------------------- PNG
const CRC = new Uint32Array(256);
for (let n = 0; n < 256; n++) {
  let c = n;
  for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
  CRC[n] = c >>> 0;
}
function crc32(buf: Uint8Array) {
  let c = 0xffffffff;
  for (let i = 0; i < buf.length; i++) c = CRC[(c ^ buf[i]) & 255] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}
function chunk(type: string, data: Uint8Array) {
  const out = Buffer.alloc(12 + data.length);
  out.writeUInt32BE(data.length, 0);
  out.write(type, 4, "latin1");
  Buffer.from(data).copy(out, 8);
  out.writeUInt32BE(crc32(out.subarray(4, 8 + data.length)), 8 + data.length);
  return out;
}
function encode(pix: Uint8Array) {
  const stride = W * 3;
  const raw = Buffer.alloc((stride + 1) * H);
  const cand = [0, 1, 2, 3, 4].map(() => new Uint8Array(stride));
  for (let y = 0; y < H; y++) {
    let bestF = 0, bestS = Infinity;
    for (let f = 0; f < 5; f++) {
      const line = cand[f];
      let sum = 0;
      for (let x = 0; x < stride; x++) {
        const cur = pix[y * stride + x];
        const a = x >= 3 ? pix[y * stride + x - 3] : 0;
        const b = y > 0 ? pix[(y - 1) * stride + x] : 0;
        const c = x >= 3 && y > 0 ? pix[(y - 1) * stride + x - 3] : 0;
        let pred = 0;
        if (f === 1) pred = a;
        else if (f === 2) pred = b;
        else if (f === 3) pred = (a + b) >> 1;
        else if (f === 4) {
          const p = a + b - c;
          const pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c);
          pred = pa <= pb && pa <= pc ? a : pb <= pc ? b : c;
        }
        const v = (cur - pred) & 255;
        line[x] = v;
        sum += v < 128 ? v : 256 - v;
      }
      if (sum < bestS) {
        bestS = sum;
        bestF = f;
      }
    }
    raw[y * (stride + 1)] = bestF;
    Buffer.from(cand[bestF]).copy(raw, y * (stride + 1) + 1);
  }
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(W, 0);
  ihdr.writeUInt32BE(H, 4);
  ihdr[8] = 8;
  ihdr[9] = 2;
  return Buffer.concat([
    Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]),
    chunk("IHDR", ihdr),
    chunk("IDAT", deflateSync(raw, { level: 9, memLevel: 9 })),
    chunk("IEND", new Uint8Array(0)),
  ]);
}

// Keep the file inside the size limit by coarsening the least visible bits.
let png = encode(rgb);
for (let step = 2; png.length > MAX_BYTES - 4096 && step <= 8; step++) {
  const q = new Uint8Array(rgb.length);
  for (let i = 0; i < rgb.length; i++) q[i] = Math.min(255, Math.round(rgb[i] / step) * step);
  png = encode(q);
}

const dir = process.env.MAKEFUN_OUTPUT_DIR || "/output";
mkdirSync(dir, { recursive: true });
writeFileSync(join(dir, "entry.png"), png);

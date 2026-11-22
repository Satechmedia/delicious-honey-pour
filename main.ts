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
    0.016 * Math.cos(a2), 0.016 * Math.sin(a2),
    0.011 * Math.cos(a3), 0.011 * Math.sin(a3),
    0.006 * Math.cos(a5), 0.006 * Math.sin(a5),
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
const POOL_X = -0.42, POOL_Z = 2.04;

let gI = 0, gHard = 0, gSoft = 0, gM = 0;
function stack(x: number, y: number, z: number) {
  let hard = 1e9, soft = 1e9, idx = 0;
  for (let i = 0; i < COUNT; i++) {
    const dy = y - CY[i];
    if (Math.abs(dy) > PH + 0.3 + Math.min(hard, 0.6)) continue;
    const dx = x - CX[i], dz = z - CZ[i];
    const r = Math.sqrt(dx * dx + dz * dz) + 1e-9;
    const c = dz / r, s = dx / r;
    const c2 = c * c - s * s, s2 = 2 * s * c;
    const c3 = c * c2 - s * s2, s3 = s * c2 + c * s2;
    const c5 = c2 * c3 - s2 * s3, s5 = s2 * c3 + c2 * s3;
    const w = WOB[i];
    const R = PR[i] * (1 + w[0] * c2 + w[1] * s2 + w[2] * c3 + w[3] * s3 + w[4] * c5 + w[5] * s5);
    const rr = PH * 0.94;
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
  const edge = 1.3 + 0.08 * Math.cos(2 * th + 0.7) + 0.06 * Math.cos(3 * th + 2.1) + 0.035 * Math.cos(7 * th + 0.3);
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

function map(x: number, y: number, z: number) {
  let best = 1e9, mat = 0;

  const pd = plateD(x, y, z);
  best = pd;
  mat = 4;

  // Honey stream falling from above onto the top pancake.
  if (y > TOP - 0.1) {
    const f = y - TOP;
    const sx = STREAM_X + 0.03 * Math.sin(f * 1.3) * f * 0.28;
    const sz = STREAM_Z + 0.022 * Math.sin(f * 0.9 + 1.1) * f * 0.24;
    const rad = 0.036 + 0.016 * Math.min(1, f / 3.4) + 0.05 * Math.exp(-Math.max(f, 0) * 7);
    const ddx = x - sx, ddz = z - sz;
    const ds = Math.sqrt(ddx * ddx + ddz * ddz) - rad;
    const mx = x - STREAM_X, mz = z - STREAM_Z, my = (y - TOP - 0.03) * 2.1;
    const mound = (Math.sqrt(mx * mx + my * my + mz * mz) - 0.24) / 2.1;
    const st = smin(ds * 0.92, mound, 0.08);
    if (st < best) {
      best = st;
      mat = 2;
    }
  }

  const rad2 = x * x + z * z;
  if (rad2 < 2.35 * 2.35 && y < TOP + 0.75) {
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
      const lobes = 0.56 + 0.09 * (co * co - si * si) + 0.06 * (2 * si * co) + 0.045 * (4 * co * co * co - 3 * co);
      const fx = pr - lobes, fy = Math.abs(y - PLATE_Y - 0.012) - 0.018;
      const mxp = fx > 0 ? fx : 0, myp = fy > 0 ? fy : 0;
      const pool = Math.min(Math.max(fx, fy), 0) + Math.sqrt(mxp * mxp + myp * myp) - 0.026;
      hd = smin(hd, pool, 0.09);
    }
    if (hd < best) {
      best = hd;
      mat = 2;
    }
    // Butter pat, gently slumped.
    const bx = x - BUTTER_X, bz = z - BUTTER_Z;
    const lx = BC * bx - BS * bz, lz = BS * bx + BC * bz;
    const ly = y - BUTTER_Y + 0.035 * lx + 0.02 * lz;
    const qbx = Math.abs(lx) - 0.4, qby = Math.abs(ly) - 0.075, qbz = Math.abs(lz) - 0.36;
    const mbx = qbx > 0 ? qbx : 0, mby = qby > 0 ? qby : 0, mbz = qbz > 0 ? qbz : 0;
    const bd = Math.sqrt(mbx * mbx + mby * mby + mbz * mbz) + Math.min(Math.max(qbx, qby, qbz), 0) - 0.06;
    if (bd < best) {
      best = bd;
      mat = 3;
    }
  } else {
    const bound = Math.max(Math.sqrt(rad2) - 2.2, y - TOP - 0.6);
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

let eR = 0, eG = 0, eB = 0;
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
    eR += sb * 15;
    eG += sb * 13.2;
    eB += sb * 10.6;
    const st = ss(3.2, 3.5, hx) * ss(4.4, 4.1, hx) * ss(-5.5, -4.5, hz) * ss(1.5, 0.5, hz);
    eR += st * 7;
    eG += st * 5.2;
    eB += st * 3.3;
  }
}

function shadow(x: number, y: number, z: number, lx: number, ly: number, lz: number, k: number) {
  let res = 1, t = 0.035;
  for (let i = 0; i < 20; i++) {
    const d = map(x + lx * t, y + ly * t, z + lz * t);
    const v = (k * d) / t;
    if (v < res) res = v;
    if (res < 0.01) return 0;
    t += clamp(d, 0.035, 0.42);
    if (t > 5.5) break;
  }
  res = clamp(res, 0, 1);
  return res * res * (3 - 2 * res);
}

function ao(x: number, y: number, z: number, nx: number, ny: number, nz: number) {
  let occ = 0, w = 1;
  for (let i = 1; i <= 5; i++) {
    const h = 0.02 + 0.075 * i;
    const d = map(x + nx * h, y + ny * h, z + nz * h);
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
const TX = 0, TY = 1.12, TZ = 0;
const EL = 0.36, AZ = 0.08, DIST = 11.2;
const RO = [TX + DIST * Math.cos(EL) * Math.sin(AZ), TY + DIST * Math.sin(EL), TZ + DIST * Math.cos(EL) * Math.cos(AZ)];
const FW = norm3(TX - RO[0], TY - RO[1], TZ - RO[2]);
const RT = norm3(FW[2] * -1, 0, FW[0]);
const UP: [number, number, number] = [
  RT[1] * FW[2] - RT[2] * FW[1],
  RT[2] * FW[0] - RT[0] * FW[2],
  RT[0] * FW[1] - RT[1] * FW[0],
];
const FOCAL = 3.75;

let cR = 0, cG = 0, cB = 0, cId = 0, cDepth = 0;

function background(dx: number, dy: number, dz: number, sx: number, sy: number) {
  // Table plane; soft by construction so it reads as depth of field.
  let r = 0.05, g = 0.024, b = 0.012;
  if (dy < -0.001) {
    const t = (-0.05 - RO[1]) / dy;
    const px = RO[0] + dx * t, pz = RO[2] + dz * t;
    const grain = fbm(px * 0.42 + 3, 0.2, pz * 1.7, 3);
    const wood = 0.72 + 0.55 * grain;
    r = 0.15 * wood;
    g = 0.074 * wood;
    b = 0.036 * wood;
    const pr = Math.hypot(px + 0.42, pz + 0.3);
    const sh = 1 - 0.8 * Math.exp(-Math.max(pr - 2.75, 0) * 1.5);
    r *= sh;
    g *= sh;
    b *= sh;
    const glow = Math.exp(-Math.max(pr - 2.2, 0) * 0.6) * 0.1;
    r += glow * 0.6;
    g += glow * 0.3;
    b += glow * 0.1;
    const far = ss(-3.2, -8.5, pz);
    r = mix(r, 0.12, far);
    g = mix(g, 0.055, far);
    b = mix(b, 0.022, far);
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
  BOKEH.push([rnd() * 2.2 - 1.1, 0.25 + rnd() * 0.85, 0.035 + rnd() * 0.075, 0.05 + rnd() * 0.17]);
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
    const face = ss(0.45, 0.86, Math.abs(v));
    const n1 = fbm(x * 1.6 + i * 3.17, y * 1.6 + i, z * 1.6, 4);
    const n2 = noise(x * 8.5, y * 8.5 + i, z * 8.5);
    const lace = ss(0.42, 0.72, n1 + 0.16 * n2);
    const cr = mix(0.46, 0.84, lace), cg = mix(0.17, 0.46, lace), cb = mix(0.035, 0.12, lace);
    const fine = noise(x * 34, y * 34, z * 34);
    const fine2 = noise(x * 13, y * 19, z * 13 + 5);
    const pore = ss(0.2, 0.42, fine * 0.65 + fine2 * 0.35);
    const k = ss(0.25, 0.75, fine2);
    let ar = mix(0.93, 1.0, k) * mix(0.72, 1, pore);
    let ag = mix(0.62, 0.8, k) * mix(0.62, 1, pore);
    let ab = mix(0.25, 0.42, k) * mix(0.5, 1, pore);
    ar = mix(ar, cr, face);
    ag = mix(ag, cg, face);
    ab = mix(ab, cb, face);
    // Crumb bump on the sides.
    const bs = 0.09 * (1 - face * 0.7);
    const e2 = 0.012;
    const f0 = noise(x * 26, y * 26, z * 26);
    const gx = (noise((x + e2) * 26, y * 26, z * 26) - f0) / e2;
    const gy = (noise(x * 26, (y + e2) * 26, z * 26) - f0) / e2;
    const gz = (noise(x * 26, y * 26, (z + e2) * 26) - f0) / e2;
    let bx = nx - bs * 0.05 * gx, by = ny - bs * 0.05 * gy, bz = nz - bs * 0.05 * gz;
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
    cR = ar * lr * 0.56;
    cG = ag * lg * 0.56;
    cB = ab * lb * 0.56;
    const hx0 = KEY[0] + vx, hy0 = KEY[1] + vy, hz0 = KEY[2] + vz;
    const hl = Math.sqrt(hx0 * hx0 + hy0 * hy0 + hz0 * hz0);
    const nh = clamp((bx * hx0 + by * hy0 + bz * hz0) / hl, 0, 1);
    const sp = Math.pow(nh, 26) * 0.17 * sKey * face;
    cR += sp * 1.1;
    cG += sp * 0.9;
    cB += sp * 0.65;
    return;
  }

  // Reflection used by every glossy material.
  const rd = dx * nx + dy * ny + dz * nz;
  const rx = dx - 2 * rd * nx, ry = dy - 2 * rd * ny, rz = dz - 2 * rd * nz;
  env(rx, ry, rz, x, y, z);
  const hx = KEY[0] + vx, hy = KEY[1] + vy, hz = KEY[2] + vz;
  const hl = Math.sqrt(hx * hx + hy * hy + hz * hz);
  const nh = clamp((nx * hx + ny * hy + nz * hz) / hl, 0, 1);

  if (mat === 2) {
    stack(x, y, z);
    const thick = clamp(gSoft, 0.004, 0.2);
    const isStream = y > TOP + 0.09;
    const path = isStream ? 0.16 : (thick * 1.8) / Math.max(nv, 0.3);
    const tR = Math.exp(-0.5 * path), tG = Math.exp(-3.3 * path), tB = Math.exp(-12.5 * path);
    const lit = clamp((ndl + 0.5) / 1.5, 0, 1) * mix(0.3, 1, sKey);
    const under = 0.48 + 1.72 * lit;
    let hr = 1.12 * tR * under + 0.1;
    let hg = 0.68 * tG * under + 0.028;
    let hb = 0.22 * tB * under + 0.004;
    // Inner glow where light passes through thin honey.
    const glow = Math.exp(-path * 5.2) * (0.3 + 0.7 * lit);
    hr += glow * 0.46;
    hg += glow * 0.25;
    hb += glow * 0.03;
    if (isStream) {
      const core = Math.pow(1 - nv, 1.5);
      hr = mix(1.25, 0.72, core);
      hg = mix(0.68, 0.24, core);
      hb = mix(0.08, 0.018, core);
    }
    // Melted butter clouds the honey around the pat.
    const bdx = x - BUTTER_X, bdz = z - BUTTER_Z;
    const near = Math.exp(-(bdx * bdx + bdz * bdz) * 3.4) * ss(TOP - 0.2, TOP, y);
    hr = mix(hr, 1.4, near * 0.48);
    hg = mix(hg, 1.05, near * 0.48);
    hb = mix(hb, 0.34, near * 0.48);
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
    const bl = 1.72 * lit + lift * occ;
    cR = 1.0 * bl + 0.08;
    cG = 0.8 * bl + 0.05;
    cB = 0.3 * bl + 0.012;
    const F = 0.035 + 0.6 * fres;
    cR = cR * (1 - F) + eR * F;
    cG = cG * (1 - F) + eG * F;
    cB = cB * (1 - F) + eB * F;
    const sp = Math.pow(nh, 90) * 1.9 * sKey;
    cR += sp;
    cG += sp * 0.93;
    cB += sp * 0.78;
    return;
  }

  // Plate: warm cream glazed stoneware.
  const speck = ss(0.8, 0.9, noise(x * 16, 1.3, z * 16));
  const pa = 0.86 - speck * 0.2;
  const lit = clamp(ndl, 0, 1) * mix(0.14, 1, sKey);
  const amb = (0.28 + 0.2 * ny) * occ;
  const r2 = Math.sqrt(x * x + z * z);
  const warm = Math.exp(-Math.max(r2 - 1.65, 0) * 1.9) * 0.44 * occ;
  cR = pa * (2.3 * lit + amb * 1.15 + warm * 1.2);
  cG = pa * 0.92 * (2.14 * lit + amb * 1.0 + warm * 0.68);
  cB = pa * 0.8 * (1.9 * lit + amb * 0.84 + warm * 0.28);
  const F = 0.04 + 0.7 * fres;
  cR = cR * (1 - F) + eR * F * 0.8;
  cG = cG * (1 - F) + eG * F * 0.8;
  cB = cB * (1 - F) + eB * F * 0.8;
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
    for (let c = 0; c < 3; c++) {
      const a = mix(bloom[(y0 * BW + x0) * 3 + c], bloom[(y0 * BW + x1) * 3 + c], u);
      const b = mix(bloom[(y1 * BW + x0) * 3 + c], bloom[(y1 * BW + x1) * 3 + c], u);
      const val = (hdr[o + c] + mix(a, b, v) * 0.5) * vig * 0.92;
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

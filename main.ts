// png-squeeze: a lossless PNG recompressor for 1280x720 RGBA screenshots.
//
// Pipeline per instance:
//   1. Decode the stored input PNG to RGBA.
//   2. Screen the lossless forms (palette / grey / grey+alpha / RGB / RGBA, with a
//      transparent-colour key where legal) and the filter strategies for each,
//      weighing each candidate with zlib level 6, exactly as the contest's own
//      scale compressor does.
//   3. Re-select every row's filter with this program's own deflate cost model
//      (Huffman tables from a first lazy parse), which beats zlib level 4's
//      per-row trials as a proxy for the final deflate.
//   4. Compress the winner twice -- a lazy LZ77 parse with long hash chains, and
//      a bounded dynamic-programming optimal parse (zopfli-style, with distance
//      bands and the lazy parse's matches as extra candidates) -- and keep the
//      smaller stream. Each stream is a single zlib stream with optimal
//      (package-merge) Huffman codes and a choice of dynamic or fixed blocks.
//
// Pure Node 22 built-ins only (fs, path, zlib). No clock, no randomness, no
// network, no files outside /input, /output and this program: two runs on the
// same set write byte-identical outputs.
import { inflateSync, deflateSync, constants as zlibConstants } from 'node:zlib';
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// ---------------------------------------------------------------------------
// PNG codec: signature, CRC-32, Adler-32, chunk assembly, decoder, filters.
// ---------------------------------------------------------------------------

const PNG_SIGNATURE = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
const CHANNELS = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };

const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();

function crc32(bytes, start = 0, end = bytes.length) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

function adler32(bytes) {
  let a = 1, b = 0;
  for (let i = 0; i < bytes.length;) {
    const end = Math.min(bytes.length, i + 5552);
    for (; i < end; i++) { a += bytes[i]; b += a; }
    a %= 65521; b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

const asciiBytes = (s) => Uint8Array.from(s, (ch) => ch.charCodeAt(0));

function assemblePng(chunks) {
  let size = PNG_SIGNATURE.length;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set(PNG_SIGNATURE, 0);
  let at = PNG_SIGNATURE.length;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    out.set(asciiBytes(type), at + 4);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}

function ihdrData(width, height, colourType) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}

function paethPredictor(a, b, c) {
  const p = a + b - c;
  const pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c);
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}

// Filter one row (cur, stride samples, bpp bytes a pixel) by `type` into out.
function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) { out.set(cur); return; }
  if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paethPredictor(a, b, c);
    }
  }
}

function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

// Decode a PNG (any accepted colour type, bit depth 8, non-interlaced) to RGBA.
// Throws on anything malformed.
function decodePng(bytes) {
  if (!(bytes instanceof Uint8Array)) throw new Error('input is not bytes');
  if (bytes.length < 8 || PNG_SIGNATURE.some((b, i) => bytes[i] !== b)) throw new Error('bad PNG signature');
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let header = null, palette = null, trns = null;
  const idat = [];
  let ended = false;
  while (at < bytes.length) {
    if (ended) throw new Error('bytes after IEND');
    if (at + 12 > bytes.length) throw new Error('truncated chunk');
    const len = view.getUint32(at);
    if (len > 0x7fffffff || at + 12 + len > bytes.length) throw new Error('chunk overruns file');
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    if (crc32(bytes, at + 4, at + 8 + len) !== view.getUint32(at + 8 + len)) throw new Error(type + ' CRC mismatch');
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (type === 'IHDR') {
      if (header !== null) throw new Error('IHDR twice');
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = { width: dv.getUint32(0), height: dv.getUint32(4), depth: data[8], colourType: data[9] };
      if (header.depth !== 8) throw new Error('bit depth is not 8');
      if (!Object.hasOwn(CHANNELS, header.colourType)) throw new Error('bad colour type');
      if (data[10] !== 0 || data[11] !== 0 || data[12] !== 0) throw new Error('unsupported IHDR flags');
    } else if (type === 'PLTE') {
      if (palette !== null) throw new Error('PLTE twice');
      palette = data;
    } else if (type === 'tRNS') {
      if (trns !== null) throw new Error('tRNS twice');
      trns = data;
    } else if (type === 'IDAT') {
      idat.push(data);
    } else if (type === 'IEND') {
      ended = true;
    } else {
      throw new Error('unexpected chunk ' + type);
    }
  }
  if (!ended || !header || idat.length === 0) throw new Error('incomplete PNG');
  const { width, height, colourType } = header;
  const bpp = CHANNELS[colourType];
  const stride = width * bpp;
  const expected = height * (stride + 1);
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat), { maxOutputLength: expected + 1 });
  if (raw.length !== expected) throw new Error('inflated size mismatch');
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    if (ft > 4) throw new Error('bad filter type');
    const src = y * (stride + 1) + 1;
    const o = y * stride, p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    } else if (ft === 2) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    } else if (ft === 3) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    } else {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[o + i - bpp] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
        samples[o + i] = raw[src + i] + paethPredictor(a, b, c);
      }
    }
  }
  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    const entries = palette.length / 3;
    const lut = new Uint8Array(entries * 4);
    for (let e = 0; e < entries; e++) {
      lut[e * 4] = palette[e * 3];
      lut[e * 4 + 1] = palette[e * 3 + 1];
      lut[e * 4 + 2] = palette[e * 3 + 2];
      lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      if (e >= entries) throw new Error('palette index out of range');
      rgba[d] = lut[e * 4]; rgba[d + 1] = lut[e * 4 + 1]; rgba[d + 2] = lut[e * 4 + 2]; rgba[d + 3] = lut[e * 4 + 3];
    }
  }
  return { width, height, rgba };
}

// ---------------------------------------------------------------------------
// Lossless forms: palette / grey / grey+alpha / RGB / RGBA, tRNS key, filters.
// ---------------------------------------------------------------------------

function wordsOf(rgba) {
  const at = rgba.byteOffset % 4 === 0 ? rgba : rgba.slice();
  return new Uint32Array(at.buffer, at.byteOffset, at.length >>> 2);
}

// Whether every pixel is opaque, whether every pixel is grey, and the colours
// when there are at most 256 of them.
function analyseImage(rgba) {
  const n = rgba.length >>> 2;
  const u32 = wordsOf(rgba);
  let opaque = true, grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const c = u32[i];
      const k = counts.get(c);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(c, 1);
      } else counts.set(c, k + 1);
    }
  }
  const colours = many ? null : [...counts.keys()].map((c) => {
    const b = new Uint8Array(Uint32Array.of(c).buffer);
    return { rgba: [b[0], b[1], b[2], b[3]], word: c, count: counts.get(c) };
  });
  return { opaque, grey, colours };
}

// The one fully transparent value (grey or RGB) the image may key by tRNS
// instead of an alpha channel: every pixel opaque or that exact value at
// alpha 0, and no opaque pixel of the same value. Null when there is none.
function transparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}

function samplesOf(rgba, ct) {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) { out[s] = rgba[d]; out[s + 1] = rgba[d + 3]; }
    else { out[s] = rgba[d]; out[s + 1] = rgba[d + 1]; out[s + 2] = rgba[d + 2]; }
  }
  return out;
}

function paletteOrder(colours, order) {
  const lum = (c) => 299 * c.rgba[0] + 587 * c.rgba[1] + 114 * c.rgba[2];
  return [...colours].sort((x, y) => {
    const ta = x.rgba[3] === 255 ? 1 : 0;
    const tb = y.rgba[3] === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.rgba[3] !== y.rgba[3]) return x.rgba[3] - y.rgba[3];
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
}

function paletteForm(rgba, colours, order) {
  const entries = paletteOrder(colours, order);
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.rgba[0];
    plte[i * 3 + 1] = c.rgba[1];
    plte[i * 3 + 2] = c.rgba[2];
    if (c.rgba[3] !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.rgba[3]);
  const n = rgba.length >>> 2;
  const u32 = wordsOf(rgba);
  const indices = new Uint8Array(n);
  for (let i = 0; i < n; i++) indices[i] = index.get(u32[i]);
  return { plte, trns, indices };
}

const SCREEN_LEVEL = { level: 6, memLevel: 8, strategy: zlibConstants.Z_DEFAULT_STRATEGY };
const BRUTE_CONTEXT = 32768;
const BRUTE_LEVEL = 4;

function pairsOf(row, seen, stamp) {
  let n = 0;
  for (let i = 1; i < row.length; i++) {
    const pair = (row[i - 1] << 8) | row[i];
    if (seen[pair] !== stamp) { seen[pair] = stamp; n++; }
  }
  return n;
}

// Filtered raw data of `samples` by `choice`: a fixed filter (0-4), or
// 'minsum' / 'pairs' / 'brute' per-row heuristics. Written into `raw` when given.
function filteredData(samples, width, height, bpp, choice, raw = new Uint8Array(height * (width * bpp + 1))) {
  const stride = width * bpp;
  const trial = Array.from({ length: 5 }, (_, t) => {
    const row = new Uint8Array(stride + 1);
    row[0] = t;
    return row;
  });
  const seen = new Uint32Array(65536);
  let stamp = 0;
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - BRUTE_CONTEXT), at);
    let type = 0, best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, trial[t].subarray(1));
      let cost;
      if (choice === 'minsum') cost = signedSum(trial[t].subarray(1));
      else if (choice === 'pairs') cost = pairsOf(trial[t].subarray(1), seen, ++stamp);
      else cost = deflateSync(trial[t], before.length === 0 ? { level: BRUTE_LEVEL, memLevel: 9 } : { level: BRUTE_LEVEL, memLevel: 9, dictionary: before }).length;
      if (cost < best) { best = cost; type = t; }
    }
    raw.set(trial[type], at);
  }
  return raw;
}

const FILTERS = {
  palette: [0],
  paletteByLuminance: [0, 'brute'],
  channels: [0, 'brute'],
};

function formsOf(rgba) {
  const { opaque, grey, colours } = analyseImage(rgba);
  const forms = [];
  if (colours !== null) {
    for (const [order, filters] of [['count', FILTERS.palette], ['luminance', FILTERS.paletteByLuminance]]) {
      const p = paletteForm(rgba, colours, order);
      forms.push({ colourType: 3, bpp: 1, samples: p.indices, plte: p.plte, trns: p.trns, filters });
    }
    if (!grey) return forms;
  }
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct, trns = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = { 0: 1, 2: 3, 4: 2, 6: 4 }[ct];
  forms.push({ colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns, filters: FILTERS.channels });
  return forms;
}

const chunkBytes = (form) => (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);

// The screen's winner for an image: its form, filter choice and filtered data,
// weighed by zlib level 6 (plus PLTE/tRNS chunk bytes); the first on a tie.
function screenImage(rgba, width, height) {
  let best = null, spare = null;
  for (const form of formsOf(rgba)) {
    const size = height * (width * form.bpp + 1);
    const chunks = chunkBytes(form);
    for (const choice of form.filters) {
      const data = filteredData(form.samples, width, height, form.bpp, choice, spare !== null && spare.length === size ? spare : new Uint8Array(size));
      spare = null;
      const zlib = deflateSync(data, SCREEN_LEVEL);
      const bytes = zlib.length + chunks;
      if (best === null || bytes < best.bytes) {
        if (best !== null) spare = best.data;
        best = { form, choice, data, bytes };
      } else spare = data;
    }
  }
  return best;
}

function pngOfForm(width, height, form, idat) {
  const chunks = [['IHDR', ihdrData(width, height, form.colourType)]];
  if (form.plte !== null) chunks.push(['PLTE', form.plte]);
  if (form.trns !== null) chunks.push(['tRNS', form.trns]);
  chunks.push(['IDAT', idat]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return assemblePng(chunks);
}

// ---------------------------------------------------------------------------
// Deflate: lazy LZ77 + bounded DP optimal parse, optimal Huffman, block split.
// ---------------------------------------------------------------------------

const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

function lenCode(len) {
  let lo = 0, hi = 28;
  while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (LEN_BASE[mid] <= len) lo = mid; else hi = mid - 1; }
  return lo;
}
function distCode(d) {
  let lo = 0, hi = 29;
  while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (DIST_BASE[mid] <= d) lo = mid; else hi = mid - 1; }
  return lo;
}

// Package-merge: length-limited Huffman code lengths (maxBits) for frequencies.
function packageMerge(freq, maxBits) {
  const n = freq.length;
  const out = new Uint8Array(n);
  const syms = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) syms.push(i);
  if (syms.length === 0) return out;
  if (syms.length === 1) { out[syms[0]] = 1; return out; }
  syms.sort((a, b) => freq[a] - freq[b] || a - b);
  const limit = 2 * syms.length - 2;
  const init = syms.map((s) => ({ w: freq[s], s: [s] }));
  let cur = init;
  for (let round = 1; round < maxBits; round++) {
    const packaged = [];
    for (let i = 0; i + 1 < cur.length; i += 2) packaged.push({ w: cur[i].w + cur[i + 1].w, s: cur[i].s.concat(cur[i + 1].s) });
    const merged = [];
    let a = 0, b = 0;
    while (merged.length < limit && (a < packaged.length || b < init.length)) {
      if (b >= init.length || (a < packaged.length && packaged[a].w <= init[b].w)) merged.push(packaged[a++]);
      else merged.push(init[b++]);
    }
    cur = merged;
  }
  for (const item of cur) for (const s of item.s) out[s]++;
  return out;
}

// Canonical Huffman codes from lengths; codes are bit-reversed for LSB-first output.
function canonicalCodes(lengths) {
  const n = lengths.length;
  const codes = new Uint16Array(n);
  const blCount = new Uint16Array(16);
  for (let i = 0; i < n; i++) blCount[lengths[i]]++;
  blCount[0] = 0;
  const next = new Uint16Array(16);
  let code = 0;
  for (let b = 1; b < 16; b++) { code = (code + blCount[b - 1]) << 1; next[b] = code; }
  for (let i = 0; i < n; i++) {
    const l = lengths[i];
    if (l !== 0) { codes[i] = next[l]; next[l]++; }
  }
  const rev = new Uint16Array(n);
  for (let i = 0; i < n; i++) {
    let c = codes[i], r = 0;
    for (let k = 0; k < lengths[i]; k++) { r = (r << 1) | (c & 1); c >>= 1; }
    rev[i] = r;
  }
  return { codes: rev, lengths };
}

class BitWriter {
  constructor() { this.bytes = []; this.acc = 0; this.nbits = 0; }
  write(val, n) {
    this.acc |= (val & ((1 << n) - 1)) << this.nbits;
    this.nbits += n;
    while (this.nbits >= 8) { this.bytes.push(this.acc & 0xff); this.acc >>>= 8; this.nbits -= 8; }
  }
  writeCode(code, len) { this.write(code, len); }
  finish() {
    if (this.nbits > 0) { this.bytes.push(this.acc & 0xff); this.acc = 0; this.nbits = 0; }
    return Uint8Array.from(this.bytes);
  }
}

function fixedCode(sym) {
  let code, len;
  if (sym <= 143) { code = 0x30 + sym; len = 8; }
  else if (sym <= 255) { code = 0x190 + (sym - 144); len = 9; }
  else if (sym <= 279) { code = sym - 256; len = 7; }
  else { code = 0xc0 + (sym - 280); len = 8; }
  let r = 0;
  for (let k = 0; k < len; k++) { r = (r << 1) | (code & 1); code >>= 1; }
  return r;
}
function fixedDistCode(dc) {
  let r = 0;
  for (let k = 0; k < 5; k++) { r = (r << 1) | (dc & 1); dc >>= 1; }
  return r;
}
const fixedLitLen = (s) => s <= 143 ? 8 : s <= 255 ? 9 : s <= 279 ? 7 : 8;

// Lazy LZ77 parse: hash chains, longest match, one-step lazy evaluation.
// Returns ops {type (0 literal, 1 match), a (byte or length), b (distance)}.
function lzParse(data, maxChain = 4096) {
  const n = data.length;
  const MASK = 32767;
  const head = new Int32Array(32768).fill(-1);
  const prev = new Int32Array(32768).fill(-1);
  const type = [], a = [], b = [];
  const hashAt = (p) => (((data[p] << 10) ^ (data[p + 1] << 5) ^ data[p + 2]) & MASK);
  const insert = (p) => {
    const h = hashAt(p);
    prev[p & 32767] = head[h];
    head[h] = p;
  };
  const longest = (p) => {
    let bestLen = 0, bestDist = 0;
    const h = hashAt(p);
    let cand = head[h];
    let chain = maxChain;
    const maxLen = Math.min(258, n - p);
    if (maxLen < 3) return null;
    while (cand >= 0 && chain-- > 0) {
      const dist = p - cand;
      if (dist <= 0) { cand = prev[cand & 32767]; continue; }
      if (dist > 32768) break;
      if (data[cand + bestLen] === data[p + bestLen]) {
        let len = 0;
        while (len < maxLen && data[cand + len] === data[p + len]) len++;
        if (len > bestLen) {
          bestLen = len; bestDist = dist;
          if (len >= maxLen) break;
          if (len >= 32) chain = Math.min(chain, maxChain >> 2);
        }
      }
      cand = prev[cand & 32767];
    }
    return bestLen >= 3 ? { len: bestLen, dist: bestDist } : null;
  };
  let p = 0;
  if (n >= 3) insert(0);
  while (p < n) {
    if (p + 2 >= n) { type.push(0); a.push(data[p]); b.push(0); p++; continue; }
    const m1 = longest(p);
    if (m1 && m1.len >= 3) {
      let useIt = true;
      if (m1.len < 258 && p + 3 < n) {
        const m2 = longest(p + 1);
        if (m2 && m2.len > m1.len) useIt = false;
      }
      if (useIt) {
        type.push(1); a.push(m1.len); b.push(m1.dist);
        const end = p + m1.len;
        for (let q = p + 1; q <= end && q + 2 < n; q++) insert(q);
        p = end;
        continue;
      }
    }
    type.push(0); a.push(data[p]); b.push(0);
    if (p + 2 < n) insert(p + 1);
    p++;
  }
  return { type: Uint8Array.from(type), a: Uint16Array.from(a), b: Uint16Array.from(b) };
}

function opFreqs(ops) {
  const litFreq = new Uint32Array(288);
  const distFreq = new Uint32Array(32);
  for (let i = 0; i < ops.type.length; i++) {
    if (ops.type[i] === 0) litFreq[ops.a[i]]++;
    else { litFreq[257 + lenCode(ops.a[i])]++; distFreq[distCode(ops.b[i])]++; }
  }
  litFreq[256]++;
  return { litFreq, distFreq };
}

// Encode one block of ops [start, end): dynamic Huffman unless fixed is smaller.
function encodeBlock(bw, ops, start, end, isLast) {
  const litFreq = new Uint32Array(288);
  const distFreq = new Uint32Array(32);
  for (let i = start; i < end; i++) {
    if (ops.type[i] === 0) litFreq[ops.a[i]]++;
    else { litFreq[257 + lenCode(ops.a[i])]++; distFreq[distCode(ops.b[i])]++; }
  }
  litFreq[256]++;
  let fixedBits = 3;
  for (let i = start; i < end; i++) {
    if (ops.type[i] === 0) fixedBits += fixedLitLen(ops.a[i]);
    else {
      const lc = lenCode(ops.a[i]);
      fixedBits += fixedLitLen(257 + lc) + LEN_EXTRA[lc] + 5 + DIST_EXTRA[distCode(ops.b[i])];
    }
  }
  fixedBits += 7;
  const litLengths = packageMerge(litFreq, 15);
  const distLengths = packageMerge(distFreq, 15);
  let hlit = 288;
  while (hlit > 257 && litLengths[hlit - 1] === 0) hlit--;
  let hdist = 32;
  while (hdist > 1 && distLengths[hdist - 1] === 0) hdist--;
  const clFreq = new Uint32Array(19);
  const countCL = (lengths, upto) => {
    let run = 0, prev = -1;
    const push = (sym, cnt) => {
      if (cnt === 1) clFreq[sym]++;
      else if (sym === 0) {
        while (cnt >= 11) { clFreq[18]++; cnt -= Math.min(138, cnt); }
        if (cnt >= 3) { clFreq[17]++; cnt = 0; }
        while (cnt-- > 0) clFreq[0]++;
      } else {
        clFreq[sym]++;
        cnt--;
        while (cnt >= 3) { clFreq[16]++; cnt -= Math.min(6, cnt); }
        while (cnt-- > 0) clFreq[sym]++;
      }
    };
    for (let i = 0; i < upto; i++) {
      const l = lengths[i];
      if (l === prev) run++;
      else { if (run > 0) push(prev, run); prev = l; run = 1; }
    }
    if (run > 0) push(prev, run);
  };
  countCL(litLengths, hlit);
  countCL(distLengths, hdist);
  const clLengths = packageMerge(clFreq, 7);
  let hclen = 19;
  while (hclen > 4 && clLengths[CL_ORDER[hclen - 1]] === 0) hclen--;
  let dynBits = 3 + 14 + 3 + hclen * 3;
  const clCan = canonicalCodes(clLengths);
  const addCLBits = (lengths, upto) => {
    let run = 0, prev = -1;
    const push = (sym, cnt) => {
      if (cnt === 1) dynBits += clLengths[sym];
      else if (sym === 0) {
        while (cnt >= 11) { dynBits += clLengths[18] + 7; cnt -= Math.min(138, cnt); }
        if (cnt >= 3) { dynBits += clLengths[17] + 3; cnt = 0; }
        dynBits += cnt * clLengths[0];
      } else {
        dynBits += clLengths[sym];
        cnt--;
        while (cnt >= 3) { dynBits += clLengths[16] + 2; cnt -= Math.min(6, cnt); }
        dynBits += cnt * clLengths[sym];
      }
    };
    for (let i = 0; i < upto; i++) {
      const l = lengths[i];
      if (l === prev) run++;
      else { if (run > 0) push(prev, run); prev = l; run = 1; }
    }
    if (run > 0) push(prev, run);
  };
  addCLBits(litLengths, hlit);
  addCLBits(distLengths, hdist);
  for (let i = start; i < end; i++) {
    if (ops.type[i] === 0) dynBits += litLengths[ops.a[i]];
    else {
      const lc = lenCode(ops.a[i]);
      dynBits += litLengths[257 + lc] + LEN_EXTRA[lc];
      const dc = distCode(ops.b[i]);
      dynBits += distLengths[dc] + DIST_EXTRA[dc];
    }
  }
  dynBits += litLengths[256];

  if (fixedBits <= dynBits) {
    bw.write(isLast ? 1 : 0, 1);
    bw.write(1, 2);
    for (let i = start; i < end; i++) {
      if (ops.type[i] === 0) {
        const s = ops.a[i];
        bw.writeCode(fixedCode(s), fixedLitLen(s));
      } else {
        const lc = lenCode(ops.a[i]);
        const sym = 257 + lc;
        bw.writeCode(fixedCode(sym), fixedLitLen(sym));
        if (LEN_EXTRA[lc]) bw.write(ops.a[i] - LEN_BASE[lc], LEN_EXTRA[lc]);
        const dc = distCode(ops.b[i]);
        bw.writeCode(fixedDistCode(dc), 5);
        if (DIST_EXTRA[dc]) bw.write(ops.b[i] - DIST_BASE[dc], DIST_EXTRA[dc]);
      }
    }
    bw.writeCode(fixedCode(256), 7);
    return;
  }
  bw.write(isLast ? 1 : 0, 1);
  bw.write(2, 2);
  bw.write(hlit - 257, 5);
  bw.write(hdist - 1, 5);
  bw.write(hclen - 4, 4);
  for (let i = 0; i < hclen; i++) bw.write(clLengths[CL_ORDER[i]], 3);
  const writeCL = (lengths, upto) => {
    let run = 0, prev = -1;
    const push = (sym, cnt) => {
      if (cnt === 1) bw.writeCode(clCan.codes[sym], clLengths[sym]);
      else if (sym === 0) {
        while (cnt >= 11) { const r = Math.min(138, cnt); bw.writeCode(clCan.codes[18], clLengths[18]); bw.write(r - 11, 7); cnt -= r; }
        if (cnt >= 3) { bw.writeCode(clCan.codes[17], clLengths[17]); bw.write(cnt - 3, 3); cnt = 0; }
        while (cnt-- > 0) bw.writeCode(clCan.codes[0], clLengths[0]);
      } else {
        bw.writeCode(clCan.codes[sym], clLengths[sym]);
        cnt--;
        while (cnt >= 3) { const r = Math.min(6, cnt); bw.writeCode(clCan.codes[16], clLengths[16]); bw.write(r - 3, 2); cnt -= r; }
        while (cnt-- > 0) bw.writeCode(clCan.codes[sym], clLengths[sym]);
      }
    };
    for (let i = 0; i < upto; i++) {
      const l = lengths[i];
      if (l === prev) run++;
      else { if (run > 0) push(prev, run); prev = l; run = 1; }
    }
    if (run > 0) push(prev, run);
  };
  writeCL(litLengths, hlit);
  writeCL(distLengths, hdist);
  const litCan = canonicalCodes(litLengths);
  const distCan = canonicalCodes(distLengths);
  for (let i = start; i < end; i++) {
    if (ops.type[i] === 0) {
      const s = ops.a[i];
      bw.writeCode(litCan.codes[s], litLengths[s]);
    } else {
      const lc = lenCode(ops.a[i]);
      const sym = 257 + lc;
      bw.writeCode(litCan.codes[sym], litLengths[sym]);
      if (LEN_EXTRA[lc]) bw.write(ops.a[i] - LEN_BASE[lc], LEN_EXTRA[lc]);
      const dc = distCode(ops.b[i]);
      bw.writeCode(distCan.codes[dc], distLengths[dc]);
      if (DIST_EXTRA[dc]) bw.write(ops.b[i] - DIST_BASE[dc], DIST_EXTRA[dc]);
    }
  }
  bw.writeCode(litCan.codes[256], litLengths[256]);
}

// Encode parsed ops as one zlib stream, split into blocks of at most
// `blockBytes` of raw input each.
function deflateFromOps(ops, data, blockBytes = Infinity) {
  const bounds = [0];
  let acc = 0;
  for (let i = 0; i < ops.type.length; i++) {
    acc += ops.type[i] === 0 ? 1 : ops.a[i];
    if (acc >= blockBytes && i + 1 < ops.type.length) { bounds.push(i + 1); acc = 0; }
  }
  bounds.push(ops.type.length);
  const bw = new BitWriter();
  for (let k = 0; k < bounds.length - 1; k++) {
    encodeBlock(bw, ops, bounds[k], bounds[k + 1], k === bounds.length - 2);
  }
  const body = bw.finish();
  const out = new Uint8Array(2 + body.length + 4);
  out[0] = 0x78; out[1] = 0x9c;
  out.set(body, 2);
  const ad = adler32(data);
  out[2 + body.length] = (ad >>> 24) & 0xff;
  out[3 + body.length] = (ad >>> 16) & 0xff;
  out[4 + body.length] = (ad >>> 8) & 0xff;
  out[5 + body.length] = ad & 0xff;
  return out;
}

// Bounded DP optimal parse: at each position, literal plus the longest match,
// the longest match in each distance band, and the lazy parse's match at that
// position, each with lengths trimmed by up to TRIM. Costs from litLen/distLen.
function dpParse(data, litLen, distLen, lazyOps, maxChain = 32, trim = 8) {
  const n = data.length;
  const litBits = new Float64Array(256);
  for (let i = 0; i < 256; i++) litBits[i] = litLen[i] || 12;
  const matchBits = (len, dist) => {
    const lc = lenCode(len), dc = distCode(dist);
    return (litLen[257 + lc] || 12) + LEN_EXTRA[lc] + (distLen[dc] || 12) + DIST_EXTRA[dc];
  };
  let lazyLen = null, lazyDist = null;
  if (lazyOps) {
    lazyLen = new Int32Array(n);
    lazyDist = new Int32Array(n);
    let p = 0;
    for (let i = 0; i < lazyOps.type.length; i++) {
      if (lazyOps.type[i] === 1) { lazyLen[p] = lazyOps.a[i]; lazyDist[p] = lazyOps.b[i]; p += lazyOps.a[i]; }
      else p += 1;
    }
  }
  const MASK = 32767;
  const head = new Int32Array(32768).fill(-1);
  const prev = new Int32Array(32768).fill(-1);
  const hashAt = (p) => (((data[p] << 10) ^ (data[p + 1] << 5) ^ data[p + 2]) & MASK);
  const cost = new Float64Array(n + 1).fill(Infinity);
  const backLen = new Int32Array(n + 1);
  const backDist = new Int32Array(n + 1);
  cost[0] = 0;
  if (n >= 3) {
    const h = hashAt(0);
    prev[0] = head[h]; head[h] = 0;
  }
  const BANDS = [16, 256, 1024, 4096, 32768];
  for (let i = 0; i < n; i++) {
    const ci = cost[i];
    if (ci === Infinity) continue;
    const lc0 = ci + litBits[data[i]];
    if (lc0 < cost[i + 1]) { cost[i + 1] = lc0; backLen[i + 1] = 0; }
    if (i + 2 >= n) continue;
    const h = hashAt(i);
    let cand = head[h];
    let chain = maxChain;
    let bestLen = 0, bestDist = 0;
    const bandLen = [0, 0, 0, 0, 0];
    const bandDist = [0, 0, 0, 0, 0];
    const maxLen = Math.min(258, n - i);
    while (cand >= 0 && chain-- > 0) {
      const dist = i - cand;
      if (dist <= 0) { cand = prev[cand & 32767]; continue; }
      if (dist > 32768) break;
      let need = data[cand + bestLen] === data[i + bestLen];
      if (!need) {
        for (let k = 0; k < BANDS.length; k++) {
          if (dist <= BANDS[k] && data[cand + bandLen[k]] === data[i + bandLen[k]]) { need = true; break; }
        }
      }
      if (need) {
        let len = 0;
        while (len < maxLen && data[cand + len] === data[i + len]) len++;
        if (len > bestLen) { bestLen = len; bestDist = dist; if (len >= maxLen) break; }
        for (let k = 0; k < BANDS.length; k++) {
          if (dist <= BANDS[k] && len > bandLen[k]) { bandLen[k] = len; bandDist[k] = dist; }
        }
      }
      cand = prev[cand & 32767];
    }
    const addCand = (L, D) => {
      if (L < 3) return;
      const lo = Math.max(3, L - trim);
      for (let len = L; len >= lo; len--) {
        const c = ci + matchBits(len, D);
        if (c < cost[i + len]) { cost[i + len] = c; backLen[i + len] = len; backDist[i + len] = D; }
      }
    };
    addCand(bestLen, bestDist);
    for (let k = 0; k < BANDS.length; k++) {
      if (bandDist[k] !== 0 && bandDist[k] !== bestDist) addCand(bandLen[k], bandDist[k]);
    }
    if (lazyLen !== null && lazyLen[i] >= 3) addCand(lazyLen[i], lazyDist[i]);
    if (i + 3 < n) {
      const hh = hashAt(i + 1);
      prev[(i + 1) & 32767] = head[hh];
      head[hh] = i + 1;
    }
  }
  const type = [], a = [], b = [];
  let p = n;
  while (p > 0) {
    const L = backLen[p];
    if (L === 0) { type.push(0); a.push(data[p - 1]); b.push(0); p--; }
    else { type.push(1); a.push(L); b.push(backDist[p]); p -= L; }
  }
  type.reverse(); a.reverse(); b.reverse();
  return { type: Uint8Array.from(type), a: Uint16Array.from(a), b: Uint16Array.from(b) };
}

// ---------------------------------------------------------------------------
// Per-row filter re-selection with this program's own deflate cost model.
// ---------------------------------------------------------------------------

// Lazy-parse bit cost of data[start..end) given the hash state for positions
// below `start`. Inserts positions as it advances (mutates head/prev), so
// pass copies for trials.
function parseCost(data, start, end, head, prev, litLen, distLen, maxChain) {
  const MASK = 32767;
  const hashAt = (p) => (((data[p] << 10) ^ (data[p + 1] << 5) ^ data[p + 2]) & MASK);
  const litBits = (b) => litLen[b] || 12;
  const matchBits = (len, dist) => {
    const lc = lenCode(len), dc = distCode(dist);
    return (litLen[257 + lc] || 12) + LEN_EXTRA[lc] + (distLen[dc] || 12) + DIST_EXTRA[dc];
  };
  let nextInsert = start;
  const insertUpTo = (p) => {
    while (nextInsert <= p && nextInsert + 2 < end) {
      const h = hashAt(nextInsert);
      prev[nextInsert & 32767] = head[h];
      head[h] = nextInsert;
      nextInsert++;
    }
  };
  const longest = (q) => {
    let bestLen = 0, bestDist = 0;
    const h = hashAt(q);
    let cand = head[h];
    let chain = maxChain;
    const maxLen = Math.min(258, end - q);
    if (maxLen < 3) return null;
    while (cand >= 0 && chain-- > 0) {
      const dist = q - cand;
      if (dist <= 0) { cand = prev[cand & 32767]; continue; }
      if (dist > 32768) break;
      if (data[cand + bestLen] === data[q + bestLen]) {
        let len = 0;
        while (len < maxLen && data[cand + len] === data[q + len]) len++;
        if (len > bestLen) {
          bestLen = len; bestDist = dist;
          if (len >= maxLen) break;
          if (len >= 32) chain = Math.min(chain, maxChain >> 2);
        }
      }
      cand = prev[cand & 32767];
    }
    return bestLen >= 3 ? { len: bestLen, dist: bestDist } : null;
  };
  let cost = 0;
  let p = start;
  while (p < end) {
    insertUpTo(p);
    if (p + 2 >= end) { cost += litBits(data[p]); p++; continue; }
    const m1 = longest(p);
    if (m1) {
      let useIt = true;
      if (m1.len < 258 && p + 3 < end) {
        const m2 = longest(p + 1);
        if (m2 && m2.len > m1.len) useIt = false;
      }
      if (useIt) { cost += matchBits(m1.len, m1.dist); p += m1.len; continue; }
    }
    cost += litBits(data[p]);
    p++;
  }
  return cost;
}

// Re-select every row's filter by the deflate cost model, committing rows in
// order so later rows see earlier ones as dictionary context.
function reselectFilters(samples, width, height, bpp, litLen, distLen) {
  const stride = width * bpp;
  const out = new Uint8Array(height * (stride + 1));
  const head = new Int32Array(32768).fill(-1);
  const prev = new Int32Array(32768).fill(-1);
  const headCopy = new Int32Array(32768);
  const prevCopy = new Int32Array(32768);
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prevRow = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    let bestT = 0, bestCost = Infinity;
    for (let t = 0; t < 5; t++) {
      out[at] = t;
      filterRow(t, cur, prevRow, bpp, out.subarray(at + 1, at + 1 + stride));
      headCopy.set(head);
      prevCopy.set(prev);
      const c = parseCost(out, at, at + 1 + stride, headCopy, prevCopy, litLen, distLen, 32);
      if (c < bestCost) { bestCost = c; bestT = t; }
    }
    out[at] = bestT;
    filterRow(bestT, cur, prevRow, bpp, out.subarray(at + 1, at + 1 + stride));
    parseCost(out, at, at + 1 + stride, head, prev, litLen, distLen, 32);
  }
  return out;
}

// ---------------------------------------------------------------------------
// Driver: one program answers every instance of the set.
// ---------------------------------------------------------------------------

const BLOCK_SIZES = [Infinity, 262144, 65536];

// The smallest zlib stream for parsed `ops` over the tried block sizes.
function deflateBest(ops, data) {
  let best = null;
  for (const bs of BLOCK_SIZES) {
    const z = deflateFromOps(ops, data, bs);
    if (best === null || z.length < best.length) best = z;
  }
  return best;
}

function compressInstance(rgba, width, height, id) {
  const win = screenImage(rgba, width, height);
  // Lazy parse of the screened data: its stream, and the cost tables the
  // filter re-selection and the DP parse are weighed with.
  const lazyOps0 = lzParse(win.data, 4096);
  const f0 = opFreqs(lazyOps0);
  const litLen0 = packageMerge(f0.litFreq, 15);
  const distLen0 = packageMerge(f0.distFreq, 15);
  let bestStream = deflateBest(lazyOps0, win.data);
  const l0 = bestStream;
  // Re-select every row's filter with this program's own deflate cost model.
  const reselected = reselectFilters(win.form.samples, width, height, win.form.bpp, litLen0, distLen0);
  const lazyOps1 = lzParse(reselected, 4096);
  const l1 = deflateBest(lazyOps1, reselected);
  if (l1.length < bestStream.length) bestStream = l1;
  // One bounded DP optimal parse. The re-selection is kept only when the lazy
  // stream on it is not far worse than on the screened data: its cost model
  // can misjudge rows whose best matches only a long-chain parse finds, and
  // then the DP runs on the screened data instead.
  let dpData = reselected, dpLazy = lazyOps1, dpLit, dpDist;
  if (l1.length * 10 > l0.length * 11) {
    dpData = win.data; dpLazy = lazyOps0; dpLit = litLen0; dpDist = distLen0;
  } else {
    const f1 = opFreqs(lazyOps1);
    dpLit = packageMerge(f1.litFreq, 15);
    dpDist = packageMerge(f1.distFreq, 15);
  }
  const dpOps = dpParse(dpData, dpLit, dpDist, dpLazy, 32, 8);
  const d1 = deflateBest(dpOps, dpData);
  if (d1.length < bestStream.length) bestStream = d1;
  return pngOfForm(width, height, win.form, bestStream);
}

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

for (const id of readdirSync(INPUT_DIR).sort()) {
  const image = decodePng(new Uint8Array(readFileSync(join(INPUT_DIR, id, 'image.png'))));
  const png = compressInstance(image.rgba, image.width, image.height, id);
  mkdirSync(join(OUTPUT_DIR, id), { recursive: true });
  writeFileSync(join(OUTPUT_DIR, id, 'image.png'), png);
}

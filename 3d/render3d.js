/* =========================================================================
   ABSHERON RISING — the Three.js renderer.

   This replaces the PixiJS renderer wholesale and nothing else: the economy,
   the utilities, the history layer, the interface and the save format are the
   2D game's, untouched. They live in the page's classic script; this module
   reads them as globals (G, DEFS, tile(), hash2() ...) and publishes the
   functions the classic script calls (render, unproj, syncBuildings ...) onto
   window before the game starts.

   World space: x = tile x, z = tile y, y is up, one tile is one unit. A model
   baked in Blender lands correctly with no rotation, because Blender's -y is
   this world's +z (the glTF exporter does that swap).
   ========================================================================= */
import * as THREE from 'three';
import { GLTFLoader } from 'three/addons/loaders/GLTFLoader.js';
import { mergeGeometries } from 'three/addons/utils/BufferGeometryUtils.js';
import { RoomEnvironment } from 'three/addons/environments/RoomEnvironment.js';
import { buildMaterial, NIGHT } from './matlib.js';

const TAU = Math.PI * 2;
const FOV = 32 * Math.PI / 180;
const D0 = 21;                       /* camera distance at zoom 1, in tiles */
const LIB = '3d/models/lib/';
const Y_AXIS = new THREE.Vector3(0, 1, 0);

let renderer, scene, camera, sun, hemi, envTex;
let matData = null;
const MODELS = new Map();            /* name -> {parts:[{geo,mat}], h, minY} */
const grp = {};

/* ======================================================================
   HEIGHTFIELD — the peninsula is not a table. Land rises from a sloping
   beach, the ridge is a hill, dunes roll, and the sea floor falls away. Each
   built tile gets a levelled pad (the average of the ground under it), so a
   street or a house sits flat on a slope instead of cutting into it.
   `hAt(x, z)` is the ground height anywhere; everything that stands on the
   map asks it.
   ====================================================================== */
const WATER_Y = -0.20;
let VX = 0, VZ = 0, H0 = null, HV = null, terrGeo = null, padKey = '', padVer = 0;
function vn(x, z, s) {
  const xi = Math.floor(x), zi = Math.floor(z), fx = x - xi, fz = z - zi;
  const a = hash2(xi, zi, s), b = hash2(xi + 1, zi, s), c = hash2(xi, zi + 1, s), d = hash2(xi + 1, zi + 1, s);
  const u = fx * fx * (3 - 2 * fx), v = fz * fz * (3 - 2 * fz);
  return a + (b - a) * u + (c - a) * v + (a - b - c + d) * u * v;
}
const fbm2 = (x, z, s) => vn(x, z, s) * 0.55 + vn(x * 2.1, z * 2.1, s + 1) * 0.3 + vn(x * 4.3, z * 4.3, s + 2) * 0.15;
const sstep = (a, b, x) => { const t = clamp((x - a) / (b - a), 0, 1); return t * t * (3 - 2 * t) };
function hAt(x, z) {
  if (!HV) return 0;
  x = clamp(x, 0, GW - 0.0001); z = clamp(z, 0, GH - 0.0001);
  const xi = x | 0, zi = z | 0, fx = x - xi, fz = z - zi, i = zi * VX + xi;
  return HV[i] * (1 - fx) * (1 - fz) + HV[i + 1] * fx * (1 - fz) + HV[i + VX] * (1 - fx) * fz + HV[i + VX + 1] * fx * fz;
}
window.heightAt = hAt;
function bfsDist(sources, passable) {
  const d = new Int16Array(NC).fill(-1), q = [];
  for (let i = 0; i < NC; i++) if (sources(i)) { d[i] = 0; q.push(i) }
  for (let h = 0; h < q.length; h++) {
    const i = q[h], x = i % GW, y = (i / GW) | 0, k = d[i];
    if (k >= 18) continue;
    for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
      const nx = x + dx, ny = y + dy; if (nx < 0 || ny < 0 || nx >= GW || ny >= GH) continue;
      const j = ny * GW + nx; if (d[j] < 0) { d[j] = k + 1; q.push(j) }
    }
  }
  return d;
}
function boxBlur(a, r) {
  const t = new Float32Array(NC), o = new Float32Array(NC), n = 2 * r + 1;
  for (let y = 0; y < GH; y++) {
    let s = 0; for (let x = -r; x <= r; x++) s += a[y * GW + clamp(x, 0, GW - 1)];
    for (let x = 0; x < GW; x++) { t[y * GW + x] = s / n; s += a[y * GW + clamp(x + r + 1, 0, GW - 1)] - a[y * GW + clamp(x - r, 0, GW - 1)] }
  }
  for (let x = 0; x < GW; x++) {
    let s = 0; for (let y = -r; y <= r; y++) s += t[clamp(y, 0, GH - 1) * GW + x];
    for (let y = 0; y < GH; y++) { o[y * GW + x] = s / n; s += t[clamp(y + r + 1, 0, GH - 1) * GW + x] - t[clamp(y - r, 0, GH - 1) * GW + x] }
  }
  return o;
}
let tileCol = null;
function buildHeights() {
  VX = GW + 1; VZ = GH + 1;
  const water = i => isWater(G.tiles[i].t);
  const dLand = bfsDist(i => water(i)), dSea = bfsDist(i => !water(i));
  const sd = new Float32Array(NC);
  for (let i = 0; i < NC; i++) sd[i] = water(i) ? -Math.max(1, dSea[i] < 0 ? 18 : dSea[i]) : Math.max(1, dLand[i] < 0 ? 18 : dLand[i]);
  const R = new Float32Array(NC), D = new Float32Array(NC);
  for (let i = 0; i < NC; i++) { const t = G.tiles[i].t; R[i] = t === T_RIDGE ? 1 : t === T_ROCK ? 1.3 : 0; D[i] = t === T_DUNE ? 1 : 0 }
  const Rb = boxBlur(boxBlur(R, 3), 2), Db = boxBlur(D, 2);
  /* what colour each tile is: land by its terrain, sea floor by how deep it is */
  tileCol = new Float32Array(NC * 3);
  for (let i = 0; i < NC; i++) {
    const t = G.tiles[i], x = i % GW, y = (i / GW) | 0;
    let hex;
    if (GROUND[t.t] != null) hex = GROUND[t.t];
    else { const d = clamp(-sd[i], 1, 9); hex = d < 2.5 ? 0xd2c598 : d < 4.5 ? 0x9aa88a : 0x4a6a70 }
    const j = 0.92 + 0.12 * hash2(x, y, 9) + (t.t === T_PLAIN ? 0.04 * (t.v - 0.5) : 0);
    _c.setHex(hex).multiplyScalar(j);
    tileCol[i * 3] = _c.r; tileCol[i * 3 + 1] = _c.g; tileCol[i * 3 + 2] = _c.b;
  }
  H0 = new Float32Array(VX * VZ);
  const vcol = new Float32Array(VX * VZ * 3);
  for (let vz = 0; vz < VZ; vz++) for (let vx = 0; vx < VX; vx++) {
    let ssd = 0, rr = 0, dd = 0, cr = 0, cg = 0, cb = 0;
    for (let k = 0; k < 4; k++) {
      const tx = clamp(vx - 1 + (k & 1), 0, GW - 1), tz = clamp(vz - 1 + (k >> 1), 0, GH - 1), i = tz * GW + tx;
      ssd += sd[i]; rr += Rb[i]; dd += Db[i]; cr += tileCol[i * 3]; cg += tileCol[i * 3 + 1]; cb += tileCol[i * 3 + 2];
    }
    ssd *= 0.25; rr *= 0.25; dd *= 0.25;
    let h;
    if (ssd >= 0) {
      const lw = sstep(0.5, 2.8, ssd);
      /* relief only ever adds to the coast, so low inland ground can never dip under the sea */
      h = -0.15 * (1 - sstep(0, 2.2, ssd));
      h += lw * 0.62 * fbm2(vx * 0.035, vz * 0.035, 3);
      h += lw * 0.07 * vn(vx * 0.45, vz * 0.45, 8);
      h += lw * 2.7 * Math.pow(clamp(rr, 0, 1), 1.35) * (0.75 + 0.5 * fbm2(vx * 0.09, vz * 0.09, 12));
      h += lw * dd * 0.42 * fbm2(vx * 0.16, vz * 0.16, 15);
    } else h = WATER_Y - Math.min(1.6, 0.30 * Math.pow(-ssd, 0.85));
    H0[vz * VX + vx] = h;
    vcol[(vz * VX + vx) * 3] = cr * 0.25; vcol[(vz * VX + vx) * 3 + 1] = cg * 0.25; vcol[(vz * VX + vx) * 3 + 2] = cb * 0.25;
  }
  HV = new Float32Array(H0);
  /* the grid; cells that are deep sea in every corner are never seen */
  const pos = new Float32Array(VX * VZ * 3), idx = [];
  for (let vz = 0; vz < VZ; vz++) for (let vx = 0; vx < VX; vx++) {
    const v = vz * VX + vx; pos[v * 3] = vx; pos[v * 3 + 1] = HV[v]; pos[v * 3 + 2] = vz;
  }
  for (let z = 0; z < GH; z++) for (let x = 0; x < GW; x++) {
    const a = z * VX + x, b = a + 1, c = a + VX, d = c + 1;
    if (H0[a] < -1.45 && H0[b] < -1.45 && H0[c] < -1.45 && H0[d] < -1.45) continue;
    idx.push(a, c, d, a, d, b);
  }
  const g = new THREE.BufferGeometry();
  g.setAttribute('position', new THREE.BufferAttribute(pos, 3));
  g.setAttribute('color', new THREE.BufferAttribute(vcol, 3));
  g.setIndex(idx); g.computeVertexNormals();
  if (terrGeo) terrGeo.dispose();
  terrGeo = g; padKey = '';
  updateDrapeTex();
  return g;
}
/* Flatten the ground under what is built. Returns true if anything moved. */
function applyPads() {
  if (!HV || !terrGeo) return false;
  let key = 0, n = 0;
  const built = new Uint8Array(NC);
  for (const b of G.blds) {
    if (!b) continue; const d = DEFS[b.key], sl = slotOf(d);
    if (sl !== 'b' && sl !== 'r') continue;
    if (d.bridge) continue;                       /* a deck over water must not raise the sea floor */
    if (d.grow) continue;                         /* a wood follows the land */
    for (let y = b.y; y < b.y + b.h; y++) for (let x = b.x; x < b.x + b.w; x++) { if (x >= 0 && y >= 0 && x < GW && y < GH) { built[y * GW + x] = 1 } }
    key = (key * 31 + b.x * 131 + b.y * 17 + b.w) | 0; n++;
  }
  const k = n + ':' + key;
  if (k === padKey) return false;
  padKey = k;
  HV.set(H0);
  const acc = new Float32Array(VX * VZ), cnt = new Uint8Array(VX * VZ);
  for (let i = 0; i < NC; i++) {
    if (!built[i]) continue;
    const x = i % GW, z = (i / GW) | 0, a = z * VX + x;
    const gh = (H0[a] + H0[a + 1] + H0[a + VX] + H0[a + VX + 1]) * 0.25;
    for (const v of [a, a + 1, a + VX, a + VX + 1]) { acc[v] += gh; cnt[v]++ }
  }
  for (let v = 0; v < VX * VZ; v++) if (cnt[v]) HV[v] = acc[v] / cnt[v];
  const pa = terrGeo.attributes.position.array;
  for (let v = 0; v < VX * VZ; v++) pa[v * 3 + 1] = HV[v];
  terrGeo.attributes.position.needsUpdate = true;
  terrGeo.computeVertexNormals();
  padVer++; syncOverlayHeights(); updateDrapeTex();
  return true;
}
/* The top of a pad: flat pieces sit here so no corner of the ground pokes through them. */
function padTop(x, y, w, h) {
  let m = -9;
  for (let vz = y; vz <= y + h; vz++) for (let vx = x; vx <= x + w; vx++) { const v = HV[clamp(vz, 0, GH) * VX + clamp(vx, 0, GW)]; if (v > m) m = v }
  return m + 0.012;
}
/* Flat pieces (streets, mains, cables, rails, plots) are draped: the vertex shader
   puts every vertex on the real ground, so a road follows a slope instead of
   being a row of level slabs. The height grid goes up as a half-float texture. */
const DRAPE = { tex: { value: null }, grid: { value: new THREE.Vector2(1, 1) } };
const DRAPE_RE = /^(road_|dirt_|stone_|prom_|aven_|pipe_|cable_|mtun_|tram_|lot_|cons_pad|rw_|tw_|arw_|hwy_|pk_|cpk_|ff_|pth_)/;
function updateDrapeTex() {
  if (!HV) return;
  const n = VX * VZ;
  if (!DRAPE.tex.value || DRAPE.tex.value.image.width !== VX || DRAPE.tex.value.image.height !== VZ) {
    const t = new THREE.DataTexture(new Uint16Array(n), VX, VZ, THREE.RedFormat, THREE.HalfFloatType);
    t.magFilter = t.minFilter = THREE.LinearFilter; t.wrapS = t.wrapT = THREE.ClampToEdgeWrapping; t.generateMipmaps = false;
    DRAPE.tex.value = t; DRAPE.grid.value.set(VX, VZ);
  }
  const d = DRAPE.tex.value.image.data;
  for (let v = 0; v < n; v++) d[v] = THREE.DataUtils.toHalfFloat(HV[v]);
  DRAPE.tex.value.needsUpdate = true;
}
const drapeCache = new Map();
function drapeMaterial(base) {
  let m = drapeCache.get(base);
  if (m) return m;
  m = base.clone();
  const orig = base.onBeforeCompile, key = (base.customProgramCacheKey ? base.customProgramCacheKey() : '') + '|drape';
  m.customProgramCacheKey = () => key;
  m.onBeforeCompile = sh => {
    if (orig) orig.call(m, sh);
    sh.uniforms.uHT = DRAPE.tex; sh.uniforms.uHG = DRAPE.grid;
    sh.vertexShader = sh.vertexShader
      .replace('#include <common>', '#include <common>\nuniform sampler2D uHT; uniform vec2 uHG;')
      .replace('#include <project_vertex>', `
        vec4 mvPosition = vec4( transformed, 1.0 );
        #ifdef USE_INSTANCING
          vec4 wpD = instanceMatrix * mvPosition;
          float hD = texture2D(uHT, (wpD.xz + 0.5) / uHG).r;
          float bD = texture2D(uHT, (instanceMatrix[3].xz + 0.5) / uHG).r;
          wpD.y += hD - bD;
          mvPosition = wpD;
        #endif
        mvPosition = modelViewMatrix * mvPosition;
        gl_Position = projectionMatrix * mvPosition;`);
  };
  drapeCache.set(base, m);
  return m;
}
window.applyPads = applyPads;

/* ======================================================================
   CAMERA — an orbit round a point on the ground. `cam.z` is still a zoom
   factor so the interface code that sets it keeps working.
   ====================================================================== */
const camDist = cm => D0 / (cm || cam).z;

function updateCamera() {
  const D = camDist(), cp = Math.cos(cam.pitch), sp = Math.sin(cam.pitch);
  const gh = hAt(cam.tx, cam.ty);
  camera.position.set(cam.tx + D * cp * Math.sin(cam.yaw), gh + D * sp, cam.ty + D * cp * Math.cos(cam.yaw));
  camera.lookAt(cam.tx, gh, cam.ty);
  camera.aspect = VW / VH;
  camera.near = Math.max(0.25, D * 0.04);
  camera.far = D * 14 + 300;
  camera.updateProjectionMatrix();
  camera.updateMatrixWorld();
}

/* The ground point under a screen pixel, for any camera state — pan and zoom
   both need to ask "where WOULD that pixel land" about a camera they are not
   currently using. Rays that miss the ground land on the horizon. */
function groundAt(cm, sx, sy) {
  const D = D0 / cm.z, cp = Math.cos(cm.pitch), sp = Math.sin(cm.pitch);
  const gh0 = hAt(cm.tx, cm.ty);
  const px_ = cm.tx + D * cp * Math.sin(cm.yaw), py_ = gh0 + D * sp, pz_ = cm.ty + D * cp * Math.cos(cm.yaw);
  const fx = -cp * Math.sin(cm.yaw), fy = -sp, fz = -cp * Math.cos(cm.yaw);
  let rx = -fz, rz = fx; const rl = Math.hypot(rx, rz) || 1; rx /= rl; rz /= rl;
  const ux = -rz * fy, uy = rz * fx - rx * fz, uz = rx * fy;
  const th = Math.tan(FOV / 2), asp = VW / VH;
  const nx = (sx / VW * 2 - 1) * th * asp, ny = (1 - sy / VH * 2) * th;
  const dx = fx + rx * nx + ux * ny, dy = fy + uy * ny, dz = fz + rz * nx + uz * ny;
  if (dy < -0.015) {
    /* the plane through the target first, then settle onto the real ground */
    let t = (gh0 - py_) / dy, X = px_ + dx * t, Z = pz_ + dz * t;
    for (let k = 0; k < 4; k++) { t = (hAt(X, Z) - py_) / dy; X = px_ + dx * t; Z = pz_ + dz * t }
    return [X, Z];
  }
  const hl = Math.hypot(dx, dz) || 1;                      /* above the horizon */
  return [px_ + dx / hl * 260, pz_ + dz / hl * 260];
}
window.unproj = (sx, sy) => groundAt(cam, sx, sy);
window.centerOn = (x, y) => { cam.tx = x; cam.ty = y };
window.clampCam = () => {
  cam.tx = clamp(cam.tx, 0, GW); cam.ty = clamp(cam.ty, 0, GH);
  cam.pitch = clamp(cam.pitch, 0.30, 1.30);
};
window.syncSize = () => {
  const r = stageEl.getBoundingClientRect();
  VW = Math.max(1, Math.round(r.width)); VH = Math.max(1, Math.round(r.height));
  if (renderer) renderer.setSize(VW, VH, false);
};
window.camSnapshot = () => ({ tx: cam.tx, ty: cam.ty, yaw: cam.yaw, pitch: cam.pitch, z: cam.z });
window.groundAt = groundAt;
window.camDist = camDist;
window.screenOf = (x, y, z) => {
  const v = new THREE.Vector3(x, (z || 0) + hAt(x, y), y).project(camera);
  return [(v.x * 0.5 + 0.5) * VW, (-v.y * 0.5 + 0.5) * VH, v.z];
};
window.rotateView = dir => {
  cam.tyaw = (cam.tyaw == null ? cam.yaw : cam.tyaw) + dir * Math.PI / 2;
  const d = ((Math.round(cam.tyaw / (Math.PI / 2)) % 4) + 4) % 4;
  note(["Cənub-şərqdən", "Cənub-qərbdən", "Şimal-qərbdən", "Şimal-şərqdən"][d] + " baxış.");
};

/* ======================================================================
   MODELS — the whole library is one glTF. Each model's meshes are merged by
   material, so a model costs one draw call per material and the instancing
   below never sees more than a handful of parts per building.
   ====================================================================== */
const bootSay = (label, f) => { if (window.__boot) window.__boot(label, f) };
/* fetch a JSON file and say how far along it is (the loading bar), falling back to a plain read */
async function fetchJSONProgress(url, onFrac) {
  const r = await fetch(url, { cache: 'no-cache' });
  const total = +r.headers.get('content-length') || 0;
  if (!r.body || !total) { const j = await r.json(); onFrac(1); return j }
  const reader = r.body.getReader(), chunks = []; let got = 0;
  for (;;) { const { done, value } = await reader.read(); if (done) break; chunks.push(value); got += value.length; onFrac(Math.min(1, got / total)) }
  const buf = new Uint8Array(got); let o = 0; for (const c of chunks) { buf.set(c, o); o += c.length }
  return JSON.parse(new TextDecoder().decode(buf));
}
async function loadLibrary() {
  const loader = new GLTFLoader();
  /* the model library ships as base64 in a .json: the artifact host serves no .glb */
  bootSay('Modellər yüklənir…', 0.24);
  const [gltf, mats] = await Promise.all([
    fetchJSONProgress(LIB + 'library.json', f => bootSay('Modellər yüklənir… ' + Math.round(f * 100) + '%', 0.24 + 0.50 * f))
      .then(j => { bootSay('Modellər açılır…', 0.76); return fetch('data:application/octet-stream;base64,' + j.glb) }).then(r => r.arrayBuffer())
      .then(buf => new Promise((res, rej) => loader.parse(buf, '', res, rej))),
    fetch(LIB + 'materials.json', { cache: 'no-cache' }).then(r => r.json()),
  ]);
  bootSay('Materiallar qurulur…', 0.86);
  matData = mats;
  gltf.scene.updateMatrixWorld(true);
  for (const root of gltf.scene.children) {
    const byMat = new Map();
    let minY = 1e9, maxY = -1e9, minX = 1e9, maxX = -1e9, minZ = 1e9, maxZ = -1e9;
    root.traverse(o => {
      if (!o.isMesh) return;
      const g = o.geometry.clone();
      g.applyMatrix4(o.matrixWorld);
      for (const a of ['uv', 'uv1', 'color', 'tangent']) if (g.getAttribute(a)) g.deleteAttribute(a);
      if (!g.index) { const n = g.getAttribute('position').count, ix = new Uint32Array(n); for (let i = 0; i < n; i++) ix[i] = i; g.setIndex(new THREE.BufferAttribute(ix, 1)) }
      g.computeBoundingBox();
      const bb = g.boundingBox;
      minY = Math.min(minY, bb.min.y); maxY = Math.max(maxY, bb.max.y);
      minX = Math.min(minX, bb.min.x); maxX = Math.max(maxX, bb.max.x);
      minZ = Math.min(minZ, bb.min.z); maxZ = Math.max(maxZ, bb.max.z);
      const m = o.material.name;
      if (!byMat.has(m)) byMat.set(m, []);
      byMat.get(m).push(g);
    });
    const parts = [];
    for (const [m, arr] of byMat) {
      const geo = arr.length > 1 ? mergeGeometries(arr, false) : arr[0];
      parts.push({ geo, mat: m });
    }
    MODELS.set(root.name, { parts, h: Math.max(0.05, maxY), minY, box: [minX, maxX, minZ, maxZ], drape: DRAPE_RE.test(root.name), name: root.name });
  }
  procModels();
}
const FLAT = /^(road_|dirt_|stone_|prom_|aven_|pipe_|cable_|mtun_|tram_|lot_|cons_|rw_|tw_|arw_|hwy_|pk_|cpk_|ff_|pth_|v_ped|deco_scrub)/;

/* ======================================================================
   PROCEDURAL MODELS — small things the Blender library does not hold are built
   here from boxes, then go through exactly the same instancing, materials and
   thumbnails as everything else.
   ====================================================================== */
const PROC_MATS = {
  proc_dark:  { kind: 'rough', col: [0.035, 0.04, 0.045], rough: 0.5, metallic: 0.55, noise: 3, vary: 0.10 },
  proc_blue:  { kind: 'rough', col: [0.015, 0.10, 0.30], rough: 0.45, metallic: 0.2, noise: 2, vary: 0.05 },
  proc_glass: { kind: 'rough', col: [0.40, 0.58, 0.68], rough: 0.12, metallic: 0.1, noise: 1, vary: 0.04 },
  proc_stone: { kind: 'rough', col: [0.40, 0.38, 0.34], rough: 0.92, metallic: 0, noise: 6, vary: 0.25 },
  proc_white: { kind: 'rough', col: [0.80, 0.81, 0.80], rough: 0.4, metallic: 0.15, noise: 2, vary: 0.04 },
  proc_red:   { kind: 'rough', col: [0.45, 0.04, 0.03], rough: 0.5, metallic: 0.1, noise: 2, vary: 0.05 },
  proc_grey:  { kind: 'rough', col: [0.30, 0.31, 0.32], rough: 0.7, metallic: 0.25, noise: 3, vary: 0.12 },
  proc_asphalt:{ kind: 'rough', col: [0.045, 0.047, 0.052], rough: 0.92, metallic: 0, noise: 9, vary: 0.22 },
  proc_apron: { kind: 'rough', col: [0.16, 0.165, 0.17], rough: 0.88, metallic: 0, noise: 7, vary: 0.18 },
  proc_yel:   { kind: 'rough', col: [0.72, 0.50, 0.03], rough: 0.6, metallic: 0, noise: 2, vary: 0.04 },
  proc_path:  { kind: 'rough', col: [0.78, 0.72, 0.60], rough: 0.92, metallic: 0, noise: 9, vary: 0.16 },
  proc_lawn:  { kind: 'rough', col: [0.30, 0.47, 0.22], rough: 0.95, metallic: 0, noise: 9, vary: 0.2 },
  proc_wood:  { kind: 'rough', col: [0.13, 0.27, 0.14], rough: 0.95, metallic: 0, noise: 9, vary: 0.2 },
  proc_lot:   { kind: 'rough', col: [0.17, 0.175, 0.18], rough: 0.9, metallic: 0, noise: 9, vary: 0.15 },
};
function procModel(name, boxes) {
  const by = new Map(); let minX = 1e9, maxX = -1e9, minZ = 1e9, maxZ = -1e9, maxY = 0;
  for (const [m, w, h, d, x, y, z, ry] of boxes) {
    const g = new THREE.BoxGeometry(w, h, d); g.deleteAttribute('uv');
    if (ry) g.rotateY(ry);
    g.translate(x, y + h / 2, z);
    g.computeBoundingBox(); const bb = g.boundingBox;
    minX = Math.min(minX, bb.min.x); maxX = Math.max(maxX, bb.max.x); minZ = Math.min(minZ, bb.min.z); maxZ = Math.max(maxZ, bb.max.z); maxY = Math.max(maxY, bb.max.y);
    if (!by.has(m)) by.set(m, []); by.get(m).push(g);
  }
  const parts = [...by].map(([m, arr]) => ({ geo: arr.length > 1 ? mergeGeometries(arr, false) : arr[0], mat: m }));
  MODELS.set(name, { parts, h: Math.max(0.05, maxY), minY: 0, box: [minX, maxX, minZ, maxZ], drape: DRAPE_RE.test(name), name });
}
const BRIDGE_Y = 0.17;
/* A bridge is the street piece for its connections, raised off the water on a
   slab with parapets along the run and a pier under it. Not draped: the deck
   stays level over a sea floor that falls away. */
function bridgeModels() {
  for (let m = 0; m < 16; m++) {
    const base = MODELS.get('road_' + m); if (!base) continue;
    const ns = (m & 5) && !(m & 10), ew = (m & 10) && !(m & 5);
    const boxes = [['proc_stone', 0.98, 0.07, 0.98, 0, -0.07, 0]];
    if (ns) for (const s of [-1, 1]) boxes.push(['proc_stone', 0.05, 0.08, 1.0, s * 0.455, 0, 0]);
    if (ew) for (const s of [-1, 1]) boxes.push(['proc_stone', 1.0, 0.08, 0.05, 0, 0, s * 0.455]);
    boxes.push(['proc_stone', ns ? 0.6 : ew ? 0.14 : 0.3, 1.0, ew ? 0.6 : ns ? 0.14 : 0.3, 0, -1.07, 0]);
    procModel('brg_tmp', boxes);
    const extra = MODELS.get('brg_tmp'); MODELS.delete('brg_tmp');
    MODELS.set('brg_' + m, { parts: base.parts.concat(extra.parts), h: base.h + 0.1, minY: -1.07, box: base.box, drape: false, name: 'brg_' + m });
  }
}
/* the highway is the avenue with a concrete median down the run */
function highwayModels() {
  for (let m = 0; m < 16; m++) {
    const base = MODELS.get('aven_' + m); if (!base) continue;
    const ns = (m & 5) && !(m & 10), ew = (m & 10) && !(m & 5);
    procModel('hwy_tmp', [['proc_stone', ns ? 0.07 : ew ? 1.0 : 0.16, 0.06, ew ? 0.07 : ns ? 1.0 : 0.16, 0, 0.02, 0]]);
    const extra = MODELS.get('hwy_tmp'); MODELS.delete('hwy_tmp');
    MODELS.set('hwy_' + m, { parts: base.parts.concat(extra.parts), h: base.h + 0.08, minY: base.minY, box: base.box, drape: true, name: 'hwy_' + m });
  }
}
function procModels() {
  Object.assign(matData.materials, PROC_MATS);
  bridgeModels(); highwayModels();
  /* the paved path from a door to the street: a stub from the middle of the tile to every edge in the mask
     (1 north, 2 east, 4 south, 8 west), the same bitmask the streets use */
  for (let m = 1; m < 16; m++) {
    const w = 0.18, b = [['proc_path', w, 0.012, w, 0, 0, 0]];
    if (m & 1) b.push(['proc_path', w, 0.012, 0.5, 0, 0, -0.25]);
    if (m & 2) b.push(['proc_path', 0.5, 0.012, w, 0.25, 0, 0]);
    if (m & 4) b.push(['proc_path', w, 0.012, 0.5, 0, 0, 0.25]);
    if (m & 8) b.push(['proc_path', 0.5, 0.012, w, -0.25, 0, 0]);
    procModel('pth_' + m, b);
  }
  /* a wood in its first months: bare ground, staked saplings in rows */
  { const b = [['proc_wood', 1.0, 0.016, 1.0, 0, 0, 0]];
    for (const gx of [-0.3, 0, 0.3]) for (const gz of [-0.3, 0, 0.3]) {
      const x = gx + (hash2(gx * 10 + 7, gz * 10 + 9, 5) - 0.5) * 0.12, z = gz + (hash2(gx * 10 + 3, gz * 10 + 11, 6) - 0.5) * 0.12;
      b.push(['proc_stone', 0.025, 0.15, 0.025, x, 0.016, z], ['proc_lawn', 0.12, 0.10, 0.12, x, 0.12, z]);
    }
    procModel('ff_young', b); }
  /* what a park, a car park and a wood are from far away: a flat patch of their own colour */
  procModel('pk_lo', [['proc_lawn', 1.0, 0.016, 1.0, 0, 0, 0]]);
  procModel('cpk_lo', [['proc_lot', 1.0, 0.012, 1.0, 0, 0, 0]]);
  procModel('ff_lo', [['proc_wood', 1.0, 0.016, 1.0, 0, 0, 0], ['proc_lawn', 0.34, 0.2, 0.34, -0.22, 0, -0.2], ['proc_wood', 0.34, 0.26, 0.34, 0.2, 0, 0.18], ['proc_lawn', 0.3, 0.18, 0.3, 0.18, 0, -0.26]]);
  /* the arrow painted on a one-way street, pointing north at yaw 0 */
  procModel('arw_1', [
    ['proc_white', 0.06, 0.012, 0.36, 0, 0.012, 0.06],
    ['proc_white', 0.06, 0.012, 0.22, -0.075, 0.012, -0.12, 0.75], ['proc_white', 0.06, 0.012, 0.22, 0.075, 0.012, -0.12, -0.75]]);
  /* the balustrade along the sea edge of the promenade: faces +z, the caller turns it */
  procModel('prom_rail', (() => {
    const b = [['proc_stone', 1.0, 0.05, 0.07, 0, 0, 0.46], ['proc_white', 1.0, 0.022, 0.034, 0, 0.14, 0.46], ['proc_white', 1.0, 0.016, 0.026, 0, 0.075, 0.46]];
    for (const x of [-0.5, -0.25, 0, 0.25, 0.5]) b.push(['proc_white', 0.036, 0.165, 0.04, x, 0.05, 0.46]);
    return b;
  })());
  /* a bus shelter on a paved pad, with its sign */
  procModel('busstop', [
    ['proc_stone', 0.66, 0.02, 0.42, 0, 0, 0],
    ['proc_dark', 0.025, 0.27, 0.025, -0.28, 0.02, -0.16], ['proc_dark', 0.025, 0.27, 0.025, -0.28, 0.02, 0.16],
    ['proc_dark', 0.025, 0.27, 0.025, 0.28, 0.02, -0.16], ['proc_dark', 0.025, 0.27, 0.025, 0.28, 0.02, 0.16],
    ['proc_blue', 0.68, 0.03, 0.44, 0, 0.29, 0],
    ['proc_glass', 0.56, 0.2, 0.012, 0, 0.09, -0.18],
    ['proc_dark', 0.42, 0.022, 0.09, 0, 0.075, -0.1],
    ['proc_dark', 0.014, 0.40, 0.014, 0.38, 0.02, 0.2], ['proc_blue', 0.09, 0.09, 0.014, 0.38, 0.33, 0.2],
  ]);
  /* runway: dark strip, edge lines, a dashed centre line; the end tiles carry the threshold bars */
  const rwBase = rot => {
    const b = [['proc_asphalt', 1.0, 0.012, 1.0, 0, 0, 0]];
    for (const x of [-0.34, 0, 0.34]) b.push(['proc_white', 0.2, 0.003, 0.035, x, 0.012, 0]);
    for (const z of [-0.455, 0.455]) b.push(['proc_white', 1.0, 0.003, 0.018, 0, 0.012, z]);
    return b;
  };
  const rwEnd = sign => { const b = rwBase(); for (let k = -2; k <= 2; k++) b.push(['proc_white', 0.2, 0.003, 0.075, sign * 0.36, 0.012, k * 0.18]); return b };
  const turn = (boxes, swap) => boxes.map(([m, w, h, d, x, y, z]) => swap ? [m, d, h, w, z, y, x] : [m, w, h, d, x, y, z]);
  procModel('rw_x', rwBase()); procModel('rw_x_w', rwEnd(-1)); procModel('rw_x_e', rwEnd(1));
  procModel('rw_z', turn(rwBase(), 1)); procModel('rw_z_n', turn(rwEnd(-1), 1)); procModel('rw_z_s', turn(rwEnd(1), 1));
  /* taxiways: a narrower grey strip with a yellow centre line; junctions are a plain apron with a cross */
  procModel('tw_x', [['proc_apron', 1.0, 0.01, 0.62, 0, 0, 0], ['proc_yel', 1.0, 0.003, 0.03, 0, 0.01, 0]]);
  procModel('tw_z', [['proc_apron', 0.62, 0.01, 1.0, 0, 0, 0], ['proc_yel', 0.03, 0.003, 1.0, 0, 0.01, 0]]);
  procModel('tw_c', [['proc_apron', 1.0, 0.01, 1.0, 0, 0, 0], ['proc_yel', 1.0, 0.003, 0.03, 0, 0.01, 0], ['proc_yel', 0.03, 0.003, 1.0, 0, 0.01, 0]]);
  /* control tower and hangar */
  procModel('atower', [
    ['proc_stone', 0.5, 0.05, 0.5, 0, 0, 0], ['proc_white', 0.17, 0.5, 0.17, 0, 0.05, 0],
    ['proc_glass', 0.36, 0.13, 0.36, 0, 0.55, 0], ['proc_dark', 0.42, 0.03, 0.42, 0, 0.68, 0], ['proc_red', 0.014, 0.22, 0.014, 0, 0.71, 0],
  ]);
  procModel('hangar', [
    ['proc_grey', 1.9, 0.30, 0.8, 0, 0, 0], ['proc_blue', 1.96, 0.045, 0.86, 0, 0.30, 0], ['proc_dark', 0.95, 0.23, 0.012, 0, 0, -0.405],
    ['proc_blue', 1.96, 0.04, 0.5, 0, 0.345, 0],
  ]);

  /* ---- services (T1): drawn from boxes like the aircraft, so they need no bake ---- */
  /* the city hospital: a white slab with glass bands, a taller centre block carrying the red cross, a canopy over the door and a pad on the wing */
  procModel('hospital', (() => {
    const b = [
      ['proc_white', 2.72, 0.34, 1.5, 0, 0, 0], ['proc_white', 1.0, 0.62, 1.34, 0, 0, 0],
      ['proc_glass', 2.74, 0.06, 1.52, 0, 0.1, 0], ['proc_glass', 2.74, 0.06, 1.52, 0, 0.23, 0],
      ['proc_glass', 1.02, 0.06, 1.36, 0, 0.38, 0], ['proc_glass', 1.02, 0.06, 1.36, 0, 0.52, 0],
      ['proc_red', 0.5, 0.02, 0.14, 0, 0.62, 0], ['proc_red', 0.14, 0.02, 0.5, 0, 0.62, 0],
      ['proc_blue', 0.8, 0.04, 0.32, 0, 0.17, 0.84], ['proc_grey', 2.74, 0.02, 1.52, 0, 0.34, 0],
      ['proc_grey', 0.5, 0.012, 0.5, -0.98, 0.36, 0], ['proc_yel', 0.3, 0.014, 0.04, -0.98, 0.372, 0], ['proc_yel', 0.04, 0.014, 0.3, -0.98, 0.372, 0],
    ];
    for (const x of [-0.32, 0.32]) b.push(['proc_white', 0.04, 0.17, 0.04, x, 0, 0.84]);
    return b;
  })());
  /* the university: a stone hall with a portico of columns, a pediment, a blue dome and two glazed wings */
  procModel('univ', (() => {
    const b = [
      ['proc_stone', 2.8, 0.05, 1.8, 0, 0, 0], ['proc_stone', 1.6, 0.44, 1.2, 0, 0.05, 0],
      ['proc_stone', 0.74, 0.32, 1.0, -1.04, 0.05, 0], ['proc_stone', 0.74, 0.32, 1.0, 1.04, 0.05, 0],
      ['proc_glass', 0.76, 0.05, 1.02, -1.04, 0.14, 0], ['proc_glass', 0.76, 0.05, 1.02, 1.04, 0.14, 0], ['proc_glass', 0.76, 0.05, 1.02, -1.04, 0.26, 0], ['proc_glass', 0.76, 0.05, 1.02, 1.04, 0.26, 0],
      ['proc_white', 1.5, 0.04, 0.3, 0, 0.49, 0.64], ['proc_white', 1.0, 0.05, 0.22, 0, 0.53, 0.64],
      ['proc_white', 0.5, 0.2, 0.5, 0, 0.49, -0.05], ['proc_blue', 0.4, 0.13, 0.4, 0, 0.69, -0.05], ['proc_yel', 0.03, 0.12, 0.03, 0, 0.82, -0.05],
    ];
    for (let k = -2; k <= 2; k++) b.push(['proc_white', 0.05, 0.42, 0.05, k * 0.28, 0.05, 0.68]);
    return b;
  })());
  /* the cemetery: lawn, crossing paths, rows of headstones, cypresses and a gate in the low wall */
  procModel('cemetery', (() => {
    const b = [['proc_lawn', 2.9, 0.02, 1.9, 0, 0, 0], ['proc_path', 0.14, 0.024, 1.9, 0, 0, 0], ['proc_path', 2.9, 0.024, 0.14, 0, 0, 0.1],
      ['proc_stone', 1.3, 0.08, 0.05, -0.8, 0.02, 0.93], ['proc_stone', 1.3, 0.08, 0.05, 0.8, 0.02, 0.93],
      ['proc_stone', 0.12, 0.22, 0.12, -0.2, 0.02, 0.93], ['proc_stone', 0.12, 0.22, 0.12, 0.2, 0.02, 0.93]];
    for (const z of [-0.72, -0.44, 0.36, 0.64]) for (let x = -1.2; x <= 1.21; x += 0.3) if (Math.abs(x) > 0.16) b.push(['proc_stone', 0.1, 0.12, 0.03, x, 0.02, z]);
    for (const [x, z] of [[-1.3, -0.82], [1.3, -0.82], [-1.3, 0.78], [1.3, 0.78]]) b.push(['proc_wood', 0.13, 0.5, 0.13, x, 0.02, z]);
    return b;
  })());
  /* the crematorium: a plain grey hall, a white annex and a tall chimney */
  procModel('krem', [
    ['proc_stone', 1.2, 0.34, 1.0, -0.2, 0, 0.1], ['proc_grey', 1.26, 0.03, 1.06, -0.2, 0.34, 0.1], ['proc_white', 0.5, 0.22, 0.8, 0.62, 0, 0.1],
    ['proc_white', 1.22, 0.03, 0.04, -0.2, 0.2, 0.61], ['proc_dark', 0.5, 0.03, 0.54, 0.62, 0.22, 0.1],
    ['proc_dark', 0.28, 0.2, 0.012, -0.2, 0, 0.605], ['proc_dark', 0.14, 0.92, 0.14, -0.5, 0.37, -0.2], ['proc_grey', 0.2, 0.04, 0.2, -0.5, 1.29, -0.2],
    ['proc_glass', 0.4, 0.07, 0.012, 0.62, 0.1, 0.505], ['proc_stone', 1.8, 0.02, 1.8, 0, 0, 0],
  ]);

  /* the neighbourhood mosque: a courtyard, a prayer hall under a blue dome, two slim minarets */
  procModel('mescid', (() => {
    const b = [
      ['proc_stone', 1.9, 0.03, 1.9, 0, 0, 0], ['proc_white', 1.1, 0.36, 1.0, -0.1, 0.03, 0.15],
      ['proc_blue', 0.82, 0.08, 0.76, -0.1, 0.39, 0.15], ['proc_blue', 0.56, 0.1, 0.52, -0.1, 0.47, 0.15], ['proc_blue', 0.28, 0.08, 0.26, -0.1, 0.57, 0.15],
      ['proc_yel', 0.025, 0.14, 0.025, -0.1, 0.65, 0.15], ['proc_glass', 0.5, 0.15, 0.012, -0.1, 0.09, 0.655], ['proc_white', 0.5, 0.05, 0.3, -0.1, 0.03, 0.78],
    ];
    for (const x of [-0.82, 0.62]) b.push(['proc_white', 0.13, 0.82, 0.13, x, 0.03, -0.6], ['proc_white', 0.2, 0.03, 0.2, x, 0.62, -0.6], ['proc_blue', 0.15, 0.1, 0.15, x, 0.85, -0.6], ['proc_yel', 0.02, 0.1, 0.02, x, 0.95, -0.6]);
    return b;
  })());
  /* a street court: painted tarmac, lines, two hoops */
  procModel('court', [
    ['proc_apron', 0.96, 0.02, 0.96, 0, 0, 0], ['proc_blue', 0.8, 0.005, 0.76, 0, 0.02, 0], ['proc_white', 0.8, 0.006, 0.02, 0, 0.025, 0], ['proc_white', 0.02, 0.006, 0.76, 0, 0.025, 0],
    ['proc_dark', 0.025, 0.3, 0.025, -0.44, 0.02, 0], ['proc_dark', 0.025, 0.3, 0.025, 0.44, 0.02, 0], ['proc_white', 0.012, 0.1, 0.14, -0.43, 0.27, 0], ['proc_white', 0.012, 0.1, 0.14, 0.43, 0.27, 0],
  ]);
  /* the stadium: a pitch inside four stands, a floodlight at every corner */
  procModel('stadion', (() => {
    const b = [['proc_stone', 2.9, 0.02, 2.9, 0, 0, 0], ['proc_lawn', 1.7, 0.03, 1.1, 0, 0.02, 0], ['proc_white', 1.7, 0.006, 0.02, 0, 0.05, 0], ['proc_white', 0.02, 0.006, 1.1, 0, 0.05, 0]];
    for (const [w, d, x, z] of [[2.7, 0.55, 0, 1.15], [2.7, 0.55, 0, -1.15], [0.55, 1.75, 1.15, 0], [0.55, 1.75, -1.15, 0]])
      b.push(['proc_grey', w, 0.2, d, x, 0.02, z], ['proc_white', w * 0.92, 0.1, d * 0.8, x, 0.22, z], ['proc_blue', w, 0.03, d, x, 0.32, z]);
    for (const [x, z] of [[-1.32, -1.32], [1.32, -1.32], [-1.32, 1.32], [1.32, 1.32]]) b.push(['proc_grey', 0.05, 0.78, 0.05, x, 0.02, z], ['proc_yel', 0.18, 0.05, 0.1, x, 0.8, z]);
    return b;
  })());

  /* the prison: a plain block behind a wall, a tower at every corner, a heavy door */
  procModel('prison', (() => {
    const b = [
      ['proc_stone', 2.9, 0.02, 1.9, 0, 0, 0], ['proc_grey', 1.7, 0.34, 0.9, 0, 0.02, -0.15], ['proc_dark', 1.76, 0.03, 0.96, 0, 0.36, -0.15],
      ['proc_glass', 1.72, 0.03, 0.92, 0, 0.2, -0.15], ['proc_dark', 0.3, 0.2, 0.012, 0, 0.02, 0.31],
      ['proc_stone', 2.8, 0.2, 0.06, 0, 0.02, 0.88], ['proc_stone', 2.8, 0.2, 0.06, 0, 0.02, -0.88],
      ['proc_stone', 0.06, 0.2, 1.8, -1.4, 0.02, 0], ['proc_stone', 0.06, 0.2, 1.8, 1.4, 0.02, 0],
    ];
    for (const [x, z] of [[-1.38, -0.86], [1.38, -0.86], [-1.38, 0.86], [1.38, 0.86]]) b.push(['proc_grey', 0.2, 0.46, 0.2, x, 0.02, z], ['proc_dark', 0.26, 0.04, 0.26, x, 0.48, z]);
    return b;
  })());

  /* ---- transport (T4): the monorail rides a beam on pillars, joined by the same bitmask as the streets (1 N, 2 E, 4 S, 8 W) ---- */
  for (let m = 0; m < 16; m++) {
    const b = [['proc_grey', 0.2, 0.07, 0.2, 0, 0.44, 0], ['proc_stone', 0.08, 0.44, 0.08, 0, 0, 0], ['proc_yel', 0.04, 0.012, 0.04, 0, 0.51, 0]];
    if (m & 1) b.push(['proc_grey', 0.14, 0.07, 0.5, 0, 0.44, -0.25]);
    if (m & 2) b.push(['proc_grey', 0.5, 0.07, 0.14, 0.25, 0.44, 0]);
    if (m & 4) b.push(['proc_grey', 0.14, 0.07, 0.5, 0, 0.44, 0.25]);
    if (m & 8) b.push(['proc_grey', 0.5, 0.07, 0.14, -0.25, 0.44, 0]);
    procModel('mono_' + m, b);
  }
  procModel('monostop', [
    ['proc_stone', 0.1, 0.4, 0.1, 0, 0, 0], ['proc_stone', 0.9, 0.06, 0.5, 0, 0.4, 0], ['proc_blue', 0.95, 0.04, 0.56, 0, 0.64, 0],
    ['proc_white', 0.04, 0.2, 0.04, -0.42, 0.46, -0.2], ['proc_white', 0.04, 0.2, 0.04, 0.42, 0.46, -0.2], ['proc_white', 0.04, 0.2, 0.04, -0.42, 0.46, 0.2], ['proc_white', 0.04, 0.2, 0.04, 0.42, 0.46, 0.2],
    ['proc_white', 0.7, 0.1, 0.2, 0, 0.46, 0.06], ['proc_blue', 0.7, 0.025, 0.205, 0, 0.5, 0.06],
  ]);
  procModel('monodepot', [
    ['proc_grey', 1.9, 0.3, 0.8, 0, 0, 0], ['proc_blue', 1.96, 0.04, 0.86, 0, 0.3, 0], ['proc_dark', 0.9, 0.22, 0.012, -0.4, 0, 0.405],
    ['proc_stone', 0.1, 0.4, 0.1, 0.78, 0, 0.3], ['proc_grey', 0.4, 0.07, 0.2, 0.78, 0.4, 0.3], ['proc_white', 0.5, 0.1, 0.18, 0.7, 0.47, 0.3],
  ]);
  /* the container terminal: an apron, rows of stacked boxes in four liveries, a gantry crane */
  procModel('freight', (() => {
    const b = [['proc_apron', 2.9, 0.02, 1.9, 0, 0, 0]], cols = ['proc_red', 'proc_blue', 'proc_yel', 'proc_white', 'proc_grey'];
    for (let r = 0; r < 3; r++) for (let c = 0; c < 5; c++) { const h = 1 + ((r * 5 + c) % 3); for (let k = 0; k < h; k++) b.push([cols[(r + c + k) % 5], 0.42, 0.15, 0.2, -1.0 + c * 0.5, 0.02 + k * 0.15, 0.2 + r * 0.26]) }
    b.push(['proc_yel', 0.06, 0.78, 0.06, -0.95, 0.02, -0.7], ['proc_yel', 0.06, 0.78, 0.06, 0.95, 0.02, -0.7], ['proc_yel', 2.1, 0.06, 0.14, 0, 0.8, -0.7], ['proc_dark', 0.2, 0.08, 0.2, 0.4, 0.74, -0.7]);
    return b;
  })());
  /* the aircraft: nose along +x */
  procModel('plane', [
    ['proc_white', 0.92, 0.095, 0.095, 0, 0.02, 0], ['proc_white', 0.14, 0.07, 0.07, 0.5, 0.033, 0],
    ['proc_grey', 0.2, 0.014, 0.98, 0.03, 0.045, 0], ['proc_dark', 0.12, 0.05, 0.05, 0.12, 0.0, 0.25], ['proc_dark', 0.12, 0.05, 0.05, 0.12, 0.0, -0.25],
    ['proc_blue', 0.17, 0.19, 0.014, -0.42, 0.09, 0], ['proc_grey', 0.11, 0.012, 0.34, -0.42, 0.075, 0],
  ]);
}


/* ======================================================================
   INSTANCES — every building, tree and car of one kind is one draw call
   per material. Matrices are written straight into a shared buffer.
   ====================================================================== */
const Z_AXIS = new THREE.Vector3(0, 0, 1), _q2 = new THREE.Quaternion();
const _m = new THREE.Matrix4(), _q = new THREE.Quaternion(), _p = new THREE.Vector3(), _s = new THREE.Vector3();
class InstSet {
  constructor(group, shadows = true) { this.group = group; this.shadows = shadows; this.ground = true; this.k = new Map(); this.missing = new Set(); this.xray = false }
  make(name) {
    const model = MODELS.get(name);
    if (!model) { if (!this.missing.has(name)) { this.missing.add(name); console.warn('no model', name) } return null }
    const k = { model, cap: 0, n: 0, meshes: [], attr: null, arr: null };
    this.k.set(name, k); this.grow(k, 32); return k;
  }
  grow(k, cap) {
    cap = cap || k.cap * 2;
    const old = k.arr, oldLit = k.lit;
    k.arr = new Float32Array(cap * 16); k.lit = new Float32Array(cap * 2);
    if (old) { k.arr.set(old.subarray(0, Math.min(old.length, k.arr.length))); k.lit.set(oldLit.subarray(0, Math.min(oldLit.length, k.lit.length))) }
    k.attr = new THREE.InstancedBufferAttribute(k.arr, 16); k.attr.setUsage(THREE.DynamicDrawUsage);
    k.litAttr = new THREE.InstancedBufferAttribute(k.lit, 2); k.litAttr.setUsage(THREE.DynamicDrawUsage);
    for (const m of k.meshes) { this.group.remove(m); m.dispose && m.dispose() }
    k.meshes = [];
    for (const part of k.model.parts) {
      /* the model's buffers are shared; only the per-building window state is new */
      const geo = new THREE.BufferGeometry();
      geo.index = part.geo.index;
      for (const n in part.geo.attributes) geo.setAttribute(n, part.geo.attributes[n]);
      geo.setAttribute('aLitInfo', k.litAttr);
      const mesh = new THREE.InstancedMesh(geo, this.material(part.mat, k.model.drape, k.model), 1);
      mesh.userData.part = part;
      mesh.instanceMatrix = k.attr;
      mesh.frustumCulled = false;
      mesh.castShadow = this.shadows && !this.xray && !FLAT.test(k.model.name || '');
      mesh.receiveShadow = true;
      mesh.count = k.n;
      this.group.add(mesh); k.meshes.push(mesh);
    }
    k.cap = cap;
  }
  material(n, drape, model) {
    if (this.xray) return xrayMaterial(drape, model);
    const m = buildMaterial(n, matData.materials); return drape ? drapeMaterial(m) : m;
  }
  /* the cutaway shows the surface as glass: streets as pale ribbons, buildings as faint solids,
     and the things that feed the network (plants, pumps, stations) a little stronger */
  setXray(on) {
    if (this.xray === on) return;
    this.xray = on;
    for (const k of this.k.values()) for (const m of k.meshes) {
      m.material = this.material(m.userData.part.mat, k.model.drape, k.model);
      m.castShadow = this.shadows && !on && !FLAT.test(k.model.name || '');
    }
  }
  begin() { for (const k of this.k.values()) k.n = 0 }
  add(name, x, y, z, yaw, sc, sy, pitch, li) {
    let k = this.k.get(name) || this.make(name);
    if (!k) return;
    if (k.n >= k.cap) this.grow(k);
    _p.set(x, y + Math.max(hAt(x, z), WATER_Y), z); _q.setFromAxisAngle(Y_AXIS, yaw || 0);
    if (pitch) { _q2.setFromAxisAngle(Z_AXIS, pitch); _q.multiply(_q2) } const f = sc || 1; _s.set(f, f * (sy == null ? 1 : sy), f);
    _m.compose(_p, _q, _s);
    k.arr.set(_m.elements, k.n * 16);
    k.lit[k.n * 2] = li ? li[0] : 0; k.lit[k.n * 2 + 1] = li ? li[1] : 0;
    k.n++;
  }
  end() {
    for (const k of this.k.values()) {
      k.attr.needsUpdate = true; k.litAttr.needsUpdate = true;
      for (const m of k.meshes) { m.count = k.n; m.visible = k.n > 0 }
    }
  }
}
const XR = {
  bld: new THREE.MeshStandardMaterial({ color: 0xcfe0ec, transparent: true, opacity: 0.17, depthWrite: false, roughness: 0.9, metalness: 0 }),
  mark: new THREE.MeshStandardMaterial({ color: 0xffd36a, transparent: true, opacity: 0.55, depthWrite: false, roughness: 0.8, metalness: 0 }),
  road: new THREE.MeshStandardMaterial({ color: 0x9fb4c4, transparent: true, opacity: 0.62, depthWrite: false, roughness: 0.9, metalness: 0 }),
};
const XRAY_MARK = new Set(['power', 'diesel', 'gasps', 'windt', 'solar', 'nobel', 'pumpjack', 'platform', 'tankfarm', 'refinery', 'well', 'desal', 'busdepot', 'tramdepot', 'metrodepot', 'taxidepot', 'taxistand', 'metro', 'tramstop', 'busstop', 'port', 'derr', 'zibil', 'yandir', 'emerg']);
let xrayRoad = null;
function xrayMaterial(drape, model) {
  if (drape) return xrayRoad || (xrayRoad = drapeMaterial(XR.road));
  return model && XRAY_MARK.has(model.name) ? XR.mark : XR.bld;
}
/* the model's own name is needed to decide whether it casts a shadow */
const _make = InstSet.prototype.make;
InstSet.prototype.make = function (name) { const r = _make.call(this, name); if (r) r.model.name = name; return r };

/* ======================================================================
   TERRAIN AND WATER
   ====================================================================== */
const GROUND = {
  [T_SAND]: 0xe0d0a6, [T_PLAIN]: 0xc4b585, [T_SCRUB]: 0xb4ae79, [T_RIDGE]: 0xa89668,
  [T_ROCK]: 0x918360, [T_OIL]: 0x7b7057, [T_SALT]: 0xe6e2db, [T_MARSH]: 0x767f65,
  [T_ORCH]: 0x8a8560, [T_DUNE]: 0xe8dcb4,
};
const _c = new THREE.Color();
const groundSnow = { value: 0 };
let groundMesh = null, waterMesh = null, soilMesh = null, depthTex = null, aqMesh = null;
const waterU = { uTime: { value: 0 }, uDepth: { value: null }, uGrid: { value: new THREE.Vector2(1, 1) },
                 uShal: { value: new THREE.Color(0x4fb3c4) }, uDeep: { value: new THREE.Color(0x2f86a6) },
                 uOil: { value: new THREE.Color(0x35768c) } };

const NOISE_GLSL = `
float h3(vec3 p){ p=fract(p*0.3183099+.1); p*=17.0; return fract(p.x*p.y*p.z*(p.x+p.y+p.z)); }
float vnoise(vec3 x){ vec3 i=floor(x), f=fract(x); f=f*f*(3.0-2.0*f);
  return mix(mix(mix(h3(i),h3(i+vec3(1,0,0)),f.x),mix(h3(i+vec3(0,1,0)),h3(i+vec3(1,1,0)),f.x),f.y),
             mix(mix(h3(i+vec3(0,0,1)),h3(i+vec3(1,0,1)),f.x),mix(h3(i+vec3(0,1,1)),h3(i+vec3(1,1,1)),f.x),f.y),f.z); }
float fbm(vec3 p){ return vnoise(p)*0.5+vnoise(p*2.03)*0.3+vnoise(p*4.1)*0.2; }`;

function patchWorld(mat, key, uniforms, frag, fragNormal) {
  mat.customProgramCacheKey = () => key;
  mat.onBeforeCompile = sh => {
    Object.assign(sh.uniforms, uniforms);
    const decl = Object.keys(uniforms).map(k => {
      const v = uniforms[k].value;
      return 'uniform ' + (typeof v === 'number' ? 'float' : v.isTexture ? 'sampler2D' : v.isColor ? 'vec3'
        : v.isVector2 ? 'vec2' : 'vec3') + ' ' + k + ';';
    }).join('\n');
    sh.vertexShader = sh.vertexShader
      .replace('#include <common>', '#include <common>\nvarying vec3 vW;')
      .replace('#include <begin_vertex>', '#include <begin_vertex>\nvW=(modelMatrix*vec4(transformed,1.0)).xyz;');
    sh.fragmentShader = sh.fragmentShader
      .replace('#include <common>', '#include <common>\nvarying vec3 vW;\n' + decl + '\n' + NOISE_GLSL)
      .replace('#include <color_fragment>', '#include <color_fragment>\n' + frag);
    if (fragNormal) sh.fragmentShader = sh.fragmentShader.replace('#include <normal_fragment_maps>', '#include <normal_fragment_maps>\n' + fragNormal);
  };
  return mat;
}

function buildTerrain() {
  const g = buildHeights();
  if (groundMesh) { groundMesh.geometry = g }
  else {
    const mat = new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.97, metalness: 0 });
    mat.customProgramCacheKey = () => 'ground4';
    mat.onBeforeCompile = sh => {
      sh.uniforms.uSnow = groundSnow;
      sh.vertexShader = sh.vertexShader
        .replace('#include <common>', '#include <common>\nvarying vec3 vW; varying float vUp;')
        .replace('#include <begin_vertex>', '#include <begin_vertex>\nvW=(modelMatrix*vec4(transformed,1.0)).xyz; vUp=normal.y;');
      sh.fragmentShader = sh.fragmentShader
        .replace('#include <common>', '#include <common>\nvarying vec3 vW; varying float vUp;\nuniform float uSnow;\n' + NOISE_GLSL)
        .replace('#include <color_fragment>', `#include <color_fragment>
      /* fine noise fades with distance, or it beats against the pixel grid into stripes */
      float fw = length(fwidth(vW.xz));
      float a9 = 1.0 - smoothstep(0.03, 0.09, fw), a38 = 1.0 - smoothstep(0.007, 0.022, fw);
      float gr = fbm(vW * 1.7) * 0.5 + mix(0.5, fbm(vW * 9.0), a9) * 0.4 + mix(0.5, vnoise(vW * 38.0), a38) * 0.30;
      diffuseColor.rgb *= 0.80 + gr * 0.42;
      /* steep ground shows rock; the crest of a hill bleaches */
      float steep = smoothstep(0.90, 0.72, vUp);
      vec3 rock = vec3(0.50, 0.44, 0.34) * (0.75 + 0.5 * fbm(vW * 5.0));
      diffuseColor.rgb = mix(diffuseColor.rgb, rock, steep * 0.75);
      diffuseColor.rgb = mix(diffuseColor.rgb, diffuseColor.rgb * vec3(1.10, 1.07, 0.98), smoothstep(0.6, 2.2, vW.y) * 0.5);
      /* wet sand at the water line, a dark sea floor below it */
      diffuseColor.rgb *= mix(1.0, 0.62, smoothstep(-0.10, -0.24, vW.y));
      diffuseColor.rgb *= mix(1.0, 0.82, smoothstep(0.06, -0.10, vW.y) * step(-0.24, vW.y));
      /* snow lies above the tide line, thinner on steep rock; a multiply tint cannot whiten, so it is mixed here */
      float snowA = uSnow * smoothstep(0.02, 0.16, vW.y) * (1.0 - 0.45 * steep) * (0.82 + 0.18 * gr);
      diffuseColor.rgb = mix(diffuseColor.rgb, vec3(0.94, 0.96, 0.98) * (0.90 + 0.10 * gr), clamp(snowA, 0.0, 0.94));`);
    };
    groundMesh = new THREE.Mesh(g, mat);
    groundMesh.receiveShadow = true; groundMesh.renderOrder = -2;
    scene.add(groundMesh);
  }
  applyPads();

  /* water: how far each water tile is from land, as a texture the sea reads */
  const dist = new Float32Array(NC).fill(99), q = [];
  for (let i = 0; i < NC; i++) if (!isWater(G.tiles[i].t)) { dist[i] = 0; q.push(i) }
  for (let h = 0; h < q.length; h++) {
    const i = q[h], x = i % GW, y = (i / GW) | 0, d = dist[i];
    if (d >= 11) continue;
    for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
      const nx = x + dx, ny = y + dy; if (nx < 0 || ny < 0 || nx >= GW || ny >= GH) continue;
      const j = ny * GW + nx; if (dist[j] > d + 1) { dist[j] = d + 1; q.push(j) }
    }
  }
  const data = new Uint8Array(NC * 4);
  for (let i = 0; i < NC; i++) {
    data[i * 4] = Math.min(255, dist[i] / 10 * 255);
    data[i * 4 + 1] = G.tiles[i].t === T_OILSEA ? 255 : 0;
    data[i * 4 + 3] = 255;
  }
  if (!depthTex) {
    depthTex = new THREE.DataTexture(data, GW, GH, THREE.RGBAFormat, THREE.UnsignedByteType);
    depthTex.magFilter = depthTex.minFilter = THREE.LinearFilter;
    depthTex.wrapS = depthTex.wrapT = THREE.ClampToEdgeWrapping;
  } else { depthTex.image.data.set(data) }
  depthTex.needsUpdate = true;
  waterU.uDepth.value = depthTex; waterU.uGrid.value.set(GW, GH);

  if (!soilMesh) {
    /* what lies beneath: only ever seen through the see-through ground in the cutaway */
    const mat = patchWorld(new THREE.MeshStandardMaterial({ color: 0x3b4852, roughness: 1, metalness: 0 }),
      'soil2', {}, /* glsl */`
      float sg = fbm(vW * 5.0) * 0.55 + fbm(vW * 23.0) * 0.45;
      diffuseColor.rgb *= 0.78 + sg * 0.40;
      /* a tile grid, brighter every eight tiles, so it is plain which tile is being worked on */
      float fw = length(fwidth(vW.xz));
      vec2 gq = abs(fract(vW.xz) - 0.5), g8 = abs(fract(vW.xz / 8.0) - 0.5);
      float l1 = smoothstep(0.455, 0.49, max(gq.x, gq.y)) * (1.0 - smoothstep(0.05, 0.16, fw));
      float l8 = smoothstep(0.488, 0.499, max(g8.x, g8.y)) * (1.0 - smoothstep(0.30, 0.90, fw));
      diffuseColor.rgb = mix(diffuseColor.rgb, vec3(0.62, 0.76, 0.86), l1 * 0.20 + l8 * 0.30);`);
    soilMesh = new THREE.Mesh(new THREE.PlaneGeometry(GW + 80, GH + 80), mat);
    soilMesh.rotation.x = -Math.PI / 2; soilMesh.position.set(GW / 2, -0.90, GH / 2);
    soilMesh.receiveShadow = false; soilMesh.visible = false; scene.add(soilMesh);
  }
  /* the sweet water under the ground, seen in the cutaway: teal where there is any, richer where it is deeper */
  if (!aqMesh && typeof gAq !== 'undefined' && gAq) {
    const d = new Uint8Array(GW * GH * 4);
    for (let y = 0; y < GH; y++) for (let x = 0; x < GW; x++) {
      const r = gAq[y * GW + x], o = ((GH - 1 - y) * GW + x) * 4;
      if (r < 0.06) continue;
      d[o] = 40 + (r > 0.55 ? 10 : 0); d[o + 1] = 150 + r * 70; d[o + 2] = 190 + r * 40; d[o + 3] = Math.min(235, 60 + r * 200);
    }
    const tex = new THREE.DataTexture(d, GW, GH, THREE.RGBAFormat, THREE.UnsignedByteType);
    tex.magFilter = tex.minFilter = THREE.LinearFilter; tex.needsUpdate = true;
    const pg = new THREE.PlaneGeometry(GW, GH); pg.rotateX(-Math.PI / 2); pg.translate(GW / 2, 0, GH / 2);
    aqMesh = new THREE.Mesh(pg, new THREE.MeshBasicMaterial({ map: tex, transparent: true, depthWrite: false, toneMapped: false }));
    aqMesh.position.y = -0.86; aqMesh.renderOrder = -1; aqMesh.visible = false; scene.add(aqMesh);
  }
  if (!waterMesh) {
    const mat = patchWorld(new THREE.MeshStandardMaterial({ color: 0xffffff, roughness: 0.14, metalness: 0.05, transparent: true }),
      'water', waterU, /* glsl */`
      vec2 g = vW.xz / uGrid;
      vec4 dd = (g.x > 0.0 && g.y > 0.0 && g.x < 1.0 && g.y < 1.0) ? texture2D(uDepth, g) : vec4(1.0, 0.0, 0.0, 1.0);
      float depth = dd.r;
      vec3 sea = mix(uShal, uDeep, smoothstep(0.02, 0.85, depth));
      sea = mix(sea, uOil, dd.g * 0.7);
      float rip = fbm(vec3(vW.xz * 1.9, uTime * 0.22)) * 0.6 + fbm(vec3(vW.xz * 7.0, uTime * 0.5)) * 0.4;
      sea *= 0.90 + rip * 0.22;
      float foam = (1.0 - smoothstep(0.0, 0.085, depth)) * (0.55 + 0.45 * sin(uTime * 1.6 + vW.x * 3.1 + vW.z * 2.3));
      diffuseColor.rgb = mix(sea, vec3(0.93, 0.97, 0.96), clamp(foam, 0.0, 0.85));
      diffuseColor.a = mix(0.50, 0.97, smoothstep(0.0, 0.50, depth));
      diffuseColor.a = max(diffuseColor.a, clamp(foam, 0.0, 0.9));`,
      /* a travelling ripple on the normal gives the sun something to glint on */`
      { float e = 0.03, w0 = fbm(vec3(vW.xz * 1.6, uTime * 0.30)), wx = fbm(vec3((vW.xz + vec2(e, 0.0)) * 1.6, uTime * 0.30)), wz = fbm(vec3((vW.xz + vec2(0.0, e)) * 1.6, uTime * 0.30));
        vec3 pert = (viewMatrix * vec4((w0 - wx) / e * 0.10, 0.0, (w0 - wz) / e * 0.10, 0.0)).xyz;
        normal = normalize(normal + pert); }`);
    waterMesh = new THREE.Mesh(new THREE.PlaneGeometry(2600, 2600), mat);
    waterMesh.rotation.x = -Math.PI / 2; waterMesh.position.set(GW / 2, WATER_Y, GH / 2);
    waterMesh.receiveShadow = true; waterMesh.renderOrder = -3;
    scene.add(waterMesh);
  }
}
window.buildTerrain = buildTerrain;
window.layoutTerrain = () => {};
window.sampleGround = () => {};
window.dropSprite = () => {};

/* ======================================================================
   BUILDINGS
   ====================================================================== */
let surf = null, under = null, deco = null;
const UG_Y = { c: -0.16, u: -0.36, m: -0.58 };

function stripName(b, d) {
  const same = (x, y) => { const n = bldAt(x, y); return !!(n && n.key === b.key) };
  if (d.runway) {
    const w = same(b.x - 1, b.y), e = same(b.x + 1, b.y), n = same(b.x, b.y - 1), s = same(b.x, b.y + 1);
    if (w || e || !(n || s)) return w && e ? 'rw_x' : e ? 'rw_x_w' : w ? 'rw_x_e' : 'rw_x';
    return n && s ? 'rw_z' : s ? 'rw_z_n' : 'rw_z_s';
  }
  const rm = b.rm | 0, h = rm & 10, v = rm & 5;
  return h && !v ? 'tw_x' : v && !h ? 'tw_z' : 'tw_c';
}
function modelFor(b) {
  const d = DEFS[b.key];
  if (d.layout) return null;                       /* the Old City is drawn piece by piece (drawOldCity) */
  if (d.area) return d.grow && (b.age || 0) < 6 ? 'ff_young' : d.tiles + 'abc'[(hash2(b.x, b.y, 17) * 3) | 0];
  if (d.strip) return stripName(b, d);
  if (d.tunnel) return 'mtun_' + b.rm;
  if (d.rail) return (d.mono ? 'mono_' : 'tram_') + b.rm;
  if (d.under && d.conduct) return 'cable_' + b.rm;
  if (d.conduct) return 'pylon';
  if (d.pipe) return 'pipe_' + b.rm;
  if (d.bridge) return 'brg_' + b.rm;
  if (d.hwy) return 'hwy_' + b.rm;
  if (d.prom) return 'prom_' + b.rm;
  if (d.road) return (d.aven ? 'aven_' : d.tier === 0 ? 'dirt_' : d.tier === 1 ? 'stone_' : 'road_') + b.rm;
  if (d.zone) {
    if (b.lvl === 0) return 'lot_' + d.zone;
    return ZSPR[d.zone][d.inc | 0][b.lvl - 1][Math.min(b.var | 0, 2)];
  }
  return d.spr;
}
window.modelFor = modelFor;

/* Buildings are drawn smaller than their tile. A tile is about 40 m of ground
   and the map is 240 of them, so a body that filled it from edge to edge made the
   whole peninsula read as a model railway: blocks towering over trees, cars
   and the width of the street. Only bodies shrink — streets, pipes, rails,
   runways, plots, poles and the curtain wall keep the full tile, and a
   building's footprint (what it occupies, what picks it) is unchanged. */
const BSCALE = 0.68;
function bodyScale(b, d, name) {
  if (d.road || d.prom || d.rail || d.under || d.tunnel || d.conduct || d.pipe) return 1;
  if (DRAPE_RE.test(name) || /^(wall_|gate_)/.test(b.key)) return 1;
  return BSCALE;
}
window.bodyScale = bodyScale;

/* Which windows burn after dark is a fact about the building, not the model: an
   unpowered or empty one is dark, a shop or office burns late, a home somewhere
   between, and no two have the same pattern. Returned as the [threshold offset,
   seed] the window shader reads per instance. */
const _li = [0, 0];
function litFor(b, d) {
  if (d.road || d.prom || d.rail || d.under || d.tunnel || d.conduct || d.pipe) return null;
  const h = hash2(b.x, b.y, 53); _li[1] = hash2(b.x, b.y, 59);
  if (d.zone) {
    if (b.lvl === 0 || !b.pw) _li[0] = 0.5;
    else if (d.zone === 'r') _li[0] = (b.pop > 0 ? -0.30 : 0.5) + (b.pop > 0 ? h * 0.65 : 0);
    else if (d.zone === 'c') _li[0] = -0.38 + h * 0.4;
    else _li[0] = -0.1 + h * 0.4;
  } else if (d.fixed) _li[0] = -0.15 + h * 0.6;
  else if (d.unique) _li[0] = b.pw === false ? 0.5 : -0.3;
  else _li[0] = (b.pw === false && !d.power) ? 0.5 : -0.25 + h * 0.3;
  return _li;
}
window.litFor = litFor;

/* A building that is new, or has just grown into a bigger model, is BUILT: a site
   goes up round it (fence, trampled ground, a cabin, heaps of sand and block, a
   concrete mixer), the walls rise storey by storey inside a scaffold, a tower
   crane swings over anything big, and dust hangs about the foot of it all. When
   it is done the scaffold comes down, the fence goes, the crane is lifted away.
   How long that takes follows what is being built (riseMs). The first sync after
   a load only records what is standing, so a saved city does not all rise at
   once, and anything beyond the view is not worth animating. */
const rise = new Map(), seenModel = new Map();
let riseReady = false, lamps = [];
const sstep3 = u => u * u * (3 - 2 * u);
function riseMs(b, d) {
  if (d.layout) return 24000;
  if (d.zone) return 1400 + b.lvl * 800 + (d.inc | 0) * 400;
  return Math.min(14000, 2600 + 1100 * Math.sqrt(b.w * b.h) + Math.min(5000, (d.cost || 0) / 7));
}
/* where the walls have got to, 0..1: a foundation first, then storey by storey with a pause
   between, then the finish */
function buildProgress(u, floors) {
  const p = clamp((u - 0.14) / 0.74, 0, 1);
  if (floors <= 1) return p;
  const f = p * floors, k = Math.min(floors - 1, Math.floor(f));
  return (k + sstep3(clamp((f - k) / 0.45, 0, 1))) / floors;
}
let siteList = [], siteCount = 0, cranesNow = 0;
const MAX_CRANES = 6;                       /* a boom town should not forest the skyline */
function craneName(H) {
  const need = H + 0.55;
  return need <= 0.93 ? 'crane_mast_1' : need <= 1.53 ? 'crane_mast_2' : 'crane_mast_3';
}
/* one tower crane: the mast, and the jib slewing over the work */
function addCrane(mx, mz, lift, H, tx, tz, seed, now) {
  const mn = craneName(H), mast = MODELS.get(mn), jib = MODELS.get('crane_jib');
  if (!mast || !jib || cranesNow >= MAX_CRANES) return;
  cranesNow++;
  surf.add(mn, mx, lift, mz, 0, 1, 1);
  const home = Math.atan2(-(tz - mz), tx - mx);
  surf.add('crane_jib', mx, lift + mast.h - 0.03, mz, home + Math.sin(now / 2700 + seed * 6.28) * 1.15 + 0.2 * Math.sin(now / 900 + seed * 3), 1, 1);
}
/* the site round a building that is going up; returns how tall its walls are, 0..1 */
function drawSite(b, d, model, bs, u, cx, cz, lift, now) {
  const H = model.h * bs, zone = !!d.zone;
  const floors = Math.max(1, Math.round(H / 0.27));
  const body = Math.max(0.04, buildProgress(u, floors));
  const fenceK = u > 0.93 ? clamp(1 - (u - 0.93) / 0.07, 0.02, 1) : 1;
  const hx = bs * b.w / 2, hz = bs * b.h / 2;
  if (!zone && !d.offshore) {
    for (let j = 0; j < b.h; j++) for (let i = 0; i < b.w; i++) surf.add('cons_pad', b.x + i + 0.5, lift, b.y + j + 0.5, 0, 1, fenceK);
    for (let i = 0; i < b.w; i++) {
      surf.add('cons_fence', b.x + i + 0.5, lift, b.y + 0.03, 0, 1, fenceK);
      surf.add('cons_fence', b.x + i + 0.5, lift, b.y + b.h - 0.03, Math.PI, 1, fenceK);
    }
    for (let j = 0; j < b.h; j++) {
      surf.add('cons_fence', b.x + 0.03, lift, b.y + j + 0.5, Math.PI / 2, 1, fenceK);
      surf.add('cons_fence', b.x + b.w - 0.03, lift, b.y + j + 0.5, -Math.PI / 2, 1, fenceK);
    }
    surf.add('cons_cabin', b.x + 0.30, lift + 0.014, b.y + 0.22, 0, 0.62, fenceK);
    surf.add('cons_pile_a', b.x + b.w - 0.26, lift + 0.014, b.y + b.h - 0.22, 0.5, 0.65, fenceK);
    if (b.w * b.h >= 2) surf.add('cons_pile_b', b.x + 0.24, lift + 0.014, b.y + b.h - 0.22, 0, 0.65, fenceK);
    if (b.w * b.h >= 4) surf.add('cons_mixer', b.x + b.w - 0.46, lift + 0.014, b.y + 0.24, 0.3 * Math.sin(now / 5000), 0.7, fenceK);
  }
  /* scaffold, as tall as the walls are, and lowered once they are finished */
  if (H >= 0.45) {
    const sh = u < 0.86 ? H * body + 0.10 : (H + 0.10) * (1 - (u - 0.86) / 0.14);
    if (sh > 0.05) {
      const sy = sh / bs;
      for (let i = 0; i < b.w; i++) {
        const x = cx - hx + bs * (i + 0.5);
        surf.add('scaf_edge', x, lift, cz - hz - 0.012, 0, bs, sy);
        surf.add('scaf_edge', x, lift, cz + hz + 0.012, Math.PI, bs, sy);
      }
      for (let j = 0; j < b.h; j++) {
        const z = cz - hz + bs * (j + 0.5);
        surf.add('scaf_edge', cx - hx - 0.012, lift, z, Math.PI / 2, bs, sy);
        surf.add('scaf_edge', cx + hx + 0.012, lift, z, -Math.PI / 2, bs, sy);
      }
    }
  }
  if ((H >= 0.8 || b.w * b.h >= 4 || d.unique) && u < 0.97) {
    const k = Math.floor(hash2(b.x, b.y, 71) * 4), sx = k & 1 ? 1 : -1, sz = k & 2 ? 1 : -1;
    addCrane(cx + sx * (b.w / 2 + 0.55), cz + sz * (b.h / 2 + 0.55), lift, H, cx, cz, hash2(b.x, b.y, 73), now);
  }
  siteList.push(cx, cz, b.w, b.h, H * body, lift + Math.max(hAt(cx, cz), WATER_Y));
  return body;
}
/* The walled city, a piece at a time: wall first, then bastions and gate, then the lanes. */
function drawOldCity(b, d, u, now) {
  const L = oldLayout(), N = L.length, P = u >= 1 ? 1 : clamp((u - 0.04) / 0.92, 0, 1);
  for (let i = 0; i < N; i++) {
    const [key, lx, ly] = L[i], pd = DEFS[key], w = pd.w, h = pd.h, x = b.x + lx, y = b.y + ly, cx = x + w / 2, cz = y + h / 2;
    if (cx < cullBox[0] || cx > cullBox[1] || cz < cullBox[2] || cz > cullBox[3]) continue;
    const k = P >= 1 ? 1 : clamp((P * (N + 7) - i) / 7, 0, 1);
    if (k <= 0) continue;
    const sc = /^(wall_|gate_)/.test(key) ? 1 : BSCALE;
    const lift = padTop(x, y, w, h) - Math.max(hAt(cx, cz), WATER_Y);
    surf.add(pd.spr, cx, lift, cz, 0, sc, k >= 1 ? 1 : Math.max(0.04, k), 0, litFor({ x, y }, pd));
  }
  if (u < 0.97 && !ugView) {
    const ox = b.x, oy = b.y, ow = b.w, oh = b.h, cxm = ox + ow / 2, czm = oy + oh / 2;
    const lift = padTop(ox, oy, 1, 1) - Math.max(hAt(ox, oy), WATER_Y);
    for (const [sx, sz] of [[-1, -1], [1, -1], [-1, 1], [1, 1]])
      addCrane(cxm + sx * (ow / 2 + 0.9), czm + sz * (oh / 2 + 0.9), lift, 2.3, cxm, czm, hash2(sx + 3, sz + 5, 79), now);
    siteList.push(cxm, czm, ow, oh, 1.2 * P, lift + Math.max(hAt(cxm, czm), WATER_Y));
  }
}

/* ---- what is worth drawing -------------------------------------------
   Every instance of every building used to be submitted whether or not it was
   anywhere near the screen, and at full detail however small it was: a dense
   city was about 3.5 M triangles at every zoom. Now only what falls in the box
   the camera sees (plus a margin) is submitted, and when the camera is far
   enough back that a house is a few pixels, an ordinary building is a plain
   block in its own wall material. Landmarks, the Old City and everything
   else with a body of its own keep their models. The box is bucketed so a
   pan does not resync every frame. */
let cullBox = [-1e9, 1e9, -1e9, 1e9], cullLod = 0, cullSig = '', lodR2 = 1e12;
const LOD_Z = 0.5;
function updateCull() {
  let x0 = 1e9, x1 = -1e9, z0 = 1e9, z1 = -1e9;
  for (const [sx, sy] of [[0, 0], [VW, 0], [VW, VH], [0, VH], [VW / 2, VH / 2]]) {
    const g = groundAt(cam, sx, sy);
    if (!g || !isFinite(g[0]) || !isFinite(g[1])) { x0 = -1e9; x1 = 1e9; z0 = -1e9; z1 = 1e9; break }
    x0 = Math.min(x0, g[0]); x1 = Math.max(x1, g[0]); z0 = Math.min(z0, g[1]); z1 = Math.max(z1, g[1]);
  }
  const m = 8, q = v => Math.round(v / 6) * 6;
  const box = [q(x0 - m), q(x1 + m), q(z0 - m), q(z1 + m)], lod = cam.z < LOD_Z ? 1 : 0;
  const sig = box.join() + '|' + lod + '|' + (ugView ? 1 : 0) + '|' + Math.round(camDist() / 3) + '|' + Math.round(cam.tx / 4) + ',' + Math.round(cam.ty / 4);
  if (sig !== cullSig) { cullSig = sig; cullBox = box; cullLod = lod; dirtyOrder = true }
}
const lodMemo = new Map();
function lodName(name, d, d2) {
  if ((cullLod || d2 > lodR2) && /^(pk_|cpk_|ff_)[abc]$/.test(name)) return name.replace(/[abc]$/, 'lo');
  if (!(cullLod || d2 > lodR2) || d.unique || d.fixed || DRAPE_RE.test(name) || FLAT.test(name) || /^brg_/.test(name)) return name;
  const ln = name + '~lo';
  if (lodMemo.has(name)) return lodMemo.get(name) ? ln : name;
  const m = MODELS.get(name);
  if (!m || m.h < 0.2) { lodMemo.set(name, false); return name }
  /* the dominant material is the one with most triangles; a window-grid material on
     a plain box reads as a building from far away */
  let best = null, bn = -1;
  const KIND = { windows: 3, stone: 2, rough: 1 };
  for (const p of m.parts) {
    const r = matData.materials[p.mat], tri = p.geo.index ? p.geo.index.count : p.geo.attributes.position.count;
    const score = (r && KIND[r.kind] ? KIND[r.kind] : 0) * 1e7 + tri;
    if (score > bn) { bn = score; best = p }
  }
  const [x0, x1, z0, z1] = m.box, g = new THREE.BoxGeometry(x1 - x0, m.h, z1 - z0);
  g.deleteAttribute('uv'); g.translate((x0 + x1) / 2, m.h / 2, (z0 + z1) / 2);
  MODELS.set(ln, { parts: [{ geo: g, mat: best.mat }], h: m.h, minY: 0, box: m.box, drape: false, name: ln });
  lodMemo.set(name, true); return ln;
}
/* ---- pathways -------------------------------------------------------------
   Every building that is lived or worked in is joined to its street by a paved path: straight to the
   kerb when a street runs beside it, otherwise across the (up to three) free tiles between, the way a
   person would walk. A house turns to face the street it is joined to. The paths are pieces of tile
   (pth_<connection mask>), draped like streets; they are worked out only when something is built,
   removed or grows, never per frame. */
let pathSig = '';
const pathCells = new Map(), faceOf = new Map();
const PATH_FREE = 3;
function wantsPath(b, d) {
  if (d.road || d.prom || d.rail || d.under || d.tunnel || d.conduct || d.pipe || d.strip || d.area || d.fixed || d.layout || d.offshore || d.stop || d.rank || d.tool) return false;
  if (d.zone && b.lvl === 0) return false;
  return true;
}
function computePaths() {
  pathCells.clear(); faceOf.clear();
  const roadAt = (x, y) => { const t = tile(x, y); if (!t || t.b < 0) return false; const bb = G.blds[t.b]; return !!(bb && DEFS[bb.key].road) };
  const freeAt = (x, y) => { const t = tile(x, y); return !!t && t.b < 0 && t.r < 0 && !isWater(t.t) && t.t !== T_ROCK };
  const mark = (x, y, bit) => { const k = y * GW + x; pathCells.set(k, (pathCells.get(k) | 0) | bit) };
  for (const b of G.blds) {
    if (!b) continue;
    const d = DEFS[b.key]; if (!wantsPath(b, d)) continue;
    const cx = b.x + b.w / 2, cz = b.y + b.h / 2, front = (2 + (b.rot | 0)) & 3, ring = [];
    for (let i = 0; i < b.w; i++) { ring.push([b.x + i, b.y, 0]); ring.push([b.x + i, b.y + b.h - 1, 2]) }
    for (let j = 0; j < b.h; j++) { ring.push([b.x, b.y + j, 3]); ring.push([b.x + b.w - 1, b.y + j, 1]) }
    /* 1) a street right beside the footprint: join it on the side nearest the middle, preferring the front door */
    let best = null, bd = 1e9;
    for (const [fx, fy, k] of ring) {
      if (!roadAt(fx + DV[k][0], fy + DV[k][1])) continue;
      const dd = (fx + 0.5 - cx) ** 2 + (fy + 0.5 - cz) ** 2 + hash2(fx, fy, 61 + k) * 0.05 - (k === front && !d.zone ? 0.8 : 0);
      if (dd < bd) { bd = dd; best = [fx, fy, k] }
    }
    if (best) { mark(best[0], best[1], 1 << best[2]); if (d.zone) faceOf.set(b.id, best[2]); continue }
    /* 2) otherwise walk to the nearest street across free ground */
    const seen = new Map(), q = [];
    for (const [fx, fy, k] of ring) {
      const nx = fx + DV[k][0], ny = fy + DV[k][1], key = ny * GW + nx;
      if (freeAt(nx, ny) && !seen.has(key)) { seen.set(key, { px: fx, py: fy, k, depth: 1 }); q.push([nx, ny]) }
    }
    let found = null;
    for (let h = 0; h < q.length && !found; h++) {
      const [x, y] = q[h], cur = seen.get(y * GW + x);
      for (let k = 0; k < 4 && !found; k++) {
        const nx = x + DV[k][0], ny = y + DV[k][1];
        if (roadAt(nx, ny)) found = { x, y, k, cur };
        else if (cur.depth < PATH_FREE && freeAt(nx, ny) && !seen.has(ny * GW + nx)) { seen.set(ny * GW + nx, { px: x, py: y, k, depth: cur.depth + 1 }); q.push([nx, ny]) }
      }
    }
    if (!found) continue;
    let x = found.x, y = found.y, cur = found.cur;
    mark(x, y, 1 << found.k);
    for (;;) {
      mark(x, y, 1 << ((cur.k + 2) & 3)); mark(cur.px, cur.py, 1 << cur.k);
      if (cur.depth === 1) { if (d.zone) faceOf.set(b.id, cur.k); break }
      x = cur.px; y = cur.py; cur = seen.get(y * GW + x);
    }
  }
}
/* moving parts: wind rotors turn at the pace of the wind, a pumpjack's beam rocks while it pumps */
const animList = [];
let animSet = null, rotAng = 0, animT = 0, animNow = 0;
function drawAnim() {
  if (!animSet) return;
  const now = performance.now(), dt = clamp(now - (animNow || now), 0, 120); animNow = now;
  const running = G.speed > 0 || window.__intro;
  if (running) { animT += dt / 1000; rotAng += dt / 1000 * (0.35 + 3.0 * (typeof windNow === 'function' ? windNow() : 0.5)) }
  animSet.begin();
  if (!ugView) for (let i = 0; i < animList.length; i += 8) {
    const kind = animList[i], cx = animList[i + 1], lift = animList[i + 2], cz = animList[i + 3], yaw = animList[i + 4], bs = animList[i + 5], ph = animList[i + 6], live = animList[i + 7];
    if (kind === 0) animSet.add('windrotor', cx + Math.sin(yaw) * 0.16 * bs, lift + 1.35 * bs, cz + Math.cos(yaw) * 0.16 * bs, yaw, bs, 1, rotAng + ph * 6.28);
    else animSet.add('pumpbeam', cx, lift + 0.46 * bs, cz, yaw, bs, 1, live ? 0.20 * Math.sin(animT * 1.9 + ph * 6.28) : 0.06);
  }
  animSet.end();
}
function syncBuildings() {
  applyPads();
  { let lv = 0; for (const b of G.blds) if (b && b.lvl > 0 && DEFS[b.key].zone) lv++;
    const sig = bldVer + ':' + lv + ':' + G.blds.length;
    if (sig !== pathSig) { pathSig = sig; computePaths() } }
  animList.length = 0;
  surf.begin(); under.begin();
  lodR2 = Math.pow(camDist() * 0.6 + 5, 2);
  const now = performance.now(), R2 = Math.pow(camDist() * 1.6 + 10, 2);
  lamps = []; lampTiles = []; siteList = []; cranesNow = 0;
  const alive = new Set();
  for (const b of G.blds) {
    if (!b) continue;
    const d = DEFS[b.key];
    const cx = b.x + b.w / 2, cz = b.y + b.h / 2;
    const vis = b.x + b.w >= cullBox[0] && b.x <= cullBox[1] && b.y + b.h >= cullBox[2] && b.y <= cullBox[3];
    const id = b.id != null ? b.id : b.x * 4096 + b.y;
    alive.add(id);
    if (d.layout) {
      /* the Old City: nothing stands until it is founded, then it is raised over many seconds */
      if (seenModel.get(id) !== 'layout') {
        seenModel.set(id, 'layout');
        if (riseReady) { rise.set(id, now); if (window.sfx) sfx('found') }
      }
      if (!vis) continue;
      let u = 1; const t0 = rise.get(id);
      if (t0 != null) { u = (now - t0) / riseMs(b, d); if (u >= 1) { rise.delete(id); u = 1; if (window.sfx) sfx('done', { big: 1 }) } }
      drawOldCity(b, d, u, now);
      continue;
    }
    const mname = modelFor(b);
    if (!mname) continue;
    const name = vis ? lodName(mname, d, (cx - cam.tx) * (cx - cam.tx) + (cz - cam.ty) * (cz - cam.ty)) : mname;
    if (d.tunnel || (d.under && !d.tunnel)) {
      if (!vis) continue;
      const sl = slotOf(d);
      under.add(name, cx, UG_Y[sl] != null ? UG_Y[sl] : -0.2, cz, 0);
    } else {
      let sy = 1, u = 1;
      if (!d.road && !d.rail && !d.fixed && !d.area) {
        /* record what stands even when it is off screen, or panning would make it all rise */
        if (seenModel.get(id) !== mname) {
          seenModel.set(id, mname);
          const dx = cx - cam.tx, dz = cz - cam.ty;
          if (vis && riseReady && dx * dx + dz * dz < R2) {
            rise.set(id, now);
            if (window.sfx) sfx('start', { x: cx, z: cz, big: d.zone ? (b.lvl >= 2 ? 1 : 0) : 1, zone: d.zone ? 1 : 0 });
          }
        }
        if (!vis) continue;
        const t0 = rise.get(id);
        if (t0 != null) {
          u = (now - t0) / riseMs(b, d);
          if (u >= 1) { rise.delete(id); u = 1; if (window.sfx) sfx('done', { x: cx, z: cz, big: d.zone ? 0 : 1 }) }
        }
      }
      /* a rail rides on the street it shares; everything stands on the top of its pad */
      if (!vis) continue;
      /* an offshore rig or platform stands on its legs at the waterline, not on a sea floor that is up to two units down */
      const lift = d.bridge ? BRIDGE_Y : d.offshore ? 0.02 : DRAPE_RE.test(name) ? 0.012 : padTop(b.x, b.y, b.w, b.h) - Math.max(hAt(cx, cz), WATER_Y);
      const bs = bodyScale(b, d, name);
      if (u < 1 && !ugView) { const model = MODELS.get(mname); if (model) sy = drawSite(b, d, model, bs, u, cx, cz, lift, now) }
      let yaw = d.road ? 0 : -(b.rot || 0) * Math.PI / 2;
      if (d.zone && b.lvl > 0) { const fk = faceOf.get(id); if (fk != null) yaw = (2 - fk) * Math.PI / 2 }       /* a house faces its street */
      if (d.grow) sy = 0.62 + 0.38 * Math.min(1, (b.age || 0) / 36);                                          /* saplings, then a wood */
      surf.add(name, cx, lift + (d.rail ? 0.036 : 0), cz, yaw, bs, sy, 0, litFor(b, d));
      if (u >= 1 && (d.src === 'wind' || b.key === 'pumpjack')) animList.push(d.src === 'wind' ? 0 : 1, cx, lift, cz, yaw, bs, hash2(b.x, b.y, 83), b.pw === false ? 0 : 1);
      if (d.oneway) surf.add('arw_1', cx, d.bridge ? lift : 0.012, cz, -(b.rot || 0) * Math.PI / 2, 1, 1);
      /* a balustrade on every side of the promenade that meets the sea */
      if (d.prom) for (let k = 0; k < 4; k++) { const n = tile(b.x + DV[k][0], b.y + DV[k][1]); if (n && isWater(n.t)) surf.add('prom_rail', cx, lift, cz, Math.atan2(DV[k][0], DV[k][1]), 1, 1) }
      /* one lamp on about every third street tile, set to the side of the carriageway */
      if (d.road && !d.rail && !d.bridge && ((b.x * 7 + b.y * 13) % 3 === 0)) { lamps.push(cx + 0.36, cz + 0.36); lampTiles.push(cx + 0.36, cz + 0.36, b.y * GW + b.x) }
    }
  }
  for (const [k, m] of pathCells) {
    const x = k % GW, y = (k / GW) | 0;
    if (x + 1 < cullBox[0] || x > cullBox[1] || y + 1 < cullBox[2] || y > cullBox[3]) continue;
    const t = G.tiles[k]; if (!t || (t.b >= 0 && DEFS[G.blds[t.b].key].road)) continue;
    surf.add('pth_' + m, x + 0.5, 0.012, y + 0.5, 0, 1, 1);
  }
  surf.end(); under.end();
  /* a building pulled down while it was still rising leaves its entry behind, which
     would keep every frame resyncing the whole city */
  for (const id of rise.keys()) if (!alive.has(id) || now - rise.get(id) > 25000) rise.delete(id);
  for (const id of seenModel.keys()) if (!alive.has(id)) seenModel.delete(id);
  siteCount = siteList.length / 6;
  if (!rise.size) flowT = -1e9;
  riseReady = true;
  dirtyOrder = false; decoKey = '';
}
window.syncBuildings = syncBuildings;

/* ---- scatter: trees and scrub, only near what is being looked at ---- */
let decoKey = '';
function decoAtTile(x, y) {
  const t = tile(x, y);
  if (!t || t.b >= 0 || t.r >= 0) return null;
  if (hash2(x, y, 23) > 0.17) return null;
  const k = hash2(x, y, 29);
  switch (t.t) {
    case T_PLAIN: return k < 0.42 ? 'deco_tree' : k < 0.76 ? 'deco_tree2' : 'deco_yard';
    case T_ORCH:  return k < 0.55 ? 'deco_tree' : 'deco_tree2';
    case T_SCRUB: return k < 0.80 ? 'deco_scrub' : 'deco_tree2';
    case T_RIDGE: return k < 0.70 ? 'deco_scrub' : null;
    case T_SAND:  return k < 0.35 ? 'deco_palm' : k < 0.55 ? 'deco_scrub' : null;
    case T_DUNE:  return k < 0.25 ? 'deco_palm' : null;
    default:      return null;
  }
}
function syncDeco() {
  if (ugView) return;
  const R = Math.min(48, camDist() * 1.1 + 5);
  const key = Math.round(cam.tx / 6) + ',' + Math.round(cam.ty / 6) + ',' + Math.round(R / 4);
  if (key === decoKey) return;
  decoKey = key;
  deco.begin();
  const x0 = Math.max(0, Math.floor(cam.tx - R)), x1 = Math.min(GW - 1, Math.ceil(cam.tx + R));
  const y0 = Math.max(0, Math.floor(cam.ty - R)), y1 = Math.min(GH - 1, Math.ceil(cam.ty + R));
  for (let y = y0; y <= y1; y++) for (let x = x0; x <= x1; x++) {
    const nm = decoAtTile(x, y); if (!nm) continue;
    const j = hash2(x, y, 31);
    deco.add(nm, x + 0.5 + (j - 0.5) * 0.25, 0, y + 0.5 + (hash2(x, y, 37) - 0.5) * 0.25,
             j * TAU, 0.85 + 0.35 * hash2(x, y, 41));
  }
  deco.end();
  wxVis.season = -1;                      /* new meshes have not been tinted for the season yet */
}

/* ======================================================================
   LIGHT — the sun moves and the sky changes with the one clock
   ====================================================================== */
/* ======================================================================
   WEATHER — what G.wx says, eased so a front rolls in rather than switches on: overcast dims the
   sun and greys the sky, rain falls in streaks round the camera, snow drifts and lies on the
   ground, wet ground goes dark, a storm flashes. The trees turn with the seasons.
   ====================================================================== */
const wxVis = { fog: 0, cloud: 0, rain: 0, snow: 0, storm: 0, cover: 0, wet: 0, flash: 0, t: 0, nextFlash: 0, season: -1, cov10: -1, live: 1 };
/* Paused means paused: the rain stops falling, the snow stops, storms hold their lightning, clouds hang
   where they are. `live` eases to 0 while the game is stopped (the intro flight counts as running). */
const isPaused = () => G.speed === 0 && !window.__intro;
const WX_TARGET = { clear: [0, 0, 0, 0], cloudy: [0.55, 0, 0, 0], rain: [0.85, 0.7, 0, 0], snow: [0.75, 0, 1, 0], storm: [1, 1, 0, 1] };
function updateWeatherVis() {
  const now = performance.now(), dt = clamp(now - (wxVis.t || now), 0, 250); wxVis.t = now;
  const w = G.wx || { kind: 'clear', snow: 0, wet: 0 }, tg = WX_TARGET[w.kind] || WX_TARGET.clear;
  const k = 1 - Math.exp(-dt / 2200);
  wxVis.live += ((isPaused() ? 0 : 1) - wxVis.live) * (1 - Math.exp(-dt / 380));
  wxVis.cloud += (tg[0] - wxVis.cloud) * k; wxVis.rain += (tg[1] - wxVis.rain) * k;
  wxVis.snow += (tg[2] - wxVis.snow) * k; wxVis.storm += (tg[3] - wxVis.storm) * k;
  /* fog: a foggy spell is thickest at dawn and thins by midmorning */
  wxVis.fog += (((w.fog ? 1 : 0) * clamp(1 - Math.abs(dayFrac() - 0.33) / 0.24, 0.18, 1)) - wxVis.fog) * k;
  wxVis.cover += ((w.snow || 0) - wxVis.cover) * k; wxVis.wet += ((w.wet || 0) - wxVis.wet) * k;
  wxVis.flash = Math.max(0, wxVis.flash - dt / 260);
  if (wxVis.storm > 0.6 && wxVis.live > 0.9 && now > wxVis.nextFlash) {
    wxVis.flash = 1; wxVis.nextFlash = now + 4000 + Math.random() * 9000;
    if (window.sfx) setTimeout(() => sfx('thunder'), 300 + Math.random() * 1500);
  }
}
let rainM = null, snowM = null;
const WX_VERT = `uniform vec3 uC; uniform vec3 uBox; uniform float uT; uniform float uFall; uniform vec2 uWind; uniform float uLen;
  attribute float aSide; varying float vA;
  void main(){
    vec3 p = position;
    vec3 q = p * uBox + vec3(uWind.x * uT, -uFall * uT, uWind.y * uT);
    q = mod(q, uBox) - 0.5 * uBox;
    vec3 w = uC + q;
    w.y = max(w.y, 0.0) + 0.0;
    float edge = 1.0 - smoothstep(0.35, 0.5, length(q.xz) / uBox.x);
    vA = edge;
    vec3 tail = vec3(-uWind.x, uFall, -uWind.y) * uLen * aSide;
    vec4 mv = modelViewMatrix * vec4(w + tail, 1.0);
    gl_Position = projectionMatrix * mv;
    gl_PointSize = 2.6 * aSide;
  }`;
function initWeather() {
  const N = 2600, pos = new Float32Array(N * 2 * 3), side = new Float32Array(N * 2);
  for (let i = 0; i < N; i++) { const a = Math.random(), b = Math.random(), c = Math.random(); for (let e = 0; e < 2; e++) { pos.set([a, b, c], (i * 2 + e) * 3); side[i * 2 + e] = e } }
  const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.BufferAttribute(pos, 3)); g.setAttribute('aSide', new THREE.BufferAttribute(side, 1));
  rainM = new THREE.LineSegments(g, new THREE.ShaderMaterial({
    transparent: true, depthWrite: false, uniforms: { uC: { value: new THREE.Vector3() }, uBox: { value: new THREE.Vector3(40, 26, 40) }, uT: { value: 0 }, uFall: { value: 22 }, uWind: { value: new THREE.Vector2(3, 1) }, uLen: { value: 0.045 }, uOp: { value: 0 } },
    vertexShader: WX_VERT, fragmentShader: `uniform float uOp; varying float vA; void main(){ gl_FragColor = vec4(0.78, 0.86, 0.95, 0.5 * uOp * vA); }` }));
  rainM.frustumCulled = false; rainM.renderOrder = 7; rainM.visible = false; scene.add(rainM);
  const M = 2200, sp = new Float32Array(M * 3), ss = new Float32Array(M).fill(1);
  for (let i = 0; i < M; i++) sp.set([Math.random(), Math.random(), Math.random()], i * 3);
  const g2 = new THREE.BufferGeometry(); g2.setAttribute('position', new THREE.BufferAttribute(sp, 3)); g2.setAttribute('aSide', new THREE.BufferAttribute(ss, 1));
  snowM = new THREE.Points(g2, new THREE.ShaderMaterial({
    transparent: true, depthWrite: false, uniforms: { uC: { value: new THREE.Vector3() }, uBox: { value: new THREE.Vector3(40, 22, 40) }, uT: { value: 0 }, uFall: { value: 1.7 }, uWind: { value: new THREE.Vector2(0.8, 0.3) }, uLen: { value: 0.0 }, uOp: { value: 0 } },
    vertexShader: WX_VERT.replace('gl_PointSize = 2.6 * aSide;', 'gl_PointSize = 3.4;'),
    fragmentShader: `uniform float uOp; varying float vA; void main(){ float d = length(gl_PointCoord - 0.5); if (d > 0.5) discard; gl_FragColor = vec4(1.0, 1.0, 1.0, 0.9 * uOp * vA * smoothstep(0.5, 0.2, d)); }` }));
  snowM.frustumCulled = false; snowM.renderOrder = 7; snowM.visible = false; scene.add(snowM);
}
function drawWeather() {
  if (!rainM) return;
  const near = !ugView && cam.z > 0.3;
  const box = clamp(camDist() * 1.5 + 8, 22, 70), gy = Math.max(hAt(cam.tx, cam.ty), WATER_Y);
  const t = T / 1000;
  const live = wxVis.live;
  rainM.visible = near && wxVis.rain * live > 0.02;
  if (rainM.visible) {
    const u = rainM.material.uniforms;
    u.uC.value.set(cam.tx, gy + box * 0.35, cam.ty); u.uBox.value.set(box, box * 0.8, box); u.uT.value = t; u.uOp.value = clamp(wxVis.rain * live * 1.2, 0, 1);
    u.uWind.value.set(2 + 5 * wxVis.storm, 1 + 2 * wxVis.storm); u.uLen.value = 0.05 + 0.03 * wxVis.storm;
  }
  snowM.visible = near && wxVis.snow * live > 0.02;
  if (snowM.visible) {
    const u = snowM.material.uniforms;
    u.uC.value.set(cam.tx, gy + box * 0.3, cam.ty); u.uBox.value.set(box, box * 0.7, box); u.uT.value = t; u.uOp.value = clamp(wxVis.snow * live, 0, 1);
    u.uWind.value.set(Math.sin(t * 0.3) * 1.2, Math.cos(t * 0.23) * 0.8);
  }
}
/* leaves go yellow and fall bare, palms bleach, and snow lies on what is left */
const LEAF_TINT = [[0.74, 0.70, 0.62], [0.92, 1.10, 0.82], [1.05, 0.98, 0.72], [1.40, 0.92, 0.50]];   /* winter, spring, summer, autumn */
function tintSeason() {
  const season = seasonOf(G.month), cov10 = Math.round(wxVis.cover * 10);
  if (season === wxVis.season && cov10 === wxVis.cov10) return;
  wxVis.season = season; wxVis.cov10 = cov10;
  const [r, g, b] = LEAF_TINT[season], c = wxVis.cover * 0.55;
  for (const k of deco.k.values()) for (const m of k.meshes) {
    const nm = m.userData.part && m.userData.part.mat;
    if (nm && /^(leaf|frond)/.test(nm)) m.material.color.setRGB(r + (1 - r) * c, g + (1 - g) * c, b + (1 - b) * c);
  }
}
const _sunDir = new THREE.Vector3();
function paintScene() {
  updateWeatherVis();
  const L = sunLight();
  NIGHT.value = L.night;
  const day = clamp(L.day, 0, 1);
  /* azimuth sweeps east -> south -> west across the day; elevation from the clock */
  const p = dayFrac(), az = (p - 0.25) * 2 * Math.PI;           /* 0 at sunrise */
  const el = clamp(L.elev, -1, 1);
  const up = Math.max(0.10, 0.18 + 0.82 * Math.max(0, el));
  _sunDir.set(Math.cos(az) * 0.95, up * 1.15, -Math.sin(az) * 0.6 + 0.45).normalize();
  if (L.night > 0.5) _sunDir.set(-0.4, 0.8, 0.45).normalize();    /* the moon, fixed */
  sun.color.setHex(L.night > 0.5 ? 0x8fa4d8 : L.col);
  const ov = ugView ? 0 : wxVis.cloud;
  sun.intensity = (day * 2.35 + L.night * 0.62) * (1 - 0.62 * ov);
  const cx = Math.round(cam.tx), cz = Math.round(cam.ty);
  sun.target.position.set(cx, 0, cz);
  sun.position.set(cx + _sunDir.x * 70, _sunDir.y * 70, cz + _sunDir.z * 70);
  sun.target.updateMatrixWorld();
  const ext = clamp(camDist() * 0.95, 12, 58);
  const sc = sun.shadow.camera;
  if (Math.abs(sc.right - ext) > 1) { sc.left = -ext; sc.right = ext; sc.top = ext; sc.bottom = -ext; sc.updateProjectionMatrix() }
  sun.castShadow = day > 0.12 && !ugView;
  hemi.intensity = ugView ? 0.95 : (0.18 + 0.40 * day + 0.34 * L.night) * (1 + 0.25 * ov) + wxVis.flash * 1.4;
  if (sun.shadow && 'intensity' in sun.shadow) sun.shadow.intensity = 1 - 0.85 * ov;
  hemi.color.setHex(mixCol(0xdfeaf0, L.col, 0.35)); hemi.groundColor.setHex(0xb59f78);
  scene.environmentIntensity = ugView ? 0.35 : 0.08 + 0.28 * day + 0.10 * L.night;
  /* the sky: the washed light colour, a touch of sea blue, dark at night */
  const sky0 = mixCol(mulCol(0xa9d2e8, L.col), L.sky, 0.25 + 0.5 * L.night);
  /* overcast greys the sky towards slate, a fall of snow towards white, a flash of lightning to a glare */
  const grey = mixCol(0x8c979f, 0x1a202a, L.night * 0.85), sky1 = mixCol(sky0, mixCol(grey, 0xe4e9ec, wxVis.snow * 0.55), ov * 0.78);
  const sky = wxVis.flash > 0.02 ? mixCol(sky1, 0xffffff, wxVis.flash * 0.55) : sky1;
  const bg = ugView ? 0x121a22 : sky;
  const bgF = wxVis.fog > 0.01 && !ugView ? mixCol(bg, 0xc9d0d3, wxVis.fog * 0.65) : bg;
  scene.background.setHex(bgF); scene.fog.color.setHex(bgF);
  scene.fog.near = 55 * (1 - 0.55 * Math.max(wxVis.rain, wxVis.snow)) * (1 - 0.85 * wxVis.fog); scene.fog.far = 330 * (1 - 0.5 * Math.max(wxVis.rain, wxVis.snow * 0.8)) * (1 - 0.72 * wxVis.fog);
  if (skyM) {
    const u = skyM.material.uniforms;
    u.uHor.value.setHex(bg);
    u.uTop.value.setHex(mixCol(mixCol(mixCol(0x2e6fb0, 0xffffff, 0.10), 0x07122c, L.night * 0.92), grey, ov * 0.85));
    u.uSunDir.value.copy(_sunDir); u.uSun.value.setHex(L.col);
    u.uGlow.value = L.night > 0.5 ? 0 : clamp(day, 0, 1);
  }
  /* the ground takes the season's tint; the sea takes the clock's */
  const gSeason = mulCol(SEASON[seasonOf(G.month)].g, 0xffffff);
  /* snow lies on the ground, rain darkens it */
  groundMesh.material.color.setHex(ugView ? 0xa9bcc7 : mulCol(gSeason, mixCol(0xffffff, 0x9a9a9a, wxVis.wet * 0.45)));
  groundSnow.value = ugView ? 0 : wxVis.cover;
  if (!ugView) tintSeason();
  waterU.uDeep.value.setHex(mixCol(0x2f86a6, L.sky, 0.55 * L.night + 0.18));
  waterU.uTime.value = T / 1000;
}

  /* ======================================================================
   SKY — a gradient dome, hazy at the horizon where the fog ends and deeper
   overhead, with a glow round the sun. It follows the camera.
   ====================================================================== */
let skyM = null;
function initSky() {
  skyM = new THREE.Mesh(new THREE.SphereGeometry(1, 40, 20), new THREE.ShaderMaterial({
    side: THREE.BackSide, depthWrite: false, fog: false,
    uniforms: { uTop: { value: new THREE.Color(0x4f86b5) }, uHor: { value: new THREE.Color(0xa9d2e8) },
                uSunDir: { value: new THREE.Vector3(0, 1, 0) }, uSun: { value: new THREE.Color(0xfff1dc) }, uGlow: { value: 0 } },
    vertexShader: `varying vec3 vD; void main(){ vD = normalize(position); gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0); gl_Position.z = gl_Position.w; }`,
    fragmentShader: `varying vec3 vD; uniform vec3 uTop, uHor, uSun, uSunDir; uniform float uGlow;
      void main(){
        vec3 d = normalize(vD); float h = clamp(d.y, 0.0, 1.0);
        vec3 c = mix(uHor, uTop, pow(h, 0.5));
        float s = max(dot(d, normalize(uSunDir)), 0.0);
        c += uSun * (pow(s, 40.0) * 0.55 + pow(s, 5.0) * 0.10) * uGlow;
        gl_FragColor = vec4(c, 1.0);
        #include <tonemapping_fragment>
        #include <colorspace_fragment>
      }`,
  }));
  skyM.renderOrder = -100; skyM.frustumCulled = false; scene.add(skyM);
}

/* ======================================================================
   UNDERGROUND VIEW
   ====================================================================== */
window.applyView = () => {
  if (!scene) return;
  const m = groundMesh && groundMesh.material;
  if (m) { m.transparent = ugView; m.opacity = ugView ? 0.22 : 1; m.depthWrite = !ugView; m.needsUpdate = true }
  if (soilMesh) soilMesh.visible = ugView;
  if (aqMesh) aqMesh.visible = ugView;
  if (waterMesh) waterMesh.visible = !ugView;
  surf.setXray(ugView);                  /* the surface stays, as glass: streets, buildings, plants */
  surf.group.visible = true;
  deco.group.visible = !ugView;
  if (grp.anim) grp.anim.visible = !ugView;
  under.group.visible = ugView;          /* hidden by the ground otherwise — do not pay for them */
  const lg = $('ugLegend'); if (lg) lg.classList.toggle('on', ugView);
  const b = $('bUnder'); if (b) b.setAttribute('aria-pressed', String(ugView));
};
window.setView = on => {
  if (ugView === on) return;
  ugView = on; applyView();
  note(ugView ? 'Yeraltı görünüş — üst qat şüşə kimi görünür; kəmər, kabel və metro tuneli altındadır.' : 'Səth görünüşü.');
  if (window.sfx) sfx(ugView ? 'ugOn' : 'ugOff');
};

/* ======================================================================
   THE FRAME
   ====================================================================== */
window.render = () => {
  if (!ready) return;
  if (dirtyTerrain) { dirtyTerrain = false; buildTerrain(); mmBase = null; dirtyMini = true; dirtyOrder = true }
  updateCamera();
  updateCull();
  if (dirtyOrder || rise.size) syncBuildings();
  syncDeco();
  if (skyM) { skyM.position.copy(camera.position); skyM.scale.setScalar(camera.far * 0.92); skyM.visible = !ugView }
  if (dirtyOver) drawOverlay();
  if (dirtyWire) drawWires();
  wireM && (wireM.visible = !ugView);
  drawCursor(); updateLabels(); drawLive(); drawFlow(); drawLamps(); drawPlanes(); drawAlerts(); drawWeather(); drawAnim();
  drawClouds();
  paintScene();
  if (window.sfxFrame) sfxFrame({ sites: isPaused() ? 0 : siteCount, ug: ugView, zoom: cam.z, night: sunLight().night, x: cam.tx, z: cam.ty,
    rain: wxVis.rain * wxVis.live, snow: wxVis.snow * wxVis.live, storm: wxVis.storm * wxVis.live, cloud: wxVis.cloud, paused: isPaused() });
  renderer.render(scene, camera);
  watchFrameTime();
};


/* ======================================================================
   THE WALLED CITY'S GHOST — while its tool is in hand, the whole of İçərişəhər (wall, towers,
   lanes) as one translucent mesh follows the cursor, green where it can stand and red where not.
   ====================================================================== */
let oldGhostGeo = null, oldGhostMesh = null;
function oldGhostGeometry() {
  if (oldGhostGeo) return oldGhostGeo;
  const geos = [], m4 = new THREE.Matrix4(), q = new THREE.Quaternion(), p = new THREE.Vector3(), sc = new THREE.Vector3();
  for (const [key, x, y] of oldLayout()) {
    const pd = DEFS[key], model = MODELS.get(pd.spr); if (!model) continue;
    const f = /^(wall_|gate_)/.test(key) ? 1 : BSCALE;
    m4.compose(p.set(x + pd.w / 2, 0, y + pd.h / 2), q.identity(), sc.set(f, f, f));
    for (const part of model.parts) { const g = part.geo.clone(); g.applyMatrix4(m4); geos.push(g) }
  }
  return oldGhostGeo = mergeGeometries(geos, false);
}
function setOldGhost(on, ok, x, y) {
  if (!on) { if (oldGhostMesh) oldGhostMesh.visible = false; return }
  if (!oldGhostMesh) { oldGhostMesh = new THREE.Mesh(oldGhostGeometry(), GHOST_OK); oldGhostMesh.renderOrder = 8; curG.add(oldGhostMesh) }
  oldGhostMesh.material = ok ? GHOST_OK : GHOST_NO; oldGhostMesh.visible = true;
  const d = DEFS.icheri;
  oldGhostMesh.position.set(x, Math.max(hAt(x + d.w / 2, y + d.h / 2), WATER_Y), y);
}

/* ======================================================================
   CLOUDS — soft puffs drifting over the peninsula, there to give the far view
   a sense of scale: a tile is about 40 m and a cloud is a kilometre across.
   They fade in as the camera pulls back, are gone up close (they would
   only get in the way) and in the underground view, and take the colour of the
   light, so they go slate-blue at night. Drift follows the wall clock, not the
   game speed. One InstancedMesh, about 500 quads.
   ====================================================================== */
const CLOUD_Y = 11, CLOUD_CLUSTERS = 22, CLOUD_SPAN = 140;
let cloudM = null, cloudMat = null;
const cloudPuffs = [];
function cloudTexture() {
  const c = document.createElement('canvas'); c.width = c.height = 256;
  const g = c.getContext('2d');
  for (let i = 0; i < 26; i++) {
    const a = hash2(i, 3, 91) * Math.PI * 2, r = Math.pow(hash2(i, 5, 92), 0.7) * 62;
    const x = 128 + Math.cos(a) * r * 1.25, y = 128 + Math.sin(a) * r * 0.8, rad = 34 + hash2(i, 7, 93) * 40;
    const gr = g.createRadialGradient(x, y, 0, x, y, rad);
    gr.addColorStop(0, 'rgba(255,255,255,0.42)'); gr.addColorStop(0.55, 'rgba(255,255,255,0.20)'); gr.addColorStop(1, 'rgba(255,255,255,0)');
    g.fillStyle = gr; g.fillRect(0, 0, 256, 256);
  }
  const t = new THREE.CanvasTexture(c); t.colorSpace = THREE.SRGBColorSpace; return t;
}
function initClouds() {
  const g = new THREE.PlaneGeometry(1, 1); g.rotateX(-Math.PI / 2);
  cloudMat = new THREE.MeshBasicMaterial({ map: cloudTexture(), transparent: true, depthWrite: false, fog: false, toneMapped: false, opacity: 0 });
  const W = CLOUD_SPAN, H = CLOUD_SPAN;
  for (let c = 0; c < CLOUD_CLUSTERS; c++) {
    const cx = hash2(c, 1, 81) * W, cz = hash2(c, 2, 82) * H, n = 4 + ((hash2(c, 3, 83) * 4) | 0);
    for (let k = 0; k < n; k++) {
      const a = hash2(c, k + 10, 84) * Math.PI * 2, r = hash2(c, k + 30, 85) * 11;
      cloudPuffs.push({ x: cx + Math.cos(a) * r * 1.5, z: cz + Math.sin(a) * r, s: 7 + hash2(c, k + 50, 86) * 8,
                        yaw: (hash2(c, k + 70, 87) - 0.5) * 0.9, dy: hash2(c, k, 88) * 1.6 });
    }
  }
  cloudM = new THREE.InstancedMesh(g, cloudMat, cloudPuffs.length);
  cloudM.name = 'clouds'; cloudM.frustumCulled = false; cloudM.renderOrder = 6; cloudM.visible = false; scene.add(cloudM);
}
const _cq = new THREE.Quaternion(), _cp = new THREE.Vector3(), _cs = new THREE.Vector3(), _cm = new THREE.Matrix4();
function drawClouds() {
  if (!cloudM) return;
  /* during a new game's flight the deck is thick, higher than the city, and thins out as the camera passes it */
  const iu = window.__intro && window.__introClouds && window.__introU != null ? window.__introU : -1;
  let a = ugView ? 0 : clamp((0.62 - cam.z) / 0.30, 0, 1);
  if (iu >= 0) a = clamp((0.86 - iu) / 0.30, 0, 1);
  cloudM.visible = a > 0.01;
  if (!cloudM.visible) return;
  const L = sunLight();
  cloudMat.color.setHex(mixCol(mixCol(0xffffff, L.col, 0.12), 0x1b2540, clamp(L.night * 0.85, 0, 1)));
  cloudMat.opacity = a * (0.7 + 0.25 * wxVis.cloud);
  if (wxVis.cloud > 0.05) cloudMat.color.setHex(mixCol(cloudMat.color.getHex(), 0x6f7981, wxVis.cloud * 0.55));
  const t = animT + 500, W = iu >= 0 ? 300 : CLOUD_SPAN, H = W, kx = W / CLOUD_SPAN;     /* the world's clock: it stops with the game */
  const wrap = (v, m) => ((v % m) + m) % m;
  for (let i = 0; i < cloudPuffs.length; i++) {
    const p = cloudPuffs[i];
    _cp.set(cam.tx + wrap(p.x * kx + t * 0.5 - cam.tx, W) - W / 2, iu >= 0 ? 34 + p.dy * 8.75 : CLOUD_Y + p.dy, cam.ty + wrap(p.z * kx + t * 0.18 - cam.ty, H) - H / 2);
    _cq.setFromAxisAngle(Y_AXIS, p.yaw); _cs.set(p.s * 1.25 * (iu >= 0 ? 3.0 : 1), 1, p.s * 0.85 * (iu >= 0 ? 3.0 : 1));
    _cm.compose(_cp, _cq, _cs); cloudM.setMatrixAt(i, _cm);
  }
  cloudM.instanceMatrix.needsUpdate = true;
}

/* ======================================================================
   THUMBNAILS — the dock and the monument cards show each model. They are
   rendered once, on demand, by a second small renderer, and cached.
   ====================================================================== */
let tr = null, trScene = null, trCam = null;
const thumbMap = new Map();
function thumbBitmap(name) {
  if (thumbMap.has(name)) return thumbMap.get(name);
  const model = MODELS.get(name);
  let out = null;
  if (model) {
    if (!tr) {
      tr = new THREE.WebGLRenderer({ alpha: true, antialias: true, preserveDrawingBuffer: true });
      tr.setSize(256, 192, false); tr.setClearColor(0x000000, 0);
      tr.outputColorSpace = THREE.SRGBColorSpace;
      tr.toneMapping = THREE.ACESFilmicToneMapping; tr.toneMappingExposure = 0.95;
      trScene = new THREE.Scene();
      trScene.environment = new THREE.PMREMGenerator(tr).fromScene(new RoomEnvironment(), 0.04).texture;
      trScene.environmentIntensity = 0.45;
      trScene.add(new THREE.HemisphereLight(0xdfeaf0, 0xb59f78, 0.55));
      const dl = new THREE.DirectionalLight(0xfff1dc, 2.2); dl.position.set(-4, 7, 5); trScene.add(dl);
      trCam = new THREE.OrthographicCamera(-1, 1, 1, -1, 0.1, 200);
    }
    const g = new THREE.Group();
    for (const part of model.parts) g.add(new THREE.Mesh(part.geo, buildMaterial(part.mat, matData.materials)));
    trScene.add(g);
    const [x0, x1, z0, z1] = model.box, h = model.h;
    const cx = (x0 + x1) / 2, cz = (z0 + z1) / 2, cy = h / 2;
    const dir = new THREE.Vector3(Math.sin(Math.PI / 4) * Math.cos(0.58), Math.sin(0.58), Math.cos(Math.PI / 4) * Math.cos(0.58));
    trCam.position.set(cx + dir.x * 40, cy + dir.y * 40, cz + dir.z * 40);
    trCam.lookAt(cx, cy, cz); trCam.updateMatrixWorld(); trCam.matrixWorldInverse.copy(trCam.matrixWorld).invert();
    let mnx = 1e9, mxx = -1e9, mny = 1e9, mxy = -1e9;
    for (const X of [x0, x1]) for (const Y of [0, h]) for (const Z of [z0, z1]) {
      const v = new THREE.Vector3(X, Y, Z).applyMatrix4(trCam.matrixWorldInverse);
      mnx = Math.min(mnx, v.x); mxx = Math.max(mxx, v.x); mny = Math.min(mny, v.y); mxy = Math.max(mxy, v.y);
    }
    const w = (mxx - mnx) * 1.08 + 0.1, hh = (mxy - mny) * 1.08 + 0.1, asp = 256 / 192;
    const fw = Math.max(w, hh * asp), fh = fw / asp, mx = (mnx + mxx) / 2, my = (mny + mxy) / 2;
    trCam.left = mx - fw / 2; trCam.right = mx + fw / 2; trCam.top = my + fh / 2; trCam.bottom = my - fh / 2;
    trCam.updateProjectionMatrix();
    tr.render(trScene, trCam);
    out = document.createElement('canvas'); out.width = 256; out.height = 192;
    out.getContext('2d').drawImage(tr.domElement, 0, 0);
    trScene.remove(g);
  }
  thumbMap.set(name, out);
  return out;
}
const TSWATCH = { t_sand: 0xe0d0a6, t_plain0: 0xc4b585, t_marsh: 0x767f65 };
window.thumb = (canvas, name, bw, bh) => {
  const dpr = Math.min(2, devicePixelRatio || 1);
  canvas.width = bw * dpr; canvas.height = bh * dpr;
  const d = canvas.getContext('2d');
  d.setTransform(dpr, 0, 0, dpr, 0, 0); d.clearRect(0, 0, bw, bh);
  const bm = thumbBitmap(name);
  if (bm) {
    d.imageSmoothingQuality = 'high';
    const k = Math.min(bw / bm.width, bh / bm.height);
    d.drawImage(bm, (bw - bm.width * k) / 2, bh - bm.height * k, bm.width * k, bm.height * k);
  } else {                                       /* a terrain swatch for the land tools */
    const c = TSWATCH[name] || 0xc4b585;
    d.fillStyle = '#' + c.toString(16).padStart(6, '0');
    d.beginPath(); d.moveTo(bw / 2, bh * 0.15); d.lineTo(bw * 0.92, bh / 2); d.lineTo(bw / 2, bh * 0.85); d.lineTo(bw * 0.08, bh / 2);
    d.closePath(); d.fill();
  }
};

/* ======================================================================
   CURSOR — hover footprint, the planned route, a dragged rectangle, the
   selection and the translucent model of what is about to be built
   ====================================================================== */
const MAXQ = 900;
let curG, quads, outline, ringM, ghostG = null, ghostName = '', ghostOk = null;
const GHOST_OK = new THREE.MeshStandardMaterial({ color: 0x7dffb0, transparent: true, opacity: 0.55, depthWrite: false, roughness: 0.6 });
const GHOST_NO = new THREE.MeshStandardMaterial({ color: 0xff7a66, transparent: true, opacity: 0.55, depthWrite: false, roughness: 0.6 });
const _col = new THREE.Color();
function initCursor() {
  curG = new THREE.Group(); scene.add(curG);
  const pg = new THREE.PlaneGeometry(0.94, 0.94); pg.rotateX(-Math.PI / 2);
  quads = new THREE.InstancedMesh(pg, new THREE.MeshBasicMaterial({ transparent: true, opacity: 0.46, depthWrite: false, toneMapped: false }), MAXQ);
  quads.instanceColor = new THREE.InstancedBufferAttribute(new Float32Array(MAXQ * 3), 3);
  quads.frustumCulled = false; quads.renderOrder = 10; quads.count = 0; curG.add(quads);
  const og = new THREE.BufferGeometry();
  og.setAttribute('position', new THREE.BufferAttribute(new Float32Array(8 * 3 * 4), 3));
  outline = new THREE.LineSegments(og, new THREE.LineBasicMaterial({ color: 0x14b3c2, toneMapped: false, depthTest: false }));
  outline.frustumCulled = false; outline.renderOrder = 11; curG.add(outline);
  const rg = new THREE.RingGeometry(0.985, 1, 96); rg.rotateX(-Math.PI / 2);
  ringM = new THREE.Mesh(rg, new THREE.MeshBasicMaterial({ color: 0x2ca064, transparent: true, opacity: 0.6, depthWrite: false, toneMapped: false, side: THREE.DoubleSide }));
  ringM.renderOrder = 9; ringM.visible = false; curG.add(ringM);
}
let nq = 0;
function qTile(x, y, hex, a) {
  if (nq >= MAXQ) return;
  _m.makeTranslation(x + 0.5, Math.max(hAt(x + 0.5, y + 0.5), WATER_Y) + 0.05, y + 0.5); quads.setMatrixAt(nq, _m);
  quads.setColorAt(nq, _col.setHex(hex)); nq++;
}
function boxOutline(x, y, w, h) {
  const pa = outline.geometry.attributes.position.array;
  const c = [[x, y], [x + w, y], [x + w, y + h], [x, y + h]];
  let i = 0;
  for (let k = 0; k < 4; k++) {
    const a = c[k], b = c[(k + 1) % 4];
    pa[i++] = a[0]; pa[i++] = hAt(a[0], a[1]) + 0.07; pa[i++] = a[1]; pa[i++] = b[0]; pa[i++] = hAt(b[0], b[1]) + 0.07; pa[i++] = b[1];
  }
  outline.geometry.setDrawRange(0, 8); outline.geometry.attributes.position.needsUpdate = true; outline.visible = true;
}
function setRing(cx, cy, r, hex) {
  ringM.visible = true; ringM.position.set(cx, Math.max(hAt(cx, cy), WATER_Y) + 0.06, cy); ringM.scale.set(r, 1, r); ringM.material.color.setHex(hex);
}
function setGhost(name, ok, cx, cy, yaw) {
  if (!name) { if (ghostG) ghostG.visible = false; return }
  if (name !== ghostName) {
    if (ghostG) { curG.remove(ghostG) }
    ghostG = null; ghostName = name;
    const model = MODELS.get(name);
    if (model) {
      ghostG = new THREE.Group();
      for (const part of model.parts) {
        const m = new THREE.Mesh(part.geo, GHOST_OK); m.userData.part = true; ghostG.add(m);
      }
      curG.add(ghostG); ghostOk = null;
    }
  }
  if (!ghostG) return;
  if (ghostOk !== ok) { for (const m of ghostG.children) m.material = ok ? GHOST_OK : GHOST_NO; ghostOk = ok }
  ghostG.visible = true; ghostG.position.set(cx, Math.max(hAt(cx, cy), WATER_Y), cy); ghostG.rotation.y = yaw;
  const gd = DEFS[tool]; const gs = gd && !DRAPE_RE.test(ghostName) && !(gd.road || gd.rail || gd.under || gd.tunnel || gd.conduct || gd.pipe) ? BSCALE : 1; ghostG.scale.set(gs, gs, gs);
}
function drawCursor() {
  nq = 0; outline.visible = false; ringM.visible = false; setOldGhost(false);
  let ghost = null;
  if (sel) {
    const b = bldAt(sel.x, sel.y), o = b ? b : { x: sel.x, y: sel.y, w: 1, h: 1 };
    boxOutline(o.x, o.y, o.w, o.h);
    const d = b ? DEFS[b.key] : null;
    if (d && d.radius) setRing(o.x + o.w / 2, o.y + o.h / 2, d.radius * (d.svc ? (0.65 + 0.35 * (G.fund[d.svc] || 1)) : 1), 0x14b3c2);
  }
  if (plan) {
    for (const c of planInfo().cells) qTile(c.x, c.y, c.st === 0 ? 0x2ca064 : c.st === 1 ? 0x8f9a94 : c.st === 3 ? 0xe0a030 : 0xbe3a2a);
  } else if (rect) {
    const x0 = Math.min(rect.a.x, rect.b.x), x1 = Math.max(rect.a.x, rect.b.x);
    const y0 = Math.min(rect.a.y, rect.b.y), y1 = Math.max(rect.a.y, rect.b.y);
    const col = tool === 'bulldoze' ? 0xbe3a2a : 0x2ca064;
    for (let y = y0; y <= y1; y++) for (let x = x0; x <= x1; x++) qTile(x, y, col);
  } else if (hover.x >= 0) {
    const d = DEFS[tool];
    if (d && d.tool) {
      if (tool === 'bulldoze') {
        const b = bldAt(hover.x, hover.y), ok = b && !DEFS[b.key].fixed && !DEFS[b.key].unique;
        const o = b ? b : { x: hover.x, y: hover.y, w: 1, h: 1 };
        for (let y = o.y; y < o.y + o.h; y++) for (let x = o.x; x < o.x + o.w; x++) qTile(x, y, ok ? 0xbe3a2a : 0x8a8a8a);
      } else qTile(hover.x, hover.y, 0xdfe5e2);
    } else if (d && d.terra) {
      qTile(hover.x, hover.y, d.terra === 'fill' ? 0xd8c48a : d.terra === 'dig' ? 0x3a9ec4 : 0x7fa05a);
    } else if (d) {
      const chk = canPlace(tool, hover.x, hover.y, d.layout ? 0 : brushRot);
      const gw = effW(d, d.layout ? 0 : brushRot), gh = effH(d, d.layout ? 0 : brushRot);
      if (d.layout) setOldGhost(true, chk.ok, hover.x, hover.y);
      for (let y = hover.y; y < hover.y + gh; y++) for (let x = hover.x; x < hover.x + gw; x++)
        qTile(x, y, chk.ok ? 0x2ca064 : 0xbe3a2a);
      if (d.radius) setRing(hover.x + gw / 2, hover.y + gh / 2, d.radius, chk.ok ? 0x2ca064 : 0xbe3a2a);
      /* the real model, ghosted, for anything with a body */
      if (!isLineTool(d)) {
        const probe = { key: tool, x: hover.x, y: hover.y, w: gw, h: gh, rot: brushRot, lvl: 1, var: 0, rm: 15 };
        const nm = (d.zone || d.road || d.prom || d.pipe || d.conduct || d.tunnel || d.rail || d.layout) ? null : modelFor(probe);
        if (nm) ghost = [nm, chk.ok, hover.x + gw / 2, hover.y + gh / 2, -brushRot * Math.PI / 2];
      }
    }
  }
  if (ghost) setGhost(...ghost); else setGhost(null);
  quads.count = nq; quads.instanceMatrix.needsUpdate = true;
  if (quads.instanceColor) quads.instanceColor.needsUpdate = true;
}

/* ======================================================================
   DATA LAYERS — power, water, pollution, land value, traffic. One texel a
   tile, laid over the ground.
   ====================================================================== */
let ovMesh = null, ovTex = null, ovData = null;
/* the data layers lie on the ground, not above it */
function syncOverlayHeights() {
  if (!ovMesh || !HV) return;
  const pa = ovMesh.geometry.attributes.position.array;
  for (let v = 0; v < VX * VZ; v++) pa[v * 3 + 1] = Math.max(HV[v], WATER_Y) + 0.05;
  ovMesh.geometry.attributes.position.needsUpdate = true;
}
window.drawOverlay = function drawOverlay() {
  if (!ovMesh) {
    ovData = new Uint8Array(GW * GH * 4);
    ovTex = new THREE.DataTexture(ovData, GW, GH, THREE.RGBAFormat, THREE.UnsignedByteType);
    ovTex.magFilter = ovTex.minFilter = THREE.NearestFilter;
    const pg = new THREE.PlaneGeometry(GW, GH, GW, GH); pg.rotateX(-Math.PI / 2); pg.translate(GW / 2, 0, GH / 2);
    ovMesh = new THREE.Mesh(pg, new THREE.MeshBasicMaterial({ map: ovTex, transparent: true, depthWrite: false, toneMapped: false }));
    ovMesh.renderOrder = 5; scene.add(ovMesh); syncOverlayHeights();
  }
  ovMesh.visible = overlay !== 'none';
  if (overlay !== 'none') {
    ovData.fill(0);
    for (let y = 0; y < GH; y++) for (let x = 0; x < GW; x++) {
      const i = y * GW + x, t = G.tiles[i];
      if (isWater(t.t)) continue;
      let a = 0, col = 0;
      if (overlay === 'poll') { a = Math.min(1, gPoll[i]) * 0.62; col = 0x96602f }
      else if (overlay === 'value') { a = Math.min(1, gJoy[i] * 0.4 + gEdu[i] * 0.3 + gHealth[i] * 0.3) * 0.55; col = 0x46966c }
      else if (overlay === 'power') { if (pwDist[i] < 0) continue; a = 0.18 + 0.44 * Math.max(0, 1 - pwDist[i] / 45); col = 0xe0a52a }
      else if (overlay === 'water') { if (wtDist[i] < 0) continue; a = 0.20 + 0.40 * (1 - wtDist[i] / 3); col = 0x3a9ec4 }
      else if (overlay === 'traf') {
        const v = gTraf[i]; if (v <= 0.02) continue;
        a = Math.min(0.72, 0.14 + v * 0.42);
        col = v < 0.6 ? 0x4f9e5a : v < 1.0 ? 0xd8a32b : v < 1.5 ? 0xd2571c : 0xa32020;
      }
      if (a <= 0.02) continue;
      const o = ((GH - 1 - y) * GW + x) * 4;          /* the plane's v runs south to north */
      ovData[o] = col >> 16 & 255; ovData[o + 1] = col >> 8 & 255; ovData[o + 2] = col & 255; ovData[o + 3] = a * 255;
    }
    ovTex.needsUpdate = true;
  }
  dirtyOver = false;
};

/* ======================================================================
   OVERHEAD LINES — catenaries between neighbouring pylons
   ====================================================================== */
let wireM = null;
function drawWires() {
  if (!wireM) {
    wireM = new THREE.LineSegments(new THREE.BufferGeometry(), new THREE.LineBasicMaterial({ color: 0x2b3633, transparent: true, opacity: 0.8 }));
    wireM.frustumCulled = false; scene.add(wireM);
  }
  const top = (MODELS.get('pylon') ? MODELS.get('pylon').h : 1.55) * 0.96, pts = [];
  const seg = 10;
  for (const b of G.blds) {
    if (!b) continue;
    const d = DEFS[b.key]; if (!d.conduct || d.under) continue;
    for (const [dx, dy] of [[1, 0], [0, 1]]) {
      const n = bldAt(b.x + dx, b.y + dy);
      if (!n || !DEFS[n.key].conduct || DEFS[n.key].under) continue;
      for (const off of [-0.06, 0.06]) {
        const ox = dy ? off : 0, oz = dx ? off : 0;
        for (let k = 0; k < seg; k++) {
          const t0 = k / seg, t1 = (k + 1) / seg;
          for (const t of [t0, t1])
            pts.push(b.x + 0.5 + dx * t + ox, hAt(b.x + 0.5 + dx * t, b.y + 0.5 + dy * t) + top - 0.07 * 4 * t * (1 - t), b.y + 0.5 + dy * t + oz);
        }
      }
    }
  }
  wireM.geometry.setAttribute('position', new THREE.Float32BufferAttribute(pts, 3));
  wireM.geometry.setDrawRange(0, pts.length / 3);
  dirtyWire = false;
}

/* ======================================================================
   PLACE NAMES — the real names of the peninsula, hung over the map
   ====================================================================== */
let lblRoot = null; const lbls = [];
window.buildLabels = function buildLabels() {
  if (!lblRoot) {
    lblRoot = document.createElement('div');
    lblRoot.style.cssText = 'position:absolute;inset:0;overflow:hidden;pointer-events:none;z-index:1';
    stageEl.appendChild(lblRoot);
  }
  lblRoot.textContent = ''; lbls.length = 0;
  for (const [nm, x, y, imp] of (MAP.places || [])) {
    const el = document.createElement('div');
    const major = imp >= 2, region = imp === 0;
    el.textContent = region ? nm.toUpperCase() : nm;
    el.style.cssText = 'position:absolute;left:0;top:0;white-space:nowrap;will-change:transform;' +
      'font:' + (region ? 500 : major ? 600 : 500) + ' ' + (region ? 13 : major ? 12.5 : 11) + 'px "IBM Plex Sans",system-ui,sans-serif;' +
      'letter-spacing:' + (region ? '.17em' : '.01em') + ';color:' + (region ? '#2b6b7a' : major ? '#2e3a34' : '#46534d') + ';' +
      'text-shadow:0 0 3px #fff6e6,0 0 3px #fff6e6,0 0 4px #fff6e6,0 0 6px #fff6e6;display:none';
    lblRoot.appendChild(el);
    lbls.push({ el, x: x + 0.5, y: y + 0.5, imp });
  }
  /* the player's own signs: plain text on a small paper tag, shown close in */
  for (const sg of (G.signs || [])) {
    const el = document.createElement('div');
    el.textContent = sg.t;
    el.style.cssText = 'position:absolute;left:0;top:0;white-space:nowrap;will-change:transform;padding:2px 7px;border-radius:6px;' +
      'font:600 11.5px "IBM Plex Sans",system-ui,sans-serif;color:#2a2f2c;background:#fff6dcee;border:1px solid #c9a95a;display:none';
    lblRoot.appendChild(el);
    lbls.push({ el, x: sg.x + 0.5, y: sg.y + 0.5, imp: 3 });
  }
};
const _v = new THREE.Vector3();
function updateLabels() {
  if (!lblRoot) return;
  lblRoot.style.display = (labelsOn && !ugView) ? '' : 'none';
  if (!labelsOn || ugView) return;
  for (const l of lbls) {
    const imp = l.imp; let vis, al = 1;
    if (imp === 0) { vis = cam.z < 0.92; al = clamp((0.92 - cam.z) / 0.22, 0, 1) * 0.95 }
    else if (imp === 2) { vis = cam.z < 1.05; al = clamp((1.05 - cam.z) / 0.22, 0, 1) }
    else if (imp === 3) { vis = cam.z < 1.6; al = clamp((1.6 - cam.z) / 0.25, 0, 1) }
    else { vis = cam.z < 0.86; al = clamp((0.86 - cam.z) / 0.20, 0, 1) * 0.88 }
    if (!vis) { l.el.style.display = 'none'; continue }
    _v.set(l.x, Math.max(hAt(l.x, l.y), WATER_Y) + 0.35, l.y).project(camera);
    if (_v.z > 1 || Math.abs(_v.x) > 1.05 || Math.abs(_v.y) > 1.05) { l.el.style.display = 'none'; continue }
    l.el.style.display = '';
    l.el.style.opacity = al;
    l.el.style.transform = 'translate(' + ((_v.x * 0.5 + 0.5) * VW).toFixed(1) + 'px,' + ((-_v.y * 0.5 + 0.5) * VH).toFixed(1) + 'px) translate(-50%,-50%)';
  }
}

/* ======================================================================
   TRAFFIC AND PEOPLE — decoration, not simulation. Agents exist only near
   the view and arrive from its edge. Vehicles are baked per heading, so a
   car is the model for the direction it is travelling.
   ====================================================================== */
const DV = [[0, -1], [1, 0], [0, 1], [-1, 0]];
const VEH = { cart: { spr: 'v_cart', spd: 0.30 }, fayton: { spr: 'v_fayton', spd: 0.34 }, auto: { spr: 'v_auto', spd: 0.55 }, car: { spr: 'v_car', spd: 0.78 },
              car2: { spr: 'v_car2', spd: 0.82 }, car3: { spr: 'v_car3', spd: 0.74 }, bus: { spr: 'v_bus', spd: 0.56 }, taxi: { spr: 'v_taxi', spd: 0.74 } };
const PED_SPR = ['v_ped', 'v_ped2'];
/* What drives where. A street's tier decides what is on it: horse carts and cabs on dirt and cobbles, motor
   cars on asphalt, and the year decides which motor cars. When a street is raised to asphalt the carts on
   it are swapped for cars on the spot, and a car that runs onto a track of dirt becomes a cart. */
const isMotor = k => k !== 'cart' && k !== 'fayton';
function motorKind(y) {
  const m = y < 1925 ? ['auto', 'auto', 'auto', 'car'] : y < 1945 ? ['auto', 'car', 'car', 'car2'] : y < 1965 ? ['car', 'car', 'car2', 'car3']
          : ['car', 'car2', 'car3', 'car2', 'car3'];
  return m[(Math.random() * m.length) | 0];
}
const tierAt = (x, y) => { const b = bldAt(x, y); return b && DEFS[b.key].road ? roadTier(DEFS[b.key]) : -1 };
const kindFor = (tier) => tier >= 2 ? motorKind(G.year) : 'cart';
const agents = [], boats = [];
let carSet = null;
const isStreet = (x, y) => { const b = bldAt(x, y); return !!(b && DEFS[b.key].road) };
const rnd1 = a => a[(Math.random() * a.length) | 0];
function nextDir(x, y, d, animal) {
  const opts = [], w = [];
  /* on a one-way street there is one way to go */
  const here = bldAt(x, y);
  if (here && DEFS[here.key].oneway) { const k = (here.rot || 0) & 3; if (isStreet(x + DV[k][0], y + DV[k][1])) return k }
  for (let k = 0; k < 4; k++) {
    if (k === (d + 2) % 4) continue;
    if (!isStreet(x + DV[k][0], y + DV[k][1])) continue;
    const nb = bldAt(x + DV[k][0], y + DV[k][1]);               /* and nobody enters it against the arrow */
    if (nb && DEFS[nb.key].oneway && ((nb.rot || 0) & 3) === (k + 2) % 4) continue;
    /* carts keep to the rutted and cobbled streets, cars to the paved ones, when there is a choice */
    const tt = animal == null ? -1 : tierAt(x + DV[k][0], y + DV[k][1]);
    opts.push(k); w.push((k === d ? 4 : 1) * (animal == null || tt < 0 ? 1 : (tt >= 2) === !animal ? 3 : 1));
  }
  if (!opts.length) return (d + 2) % 4;
  let r = Math.random() * w.reduce((a, b) => a + b, 0);
  for (let i = 0; i < opts.length; i++) { r -= w[i]; if (r <= 0) return opts[i] }
  return opts[0];
}
window.nextDir = nextDir;
/* where a tile lands in the window, and whether that is inside it with a margin */
const _w = new THREE.Vector3();
function screenTile(x, y) {
  _w.set(x + 0.5, 0.1, y + 0.5).project(camera);
  return [(_w.x * 0.5 + 0.5) * VW, (-_w.y * 0.5 + 0.5) * VH, _w.z];
}
const SPAWN_BAND = 150;
let nStreets = 0, nStreetsAt = -1e9;
function streetCount() {
  if (T - nStreetsAt > 1500) { nStreetsAt = T; nStreets = 0; for (const b of G.blds) if (b && DEFS[b.key].road) nStreets++ }
  return nStreets;
}
/* Traffic comes from somewhere. A street with nothing beside it has none: vehicles leave from the streets that
   touch a building with people or work in it, and from the depots and ranks, and nowhere else. So a road laid
   across empty ground stays empty until something is built beside it. */
const livesIn = n => { if (!n) return false; const d = DEFS[n.key]; if (d.road || d.under || d.conduct || d.rail || d.strip || d.prom || d.tunnel) return false;
  return d.zone ? (n.lvl > 0 && (n.pop > 0 || n.jobs > 0)) : !!(d.jobs || d.rank || d.depot || d.stop) };
let spawnOrig = [], spawnTaxi = [], spawnBus = [], spawnKey = '', svcMix = { taxi: 0, bus: 0 }, svcAt = -1e9;
function spawnPools() {
  const k = [cam.tx, cam.ty, cam.yaw, cam.pitch, cam.z].map(v => v.toFixed(2)).join() + '|' + streetCount() + '|' + G.blds.length + '|' + (G.tick | 0);
  if (k === spawnKey) return;
  spawnKey = k; spawnOrig.length = 0; spawnTaxi.length = 0; spawnBus.length = 0;
  let ranks = 0, stops = 0;
  for (const b of G.blds) { const d = b && DEFS[b.key]; if (d && b.served) { if (d.rank) ranks++; else if (d.bus) stops++ } }
  svcMix = { taxi: Math.min(0.28, ranks * 0.06), bus: Math.min(0.20, stops * 0.04) };
  for (const b of G.blds) {
    if (!b || !DEFS[b.key].road) continue;
    const [X, Y, z] = screenTile(b.x, b.y);
    if (z > 1 || X < -SPAWN_BAND || X > VW + SPAWN_BAND || Y < -SPAWN_BAND || Y > VH + SPAWN_BAND) continue;
    let home = false, taxi = false, bus = false;
    for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
      if (!dx && !dy) continue;
      const n = bldAt(b.x + dx, b.y + dy); if (!n || !livesIn(n)) continue;
      home = true; const nd = DEFS[n.key];
      if ((nd.rank && n.served) || nd.depot === 'taxi') taxi = true;
      if ((nd.bus && n.served) || nd.depot === 'bus') bus = true;
    }
    if (home) spawnOrig.push(b);
    if (taxi) spawnTaxi.push(b);
    if (bus) spawnBus.push(b);
  }
}
function spawnAgent(ped, seed) {
  spawnPools();
  let pool = spawnOrig, want = null;
  if (!ped) {
    const r = Math.random();
    if (r < svcMix.taxi && spawnTaxi.length) { pool = spawnTaxi; want = 'taxi' }
    else if (r < svcMix.taxi + svcMix.bus && spawnBus.length) { pool = spawnBus; want = 'bus' }
  }
  if (!pool.length) return false;
  for (let i = 0; i < 12; i++) {
    const r = pool[(Math.random() * pool.length) | 0], x = r.x, y = r.y;
    const dirs = [];
    for (let k = 0; k < 4; k++) if (isStreet(x + DV[k][0], y + DV[k][1])) dirs.push(k);
    if (!dirs.length) continue;
    const tier = tierAt(x, y);
    let kind;
    if (ped) kind = rnd1(PED_SPR);
    else if (want === 'taxi') kind = tier >= 2 ? 'taxi' : 'fayton';
    else if (want === 'bus') { if (tier < 2) continue; kind = 'bus' }
    else kind = kindFor(tier);
    agents.push({ ped, kind, x, y, d: rnd1(dirs), p: seed ? Math.random() * 0.6 : 0, born: T,
      spd: ped ? 0.15 + Math.random() * 0.07 : VEH[kind].spd * (0.85 + Math.random() * 0.30),
      lane: ped ? 0.385 + Math.random() * 0.072 : 0.138 + Math.random() * 0.036 });
    return true;
  }
  return false;
}
/* how many are about: what the people in view would plausibly send out, never more than a few per building */
function agentTarget() {
  spawnPools();
  const z = Math.min(1, cam.z / 1.1), o = spawnOrig.length;
  return [Math.round(Math.min(60, 1 + G.pop / 90, o * 0.55) * z), Math.round(Math.min(70, 2 + G.pop / 70, o * 0.9) * z)];
}
function openSea(x, y) {
  const t = tile(x, y); if (!t || !isWater(t.t)) return false;
  for (let k = 0; k < 4; k++) { const n = tile(x + DV[k][0], y + DV[k][1]); if (!n || !isWater(n.t)) return false }
  return true;
}
function boatTarget() {
  if (!ready || ugView || cam.z < 0.5) return 0;
  let ports = 0;
  for (const b of G.blds) if (b && (DEFS[b.key].trade >= 1 || DEFS[b.key].offshore)) ports++;
  return Math.min(16, Math.round((2 + ports * 1.4 + G.pop / 900) * Math.min(1, cam.z / 1.1)));
}
function spawnBoat(seed) {
  for (let i = 0; i < 24; i++) {
    const sx = seed ? Math.random() * VW : (Math.random() < 0.5 ? (Math.random() < 0.5 ? -SPAWN_BAND : VW + SPAWN_BAND) : Math.random() * VW);
    const sy = seed ? Math.random() * VH : (Math.random() < 0.5 ? Math.random() * VH : (Math.random() < 0.5 ? -SPAWN_BAND : VH + SPAWN_BAND));
    const w = unproj(sx, sy), x = Math.floor(w[0]), y = Math.floor(w[1]);
    if (!openSea(x, y)) continue;
    const dirs = []; for (let k = 0; k < 4; k++) if (openSea(x + DV[k][0], y + DV[k][1])) dirs.push(k);
    if (!dirs.length) continue;
    const big = Math.random() < 0.35;
    boats.push({ kind: big ? 'v_ship' : 'v_boat', x, y, d: rnd1(dirs), p: Math.random(), spd: (big ? 0.16 : 0.26) * (0.8 + Math.random() * 0.4) });
    return true;
  }
  return false;
}
/* ======================================================================
   QUALITY — what the player picks, and what the game picks when a phone
   cannot keep up. It only ever steps DOWN by itself: stepping back up on a
   fast frame would make a borderline device flap between two looks.
   ====================================================================== */
const QUAL = { high: { dpr: 2, shadow: 2048, shadows: true }, mid: { dpr: 1.5, shadow: 1024, shadows: true },
               low: { dpr: 1, shadow: 512, shadows: false } };
const ORDER = ['high', 'mid', 'low'];
let qMode = 'auto', qLevel = (window.matchMedia && matchMedia('(pointer:coarse)').matches) ? 'mid' : 'high';
let qEma = 16, qFrames = 0, qLast = 0;
function applyQuality() {
  const q = QUAL[qLevel];
  renderer.setPixelRatio(Math.min(q.dpr, devicePixelRatio || 1));
  renderer.setSize(VW, VH, false);
  sun.shadow.mapSize.set(q.shadow, q.shadow);
  if (sun.shadow.map) { sun.shadow.map.dispose(); sun.shadow.map = null }
  renderer.shadowMap.enabled = q.shadows;
  scene.traverse(o => { if (o.material) { for (const m of [].concat(o.material)) m.needsUpdate = true } });
}
window.setQuality = mode => {
  qMode = mode;
  if (mode !== 'auto') qLevel = mode;
  qEma = 16; qFrames = 0;
  if (renderer) applyQuality();
};
window.getQualityLevel = () => qLevel;
function watchFrameTime() {
  if (qMode !== 'auto' || qLevel === 'low') return;
  const dt = T - qLast; qLast = T;
  if (dt <= 0 || dt > 200) return;                 /* a stalled tab says nothing about the device */
  qEma = qEma * 0.93 + dt * 0.07; qFrames++;
  if (qFrames > 150 && qEma > 36) {                /* under about 28 frames a second, steadily */
    qLevel = ORDER[ORDER.indexOf(qLevel) + 1]; qFrames = 0; qEma = 16;
    applyQuality();
    note('Qrafika yüngülləşdirildi: ' + ({ mid: 'orta', low: 'aşağı' })[qLevel] + '.');
  }
}

window.stepAgents = function stepAgents(dt) {
  if (!carSet || !camera) return;
  if (!ready || ugView || cam.z < 0.50) { agents.length = 0; boats.length = 0; carSet.begin(); carSet.end(); return }
  const s = dt / 1000 * ((SPEED[G.speed] || SPEED[2]).f), m = SPAWN_BAND + 70;
  carSet.begin();
  for (let i = agents.length - 1; i >= 0; i--) {
    const a = agents[i]; let gone = false;
    if (s > 0) {
      a.p += a.spd * s;
      while (a.p >= 1) {
        a.p -= 1; a.x += DV[a.d][0]; a.y += DV[a.d][1];
        if (!isStreet(a.x, a.y)) { gone = true; break }
        a.d = nextDir(a.x, a.y, a.d, a.ped ? null : !isMotor(a.kind));
      }
    }
    if (gone) { agents.splice(i, 1); continue }
    /* the street under it may have been raised to asphalt, or it may have turned onto a dirt track */
    if (!a.ped && a.kind !== 'bus' && a.kind !== 'taxi' && a.kind !== 'fayton') {
      const tr = tierAt(a.x, a.y);
      if (tr >= 2 && !isMotor(a.kind)) { a.kind = motorKind(G.year); a.spd = VEH[a.kind].spd * (0.85 + Math.random() * 0.30); a.born = T }
      else if (tr >= 0 && tr < 2 && isMotor(a.kind)) { a.kind = 'cart'; a.spd = VEH[a.kind].spd * (0.85 + Math.random() * 0.30); a.born = T }
    } else if (!a.ped && a.kind === 'fayton' && tierAt(a.x, a.y) >= 2) { a.kind = 'taxi'; a.spd = VEH[a.kind].spd * (0.85 + Math.random() * 0.30); a.born = T }
    else if (!a.ped && (a.kind === 'bus' || a.kind === 'taxi') && tierAt(a.x, a.y) >= 0 && tierAt(a.x, a.y) < 2) { a.kind = a.kind === 'taxi' ? 'fayton' : 'cart'; a.spd = VEH[a.kind].spd * (0.85 + Math.random() * 0.30); a.born = T }
    const r = DV[(a.d + 1) % 4], here = bldAt(a.x, a.y), lane = a.lane * (here && DEFS[here.key].aven && !a.ped ? 1.85 : 1) * (settings.lht && !a.ped ? -1 : 1);
    const cx = a.x + 0.5 + DV[a.d][0] * a.p + r[0] * lane, cy = a.y + 0.5 + DV[a.d][1] * a.p + r[1] * lane;
    const [X, Y, z] = screenTile(cx - 0.5, cy - 0.5);
    if (z > 1 || X < -m || X > VW + m || Y < -m || Y > VH + m) { agents.splice(i, 1); continue }
    const grow = Math.min(1, (T - (a.born || 0)) / 700), gs = 0.2 + 0.8 * grow * (2 - grow);          /* it pulls out of the yard */
    carSet.add((a.ped ? a.kind : VEH[a.kind].spr) + '_' + a.d, cx, (a.ped ? 0 : 0.036) + (here && DEFS[here.key].bridge ? BRIDGE_Y : 0), cy, 0, gs);
  }
  const want = agentTarget();
  let nc = 0, np = 0; for (const a of agents) { if (a.ped) np++; else nc++ }
  /* they leave the buildings one at a time, not all at once; a view that has just opened fills a little faster */
  const fresh = agents.length < 3 ? 0.5 : 0.10;
  if (nc < want[0] && Math.random() < fresh && spawnAgent(false, agents.length === 0)) nc++;
  if (np < want[1] && Math.random() < fresh && spawnAgent(true, agents.length === 0)) np++;
  /* boats */
  const wantB = boatTarget();
  for (let i = boats.length - 1; i >= 0; i--) {
    const b = boats[i]; let gone = false;
    if (s > 0) {
      b.p += b.spd * s;
      while (b.p >= 1) {
        b.p -= 1; b.x += DV[b.d][0]; b.y += DV[b.d][1];
        if (!openSea(b.x, b.y)) { gone = true; break }
        if (!openSea(b.x + DV[b.d][0], b.y + DV[b.d][1])) {
          const o = []; for (let k = 0; k < 4; k++) if (k !== (b.d + 2) % 4 && openSea(b.x + DV[k][0], b.y + DV[k][1])) o.push(k);
          b.d = o.length ? rnd1(o) : (b.d + 2) % 4;
        }
      }
    }
    if (gone) { boats.splice(i, 1); continue }
    const cx = b.x + 0.5 + DV[b.d][0] * b.p, cy = b.y + 0.5 + DV[b.d][1] * b.p;
    const [X, Y, z] = screenTile(cx - 0.5, cy - 0.5);
    if (z > 1 || X < -m || X > VW + m || Y < -m || Y > VH + m || !wantB) { boats.splice(i, 1); continue }
    carSet.add(b.kind + '_' + b.d, cx, 0.005 + Math.sin(T / 700 + i) * 0.006, cy, 0);
  }
  const sd = boats.length === 0;
  for (let i = 0; i < (sd ? 6 : 1) && boats.length < wantB; i++) if (!spawnBoat(sd)) break;
  carSet.end();
};

/* ======================================================================
   SMOKE AND AIRCRAFT LIGHTS — drawn, not modelled. Puffs are a pure
   function of the clock and an index, so nothing is allocated per frame.
   ====================================================================== */
let fxPts = null;
const SMOKE_N = 7, MAXFX = 1400;
function initFx() {
  const g = new THREE.BufferGeometry();
  g.setAttribute('position', new THREE.BufferAttribute(new Float32Array(MAXFX * 3), 3));
  g.setAttribute('aSize', new THREE.BufferAttribute(new Float32Array(MAXFX), 1));
  g.setAttribute('aCol', new THREE.BufferAttribute(new Float32Array(MAXFX * 4), 4));
  fxPts = new THREE.Points(g, new THREE.ShaderMaterial({
    transparent: true, depthWrite: false, uniforms: { uScale: { value: 600 } },
    vertexShader: `attribute float aSize; attribute vec4 aCol; varying vec4 vC; uniform float uScale;
      void main(){ vC=aCol; vec4 mv=modelViewMatrix*vec4(position,1.0);
        gl_PointSize=aSize*uScale/max(0.5,-mv.z); gl_Position=projectionMatrix*mv; }`,
    fragmentShader: `varying vec4 vC; void main(){ float d=length(gl_PointCoord-0.5);
      float a=smoothstep(0.5,0.12,d); gl_FragColor=vec4(vC.rgb, vC.a*a); if(gl_FragColor.a<0.01) discard; }`,
  }));
  fxPts.frustumCulled = false; fxPts.renderOrder = 8; scene.add(fxPts);
}
  /* ======================================================================
   FLOW — current along the lines, water along the mains. A breadth-first walk
   from every plant and pump through the actual pylons, cables and pipes gives
   each link a direction (away from the source); pulses ride those links. The
   overhead lines show always; the buried layers show in the cutaway or under
   their data layer. A shortage turns the current red and the water dim.
   ====================================================================== */
const MAXFLOW = 3200;
let flowPts = null, flowE = new Float32Array(0), flowN = 0, flowT = -1e9, flowVer = '';
function initFlow() {
  const g = new THREE.BufferGeometry();
  g.setAttribute('position', new THREE.BufferAttribute(new Float32Array(MAXFLOW * 3), 3));
  g.setAttribute('aSize', new THREE.BufferAttribute(new Float32Array(MAXFLOW), 1));
  g.setAttribute('aCol', new THREE.BufferAttribute(new Float32Array(MAXFLOW * 4), 4));
  flowPts = new THREE.Points(g, fxPts.material.clone());
  flowPts.material.uniforms = { uScale: fxPts.material.uniforms.uScale };
  flowPts.frustumCulled = false; flowPts.renderOrder = 9; scene.add(flowPts);
}
function flowOn(layer, x, y) {
  if (layer === 0) { const b = bldAt(x, y); return !!(b && DEFS[b.key].conduct && !DEFS[b.key].under) }
  if (layer === 1) return !!cableAt(x, y);
  const u = underAt(x, y); return !!(u && DEFS[u.key].pipe);
}
function buildFlow() {
  const out = [];
  const dist = new Int32Array(3 * NC).fill(-1);
  const walk = (layers, isSource) => {
    const q = [];
    for (const b of G.blds) {
      if (!b || !isSource(DEFS[b.key])) continue;
      for (let y = b.y - 1; y <= b.y + b.h; y++) for (let x = b.x - 1; x <= b.x + b.w; x++) {
        if (x < 0 || y < 0 || x >= GW || y >= GH) continue;
        for (const l of layers) if (flowOn(l, x, y) && dist[l * NC + y * GW + x] < 0) { dist[l * NC + y * GW + x] = 0; q.push(l * NC + y * GW + x) }
      }
    }
    for (let h = 0; h < q.length; h++) {
      const n = q[h], l = (n / NC) | 0, i = n - l * NC, x = i % GW, y = (i / GW) | 0, d = dist[n];
      for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
        const nx = x + dx, ny = y + dy; if (nx < 0 || ny < 0 || nx >= GW || ny >= GH) continue;
        if (!flowOn(l, nx, ny)) continue;
        const m = l * NC + ny * GW + nx;
        if (dist[m] < 0) { dist[m] = d + 1; q.push(m) }
        if (dist[m] === d + 1) out.push(x + 0.5, y + 0.5, nx + 0.5, ny + 0.5, l, hash2(x, y, 53 + l * 7 + dx * 3 + dy));
      }
    }
  };
  walk([0, 1], d => d.power);
  walk([2], d => d.water);
  flowE = new Float32Array(out); flowN = out.length / 6;
}
function drawFlow() {
  if (!flowPts) return;
  const pa = flowPts.geometry.attributes.position.array, sz = flowPts.geometry.attributes.aSize.array, co = flowPts.geometry.attributes.aCol.array;
  let n = 0;
  const near = cam.z >= 0.5;
  if (!near || (T - flowT > 1400)) {
    if (T - flowT > 1400) { flowT = T; if (near) buildFlow() }
  }
  if (!near) { flowPts.geometry.setDrawRange(0, 0); return }
  const t = T / 1000, R2 = Math.pow(camDist() * 1.35 + 7, 2);
  const pwOk = (G.pwR == null ? 1 : G.pwR) >= 0.999, wtOk = (G.wtR == null ? 1 : G.wtR) >= 0.999;
  const top = (MODELS.get('pylon') ? MODELS.get('pylon').h : 1.55) * 0.96;
  flowPts.material.depthTest = !(overlay === 'power' || overlay === 'water');
  for (let e = 0; e < flowN && n < MAXFLOW - 3; e++) {
    const o = e * 6, x0 = flowE[o], z0 = flowE[o + 1], x1 = flowE[o + 2], z1 = flowE[o + 3], l = flowE[o + 4] | 0, ph = flowE[o + 5];
    const dx = x0 - cam.tx, dz = z0 - cam.ty; if (dx * dx + dz * dz > R2) continue;
    if (l === 0 && ugView) continue;
    if (l === 1 && !(ugView || overlay === 'power')) continue;
    if (l === 2 && !(ugView || overlay === 'water')) continue;
    const sp = l === 2 ? 0.55 : 0.95;
    for (let k = 0; k < 3; k++) {
      const u = (t * sp + ph + k / 3) % 1;
      const x = x0 + (x1 - x0) * u, z = z0 + (z1 - z0) * u, gh = hAt(x, z);
      const y = l === 0 ? gh + top - 0.07 * 4 * u * (1 - u) : gh + (ugView ? (l === 1 ? UG_Y.c : UG_Y.u) : 0.07);
      pa[n * 3] = x; pa[n * 3 + 1] = y; pa[n * 3 + 2] = z;
      const pulse = 0.65 + 0.35 * Math.sin(u * Math.PI);
      if (l === 2) { sz[n] = 0.24; co[n * 4] = 0.35; co[n * 4 + 1] = 0.82; co[n * 4 + 2] = 1; co[n * 4 + 3] = (wtOk ? 0.95 : 0.35) * pulse }
      else { sz[n] = l === 0 ? 0.22 : 0.22; co[n * 4] = 1; co[n * 4 + 1] = pwOk ? 0.88 : 0.4; co[n * 4 + 2] = pwOk ? 0.38 : 0.22; co[n * 4 + 3] = (pwOk ? 1 : 0.8) * pulse }
      n++;
    }
  }
  flowPts.visible = true;
  flowPts.geometry.setDrawRange(0, n);
  for (const a of ['position', 'aSize', 'aCol']) flowPts.geometry.attributes[a].needsUpdate = true;
}
window.rebuildFlow = () => { flowT = -1e9 };
  /* ======================================================================
   STREET LAMPS — real posts, one in three along every street. A lamp is lit
   only where the power network reaches its street, and only after dark: an
   unlit district really is dark, which is what the power layer is for.
   ====================================================================== */
const MAXLAMP = 1800;
let lampPole = null, lampLit = null, lampDark = null, lampKey = '', lampTiles = [];
function initLamps() {
  const pole = new THREE.CylinderGeometry(0.011, 0.016, 0.44, 6); pole.translate(0, 0.22, 0);
  const arm = new THREE.BoxGeometry(0.15, 0.011, 0.011); arm.translate(0.075, 0.44, 0);
  const cap = new THREE.BoxGeometry(0.07, 0.014, 0.05); cap.translate(0.15, 0.452, 0);
  const geo = mergeGeometries([pole, arm, cap], false);
  const head = new THREE.SphereGeometry(0.034, 8, 6); head.translate(0.15, 0.43, 0);
  const mkMesh = (g, mat, shadows) => {
    const m = new THREE.InstancedMesh(g, mat, MAXLAMP); m.count = 0; m.frustumCulled = false; m.castShadow = shadows;
    scene.add(m); return m;
  };
  lampPole = mkMesh(geo, new THREE.MeshStandardMaterial({ color: 0x2c3330, roughness: 0.55, metalness: 0.6 }), false);
  lampLit = mkMesh(head, new THREE.MeshStandardMaterial({ color: 0x332d1c, emissive: 0xffd58a, emissiveIntensity: 0.1, roughness: 0.4 }), false);
  lampDark = mkMesh(head.clone(), new THREE.MeshStandardMaterial({ color: 0x59605c, roughness: 0.3, metalness: 0.2 }), false);
}
const lampPowered = i => pwDist[i] >= 0 && (G.pwR == null ? 1 : G.pwR) > 0.2;
function drawLamps() {
  if (!lampPole) return;
  const vis = !ugView && cam.z > 0.45;
  lampPole.visible = lampLit.visible = lampDark.visible = vis;
  if (!vis) return;
  const L = sunLight();
  lampLit.material.emissiveIntensity = 0.15 + 3.2 * L.night;
  /* repack only when the view moved on, the streets changed, or the power did */
  let pw = 0; for (let k = 0; k < lampTiles.length; k += 3) pw = (pw * 3 + (lampPowered(lampTiles[k + 2]) ? 1 : 0)) % 1000003;
  const key = Math.round(cam.tx / 3) + ',' + Math.round(cam.ty / 3) + ',' + Math.round(camDist() / 6) + ',' + lampTiles.length + ',' + pw;
  if (key === lampKey) return;
  lampKey = key;
  const R2 = Math.pow(camDist() * 1.3 + 8, 2);
  let np = 0, nl = 0, nd = 0;
  for (let k = 0; k < lampTiles.length && np < MAXLAMP; k += 3) {
    const x = lampTiles[k], z = lampTiles[k + 1], dx = x - cam.tx, dz = z - cam.ty;
    if (dx * dx + dz * dz > R2) continue;
    _p.set(x, Math.max(hAt(x, z), WATER_Y) + 0.012, z); _q.setFromAxisAngle(Y_AXIS, 3 * Math.PI / 4); _s.set(1, 1, 1); _m.compose(_p, _q, _s);
    lampPole.setMatrixAt(np++, _m);
    if (lampPowered(lampTiles[k + 2])) lampLit.setMatrixAt(nl++, _m); else lampDark.setMatrixAt(nd++, _m);
  }
  lampPole.count = np; lampLit.count = nl; lampDark.count = nd;
  lampPole.instanceMatrix.needsUpdate = lampLit.instanceMatrix.needsUpdate = lampDark.instanceMatrix.needsUpdate = true;
}
  /* ======================================================================
   AIRCRAFT — when the airport works, aircraft land on and leave from its
   runway. They are drawn, not simulated: they exist only while the view is near,
   one every few seconds, more when the airport can carry more. Landing is a
   glide down to the threshold and a roll-out; take-off is a roll, a rotation
   at three quarters of the strip, and a climb away.
   ====================================================================== */
const planeAgents = [];
let planeSet = null, planeAcc = 0, planeLast = 0, planeSeq = 0;
function spawnPlane(rw) {
  const flip = Math.random() < 0.5, ax = rw.axis === 'x';
  const sx = flip ? rw.x1 + 0.5 : rw.x0 + 0.5, sz = flip ? rw.z1 + 0.5 : rw.z0 + 0.5;
  const dx = ax ? (flip ? -1 : 1) : 0, dz = ax ? 0 : (flip ? -1 : 1);
  planeAgents.push({ sx, sz, dx, dz, L: rw.n, land: (planeSeq++ % 2) === 0, t: 0, dur: 0 });
  const a = planeAgents[planeAgents.length - 1]; a.dur = a.land ? 15 : 12;
}
function drawPlanes() {
  if (!planeSet) return;
  const dt = Math.min(100, Math.max(0, T - planeLast)); planeLast = T;
  const A = G.air, live = !!(A && A.ok && A.rw) && !ugView && cam.z > 0.3;
  if (live) {
    const cx = (A.rw.x0 + A.rw.x1) / 2 + 0.5, cz = (A.rw.z0 + A.rw.z1) / 2 + 0.5;
    if (G.speed > 0 && Math.hypot(cam.tx - cx, cam.ty - cz) < camDist() * 1.5 + 55) {
      planeAcc += dt;
      if (planeAcc > 15000 / (0.6 + A.cap / 22) && planeAgents.length < 3) { planeAcc = 0; spawnPlane(A.rw) }
    }
  } else if (planeAgents.length) planeAgents.length = 0;
  planeSet.begin();
  const run = G.speed > 0 ? dt / 1000 : 0;
  for (let i = planeAgents.length - 1; i >= 0; i--) {
    const a = planeAgents[i]; a.t += run;
    const u = a.t / a.dur; if (u >= 1) { planeAgents.splice(i, 1); continue }
    const L = a.L; let s, y, pitch;
    if (a.land) {
      if (u < 0.5) { const v = u / 0.5; s = -40 + 40 * v; y = 6.5 * Math.pow(1 - v, 1.25) + 0.03; pitch = -0.17 * (1 - v) }
      else { const w = (u - 0.5) / 0.5; s = L * 0.88 * (1 - (1 - w) * (1 - w)); y = 0.03; pitch = 0 }
    } else {
      if (u < 0.5) { const v = u / 0.5; s = L * 0.78 * v * v; y = 0.03; pitch = 0 }
      else { const v = (u - 0.5) / 0.5; s = L * 0.78 + (L * 0.22 + 44) * v; y = 0.03 + 7.5 * Math.pow(v, 1.5); pitch = 0.22 * Math.min(1, v * 4) }
    }
    const x = a.sx + a.dx * s, z = a.sz + a.dz * s;
    planeSet.add('plane', x, y, z, Math.atan2(-a.dz, a.dx), 1.25, 1, pitch);
  }
  planeSet.end();
}
function drawLive() {
  if (!fxPts) return;
  const pa = fxPts.geometry.attributes.position.array, sz = fxPts.geometry.attributes.aSize.array, co = fxPts.geometry.attributes.aCol.array;
  let n = 0;
  fxPts.visible = !ugView;
  if (ugView || cam.z < 0.4) { fxPts.geometry.setDrawRange(0, 0); return }
  fxPts.material.uniforms.uScale.value = VH / (2 * Math.tan(FOV / 2)) * 0.5;
  const t = T / 1000, L = sunLight();
  const em = [];
  const R2 = Math.pow(camDist() * 1.5 + 8, 2);
  for (const b of G.blds) {
    if (!b) continue;
    const d = DEFS[b.key];
    if (!(d.poll >= 8)) continue;
    if (d.zone && b.lvl < 2) continue;
    if (!b.pw && !d.power) continue;
    const dx = b.x - cam.tx, dz = b.y - cam.ty; if (dx * dx + dz * dz > R2) continue;
    const model = MODELS.get(modelFor(b)); if (!model) continue;
    em.push([b.x + b.w / 2, Math.max(hAt(b.x + b.w / 2, b.y + b.h / 2), WATER_Y) + model.h * 0.94 * bodyScale(b, d, modelFor(b)), b.y + b.h / 2, hash2(b.x, b.y, 41), Math.min(1, (d.poll || 10) / 26)]);
    if (em.length > 70) break;
  }
  for (let j = 0; j < SMOKE_N && n < MAXFX - 80; j++) {
    const q = j / SMOKE_N;
    for (const [X, Y, Z, h, s] of em) {
      if (n >= MAXFX - 1) break;
      const p = (t * 0.22 + h + q) % 1;
      pa[n * 3] = X + (0.35 * p + 0.03) * (0.5 + h * 0.9); pa[n * 3 + 1] = Y + 1.1 * p * (0.65 + s * 0.55); pa[n * 3 + 2] = Z + 0.12 * p;
      sz[n] = 0.30 + p * p * 1.3 * s;
      const c = 0.91 - 0.45 * q; co[n * 4] = c; co[n * 4 + 1] = c * 0.99; co[n * 4 + 2] = c * 0.96; co[n * 4 + 3] = (0.42 * (1 - q) + 0.05) * (1 - p * 0.4) * (0.4 + 0.6 * clamp(L.day + 0.35, 0, 1));
      n++;
    }
  }
  /* dust hanging over the building sites */
  for (let si = 0; si < siteList.length && n < MAXFX - 30; si += 6) {
    const sx = siteList[si], sz2 = siteList[si + 1], sw = siteList[si + 2], sd = siteList[si + 3], y0 = siteList[si + 5];
    const dx = sx - cam.tx, dz = sz2 - cam.ty; if (dx * dx + dz * dz > R2) continue;
    const cnt = Math.min(34, 6 + Math.round(sw * sd * 2));
    for (let j = 0; j < cnt && n < MAXFX - 2; j++) {
      const ph = (t * 0.5 + j / cnt) % 1, hh = hash2(j, si, 91), h2 = hash2(j, si, 93);
      pa[n * 3] = sx + (hh - 0.5) * sw * 0.95; pa[n * 3 + 1] = y0 + 0.05 + ph * 0.5; pa[n * 3 + 2] = sz2 + (h2 - 0.5) * sd * 0.95;
      sz[n] = 0.14 + ph * 0.36; co[n * 4] = 0.80; co[n * 4 + 1] = 0.72; co[n * 4 + 2] = 0.57; co[n * 4 + 3] = 0.30 * (1 - ph) * (0.4 + 0.6 * clamp(L.day + 0.35, 0, 1));
      n++;
    }
  }
  /* street lamps: a warm point on the pole and a faint pool of light on the road */
  if (L.night > 0.12 && cam.z > 0.55) {
    const a = clamp((L.night - 0.12) / 0.5, 0, 1);
    for (let i = 0; i < lamps.length && n < MAXFX - 4; i += 2) {
      const dx = lamps[i] - cam.tx, dz = lamps[i + 1] - cam.ty; if (dx * dx + dz * dz > R2) continue;
      if (!lampPowered(lampTiles[(i >> 1) * 3 + 2])) continue;
      const lh = hAt(lamps[i], lamps[i + 1]);
      pa[n * 3] = lamps[i] - 0.106; pa[n * 3 + 1] = lh + 0.442; pa[n * 3 + 2] = lamps[i + 1] - 0.106;
      sz[n] = 0.07; co[n * 4] = 1; co[n * 4 + 1] = 0.86; co[n * 4 + 2] = 0.55; co[n * 4 + 3] = 0.5 * a; pa[n * 3 + 1] += 0.0; n++;
      pa[n * 3] = lamps[i] - 0.106; pa[n * 3 + 1] = lh + 0.04; pa[n * 3 + 2] = lamps[i + 1] - 0.106;
      sz[n] = 0.62; co[n * 4] = 1; co[n * 4 + 1] = 0.78; co[n * 4 + 2] = 0.4; co[n * 4 + 3] = 0.16 * a; n++;
    }
  }
  if (L.night > 0.25 && ((t % 1.6) < 0.55)) {
    let k = 0;
    for (const b of G.blds) {
      if (!b) continue;
      const model = MODELS.get(modelFor(b)), bs = model ? bodyScale(b, DEFS[b.key], modelFor(b)) : 1; if (!model || model.h * bs < 1.2) continue;
      const dx = b.x - cam.tx, dz = b.y - cam.ty; if (dx * dx + dz * dz > R2) continue;
      if (n >= MAXFX) break;
      pa[n * 3] = b.x + b.w / 2; pa[n * 3 + 1] = hAt(b.x + b.w / 2, b.y + b.h / 2) + model.h * bs + 0.04; pa[n * 3 + 2] = b.y + b.h / 2;
      sz[n] = 0.16; co[n * 4] = 1; co[n * 4 + 1] = 0.22; co[n * 4 + 2] = 0.2; co[n * 4 + 3] = 0.95;
      n++; if (++k > 40) break;
    }
  }
  fxPts.geometry.setDrawRange(0, n);
  for (const a of ['position', 'aSize', 'aCol']) fxPts.geometry.attributes[a].needsUpdate = true;
}

/* ======================================================================
   PROBLEM ICONS — a badge floats over any building that lacks what it needs: no
   street within reach, no current, no water, rubbish nobody collects. It is the
   inspector's chips, hung where you are already looking. Gathered four times a
   second for what is near the camera, drawn as one batch of point sprites.
   ====================================================================== */
const MAXAL = 160;
let alertPts = null, alertT = -1e9;
function alertAtlas() {
  const c = document.createElement('canvas'); c.width = 384; c.height = 64;
  const g = c.getContext('2d');
  const badge = (i, col) => {
    g.save(); g.translate(i * 64 + 32, 32);
    g.beginPath(); g.arc(0, 0, 27, 0, Math.PI * 2); g.fillStyle = '#fffaf0'; g.fill();
    g.beginPath(); g.arc(0, 0, 23, 0, Math.PI * 2); g.fillStyle = col; g.fill();
    g.lineWidth = 2.5; g.strokeStyle = 'rgba(0,0,0,.35)'; g.stroke();
  };
  badge(0, '#e0a52a');                                   /* current: a bolt */
  g.fillStyle = '#fff'; g.beginPath(); g.moveTo(4, -17); g.lineTo(-10, 3); g.lineTo(-1, 3); g.lineTo(-5, 17); g.lineTo(11, -4); g.lineTo(1, -4); g.closePath(); g.fill(); g.restore();
  badge(1, '#2f8ec4');                                   /* water: a drop */
  g.fillStyle = '#fff'; g.beginPath(); g.moveTo(0, -17); g.bezierCurveTo(14, 0, 13, 15, 0, 15); g.bezierCurveTo(-13, 15, -14, 0, 0, -17); g.fill(); g.restore();
  badge(2, '#6b7480');                                   /* street: a road with its dashes */
  g.fillStyle = '#fff'; g.beginPath(); g.moveTo(-5, -17); g.lineTo(5, -17); g.lineTo(13, 17); g.lineTo(-13, 17); g.closePath(); g.fillStyle = '#3d444c'; g.fill();
  g.fillStyle = '#ffe9a8'; for (const y of [-12, -3, 7]) g.fillRect(-1.6, y, 3.2, 6); g.restore();
  badge(3, '#8a6a43');                                   /* rubbish: a bin */
  g.fillStyle = '#fff'; g.fillRect(-10, -9, 20, 4); g.fillRect(-8, -5, 16, 21); g.fillStyle = '#8a6a43'; for (const x of [-4, 0, 4]) g.fillRect(x - 1, -2, 2, 14); g.restore();
  badge(4, '#c4452f');                                   /* swamped / full: an exclamation mark */
  g.fillStyle = '#fff'; g.fillRect(-3.2, -16, 6.4, 20); g.beginPath(); g.arc(0, 12, 3.8, 0, Math.PI * 2); g.fill(); g.restore();
  badge(5, '#d8531f');                                   /* fire: a flame */
  g.fillStyle = '#fff'; g.beginPath(); g.moveTo(0, -18); g.bezierCurveTo(12, -4, 13, 6, 6, 13); g.bezierCurveTo(3, 16, -3, 16, -6, 13); g.bezierCurveTo(-13, 6, -12, -4, 0, -18); g.fill();
  g.fillStyle = '#d8531f'; g.beginPath(); g.moveTo(0, -4); g.bezierCurveTo(5, 2, 5, 8, 0, 11); g.bezierCurveTo(-5, 8, -5, 2, 0, -4); g.fill(); g.restore();
  const t = new THREE.CanvasTexture(c); t.colorSpace = THREE.SRGBColorSpace; t.magFilter = THREE.LinearFilter; return t;
}
function initAlerts() {
  const g = new THREE.BufferGeometry();
  g.setAttribute('position', new THREE.BufferAttribute(new Float32Array(MAXAL * 3), 3));
  g.setAttribute('aIcon', new THREE.BufferAttribute(new Float32Array(MAXAL), 1));
  alertPts = new THREE.Points(g, new THREE.ShaderMaterial({
    transparent: true, depthWrite: false, depthTest: false, uniforms: { uAtlas: { value: alertAtlas() }, uScale: { value: 600 } },
    vertexShader: `attribute float aIcon; varying float vI; uniform float uScale;
      void main(){ vI=aIcon; vec4 mv=modelViewMatrix*vec4(position,1.0);
        gl_PointSize=0.62*uScale/max(0.5,-mv.z); gl_Position=projectionMatrix*mv; }`,
    fragmentShader: `uniform sampler2D uAtlas; varying float vI;
      void main(){ vec4 c=texture2D(uAtlas, vec2((vI+gl_PointCoord.x)/6.0, 1.0-gl_PointCoord.y)); if(c.a<0.06) discard; gl_FragColor=c; }`,
  }));
  alertPts.frustumCulled = false; alertPts.renderOrder = 12; scene.add(alertPts);
}
let alertCount = 0;
function drawAlerts() {
  if (!alertPts) return;
  const on = !ugView && cam.z >= 0.45 && G.tick > 0;
  alertPts.visible = on && alertCount > 0;
  if (!on) { alertCount = 0; return }
  const t = T / 1000;
  if (T - alertT > 260) {
    alertT = T;
    const pa = alertPts.geometry.attributes.position.array, ic = alertPts.geometry.attributes.aIcon.array;
    const R2 = Math.pow(camDist() * 1.1 + 5, 2), list = [];
    for (const b of G.blds) {
      if (!b) continue;
      const d = DEFS[b.key];
      if (d.fixed || d.layout || d.road || d.under || d.conduct || d.rail || d.strip || d.tunnel || d.offshore || d.area) continue;
      const dx = b.x + b.w / 2 - cam.tx, dz = b.y + b.h / 2 - cam.ty, d2 = dx * dx + dz * dz;
      if (d2 > R2) continue;
      const id = b.id != null ? b.id : b.x * 4096 + b.y;
      if (rise.has(id)) continue;
      /* the first thing missing, in the order a mayor fixes them */
      let icon = -1;
      if (b.fire > 0) icon = 5;
      else if (d.zone && !b.road) icon = 2;
      else if (b.pw === false) icon = 0;
      else if (b.wt === false) icon = 1;
      else if (b.ws === false) icon = 3;
      else if ((d.serve && b.sover) || (d.graves && b.full)) icon = 4;
      if (icon >= 0) list.push([d2, b, d, icon]);
    }
    list.sort((a, c) => a[0] - c[0]);
    alertCount = Math.min(MAXAL, list.length);
    for (let k = 0; k < alertCount; k++) {
      const [, b, d, icon] = list[k], cx = b.x + b.w / 2, cz = b.y + b.h / 2, mn = modelFor(b), model = MODELS.get(mn);
      const top = (model ? model.h * bodyScale(b, d, mn) : 0.3) + 0.26;
      pa[k * 3] = cx; pa[k * 3 + 1] = Math.max(hAt(cx, cz), WATER_Y) + top; pa[k * 3 + 2] = cz; ic[k] = icon;
    }
    alertPts.geometry.setDrawRange(0, alertCount);
    alertPts.geometry.attributes.aIcon.needsUpdate = true; alertPts.geometry.attributes.position.needsUpdate = true;
  }
  alertPts.material.uniforms.uScale.value = VH / (2 * Math.tan(FOV / 2)) * 0.5;
  alertPts.position.y = 0.04 * Math.sin(t * 2.2);                 /* a gentle bob */
  alertPts.visible = alertCount > 0;
}

/* ======================================================================
   BOOT
   ====================================================================== */
window.initRenderer = async function initRenderer() {
  renderer = new THREE.WebGLRenderer({ canvas: cv, antialias: true, powerPreference: 'high-performance' });
  renderer.setPixelRatio(Math.min(2, devicePixelRatio || 1));
  renderer.outputColorSpace = THREE.SRGBColorSpace;
  renderer.toneMapping = THREE.ACESFilmicToneMapping; renderer.toneMappingExposure = 0.92;
  renderer.shadowMap.enabled = true; renderer.shadowMap.type = THREE.PCFSoftShadowMap;
  scene = new THREE.Scene();
  scene.background = new THREE.Color(0xa9d2e8);
  scene.fog = new THREE.Fog(0xa9d2e8, 55, 330);
  camera = new THREE.PerspectiveCamera(FOV * 180 / Math.PI, 1, 0.3, 800);
  const pm = new THREE.PMREMGenerator(renderer);
  envTex = pm.fromScene(new RoomEnvironment(), 0.04).texture; scene.environment = envTex;
  hemi = new THREE.HemisphereLight(0xdfeaf0, 0xb59f78, 0.9); scene.add(hemi);
  sun = new THREE.DirectionalLight(0xfff1dc, 3.0);
  sun.castShadow = true; sun.shadow.mapSize.set(2048, 2048);
  sun.shadow.bias = -0.0004; sun.shadow.normalBias = 0.03;
  Object.assign(sun.shadow.camera, { left: -30, right: 30, top: 30, bottom: -30, near: 1, far: 220 });
  scene.add(sun); scene.add(sun.target);
  for (const k of ['surface', 'under', 'deco']) { grp[k] = new THREE.Group(); scene.add(grp[k]) }
  syncSize();
  await loadLibrary();
  surf = new InstSet(grp.surface); under = new InstSet(grp.under, false); deco = new InstSet(grp.deco);
  grp.cars = new THREE.Group(); scene.add(grp.cars); carSet = new InstSet(grp.cars, true);
  grp.planes = new THREE.Group(); scene.add(grp.planes); planeSet = new InstSet(grp.planes, true);
  grp.anim = new THREE.Group(); scene.add(grp.anim); animSet = new InstSet(grp.anim, true);
  initSky(); initCursor(); initFx(); initFlow(); initLamps(); initClouds(); initAlerts(); initWeather();
  buildTerrain();
  syncBuildings();
};
window.__r3d = { get scene() { return scene }, get camera() { return camera }, get renderer() { return renderer }, MODELS, THREE,
  get sets() { return { surf, under, deco, carSet } },
  get rising() { return rise.size }, get planeCount() { return planeAgents.length }, spawnPlaneNow() { if (G.air && G.air.rw) spawnPlane(G.air.rw) }, get flowCount() { return flowN }, get flowDrawn() { return flowPts ? flowPts.geometry.drawRange.count : 0 }, get lampCount() { return lamps.length / 2 }, get lampMeshes() { return lampPole ? [lampPole.count, lampLit.count, lampDark.count] : [] },
  get wx() { return wxVis }, get rainMesh() { return rainM }, get snowMesh() { return snowM },
  get paths() { return pathCells }, get faces() { return faceOf }, get anim() { return animList }, get animSet() { return animSet },
  get laneSide() { return settings.lht ? -1 : 1 }, get alerts() { return alertCount }, get alertMesh() { return alertPts }, resetAlerts() { alertT = -1e9 }, get sitesActive() { return siteCount },
  get agents() { return agents }, get boats() { return boats }, get carSet() { return carSet }, get fx() { return fxPts },
  agentTarget: () => agentTarget(), streetCount: () => streetCount(), spawnPools: () => (spawnPools(), [spawnOrig.length, spawnTaxi.length, spawnBus.length]) };
window.__r3dResolve && window.__r3dResolve();

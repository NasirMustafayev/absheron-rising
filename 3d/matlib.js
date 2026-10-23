/* Rebuilds the Blender node-graph materials in Three.js from the parameter
   table the sprite pipeline records (materials.json). glTF carries none of the
   procedural texturing, so a plain export is flat colour; this puts the stone
   coursing, window grids and weathering back.

   Everything is evaluated in the model's LOCAL space, never world space. A
   building's windows must line up with its own walls wherever it stands and
   however it is turned, and the instanced copies share one material. */
import * as THREE from 'three';

const lin = c => new THREE.Color().setRGB(c[0], c[1], c[2], THREE.LinearSRGBColorSpace);

const NOISE = /* glsl */`
float h3(vec3 p){ p=fract(p*0.3183099+.1); p*=17.0; return fract(p.x*p.y*p.z*(p.x+p.y+p.z)); }
float h2(vec2 p){ return h3(vec3(p,p.x*0.37+p.y*0.71)); }
float vnoise(vec3 x){
  vec3 i=floor(x), f=fract(x); f=f*f*(3.0-2.0*f);
  return mix(mix(mix(h3(i),h3(i+vec3(1,0,0)),f.x),mix(h3(i+vec3(0,1,0)),h3(i+vec3(1,1,0)),f.x),f.y),
             mix(mix(h3(i+vec3(0,0,1)),h3(i+vec3(1,0,1)),f.x),mix(h3(i+vec3(0,1,1)),h3(i+vec3(1,1,1)),f.x),f.y),f.z);
}
float fbm(vec3 p){ return vnoise(p)*0.5+vnoise(p*2.03)*0.3+vnoise(p*4.1)*0.2; }
/* the sprite pipeline lays walls out as (x+y, z) in Blender axes; glTF is Y-up
   with Blender's y negated onto z, so that is (x - z, y) here */
vec2 wallUV(vec3 p){ return vec2(p.x - p.z, p.y); }
vec2 faceUV(vec3 p, vec3 n){ return abs(n.y) > 0.7 ? vec2(p.x + p.z * 0.37, p.z) : wallUV(p); }
`;

/* one uniform object shared by every material that glows after dark, so the
   whole city can be lit by changing a single number */
export const NIGHT = { value: 0 };

function patch(mat, key, uniforms, frag, emissiveFrag) {
  mat.customProgramCacheKey = () => key;
  mat.onBeforeCompile = sh => {
    Object.assign(sh.uniforms, uniforms);
    sh.vertexShader = sh.vertexShader
      .replace('#include <common>', '#include <common>\nvarying vec3 vLocal;\nvarying vec3 vLN;\nattribute vec2 aLitInfo;\nvarying vec2 vLitInfo;')
      .replace('#include <begin_vertex>', '#include <begin_vertex>\nvLocal = position; vLN = normal; vLitInfo = aLitInfo;');
    const decl = Object.keys(uniforms).map(k => {
      const v = uniforms[k].value;
      return 'uniform ' + (typeof v === 'number' ? 'float' : v.isColor ? 'vec3' : 'vec2') + ' ' + k + ';';
    }).join('\n');
    sh.fragmentShader = sh.fragmentShader
      .replace('#include <common>', '#include <common>\nvarying vec3 vLocal;\nvarying vec3 vLN;\nvarying vec2 vLitInfo;\n' + decl + '\n' + NOISE)
      .replace('#include <color_fragment>', '#include <color_fragment>\n' + frag)
      .replace('#include <emissivemap_fragment>',
               '#include <emissivemap_fragment>\n' + (emissiveFrag || ''));
  };
  return mat;
}

const U = v => ({ value: v });

const BUILD = {
  rough(r) {
    const m = new THREE.MeshStandardMaterial({ color: lin(r.col), roughness: r.rough, metalness: r.metallic });
    return patch(m, 'rough', { uF: U(r.noise), uV: U(r.vary * 1.7) }, /* glsl */`
      vec3 q = vLocal * uF;
      float aa = 1.0 - smoothstep(0.6, 2.4, length(fwidth(q)));
      diffuseColor.rgb *= 1.0 + (fbm(q) - 0.5) * 2.0 * uV * aa;`);
  },
  stone(r) {
    const m = new THREE.MeshStandardMaterial({ color: 0xffffff, roughness: r.rough, metalness: 0 });
    const col = lin(r.col);
    return patch(m, 'stone', {
      uC: U(col), uRow: U(r.row), uBW: U(r.bwidth), uMort: U(r.mortar), uV: U(r.vary * 1.8), uS: U(r.scale)
    }, /* glsl */`
      vec2 uv = faceUV(vLocal, normalize(vLN));
      float rw = floor(uv.y / uRow);
      float off = mod(rw, 2.0) * 0.5 * uBW;
      float cu = (uv.x + off) / uBW;
      vec2 cell = vec2(fract(cu), fract(uv.y / uRow));
      /* mortar is a band along each cell edge, kept thin so a course still reads */
      float mw = clamp(uMort * 0.28, 0.003, uRow * 0.16);
      float dEdge = min(min(cell.x * uBW, (1.0 - cell.x) * uBW), min(cell.y * uRow, (1.0 - cell.y) * uRow));
      float aaw = max(fwidth(dEdge), 1e-4);
      float flatF = step(0.7, abs(normalize(vLN).y));
      float mortar = (1.0 - smoothstep(mw, mw + aaw, dEdge)) * (1.0 - 0.92 * flatF);   /* a roof is not coursed */
      float id = h2(vec2(floor(cu), rw));
      vec3 stoneC = uC * (1.0 - uV + 2.0 * uV * id);
      stoneC *= 1.0 + (fbm(vLocal * uS) - 0.5) * 0.35;
      diffuseColor.rgb = mix(stoneC, uC * 0.55, mortar);`);
  },
  windows(r) {
    const m = new THREE.MeshStandardMaterial({ color: 0xffffff, roughness: r.wrough, metalness: 0 });
    return patch(m, 'windows', {
      uWall: U(lin(r.wall)), uGlass: U(lin(r.lit ? [1, 0.78, 0.44] : r.glass)),
      uRows: U(r.rows), uCols: U(r.cols), uM: U(r.mortar == null ? 0.045 : r.mortar), uNight: NIGHT
    }, /* glsl */`
      vec2 uv = wallUV(vLocal);
      float flatFace = step(0.7, abs(normalize(vLN).y));
      float rw = floor(uv.y * uRows);
      vec2 cell = vec2(fract(uv.x * uCols + mod(rw, 2.0) * 0.5), fract(uv.y * uRows));
      /* Blender's brick node reports the MORTAR as the wall and the brick
         interior as the window; its mortar band is ~0.045 from each edge */
      float mx = uM * uCols, my = uM * uRows;
      float dx = min(cell.x, 1.0 - cell.x), dy = min(cell.y, 1.0 - cell.y);
      float win = smoothstep(mx, mx + fwidth(dx) + 1e-4, dx) * smoothstep(my, my + fwidth(dy) + 1e-4, dy) * (1.0 - flatFace);
      vec3 wallC = uWall * (1.0 + (fbm(vLocal * 55.0) - 0.5) * 0.3);
      diffuseColor.rgb = mix(wallC, uGlass, win);
      /* after dark roughly half the windows are lit by default. A building can ask for more
         or fewer (vLitInfo.x moves the threshold, +0.5 is dark) and has its own pattern (.y) */
      float lit = win * step(0.5 + vLitInfo.x, h2(vec2(floor(uv.x * uCols + mod(rw, 2.0) * 0.5) + floor(vLocal.x * 3.0), rw) + vLitInfo.y * 37.0)) * uNight;`, /* glsl */`
      totalEmissiveRadiance += vec3(1.0, 0.74, 0.40) * lit * 1.1;`);
  },
  glass(r) {
    return new THREE.MeshStandardMaterial({ color: lin(r.col), roughness: r.rough, metalness: 0.55,
      emissive: r.emit ? lin([1, 0.82, 0.52]) : 0x000000, emissiveIntensity: r.emit || 0 });
  },
  /* glass with a floor line every `period`; the lines light up at night */
  bands(r) {
    const m = new THREE.MeshStandardMaterial({ color: lin(r.col), roughness: r.rough, metalness: r.metallic });
    return patch(m, 'bands', { uP: U(r.period), uGlow: U(lin(r.glow)), uNight: NIGHT }, /* glsl */`
      float f = fract(vLocal.y / uP);
      float line = smoothstep(0.80, 0.93, f) * (1.0 - smoothstep(0.93, 1.0, f));
      diffuseColor.rgb *= 1.0 - 0.38 * line;
      float sheen = 0.5 + 0.5 * sin(vLocal.x * 5.0 + vLocal.y * 1.3);
      diffuseColor.rgb *= 0.9 + 0.2 * sheen;
      float lit = line * uNight;`, /* glsl */`
      totalEmissiveRadiance += uGlow * lit * 1.5;`);
  },
  /* a lit LED panel */
  screen(r) {
    return new THREE.MeshStandardMaterial({ color: lin(r.col), roughness: 0.3,
      emissive: lin(r.col), emissiveIntensity: Math.min(1.2, r.strength * 0.7) });
  },
  tile(r) {
    const m = new THREE.MeshStandardMaterial({ color: lin(r.col), roughness: 0.75 });
    return patch(m, 'tile', { uV: U(0.28) }, /* glsl */`
      float w = 0.5 + 0.5 * sin(vLocal.x * 70.0 + sin(vLocal.z * 9.0) * 1.4);
      diffuseColor.rgb *= 0.78 + 0.4 * w;`);
  },
};

const cache = new Map();
export function buildMaterial(name, registry) {
  if (cache.has(name)) return cache.get(name);
  const r = registry[name];
  let m;
  if (!r || !BUILD[r.kind]) m = new THREE.MeshStandardMaterial({ color: 0xff00ff });   /* loud on purpose */
  else m = BUILD[r.kind](r);
  m.name = name; cache.set(name, m); return m;
}

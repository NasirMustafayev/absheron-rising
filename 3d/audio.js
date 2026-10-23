/* =========================================================================
   ABSHERON RISING — sound.

   The interface and building sounds are made here with the Web Audio API, so there is
   nothing to download for them: the hammering, drilling and crane beeps of a building site,
   the sea, the wind, the traffic hum, the birds by day and the crickets at night.

   Music is recorded: `3d/audio/music/playlist.json` lists the tracks (all CC0, credited
   in CREDITS.md beside them), and they are played one after another. Its shape:

       [ { "file": "heavenly.ogg", "title": "...", "by": "...", "license": "CC0",
           "mood": "day" | "night" | "any", "gain": 1.0, "loops": 1 } , ... ]

   The page's classic script calls  sfx(name, opts)  for one-shots and the
   renderer calls  sfxFrame({...})  every frame with what is going on (how many
   building sites are active, zoom, night). Browsers keep audio locked until the
   person touches the page, so the engine wakes on the first pointer or key.
   Volumes and the mute switch live in localStorage ("ar-audio").
   ========================================================================= */
(function () {
  'use strict';
  const KEY = 'ar-audio';
  const st = { music: 0.55, sfx: 0.8, amb: 0.6, muted: false };
  try { Object.assign(st, JSON.parse(localStorage.getItem(KEY) || '{}')) } catch (e) { }
  const save = () => { try { localStorage.setItem(KEY, JSON.stringify(st)) } catch (e) { } };
  const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
  const rnd = (a, b) => a + Math.random() * (b - a);
  const pick = a => a[Math.floor(Math.random() * a.length)];

  let ctx = null, master, lp, sfxBus, musicBus, ambBus, noiseW, noiseB, started = false;
  const last = {};          /* last time each one-shot played, to thin out a drag */

  /* ------------------------------------------------------------ the engine */
  function unlock() {
    if (ctx) { if (ctx.state === 'suspended') ctx.resume(); return }
    const AC = window.AudioContext || window.webkitAudioContext; if (!AC) return;
    try { ctx = new AC() } catch (e) { return }
    master = ctx.createGain(); lp = ctx.createBiquadFilter(); lp.type = 'lowpass'; lp.frequency.value = 22000; lp.Q.value = 0.4;
    const comp = ctx.createDynamicsCompressor(); comp.threshold.value = -16; comp.ratio.value = 3.5; comp.attack.value = 0.01; comp.release.value = 0.25;
    sfxBus = ctx.createGain(); musicBus = ctx.createGain(); ambBus = ctx.createGain();
    for (const b of [sfxBus, musicBus, ambBus]) b.connect(lp);
    lp.connect(comp); comp.connect(master); master.connect(ctx.destination);
    noiseW = noiseBuf(2, 'white'); noiseB = noiseBuf(5, 'brown');
    applyVolumes();
    startAmbience();
    started = true;
    startMusic();
  }
  function noiseBuf(sec, kind) {
    const n = Math.floor(ctx.sampleRate * sec), b = ctx.createBuffer(1, n, ctx.sampleRate), d = b.getChannelData(0);
    let l = 0;
    for (let i = 0; i < n; i++) {
      const w = Math.random() * 2 - 1;
      if (kind === 'brown') { l = (l + 0.02 * w) / 1.02; d[i] = l * 3.5 } else d[i] = w;
    }
    return b;
  }
  function applyVolumes() {
    if (!ctx) return;
    const t = ctx.currentTime;
    master.gain.setTargetAtTime(st.muted ? 0 : 0.9, t, 0.05);
    sfxBus.gain.setTargetAtTime(st.sfx, t, 0.05);
    musicBus.gain.setTargetAtTime(st.music, t, 0.2);
    ambBus.gain.setTargetAtTime(st.amb, t, 0.2);
  }

  /* ---------------------------------------------------------- the building blocks */
  const panFor = o => {
    if (!o || o.x == null || !window.screenOf || typeof VW === 'undefined') return null;
    const s = window.screenOf(o.x, o.z, 0);
    const p = clamp((s[0] / VW - 0.5) * 2, -1, 1);
    const near = clamp(1 - Math.hypot(o.x - cam.tx, o.z - cam.ty) / 55, 0.15, 1);
    return { p, g: near * clamp(0.4 + cam.z * 0.7, 0.4, 1.2) };
  };
  function out(node, o, bus) {
    const sp = panFor(o);
    let tail = node;
    if (sp) {
      if (ctx.createStereoPanner) { const pn = ctx.createStereoPanner(); pn.pan.value = sp.p; tail.connect(pn); tail = pn }
      const g = ctx.createGain(); g.gain.value = sp.g; tail.connect(g); tail = g;
    }
    tail.connect(bus || sfxBus);
  }
  /* an oscillator with an envelope */
  function tone(f, dur, c) {
    c = c || {};
    const t = ctx.currentTime + (c.at || 0);
    const o = ctx.createOscillator(), g = ctx.createGain();
    o.type = c.type || 'sine'; o.frequency.setValueAtTime(f, t);
    if (c.slide) o.frequency.exponentialRampToValueAtTime(Math.max(20, f * c.slide), t + dur);
    const a = c.a || 0.004, v = c.vol == null ? 0.3 : c.vol;
    g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(v, t + a);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    let n = o;
    if (c.lp) { const fl = ctx.createBiquadFilter(); fl.type = 'lowpass'; fl.frequency.value = c.lp; n.connect(fl); n = fl }
    n.connect(g); out(g, c.o, c.bus);
    o.start(t); o.stop(t + dur + 0.05);
    return o;
  }
  /* filtered noise burst */
  function noise(dur, c) {
    c = c || {};
    const t = ctx.currentTime + (c.at || 0);
    const s = ctx.createBufferSource(); s.buffer = c.brown ? noiseB : noiseW; s.playbackRate.value = c.rate || 1;
    const f = ctx.createBiquadFilter(); f.type = c.type || 'lowpass'; f.frequency.setValueAtTime(c.f || 1200, t);
    if (c.sweep) f.frequency.exponentialRampToValueAtTime(Math.max(40, c.f * c.sweep), t + dur);
    f.Q.value = c.q || 0.7;
    const g = ctx.createGain(); const v = c.vol == null ? 0.3 : c.vol;
    g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(v, t + (c.a || 0.003));
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    s.connect(f); f.connect(g); out(g, c.o, c.bus);
    s.start(t, Math.random() * 1.2); s.stop(t + dur + 0.05);
  }
  const bell = (f, at, vol, o) => { tone(f, 1.1, { at, vol, type: 'sine', a: 0.003, o }); tone(f * 2.01, 0.55, { at, vol: vol * 0.35, type: 'sine', o }); tone(f * 3.97, 0.25, { at, vol: vol * 0.12, type: 'sine', o }) };
  const knock = (at, vol, o) => { noise(0.05, { at, vol: vol * 0.9, f: 2100, type: 'bandpass', q: 1.4, o }); tone(rnd(300, 360), 0.07, { at, vol, type: 'triangle', slide: 0.55, o }) };

  /* ------------------------------------------------------------ the one-shots */
  const MIN = { click: 40, select: 60, place: 45, road: 60, zone: 70, start: 300, done: 500, error: 220, open: 120, close: 120, bulldoze: 80, notify: 400 };
  const SFX = {
    click() { tone(1100, 0.035, { vol: 0.12, type: 'triangle' }) },
    select() { tone(620, 0.05, { vol: 0.16, type: 'triangle' }); tone(930, 0.07, { vol: 0.12, at: 0.045, type: 'triangle' }) },
    open() { noise(0.16, { f: 2600, type: 'bandpass', q: 0.6, vol: 0.10, sweep: 0.5 }) },
    close() { noise(0.12, { f: 1400, type: 'bandpass', q: 0.6, vol: 0.08, sweep: 1.8 }) },
    undo() { tone(520, 0.09, { vol: 0.14, type: 'triangle', slide: 0.7 }); tone(390, 0.12, { vol: 0.12, at: 0.08, type: 'triangle', slide: 0.7 }) },
    error() { tone(150, 0.13, { vol: 0.2, type: 'square', lp: 700, slide: 0.8 }); tone(130, 0.16, { vol: 0.2, at: 0.14, type: 'square', lp: 600, slide: 0.8 }) },
    /* placing something: a thud, a knock of timber, a puff of dust — heavier for a bigger thing */
    place(o) {
      const big = o && o.big ? 1 : 0, w = o && o.w || 1;
      tone(110 - big * 30, 0.16 + big * 0.1, { vol: 0.34 + big * 0.1, type: 'sine', slide: 0.5, o });
      noise(0.1 + big * 0.1, { f: 900, vol: 0.2, brown: false, o });
      knock(0.02, 0.18, o);
      if (w > 1 || big) knock(0.12, 0.14, o);
    },
    zone() { tone(760 + Math.random() * 120, 0.06, { vol: 0.10, type: 'sine' }); noise(0.05, { f: 3000, type: 'highpass', vol: 0.04 }) },
    /* a road laid: dirt is a soft crunch, cobbles are clacks, asphalt a low roller hum */
    road(o) {
      const k = o && o.tier || 0;
      if (k === 0) { noise(0.12, { f: 500, vol: 0.2, brown: true, rate: 1.2 }); noise(0.08, { f: 2400, type: 'bandpass', q: 0.8, vol: 0.06 }) }
      else if (k === 1) { for (let i = 0; i < 3; i++) knock(i * 0.04, 0.10) ; noise(0.08, { f: 700, vol: 0.12 }) }
      else { noise(0.18, { f: 260, vol: 0.2, brown: true }); tone(72, 0.2, { vol: 0.18, type: 'sine' }) }
    },
    pipe() { tone(200, 0.12, { vol: 0.22, type: 'triangle', slide: 0.6 }); noise(0.1, { f: 4000, type: 'highpass', vol: 0.04 }) },
    bulldoze() { noise(0.45, { f: 1800, vol: 0.38, sweep: 0.18 }); tone(70, 0.4, { vol: 0.36, type: 'sine', slide: 0.5 }); knock(0.05, 0.2); knock(0.16, 0.14) },
    /* a site opens: a short hammering and a lorry's reversing beep */
    start(o) {
      if (o && (o.lot || (o.zone && !o.big))) { tone(300, 0.06, { vol: 0.06, type: 'triangle', o }); return }
      for (let i = 0; i < 4; i++) knock(i * 0.17, 0.2 - i * 0.02, o);
      tone(980, 0.11, { vol: 0.08, type: 'square', lp: 2200, at: 0.7, o }); tone(980, 0.11, { vol: 0.08, type: 'square', lp: 2200, at: 0.9, o });
    },
    /* finished: a bell, a rising chime, a breath of applause (noise) */
    done(o) {
      if (o && o.zone) { bell(880, 0, 0.10, o); return }
      bell(659, 0, 0.18, o); bell(880, 0.14, 0.16, o); bell(1319, 0.30, 0.14, o);
      noise(0.5, { f: 3200, type: 'bandpass', q: 0.5, vol: 0.05, at: 0.3, o });
      if (o && o.big) tone(196, 0.8, { vol: 0.12, type: 'sawtooth', lp: 500, at: 0.0, a: 0.05 });
    },
    found() { tone(147, 1.4, { vol: 0.22, type: 'sawtooth', lp: 420, a: 0.12 }); tone(220, 1.4, { vol: 0.16, type: 'sawtooth', lp: 420, a: 0.12, at: 0.0 }); for (let i = 0; i < 6; i++) knock(0.2 + i * 0.2, 0.22) },
    goal() { bell(784, 0, 0.18); bell(988, 0.09, 0.16); bell(1175, 0.18, 0.15); bell(1568, 0.28, 0.14) },
    chapter() { [392, 494, 587, 784].forEach((f, i) => bell(f, i * 0.16, 0.18)); [196, 247, 294].forEach((f, i) => tone(f, 1.6, { vol: 0.10, type: 'triangle', lp: 900, at: 0.5 + i * 0.02, a: 0.08 })) },
    levelup() { [523, 659, 784, 1047].forEach((f, i) => bell(f, i * 0.12, 0.14)) },
    ugOn() { noise(0.55, { f: 3000, vol: 0.12, sweep: 0.08 }); tone(120, 0.5, { vol: 0.2, type: 'sine', slide: 0.5 }); muffle(true) },
    ugOff() { noise(0.45, { f: 300, vol: 0.12, sweep: 8 }); tone(180, 0.4, { vol: 0.16, type: 'sine', slide: 1.8 }); muffle(false) },
    cash() { tone(1480, 0.07, { vol: 0.12, type: 'square', lp: 4000 }); tone(1976, 0.12, { vol: 0.12, type: 'square', lp: 4000, at: 0.07 }) },
    quake() { noise(2.4, { f: 120, vol: 0.55, brown: true, a: 0.08 }); tone(46, 2.2, { vol: 0.5, type: 'sine', slide: 0.7 }) },
    xezri() { noise(3.2, { f: 700, vol: 0.28, type: 'bandpass', q: 0.8, a: 0.9, sweep: 1.6 }) },
    blow() { noise(0.9, { f: 2400, vol: 0.5, sweep: 0.07 }); tone(60, 0.9, { vol: 0.5, type: 'sine', slide: 0.4 }); noise(1.6, { f: 1200, vol: 0.16, type: 'highpass', at: 0.2 }) },
    thunder() { noise(3.4, { f: 160, vol: 0.55, brown: true, a: 0.25, sweep: 0.5 }); noise(0.25, { f: 3200, vol: 0.28, type: 'highpass', a: 0.002 }); tone(52, 2.6, { vol: 0.34, type: 'sine', a: 0.2, slide: 0.7 }) },
    /* the new game's flight down: air rushing past, a low swell, a bell as the ground comes up */
    intro() { noise(7.5, { f: 260, vol: 0.30, type: 'bandpass', q: 0.5, a: 2.4, sweep: 7 }); tone(98, 7, { vol: 0.12, type: 'sine', a: 1.8, slide: 1.5 }); bell(784, 6.6, 0.12); bell(1175, 6.9, 0.10) },
    siren() { for (let i = 0; i < 4; i++) tone(i % 2 ? 640 : 860, 0.28, { vol: 0.12, type: 'sawtooth', lp: 1600, at: i * 0.3, a: 0.02 }) },
  };
  function muffle(on) { if (ctx) lp.frequency.setTargetAtTime(on ? 900 : 22000, ctx.currentTime, 0.12) }
  function sfx(name, o) {
    if (!ctx || st.muted || !SFX[name]) return;
    const now = performance.now(), gap = MIN[name] || 0;
    if (gap && last[name] && now - last[name] < gap) return;
    last[name] = now;
    try { SFX[name](o) } catch (e) { }
  }

  /* ------------------------------------------------------------ ambience */
  const amb = {};
  function loopNoise(buf, type, f, q, vol) {
    const s = ctx.createBufferSource(); s.buffer = buf; s.loop = true;
    const fl = ctx.createBiquadFilter(); fl.type = type; fl.frequency.value = f; fl.Q.value = q || 0.7;
    const g = ctx.createGain(); g.gain.value = vol || 0;
    s.connect(fl); fl.connect(g); g.connect(ambBus); s.start();
    return { s, fl, g };
  }
  function startAmbience() {
    amb.sea = loopNoise(noiseB, 'bandpass', 520, 0.6, 0);
    amb.wind = loopNoise(noiseW, 'lowpass', 380, 0.5, 0);
    amb.city = loopNoise(noiseB, 'lowpass', 190, 0.5, 0);
    amb.work = loopNoise(noiseB, 'lowpass', 150, 0.5, 0);
    amb.rain = loopNoise(noiseW, 'bandpass', 3400, 0.5, 0);
    amb.hush = loopNoise(noiseB, 'lowpass', 90, 0.4, 0);       /* snow: the city goes quiet */
    /* the sea breathes: a slow swell on the band's frequency and level */
    const lfo = ctx.createOscillator(), lg = ctx.createGain(); lfo.frequency.value = 0.11; lg.gain.value = 180; lfo.connect(lg); lg.connect(amb.sea.fl.frequency); lfo.start();
    const lfo2 = ctx.createOscillator(), lg2 = ctx.createGain(); lfo2.frequency.value = 0.07; lg2.gain.value = 120; lfo2.connect(lg2); lg2.connect(amb.wind.fl.frequency); lfo2.start();
    setInterval(creatures, 450);
    setInterval(siteLoop, 140);
  }
  let seaMix = 0, seaAt = 0;
  function seaNearness() {
    const now = performance.now();
    if (now - seaAt < 600) return seaMix;
    seaAt = now;
    try {
      let n = 0, k = 0;
      for (let a = 0; a < 8; a++) for (const r of [4, 9, 16]) {
        const t = tile(Math.round(cam.tx + Math.cos(a * 0.785) * r), Math.round(cam.ty + Math.sin(a * 0.785) * r));
        k++; if (!t || isWater(t.t)) n++;
      }
      seaMix = n / k;
    } catch (e) { seaMix = 0 }
    return seaMix;
  }
  let fr = { sites: 0, ug: false, zoom: 1, night: 0 }, frAt = 0, pausedNow = false;
  /* The game is paused: the music fades out and holds its place, the rain and the city stop. They come
     back where they left off when the game runs again. */
  function applyPause() {
    if (!ctx || !cur) return;
    const t = ctx.currentTime, c = cur;
    clearTimeout(c.pt);
    try { c.g.gain.cancelScheduledValues(t) } catch (e) { }
    if (pausedNow) {
      c.g.gain.setTargetAtTime(0.0001, t, 0.16);
      c.pt = setTimeout(() => { if (pausedNow && cur === c) c.a.pause() }, 650);
    } else {
      if (c.a.paused && !(st.muted || st.music < 0.02)) c.a.play().catch(() => { });
      c.g.gain.setTargetAtTime(c.fading ? 0.0001 : c.level, t, 0.45);
    }
  }
  /* called by the renderer every frame; thins itself to ten times a second */
  function sfxFrame(o) {
    fr = o;
    if (!ctx) return;
    if (!!o.paused !== pausedNow) { pausedNow = !!o.paused; applyPause() }
    const now = performance.now(); if (now - frAt < 100) return; frAt = now;
    const t = ctx.currentTime, z = clamp(o.zoom, 0.25, 1.6), near = clamp(0.30 + z * 0.62, 0.3, 1.2);
    const ug = o.ug ? 0.25 : 1, sea = seaNearness();
    const pop = (typeof G !== 'undefined' && G && G.pop) || 0, jam = (typeof G !== 'undefined' && G && G.traffic) || 0;
    amb.sea.g.gain.setTargetAtTime(0.09 * sea * near * ug, t, 0.6);
    amb.wind.g.gain.setTargetAtTime((0.025 + 0.05 * (1 - Math.min(1, pop / 3000))) * near * ug, t, 0.8);
    const run = pausedNow ? 0 : 1;                                       /* no traffic hum or hammering while stopped */
    amb.city.g.gain.setTargetAtTime(Math.min(0.13, pop / 22000 + jam * 0.025) * near * ug * run, t, 0.4);
    amb.work.g.gain.setTargetAtTime(Math.min(1, o.sites / 2) * 0.10 * near * ug * run, t, 0.25);
    const rain = o.rain || 0, snow = o.snow || 0, storm = o.storm || 0;
    amb.rain.g.gain.setTargetAtTime(0.15 * rain * ug * clamp(0.5 + near * 0.5, 0.5, 1), t, 0.8);
    amb.rain.fl.frequency.setTargetAtTime(2600 + 1600 * (1 - storm), t, 1.5);
    amb.hush.g.gain.setTargetAtTime(0.06 * snow * ug, t, 1.5);
    /* wind rises with a storm and in the cold; the city hum and the sea sink under snow */
    amb.wind.g.gain.setTargetAtTime((0.025 + 0.05 * (1 - Math.min(1, pop / 3000)) + 0.07 * storm + 0.02 * snow) * near * ug, t, 0.8);
    amb.city.g.gain.setTargetAtTime(Math.min(0.13, pop / 22000 + jam * 0.025) * near * ug * (1 - 0.5 * snow) * run, t, 0.5);
  }
  /* birds by day over a small town, crickets by night, a distant gull near the water */
  function creatures() {
    if (!ctx || st.muted || st.amb < 0.02 || fr.ug || fr.paused || (fr.rain || 0) > 0.3 || (fr.snow || 0) > 0.3) return;     /* the birds shelter */
    const day = 1 - clamp(fr.night * 1.6, 0, 1), pop = (typeof G !== 'undefined' && G && G.pop) || 0, sea = seaMix;
    if (day > 0.4 && Math.random() < 0.20 * (1 - Math.min(1, pop / 5000))) {
      const f = rnd(2600, 4200), n = 2 + Math.floor(Math.random() * 4);
      for (let i = 0; i < n; i++) tone(f * (1 + i * 0.05), 0.07, { vol: 0.035, type: 'sine', at: i * 0.09, slide: rnd(0.8, 1.3), bus: ambBus });
    }
    if (day > 0.3 && sea > 0.25 && Math.random() < 0.06) {
      const f = rnd(1500, 1900);
      tone(f, 0.38, { vol: 0.03, type: 'triangle', slide: 0.6, bus: ambBus, lp: 3200 });
      tone(f * 1.1, 0.30, { vol: 0.025, type: 'triangle', slide: 0.55, at: 0.4, bus: ambBus, lp: 3200 });
    }
    if (fr.night > 0.5 && Math.random() < 0.55) {
      const f = rnd(4300, 4900);
      for (let i = 0; i < 4; i++) tone(f, 0.035, { vol: 0.022, type: 'sine', at: i * 0.07, bus: ambBus });
    }
  }
  /* what a working site sounds like, between the steady rumble: knocks, a drill, a reversing beep */
  let nextKnock = 0, nextDrill = 0, nextBeep = 0, burst = 0;
  function siteLoop() {
    if (!ctx || st.muted || fr.ug || fr.paused || !fr.sites) return;
    const now = ctx.currentTime, near = clamp(0.28 + fr.zoom * 0.7, 0.3, 1.1), busy = Math.min(1, fr.sites / 2);
    const scale = near * (0.6 + 0.4 * busy);
    if (now > nextKnock) {
      if (burst <= 0) { burst = 3 + Math.floor(Math.random() * 4); nextKnock = now + rnd(0.8, 2.2) }
      else { knock(0, 0.10 * scale); burst--; nextKnock = now + (burst ? 0.22 : rnd(1.0, 2.6)) }
    }
    if (now > nextDrill && Math.random() < 0.5) {
      nextDrill = now + rnd(5, 11);
      for (let i = 0; i < 6; i++) tone(rnd(150, 210), 0.07, { vol: 0.045 * scale, type: 'sawtooth', lp: 900, at: i * 0.075, a: 0.01, bus: ambBus });
    }
    if (now > nextBeep) {
      nextBeep = now + rnd(4, 9);
      for (let i = 0; i < 3; i++) tone(1000, 0.14, { vol: 0.038 * scale, type: 'square', lp: 2600, at: i * 0.32, a: 0.01, bus: ambBus });
    }
  }

  /* ------------------------------------------------------------ music */
  /* Recorded tracks only (3d/audio/music/playlist.json, all CC0; see CREDITS.md there).
     Each carries a `gain` that levels it to about -20 LUFS, a `mood` (day, night, any) and
     how many times a short loop is repeated. A track fades in, plays, fades out over its last
     four seconds, and the next one — drawn from the pool for the time of day, never the one
     just heard — starts after a few seconds of quiet. */
  let playlist = null, cur = null, lastTrack = -1, nextTimer = 0, musicOn = false;
  function loadPlaylist() {
    if (!window.AR_MUSIC) return Promise.resolve(null);      /* build.py says whether a playlist ships */
    return fetch('3d/audio/music/playlist.json', { cache: 'no-cache' }).then(r => r.ok ? r.json() : null).catch(() => null);
  }
  function stopCurrent(fade) {
    if (!cur) return;
    const c = cur; cur = null; clearTimeout(c.timer);
    try { c.g.gain.cancelScheduledValues(ctx.currentTime); c.g.gain.setTargetAtTime(0.0001, ctx.currentTime, fade || 0.4) } catch (e) { }
    setTimeout(() => { try { c.a.pause(); c.g.disconnect() } catch (e) { } }, (fade || 0.4) * 4000 + 200);
  }
  function playNext(delayMs) {
    clearTimeout(nextTimer);
    nextTimer = setTimeout(() => {
      if (!playlist || !playlist.length || !musicOn || !ctx) return;
      if (st.muted || st.music < 0.02 || pausedNow) { nextTimer = setTimeout(() => playNext(0), 1500); return }
      const night = (fr.night || 0) > 0.5;
      let pool = playlist.map((p, i) => i).filter(i => i !== lastTrack && (playlist[i].mood === 'any' || !playlist[i].mood || (night ? playlist[i].mood === 'night' : playlist[i].mood === 'day')));
      if (!pool.length) pool = playlist.map((p, i) => i).filter(i => i !== lastTrack);
      if (!pool.length) pool = [0];
      const idx = pick(pool), tr = playlist[idx]; lastTrack = idx;
      const a = new Audio('3d/audio/music/' + tr.file); a.preload = 'auto';
      const src = ctx.createMediaElementSource(a), g = ctx.createGain();
      g.gain.value = 0.0001; src.connect(g); g.connect(musicBus);
      const level = clamp(tr.gain == null ? 1 : tr.gain, 0.2, 3);
      g.gain.setTargetAtTime(level, ctx.currentTime, 1.2);
      let plays = 0; const loops = Math.max(1, tr.loops | 0);
      const c = cur = { a, g, tr, timer: 0, level };
      const fadeOut = () => { if (cur !== c) return; g.gain.setTargetAtTime(0.0001, ctx.currentTime, 1.2) };
      a.addEventListener('timeupdate', () => {
        if (cur !== c || !a.duration) return;
        if (plays + 1 >= loops && a.currentTime > a.duration - 4 && !c.fading) { c.fading = true; fadeOut() }
      });
      a.addEventListener('ended', () => {
        if (cur !== c) return;
        if (++plays < loops) { a.currentTime = 0; a.play().catch(() => { }); return }
        cur = null; try { g.disconnect() } catch (e) { }
        playNext(rnd(3500, 9000));
      });
      a.addEventListener('error', () => { if (cur === c) { cur = null; playNext(2000) } });
      a.play().catch(() => { cur = null; playNext(4000) });
      api.now = tr; api.nowAt = performance.now();
      if (window.onMusicChange) window.onMusicChange(tr);
    }, delayMs == null ? 0 : delayMs);
  }
  function startMusic() {
    musicOn = true;
    loadPlaylist().then(pl => { if (pl && pl.length) { playlist = pl; api.playlist = pl; playNext(800) } });
  }
  /* skip to the next track (the settings sheet has the button) */
  function skip() { if (!playlist) return; stopCurrent(0.5); playNext(700) }
  /* a track that should not play when the music is off or the page is muted */
  setInterval(() => {
    if (!cur || !ctx) return;
    const quiet = st.muted || st.music < 0.02 || pausedNow;
    if (quiet && !cur.a.paused && (!pausedNow || !cur.pt)) cur.a.pause();
    else if (!quiet && cur.a.paused && cur.a.currentTime < cur.a.duration - 0.2) cur.a.play().catch(() => { });
  }, 1000);

  /* ------------------------------------------------------------ the page's side */
  const api = window.arAudio = {
    st, now: null, playlist: null, nowAt: 0,
    skip() { skip() },
    get current() { return cur ? { title: cur.tr.title, time: cur.a.currentTime, duration: cur.a.duration, paused: cur.a.paused, error: !!cur.a.error, gain: cur.level } : null },
    get ready() { return !!ctx },
    get paused() { return pausedNow },
    set(k, v) { st[k] = v; save(); applyVolumes() },
    toggleMute() { st.muted = !st.muted; save(); applyVolumes(); return st.muted },
    unlock,
  };
  window.sfx = sfx; window.sfxFrame = sfxFrame;
  for (const ev of ['pointerdown', 'keydown', 'touchend']) window.addEventListener(ev, unlock, { once: false, passive: true });
  /* every ordinary button gets a tick; the dock and the tools say their own thing */
  document.addEventListener('click', e => {
    const b = e.target && e.target.closest && e.target.closest('button, .seg button, [role=button]');
    if (b && !b.closest('#tools') && !b.classList.contains('t')) sfx('click');
  }, true);
})();

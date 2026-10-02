(() => {
'use strict';

/* ---------- utilidades de texto ---------- */

const $ = (s, ctx = document) => ctx.querySelector(s);
const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const fmt = n => n.toLocaleString('es-AR');
const esperar = ms => new Promise(r => setTimeout(r, ms));

/** minusculas, sin tildes ni signos */
const norm = s => (s || '').toLowerCase().normalize('NFD').replace(/[̀-ͯ]/g, '')
  .replace(/[^a-z0-9 ]+/g, ' ').replace(/\s+/g, ' ').trim();

/** raiz simple: quita plural y la vocal final (pirata/piratas, zombi/zombies) */
function stem(w) {
  if (w.length > 3 && w.endsWith('ces')) return w.slice(0, -3) + 'z';
  if (w.length > 3 && w.endsWith('s') && !w.endsWith('ss')) w = w.slice(0, -1);
  if (w.length > 3 && /[aeo]$/.test(w)) w = w.slice(0, -1);
  return w;
}

const STOPS = new Set(('de del la las el los un una unos unas y o u con sin en a al por para que se su sus mi me ' +
  'foto fotos imagen imagenes vestido vestida vestidos vestidas disfrazado disfrazada disfrazados disfrazadas ' +
  'disfraz disfraces como persona personas gente alguien algo mas muy lleva llevan es son esta estan hay ver ' +
  'quiero busco buscar edicion ediciones amigos amigas chicos chicas muchachos muchachas todos todas').split(' ').map(w => stem(norm(w))));

/** distancia de edicion (con letras cambiadas de lugar) y corte: devuelve max+1 si se pasa */
function lev(a, b, max) {
  if (Math.abs(a.length - b.length) > max) return max + 1;
  let ant = null;
  let prev = Array.from({ length: b.length + 1 }, (_, i) => i);
  for (let i = 1; i <= a.length; i++) {
    const cur = [i];
    let minimo = i;
    for (let j = 1; j <= b.length; j++) {
      let v = Math.min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1));
      if (ant && i > 1 && j > 1 && a[i - 1] === b[j - 2] && a[i - 2] === b[j - 1]) v = Math.min(v, ant[j - 2] + 1);
      cur[j] = v;
      if (v < minimo) minimo = v;
    }
    if (minimo > max) return max + 1;
    ant = prev;
    prev = cur;
  }
  return prev[b.length];
}

const guardar = (k, v) => { try { localStorage.setItem(k, JSON.stringify(v)); } catch { /* sin storage */ } };
const leer = (k, def) => { try { return JSON.parse(localStorage.getItem(k)) ?? def; } catch { return def; } };

/* ---------- estado ---------- */

const el = {
  q: $('#q'), form: $('#form-buscar'), borrar: $('#borrar'),
  resumen: $('#resumen'), selTodas: $('#sel-todas'),
  grilla: $('#grilla'), vacio: $('#vacio'), sugeridas: $('#sugeridas'),
  barra: $('#barra-sel'), selCuenta: $('#sel-cuenta'), selLimpiar: $('#sel-limpiar'), selZip: $('#sel-zip'),
  visor: $('#visor'), visorImg: $('#visor-img'), visorPos: $('#visor-pos'), visorTags: $('#visor-tags'),
  visorSel: $('#visor-sel'), visorDl: $('#visor-dl'), visorCerrar: $('#visor-cerrar'),
  visorAnt: $('#visor-ant'), visorSig: $('#visor-sig'),
};

const MAX_ZIP = 150;

let CONF, FOTOS = [], VOCAB = {};
let vista = [];
let edVista = '';   // edicion abierta ('' = pantalla principal con las tiras)
let vistaSel = [];  // fotos a las que apunta "Seleccionar estas N"
let RANK = new Map();   // etiqueta -> indices de las fotos mas parecidas (data/rank.json)
const porIdx = [];      // indice original en index.json -> foto
const porId = new Map(); // id de foto -> foto
let visorIdx = -1;
let seq = 0;
let iaActiva = true;
const elegidas = new Set();
const liPorId = new Map();
const nombreEd = new Map();
const edInfo = new Map();   // slug -> {nombre, anio}

const termMap = new Map();      // "pirat" -> Map(etiqueta -> peso)
const parcialMap = new Map();   // palabra suelta de un termino largo
const unaPalabra = [];
const edMap = new Map();        // "segund" -> "segunda"
const tagSet = new Set();
const df = new Map();
const iaCache = new Map(Object.entries(leer('dc_ia', {})));

/* ---------- indice del vocabulario ---------- */

function sumarA(mapa, clave, tag, peso) {
  let m = mapa.get(clave);
  if (!m) mapa.set(clave, m = new Map());
  if ((m.get(tag) || 0) < peso) m.set(tag, peso);
}

function indexarVocab() {
  for (const items of Object.values(VOCAB)) {
    for (const { tag, sin } of items) {
      tagSet.add(tag);
      const terminos = [[tag, 1], ...sin.map(s => [s, 0.85])];
      for (const [termino, peso] of terminos) {
        const toks = norm(termino).split(' ').map(stem);
        sumarA(termMap, toks.join(' '), tag, peso);
        if (toks.length > 1) {
          for (const t of toks) if (t.length >= 4 && !STOPS.has(t)) sumarA(parcialMap, t, tag, peso * 0.55);
        }
      }
    }
  }
  for (const k of termMap.keys()) if (!k.includes(' ')) unaPalabra.push(k);
  for (const ed of CONF.ediciones) {
    nombreEd.set(ed.slug, ed.nombre + (ed.anio ? ' ' + ed.anio : ''));
    edInfo.set(ed.slug, ed);
    edMap.set(stem(norm(ed.slug)), ed.slug);
    if (ed.anio) edMap.set(String(ed.anio), ed.slug);
  }
}

/** coincidencia por prefijo (mientras se escribe) o con errores de tipeo */
function aproximar(tok) {
  const res = new Map();
  const sumar = (clave, f) => {
    for (const [tag, w] of termMap.get(clave)) if ((res.get(tag) || 0) < w * f) res.set(tag, w * f);
  };
  if (tok.length >= 3) for (const k of unaPalabra) if (k !== tok && k.startsWith(tok)) sumar(k, 0.8);
  if (!res.size && tok.length >= 4) {
    const max = tok.length >= 8 ? 2 : 1;
    let mejor = max + 1;
    const cand = [];
    for (const k of unaPalabra) {
      if (tok.length < 5 && k[0] !== tok[0]) continue;   // palabras cortas: misma inicial para no confundir
      const d = lev(tok, k, max);
      if (d <= max) { cand.push([k, d]); if (d < mejor) mejor = d; }
    }
    for (const [k, d] of cand) if (d === mejor) sumar(k, 0.75 - 0.1 * (d - 1));
  }
  // si dos palabras quedan a la misma distancia (pirta: pirata / pista), gana la de etiqueta principal
  const mayor = Math.max(0, ...res.values());
  for (const [tag, v] of res) if (v < mayor * 0.9) res.delete(tag);
  return res.size ? res : null;
}

/* ---------- interpretar la busqueda ---------- */

function interpretar(texto) {
  const crudas = norm(texto).split(' ').filter(Boolean);
  const toks = crudas.map(stem);
  const usado = toks.map(() => false);
  const conceptos = [];
  const eds = new Set();

  // frases de 3, 2 y 1 palabra contra el vocabulario
  for (let n = Math.min(3, toks.length); n >= 1; n--) {
    for (let i = 0; i + n <= toks.length; i++) {
      if (usado.slice(i, i + n).some(Boolean)) continue;
      const clave = toks.slice(i, i + n).join(' ');
      if (n === 1 && edMap.has(clave)) { eds.add(edMap.get(clave)); usado[i] = true; continue; }
      if (n === 1 && STOPS.has(clave)) continue;
      const tags = termMap.get(clave);
      if (!tags) continue;
      conceptos.push({ pos: i, etiqueta: crudas.slice(i, i + n).join(' '), tags });
      for (let k = i; k < i + n; k++) usado[k] = true;
    }
  }

  // palabras sueltas: parte de un termino largo, prefijo o error de tipeo
  const desconocidas = [];
  toks.forEach((t, i) => {
    if (usado[i] || STOPS.has(t) || t.length < 2) return;
    const tags = parcialMap.get(t) || aproximar(t);
    if (tags) conceptos.push({ pos: i, etiqueta: crudas[i], tags });
    else desconocidas.push(crudas[i]);
  });

  conceptos.sort((a, b) => a.pos - b.pos);
  return { conceptos, eds, desconocidas };
}

/* ---------- busqueda con IA para palabras que no conocemos ---------- */

async function iaExpandir(texto) {
  if (!iaActiva) return [];
  const clave = norm(texto);
  if (iaCache.has(clave)) return iaCache.get(clave);
  try {
    const r = await fetch('buscar.php?q=' + encodeURIComponent(texto));
    if (!r.ok) throw new Error(r.status);
    const j = await r.json();
    if (j.ia === false) { iaActiva = false; return []; }
    const tags = Array.isArray(j.tags) ? j.tags.filter(t => tagSet.has(t)) : [];
    iaCache.set(clave, tags);
    guardar('dc_ia', Object.fromEntries(iaCache));
    return tags;
  } catch {
    return [];
  }
}

/* ---------- puntuar fotos ---------- */

function calcular(conceptos, eds) {
  let lista = FOTOS;
  if (eds.size) lista = lista.filter(p => eds.has(p.ed));   // solo si la busqueda nombra una edicion
  if (!conceptos.length) return { lista, relacionadas: [], parcial: false, maxCoinc: 0 };

  const puntuadas = [];
  let maxCoinc = 0;
  for (const p of lista) {
    let total = 0, coinc = 0;
    for (const c of conceptos) {
      let mejor = 0;
      for (const [tag, peso] of c.tags) {
        const pr = p.tm.get(tag);
        if (pr && peso * pr > mejor) mejor = peso * pr;
      }
      if (mejor > 0) { coinc++; total += mejor; }
    }
    if (coinc) { puntuadas.push([p, coinc, total]); if (coinc > maxCoinc) maxCoinc = coinc; }
  }
  const exactas = puntuadas.filter(x => x[1] === maxCoinc).sort((a, b) => b[2] - a[2]).map(x => x[0]);
  return {
    lista: exactas,
    relacionadas: relacionadasDe(conceptos, lista, new Set(exactas.map(p => p.id))),
    parcial: maxCoinc < conceptos.length,
    maxCoinc,
  };
}

/** fotos parecidas a lo buscado aunque la IA no les haya puesto la etiqueta (ranking de data/rank.json) */
function relacionadasDe(conceptos, base, excluidas) {
  if (!RANK.size) return [];
  const porConcepto = conceptos.map(c => {
    const m = new Map();   // id de foto -> parecido 0..1
    for (const [tag, peso] of c.tags) {
      const orden = RANK.get(tag);
      if (!orden) continue;
      orden.forEach((idx, pos) => {
        const p = porIdx[idx];
        const v = p ? peso * (1 - pos / orden.length) : 0;
        if (v > (m.get(p?.id) || 0)) m.set(p.id, v);
      });
    }
    return m;
  });
  const res = [];
  for (const p of base) {
    if (excluidas.has(p.id)) continue;
    let suma = 0, ok = true;
    conceptos.forEach((c, k) => {
      if (!ok) return;
      let v = porConcepto[k].get(p.id) || 0;
      for (const [tag, peso] of c.tags) {          // si en ese termino es coincidencia exacta, vale mas
        const pr = p.tm.get(tag);
        if (pr && peso * pr > v) v = peso * pr;
      }
      if (v <= 0) ok = false; else suma += v;
    });
    if (ok) res.push([p, suma]);
  }
  return res.sort((a, b) => b[1] - a[1]).slice(0, MAX_REL).map(x => x[0]);
}

/* ---------- pintar ---------- */

function altDe(p) {
  const claves = p.tags.filter(t => t[1] === 'disfraz' || t[1] === 'escena').map(t => t[0]);
  return `Foto de ${nombreEd.get(p.ed) || p.ed}` + (claves.length ? ': ' + claves.join(', ') : '');
}

/** rotulo de la miniatura: personaje o disfraz concreto mas probable (nunca los genericos) */
const GENERICAS = new Set(['sin disfraz', 'disfraz grupal', 'pareja disfrazada']);
function rotuloDe(p) {
  const peso = t => t[2] + (t[1] === 'personaje' ? 1 : 0);
  const t = p.tags.filter(x => (x[1] === 'personaje' || x[1] === 'disfraz') && !GENERICAS.has(x[0]))
    .sort((a, b) => peso(b) - peso(a))[0];
  return t ? t[0] : '';
}

const MUESTRA = 20;     // fotos de muestra por edicion cuando no se busca nada
const MAX_REL = 60;     // fotos relacionadas que se suman a los resultados de una busqueda
const cacheMuestra = new Map();

/** muestra de una edicion: un disfraz distinto en cada foto, las mas claras primero */
function muestraDe(ed) {
  if (cacheMuestra.has(ed)) return cacheMuestra.get(ed);
  const delEd = FOTOS.filter(p => p.ed === ed);
  const cand = [];
  for (const p of delEd) {
    const t = p.tags.filter(x => (x[1] === 'personaje' || x[1] === 'disfraz') && !GENERICAS.has(x[0]))
      .sort((a, b) => b[2] - a[2])[0];
    if (!t) continue;
    const gente = p.tm.has('una persona') ? 0.6 : p.tm.has('dos personas') ? 0.3 : 0;
    cand.push({ p, rotulo: t[0], valor: t[2] + gente });
  }
  cand.sort((a, b) => b.valor - a.valor);
  const vistos = new Set(), salida = [];
  for (const c of cand) {
    if (vistos.has(c.rotulo)) continue;
    vistos.add(c.rotulo);
    salida.push(c.p);
    if (salida.length >= MUESTRA) break;
  }
  const paso = Math.max(1, Math.floor(delEd.length / MUESTRA));
  for (let i = 0; salida.length < Math.min(MUESTRA, delEd.length) && i < delEd.length; i += paso) {
    if (!salida.includes(delEd[i])) salida.push(delEd[i]);
  }
  cacheMuestra.set(ed, salida);
  return salida;
}

function crearFoto(p, conAnio = false) {
  const i = vista.length;
  vista.push(p);
  const li = document.createElement('li');
  const ok = elegidas.has(p.id);
  const anio = conAnio ? edInfo.get(p.ed)?.anio : '';
  li.className = 'foto' + (ok ? ' elegida' : '');
  li.tabIndex = 0;
  li.dataset.i = i;
  li.dataset.id = p.id;
  li.style.setProperty('--r', (p.tw / p.th).toFixed(4));
  li.innerHTML =
    `<img src="${esc(p.t)}" width="${p.tw}" height="${p.th}" loading="lazy" decoding="async" alt="${esc(altDe(p))}">` +
    (rotuloDe(p) ? `<span class="etq">${esc(rotuloDe(p))}</span>` : '') +
    (anio ? `<span class="anio-chip">${esc(anio)}</span>` : '') +
    `<button type="button" class="sel" aria-pressed="${ok}" aria-label="Seleccionar foto">${ok ? '✓' : '+'}</button>` +
    `<a class="bajar" href="${esc(p.w)}" download="Disfracity-${esc(p.id)}.jpg" aria-label="Descargar foto">↓</a>`;
  liPorId.set(p.id, li);
  return li;
}

function tituloEd(ed, n) {
  const info = edInfo.get(ed) || { nombre: ed };
  return `<h2 class="anio-t">${info.anio ? `<span class="anio-n">${esc(info.anio)}</span>` : ''}` +
    `<span class="anio-e">${esc(info.nombre)}</span>` +
    `<span class="anio-c">${fmt(n)} ${n === 1 ? 'foto' : 'fotos'}</span></h2>`;
}

/** una tanda de la pantalla principal: titulo del anio y tira horizontal con fotos de muestra */
function crearTanda(ed, total, mostradas) {
  const sec = document.createElement('section');
  sec.className = 'anio tanda';
  sec.innerHTML =
    `<div class="tanda-cab">${tituloEd(ed, total)}<button type="button" class="anio-ver" data-ed="${esc(ed)}">Ver todas →</button></div>` +
    `<div class="tira-caja"><button type="button" class="flecha-tira izq" aria-label="Fotos anteriores">‹</button>` +
    `<ul class="tira"></ul>` +
    `<button type="button" class="flecha-tira der" aria-label="Más fotos">›</button></div>`;
  const ul = $('.tira', sec);
  for (const p of mostradas) ul.append(crearFoto(p));
  const mas = document.createElement('li');
  mas.className = 'mas';
  mas.innerHTML = `<button type="button" class="ver-todas" data-ed="${esc(ed)}"><span>${total === 1 ? 'Ver la foto' : `Ver las ${fmt(total)} fotos`}</span><b aria-hidden="true">→</b></button>`;
  ul.append(mas);
  return sec;
}

/** encabezado de la pagina de una edicion */
function cabeceraAnio(ed, n) {
  const sec = document.createElement('section');
  sec.className = 'anio';
  sec.innerHTML = `<button type="button" class="volver">← Todas las ediciones</button>${tituloEd(ed, n)}`;
  return sec;
}

/** todas las fotos de una edicion, en filas */
function grillaNormal(lista) {
  const ul = document.createElement('ul');
  ul.className = 'grilla';
  for (const p of lista) ul.append(crearFoto(p));
  return ul;
}

/** resultados de una busqueda: fotos grandes, primero las que coinciden y despues las relacionadas */
function bloquesResultado(exactas, relacionadas, conAnio) {
  const armar = (fotos, titulo) => {
    const sec = document.createElement('section');
    sec.className = 'resultado';
    sec.innerHTML = (titulo ? `<h3 class="rel-t">${titulo}<span>${fmt(fotos.length)} ${fotos.length === 1 ? 'foto' : 'fotos'}</span></h3>` : '') +
      '<ul class="grilla grande"></ul>';
    const ul = $('.grilla', sec);
    for (const p of fotos) ul.append(crearFoto(p, conAnio));
    return sec;
  };
  const bloques = [];
  if (exactas.length) bloques.push(armar(exactas, ''));
  if (relacionadas.length) bloques.push(armar(relacionadas, 'Relacionadas'));
  return bloques;
}

/* ---------- tiras en movimiento ----------
   Cada tira avanza sola, una hacia cada lado, como fotos que van pasando. Se frena al pasar el mouse,
   al tocarla, con el teclado y mientras esta abierto el visor; sigue pudiendo moverse a mano.
   Para que el giro no tenga corte se agrega una copia de las fotos al final de la tira. */
const VELOCIDAD = 46;   // px por segundo
const movimientoReducido = matchMedia('(prefers-reduced-motion: reduce)').matches;
let tirasAuto = [];
let rafTiras = 0, tUltimo = 0;
const observador = 'IntersectionObserver' in window
  ? new IntersectionObserver(entradas => {
    for (const e of entradas) {
      const s = tirasAuto.find(x => x.caja === e.target);
      if (s) s.visible = e.isIntersecting;
    }
  })
  : null;

function detenerTiras() {
  cancelAnimationFrame(rafTiras);
  observador?.disconnect();
  for (const s of tirasAuto) s.ul.querySelectorAll('[data-clon]').forEach(c => c.remove());
  tirasAuto = [];
}

function bucleTiras(t) {
  const dt = Math.min(0.064, (t - tUltimo) / 1000);
  tUltimo = t;
  const visorAbierto = !el.visor.hidden;
  for (const s of tirasAuto) {
    const quieta = s.cerca || s.tocando || s.enfoque || !s.visible || visorAbierto || t < s.pausa;
    s.corriendo = !quieta;
    if (quieta) { s.pos = s.ul.scrollLeft; continue; }
    s.pos += s.dir * s.velocidad * dt;
    if (s.pos >= s.ciclo) s.pos -= s.ciclo; else if (s.pos < 0) s.pos += s.ciclo;
    s.ul.scrollLeft = s.pos;
  }
  rafTiras = requestAnimationFrame(bucleTiras);
}

function activarTiras() {
  detenerTiras();
  if (movimientoReducido) return;
  [...el.grilla.querySelectorAll('.tira-caja')].forEach((caja, k) => {
    const ul = $('.tira', caja);
    const unidad = [...ul.children];
    if (!unidad.length || ul.scrollWidth <= ul.clientWidth + 8) return;   // si cabe entera se queda quieta
    for (const li of unidad) {
      const c = li.cloneNode(true);
      c.dataset.clon = '1';
      c.setAttribute('aria-hidden', 'true');
      c.removeAttribute('tabindex');
      c.querySelectorAll('button, a').forEach(x => { x.tabIndex = -1; });
      ul.append(c);
    }
    const ciclo = ul.children[unidad.length].offsetLeft - ul.children[0].offsetLeft;
    const s = {
      caja, ul, ciclo, dir: k % 2 ? -1 : 1, velocidad: VELOCIDAD + (k % 3) * 4, pos: 0,
      visible: true, cerca: false, tocando: false, enfoque: false, pausa: 0, corriendo: false,
    };
    if (s.dir < 0) ul.scrollLeft = ciclo - 1;   // las que van hacia el otro lado arrancan al final del ciclo
    s.pos = ul.scrollLeft;
    const demora = () => { s.pausa = performance.now() + 3000; };
    caja.addEventListener('mouseenter', () => { s.cerca = true; });
    caja.addEventListener('mouseleave', () => { s.cerca = false; });
    caja.addEventListener('touchstart', () => { s.tocando = true; }, { passive: true });
    caja.addEventListener('touchend', () => { s.tocando = false; demora(); }, { passive: true });
    caja.addEventListener('touchcancel', () => { s.tocando = false; demora(); }, { passive: true });
    caja.addEventListener('focusin', () => { s.enfoque = true; });
    caja.addEventListener('focusout', () => { s.enfoque = false; });
    caja.addEventListener('click', e => { if (e.target.closest('.flecha-tira')) s.pausa = performance.now() + 3500; });
    ul.addEventListener('wheel', demora, { passive: true });
    ul.addEventListener('scroll', () => {   // movida a mano: se mantiene dentro del ciclo
      if (s.corriendo) return;
      const x = ul.scrollLeft;
      if (x >= s.ciclo) ul.scrollLeft = x - s.ciclo; else if (x <= 0) ul.scrollLeft = x + s.ciclo;
    }, { passive: true });
    observador?.observe(caja);
    tirasAuto.push(s);
  });
  if (tirasAuto.length) {
    tUltimo = performance.now();
    rafTiras = requestAnimationFrame(bucleTiras);
  }
}

let temporizadorTamano;
window.addEventListener('resize', () => {
  clearTimeout(temporizadorTamano);
  temporizadorTamano = setTimeout(() => { if (!edVista) activarTiras(); }, 250);
});

function pintar(lista, relacionadas, hayConsulta) {
  detenerTiras();
  liPorId.clear();
  vista = [];
  const frag = document.createDocumentFragment();
  if (edVista) {
    frag.append(cabeceraAnio(edVista, lista.length));
    if (hayConsulta) frag.append(...bloquesResultado(lista, relacionadas, false));
    else frag.append(grillaNormal(lista));
  } else if (hayConsulta) {
    frag.append(...bloquesResultado(lista, relacionadas, true));   // directo a las fotos, grandes
  } else {
    for (const ed of CONF.ediciones.map(e => e.slug).reverse()) {   // la mas nueva primero
      const delEd = lista.filter(p => p.ed === ed);
      if (delEd.length) frag.append(crearTanda(ed, delEd.length, muestraDe(ed)));
    }
  }
  vistaSel = edVista || hayConsulta ? lista : [];
  el.grilla.replaceChildren(frag);
  activarTiras();
}

function textoResumen(r, interp, calc) {
  if (edVista && !interp.conceptos.length && !r.desconocidas.length) return '';   // el titulo del anio ya dice cuantas fotos hay
  const total = calc.lista.length;
  const rel = calc.relacionadas?.length || 0;
  const partes = [total || !rel
    ? `<strong>${fmt(total)} ${total === 1 ? 'foto' : 'fotos'}</strong>`
    : `<strong>${fmt(rel)} ${rel === 1 ? 'foto relacionada' : 'fotos relacionadas'}</strong>`];
  const entendidos = interp.conceptos.map(c => {
    const [mejorTag] = [...c.tags.entries()].sort((a, b) => b[1] - a[1])[0];
    const igual = norm(mejorTag) === c.etiqueta;
    return `<span class="entendi">${esc(igual ? mejorTag : `${c.etiqueta} → ${mejorTag}`)}</span>`;
  });
  if (entendidos.length) partes.push('buscando: ' + entendidos.join(' + '));
  if (total && rel) partes.push(`y ${fmt(rel)} relacionadas`);
  const eds = edVista ? [] : [...interp.eds];
  if (eds.length) partes.push('en ' + eds.map(e => esc(nombreEd.get(e) || e)).join(' y '));
  else if (!interp.conceptos.length && !edVista) partes.push(`en ${CONF.ediciones.length} ediciones`);
  if (calc.parcial && total) {
    partes.push(`ninguna cumple todo, mostrando las que coinciden con ${calc.maxCoinc} de ${interp.conceptos.length}`);
  }
  if (r.desconocidas.length) partes.push(`no conozco: «${esc(r.desconocidas.join(' '))}»`);
  if (r.pensando) partes.push('consultando IA…');
  return partes.join(' · ');
}

function refrescarSel() {
  const n = elegidas.size;
  el.barra.hidden = n === 0;
  if (n) {
    el.selCuenta.textContent = `${fmt(n)} ${n === 1 ? 'seleccionada' : 'seleccionadas'}`;
    el.selZip.disabled = n > MAX_ZIP;
    el.selZip.textContent = n > MAX_ZIP ? `Máximo ${MAX_ZIP} por ZIP` : 'Descargar ZIP';
    el.selZip.style.opacity = n > MAX_ZIP ? '.5' : '';
  }
  const todas = vistaSel.length > 0 && vistaSel.every(p => elegidas.has(p.id));
  el.selTodas.hidden = vistaSel.length === 0 || vistaSel.length > MAX_ZIP;
  el.selTodas.textContent = todas ? 'Quitar selección de estas' : `Seleccionar estas ${fmt(vistaSel.length)}`;
}

function marcarTile(id) {
  const ok = elegidas.has(id);
  for (const li of el.grilla.querySelectorAll(`[data-id="${id}"]`)) {   // incluye las copias de las tiras
    li.classList.toggle('elegida', ok);
    const b = $('.sel', li);
    b.textContent = ok ? '✓' : '+';
    b.setAttribute('aria-pressed', String(ok));
  }
}

function alternarSel(id) {
  if (elegidas.has(id)) elegidas.delete(id); else elegidas.add(id);
  marcarTile(id);
  if (visorIdx >= 0 && vista[visorIdx]?.id === id) actualizarBotonVisor();
  refrescarSel();
}

function actualizarHash(empujar = false) {
  const p = new URLSearchParams();
  if (edVista) p.set('ed', edVista);
  if (el.q.value.trim()) p.set('q', el.q.value.trim());
  const h = p.toString();
  const url = h ? '#' + h : location.pathname + location.search;
  if (empujar) history.pushState(null, '', url); else history.replaceState(null, '', url);
}

/** lleva la pantalla a los resultados: las sugeridas quedan justo debajo del buscador y despues las fotos.
    siempre=false: solo si no se ven bien (al ir escribiendo no queremos saltos de mas) */
function irAResultados(siempre) {
  const barra = $('.barra');
  const arriba = el.sugeridas.getBoundingClientRect().top;
  const bien = arriba >= barra.offsetHeight && arriba <= innerHeight * 0.4;
  if (!siempre && bien) return;
  window.scrollTo({ top: Math.max(0, scrollY + arriba - barra.offsetHeight - 6), behavior: movimientoReducido ? 'auto' : 'smooth' });
}

function entrarAnio(ed) {
  edVista = ed;
  actualizarHash(true);
  buscar({ inmediato: true });
  ponerEjemplo();
  window.scrollTo({ top: 0 });
}

function salirAnio() {
  edVista = '';
  actualizarHash(true);
  buscar({ inmediato: true });
  ponerEjemplo();
  window.scrollTo({ top: 0 });
}

/** frases de ejemplo del cuadro de busqueda: los disfraces que mas aparecen en las fotos */
let ejemplos = ['pirata', 'gente bailando', 'disfraz rojo'];
let sugeridas = [];   // busquedas sugeridas: los disfraces con mas fotos
function calcularEjemplos() {
  for (const p of FOTOS) for (const [tag] of p.tags) df.set(tag, (df.get(tag) || 0) + 1);
  const top = (grupo, n) => (VOCAB[grupo] || []).map(i => i.tag)
    .filter(t => !GENERICAS.has(t) && (df.get(t) || 0) >= 8)
    .sort((a, b) => df.get(b) - df.get(a)).slice(0, n);
  ejemplos = [...top('disfraz', 6), ...top('personaje', 4), 'gente bailando', 'brindando'];
  sugeridas = [...top('disfraz', 8), ...top('personaje', 5)].sort((a, b) => df.get(b) - df.get(a));
  for (let i = ejemplos.length - 1; i > 0; i--) {
    const k = Math.floor(Math.random() * (i + 1));
    [ejemplos[i], ejemplos[k]] = [ejemplos[k], ejemplos[i]];
  }
}

function pintarSugeridas() {
  el.sugeridas.innerHTML = '<span class="rotulo">Probá con</span>' + sugeridas.map(t =>
    `<button type="button" class="chip" data-q="${esc(t)}" aria-pressed="false">${esc(t)}</button>`).join('');
}

function marcarSugeridas() {
  const actual = norm(el.q.value);
  for (const b of el.sugeridas.querySelectorAll('[data-q]')) b.setAttribute('aria-pressed', String(norm(b.dataset.q) === actual));
}

let ponerEjemplo = () => {};
function rotarEjemplos() {
  let n = 0;
  ponerEjemplo = () => {
    if (document.hidden || el.q.value) return;
    const info = edInfo.get(edVista);
    const donde = edVista ? `Buscar en ${info?.anio || info?.nombre || edVista}` : 'Probá';
    el.q.placeholder = `${donde}: ${ejemplos[n++ % ejemplos.length]}…`;
  };
  ponerEjemplo();
  setInterval(ponerEjemplo, 3200);
}

/* ---------- ciclo de busqueda ---------- */

async function buscar({ inmediato = false, ir = '' } = {}) {
  const mi = ++seq;
  let yaFui = false;
  const texto = el.q.value;
  el.borrar.hidden = !texto;
  actualizarHash();

  const interp = interpretar(texto);
  let conceptos = interp.conceptos;
  const dibujar = (extra = {}) => {
    const calc = calcular(conceptos, edVista ? new Set([edVista]) : interp.eds);
    const sinEntender = interp.desconocidas.length > 0 && !conceptos.length;
    const lista = sinEntender ? [] : calc.lista;
    const relacionadas = sinEntender ? [] : calc.relacionadas;
    pintar(lista, relacionadas, conceptos.length > 0);
    el.resumen.innerHTML = textoResumen({ desconocidas: interp.desconocidas, ...extra }, { ...interp, conceptos }, { ...calc, lista, relacionadas });
    el.vacio.hidden = lista.length + relacionadas.length > 0;
    el.vacio.textContent = 'No encontré fotos con eso. Probá con otra palabra, por ejemplo un disfraz o un color.';
    if (!lista.length && !relacionadas.length && conceptos.length && (edVista || interp.eds.size)) {
      const otras = calcular(conceptos, new Set()).lista.length;
      if (otras) {
        el.vacio.textContent = edVista
          ? `No hay fotos de eso en esta edición. En todas las ediciones hay ${fmt(otras)}.`
          : `No hay fotos de eso en esa edición. En las demás hay ${fmt(otras)}: sacá la edición de la búsqueda.`;
      }
    }
    refrescarSel();
    marcarSugeridas();
    if (ir && !yaFui && el.q.value.trim()) { yaFui = true; irAResultados(ir === 'siempre'); }
  };

  dibujar({ pensando: interp.desconocidas.length > 0 && iaActiva });
  if (!interp.desconocidas.length || !iaActiva) return;

  if (!inmediato) await esperar(450);
  if (mi !== seq) return;
  const tags = await iaExpandir(interp.desconocidas.join(' '));
  if (mi !== seq) return;
  if (tags.length) {
    conceptos = conceptos.concat([{ pos: 99, etiqueta: interp.desconocidas.join(' '), tags: new Map(tags.map(t => [t, 0.8])) }]);
    interp.desconocidas = [];
  }
  dibujar({ pensando: false });
}

let temporizador;
el.q.addEventListener('input', () => { clearTimeout(temporizador); temporizador = setTimeout(() => buscar({ ir: 'si-hace-falta' }), 160); });
el.form.addEventListener('submit', e => { e.preventDefault(); clearTimeout(temporizador); buscar({ inmediato: true, ir: 'siempre' }); el.q.blur(); });
el.borrar.addEventListener('click', () => { el.q.value = ''; buscar(); el.q.focus(); });

el.sugeridas.addEventListener('click', e => {
  const b = e.target.closest('[data-q]');
  if (!b) return;
  el.q.value = norm(el.q.value) === norm(b.dataset.q) ? '' : b.dataset.q;   // volver a tocarla la saca
  buscar({ inmediato: true, ir: 'siempre' });
});

/* ---------- seleccion y descarga ---------- */

el.grilla.addEventListener('click', e => {
  const entrar = e.target.closest('[data-ed]');
  if (entrar) { entrarAnio(entrar.dataset.ed); return; }
  if (e.target.closest('.volver')) { salirAnio(); return; }
  const flecha = e.target.closest('.flecha-tira');
  if (flecha) {
    const tira = $('.tira', flecha.parentElement);
    tira.scrollBy({ left: (flecha.classList.contains('izq') ? -1 : 1) * tira.clientWidth * 0.85, behavior: 'smooth' });
    return;
  }
  const li = e.target.closest('.foto');
  if (!li || e.target.closest('.bajar')) return;
  const p = vista[+li.dataset.i];
  if (e.target.closest('.sel')) alternarSel(p.id); else abrirVisor(+li.dataset.i);
});
el.grilla.addEventListener('keydown', e => {
  if ((e.key === 'Enter' || e.key === ' ') && e.target.classList.contains('foto')) {
    e.preventDefault();
    abrirVisor(+e.target.dataset.i);
  }
});

el.selTodas.addEventListener('click', () => {
  const todas = vistaSel.every(p => elegidas.has(p.id));
  for (const p of vistaSel) { if (todas) elegidas.delete(p.id); else elegidas.add(p.id); marcarTile(p.id); }
  refrescarSel();
});
el.selLimpiar.addEventListener('click', () => {
  const ids = [...elegidas];
  elegidas.clear();
  ids.forEach(marcarTile);
  if (visorIdx >= 0) actualizarBotonVisor();
  refrescarSel();
});
/** el ZIP se arma en el navegador (js/zip.js): asi anda en cualquier hosting, sin PHP */
let armandoZip = false;
el.selZip.addEventListener('click', async () => {
  if (!elegidas.size || elegidas.size > MAX_ZIP || armandoZip) return;
  armandoZip = true;
  const ids = [...elegidas];
  const textoBoton = el.selZip.textContent;
  el.selZip.disabled = true;
  try {
    const archivos = [];
    const cola = [...ids];
    let hechas = 0;
    const trabajador = async () => {
      while (cola.length) {
        const id = cola.shift();
        try {
          const r = await fetch(porId.get(id).w);
          if (!r.ok) throw new Error(String(r.status));
          archivos.push({ nombre: `Disfracity-${id}.jpg`, datos: new Uint8Array(await r.arrayBuffer()) });
        } catch { /* esa foto se saltea */ }
        el.selZip.textContent = `Preparando ${++hechas}/${ids.length}…`;
      }
    };
    await Promise.all(Array.from({ length: 4 }, trabajador));   // de a 4 fotos a la vez
    if (!archivos.length) throw new Error('sin fotos');
    archivos.sort((x, y) => x.nombre.localeCompare(y.nombre));
    const url = URL.createObjectURL(crearZip(archivos));
    const enlace = document.createElement('a');
    enlace.href = url;
    enlace.download = 'Disfracity-fotos.zip';
    document.body.append(enlace);
    enlace.click();
    enlace.remove();
    setTimeout(() => URL.revokeObjectURL(url), 60000);
    if (archivos.length < ids.length) el.selCuenta.textContent = `Bajaron ${archivos.length} de ${ids.length}`;
  } catch {
    el.selCuenta.textContent = 'No se pudo armar el ZIP. Probá de nuevo.';
  } finally {
    armandoZip = false;
    el.selZip.disabled = false;
    el.selZip.textContent = textoBoton;
    if (elegidas.size) refrescarSel();
  }
});

/* ---------- visor ---------- */

function actualizarBotonVisor() {
  const p = vista[visorIdx];
  el.visorSel.textContent = elegidas.has(p.id) ? 'Quitar de la selección' : 'Seleccionar';
}

function mostrarVisor() {
  const p = vista[visorIdx];
  el.visorImg.src = p.w;
  el.visorImg.alt = altDe(p);
  el.visorPos.textContent = `${visorIdx + 1} / ${fmt(vista.length)} · ${nombreEd.get(p.ed) || p.ed}`;
  el.visorDl.href = p.w;
  el.visorDl.setAttribute('download', `Disfracity-${p.id}.jpg`);
  actualizarBotonVisor();
  el.visorTags.innerHTML = p.tags.filter(t => t[2] >= 0.2).sort((a, b) => b[2] - a[2]).slice(0, 6)
    .map(t => `<button type="button" class="chip" data-q="${esc(t[0])}">${esc(t[0])}</button>`).join('');
  for (const d of [1, -1]) { const v = vista[visorIdx + d]; if (v) new Image().src = v.w; }
}

function abrirVisor(i) {
  visorIdx = i;
  mostrarVisor();
  el.visor.hidden = false;
  document.body.style.overflow = 'hidden';
  el.visorCerrar.focus();
}
function cerrarVisor() {
  const li = vista[visorIdx] && liPorId.get(vista[visorIdx].id);
  el.visor.hidden = true;
  document.body.style.overflow = '';
  visorIdx = -1;
  if (li) li.focus({ preventScroll: true });
}
function moverVisor(d) {
  const n = visorIdx + d;
  if (n < 0 || n >= vista.length) return;
  visorIdx = n;
  mostrarVisor();
}

el.visorCerrar.addEventListener('click', cerrarVisor);
el.visorAnt.addEventListener('click', () => moverVisor(-1));
el.visorSig.addEventListener('click', () => moverVisor(1));
el.visorSel.addEventListener('click', () => alternarSel(vista[visorIdx].id));
el.visorTags.addEventListener('click', e => {
  const b = e.target.closest('[data-q]');
  if (!b) return;
  cerrarVisor();
  el.q.value = b.dataset.q;
  buscar({ inmediato: true, ir: 'siempre' });
});
el.visor.addEventListener('click', e => { if (e.target === el.visor || e.target.classList.contains('visor-foto')) cerrarVisor(); });
document.addEventListener('keydown', e => {
  if (el.visor.hidden) return;
  if (e.key === 'Escape') cerrarVisor();
  else if (e.key === 'ArrowLeft') moverVisor(-1);
  else if (e.key === 'ArrowRight') moverVisor(1);
});
let toqueX = null;
el.visor.addEventListener('touchstart', e => { toqueX = e.touches[0].clientX; }, { passive: true });
el.visor.addEventListener('touchend', e => {
  if (toqueX === null) return;
  const dx = e.changedTouches[0].clientX - toqueX;
  toqueX = null;
  if (Math.abs(dx) > 60) moverVisor(dx < 0 ? 1 : -1);
});

/* ---------- arranque ---------- */

async function iniciar() {
  if (location.protocol === 'file:') {
    el.vacio.hidden = false;
    el.vacio.textContent = 'Esta página no funciona abierta como archivo. Abrila con Abrir-Galeria.bat (o desde el hosting).';
    return;
  }
  el.resumen.textContent = 'Cargando fotos…';
  try {
    const [conf, idx, vocab] = await Promise.all(
      ['config.json', 'data/index.json', 'data/vocab.json'].map(u => fetch(u, { cache: 'no-cache' }).then(r => {
        if (!r.ok) throw new Error(u);
        return r.json();
      })));
    CONF = conf; VOCAB = vocab;
    const rango = new Map(CONF.ediciones.map((e, i) => [e.slug, i]));
    FOTOS = idx.fotos.map((p, i) => ({ ...p, i, tm: new Map(p.tags.map(t => [t[0], t[2]])) }))
      .sort((a, b) => (rango.get(b.ed) - rango.get(a.ed)) || (a.i - b.i));
  } catch {
    el.resumen.textContent = '';
    el.vacio.hidden = false;
    el.vacio.textContent = 'No pude cargar las fotos. Probá recargar la página.';
    return;
  }
  for (const p of FOTOS) { porIdx[p.i] = p; porId.set(p.id, p); }
  try {
    const r = await fetch('data/rank.json', { cache: 'no-cache' });
    if (r.ok) RANK = new Map(Object.entries(await r.json()));
  } catch { /* sin ranking: solo se muestran las que coinciden */ }
  indexarVocab();
  calcularEjemplos();
  pintarSugeridas();
  rotarEjemplos();
  if (CONF.ia === false) iaActiva = false;
  else fetch('buscar.php?estado=1').then(r => r.json()).then(j => { if (!j.ia) iaActiva = false; }).catch(() => { iaActiva = false; });

  const h = new URLSearchParams(location.hash.slice(1));
  el.q.value = h.get('q') || '';
  edVista = CONF.ediciones.some(e => e.slug === h.get('ed')) ? h.get('ed') : '';
  window.addEventListener('popstate', () => {
    const s = new URLSearchParams(location.hash.slice(1));
    edVista = CONF.ediciones.some(e => e.slug === s.get('ed')) ? s.get('ed') : '';
    el.q.value = s.get('q') || '';
    buscar({ inmediato: true });
    ponerEjemplo();
  });
  ponerEjemplo();
  buscar({ inmediato: true, ir: 'siempre' });   // si el link ya trae una busqueda, va directo a las fotos
  if (matchMedia('(hover: hover)').matches) el.q.focus({ preventScroll: true });   // el buscador es lo principal
}

iniciar();
})();

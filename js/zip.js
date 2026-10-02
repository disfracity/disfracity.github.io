/* Arma un ZIP en el navegador, sin comprimir (los JPG ya vienen comprimidos).
   Asi la descarga multiple anda en cualquier hosting, tambien en los que no tienen PHP. */
(() => {
'use strict';

const TABLA = (() => {
  const t = new Uint32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c >>> 0;
  }
  return t;
})();

function crc32(bytes) {
  let c = 0xFFFFFFFF;
  for (let i = 0; i < bytes.length; i++) c = TABLA[(c ^ bytes[i]) & 0xFF] ^ (c >>> 8);
  return (c ^ 0xFFFFFFFF) >>> 0;
}

function fechaDos(d) {
  const hora = (d.getHours() << 11) | (d.getMinutes() << 5) | (d.getSeconds() >> 1);
  const dia = ((d.getFullYear() - 1980) << 9) | ((d.getMonth() + 1) << 5) | d.getDate();
  return [hora, dia];
}

/** archivos: [{ nombre, datos: Uint8Array }]  ->  Blob application/zip */
function crearZip(archivos) {
  const enc = new TextEncoder();
  const [hora, dia] = fechaDos(new Date());
  const partes = [];
  const central = [];
  let tamCentral = 0;
  let desplazamiento = 0;

  for (const { nombre, datos } of archivos) {
    const nom = enc.encode(nombre);
    const crc = crc32(datos);

    const local = new DataView(new ArrayBuffer(30));
    local.setUint32(0, 0x04034b50, true);
    local.setUint16(4, 20, true);          // version necesaria
    local.setUint16(6, 0x0800, true);      // nombre en UTF-8
    local.setUint16(8, 0, true);           // sin compresion
    local.setUint16(10, hora, true);
    local.setUint16(12, dia, true);
    local.setUint32(14, crc, true);
    local.setUint32(18, datos.length, true);
    local.setUint32(22, datos.length, true);
    local.setUint16(26, nom.length, true);
    local.setUint16(28, 0, true);
    partes.push(local.buffer, nom, datos);

    const ent = new DataView(new ArrayBuffer(46));
    ent.setUint32(0, 0x02014b50, true);
    ent.setUint16(4, 20, true);
    ent.setUint16(6, 20, true);
    ent.setUint16(8, 0x0800, true);
    ent.setUint16(10, 0, true);
    ent.setUint16(12, hora, true);
    ent.setUint16(14, dia, true);
    ent.setUint32(16, crc, true);
    ent.setUint32(20, datos.length, true);
    ent.setUint32(24, datos.length, true);
    ent.setUint16(28, nom.length, true);
    ent.setUint16(30, 0, true);            // campo extra
    ent.setUint16(32, 0, true);            // comentario
    ent.setUint16(34, 0, true);            // disco
    ent.setUint16(36, 0, true);            // atributos internos
    ent.setUint32(38, 0, true);            // atributos externos
    ent.setUint32(42, desplazamiento, true);
    central.push(ent.buffer, nom);

    tamCentral += 46 + nom.length;
    desplazamiento += 30 + nom.length + datos.length;
  }

  const fin = new DataView(new ArrayBuffer(22));
  fin.setUint32(0, 0x06054b50, true);
  fin.setUint16(4, 0, true);
  fin.setUint16(6, 0, true);
  fin.setUint16(8, archivos.length, true);
  fin.setUint16(10, archivos.length, true);
  fin.setUint32(12, tamCentral, true);
  fin.setUint32(16, desplazamiento, true);
  fin.setUint16(20, 0, true);

  return new Blob([...partes, ...central, fin.buffer], { type: 'application/zip' });
}

globalThis.crearZip = crearZip;
if (typeof module !== 'undefined') module.exports = { crearZip };   // para probarlo con node
})();

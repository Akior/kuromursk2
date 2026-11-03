/*
 * «КуроМур: Лабиринт клипов 2024» — один длинный коридор с поворотами
 * (Three.js, библиотека в /vendor).
 *
 * Планировка: ровно один коридор-«змейка» без ветвлений, тупиков и петель.
 * Проходы чередуются: повороты на восток/запад через всю площадь, между ними
 * короткие поворотные клетки. Вдоль западного края идёт возвратная линия,
 * которая приводит конец коридора снова к входу: дошёл до конца — оказался
 * у начала ✧
 *
 * Все клипы года развешаны на гранях сплошных стен вдоль коридора. Позади
 * входа, со стороны крыльца — кнопки-порталы на коридоры других лет.
 *
 * Загрузка: видео не качается заранее. Превью (лёгкий webp) — все сразу.
 * Видео — только по клику; при клике на другую картину предыдущее
 * останавливается, фоновая музыка приглушается. При паузе (Esc /
 * потеря фокуса) весь звук выключается.
 */
import * as THREE from "../vendor/three.module.js";

/* ------------------------------ год проекта ------------------------------ */
const YYYY = "2024";

/* ------------------------------ настройки ------------------------------ */
const CFG = {
  eyeHeight: 1.7,
  walkSpeed: 5.4,
  runSpeed: 10.0,
  mouseSense: 0.0022,
  smooth: 12,

  // прыжок и присед
  jumpSpeed: 5.2,        // начальная вертикальная скорость (м/с)
  gravity: 15,           // ускорение падения (м/с²) — чуть电影的 земного, чтобы прыжок был «мягким»
  crouchEye: 1.0,        // высота глаз в приседе (м)
  crouchSpeed: 0.5,      // доля скорости ходьбы в приседе

  hallW: 10,            // ширина коридора
  hallHalf: 24,         // половина длины коридора (должна вмещать 2 зала по 22 м)
  roomW: 22,            // размер зала (увеличен под удвоенные отступы)
  wallT: 0.3,           // толщина объёмных стен-перегородок
  rowY: 1.85,
  H: 3.8,               // высота потолков
  doorHalf: 1.7,
  doorH: 2.5,
  doorOffset: 5.5,      // смещение дверей от центра зала (двери z = ±6 и ±17)
  porchLen: 4,

  // картины: на 10 % меньше прежнего (2.5 × 1.4 → ×1.5 → 3.4 × 1.9)
  videoW: 3.4,
  videoH: 1.9,
  frameGap: 0.09,
  roomCell: 5.2,        // шаг картин в зале
  hallCell: 5.0,        // шаг картин в коридоре

  audioRef: 1.6,
  audioMax: 8.0,
  previewMaxW: 640,
  previewQuality: 0.42,
  lazyDist: 20,

  defaultVolume: 0.6,
  musicVolume: 0.005,  // мелодия при входе — едва слышна (0.5 %)
};

/* палитра Куромур: пастель + мятный + розовый */
const PAL = {
  wall: 0xfdeef2,        // нежно-розовый
  wallTrim: 0xffd9e8,
  floor: 0xfff6ea,       // кремовый
  floorLine: 0xf3d8c8,
  ceil: 0xeafaf7,        // мятный
  accent: 0xff9ec0,      // розовый акцент
  accent2: 0x9fdccf,     // мята
  accent3: 0xffd97a,     // солнечный
  frame: 0xffffff,
};

/* ------------------------------ DOM ------------------------------ */
const $ = (id) => document.getElementById(id);
const canvas = $("scene");
const overlay = $("overlay");
const ovTitle = $("ov-title");
const ovSub = $("ov-sub");
const statusEl = $("status");
const barFill = $("bar-fill");
const startBtn = $("btn-start");
const btnMain = $("btn-main");
const volHud = $("vol-hud");
const hintHud = $("hint-hud");
const crosshair = $("crosshair");
const minimap = $("minimap");
const bigmap = $("bigmap");
const bigmapCanvas = $("bigmap-canvas");
const playerBadge = $("player-badge");
const playerName = $("player-name");

/* ------------------------------ состояние ------------------------------ */
let renderer, scene, camera, listener;
let yaw = 0, pitch = 0;
const keys = new Set();
const velocity = new THREE.Vector3();
let started = false, ready = false;
const UP = new THREE.Vector3(0, 1, 0);
const raycaster = new THREE.Raycaster();
const CENTER = new THREE.Vector2(0, 0);

const colliders = [];
const currentSlots = [];
const clickables = [];
const videoElements = [];
const lazyZones = [];

const balloons = [];    // воздушные шары
const confettiBursts = []; // активные залпы конфетти
const cats = [];        // гуляющие коты
const candles = [];     // свечки на тортах (свет)
const flameMeshes = []; // язычки пламени (анимация)
const teleportButtons = []; // кнопки телепорта на стенах тупиков лабиринта
let lastTeleport = -10; // защита от повторных срабатываний
let mazeSafeCells = []; // обычные клетки прохода (цели телепорта)

let activeSlot = null;  // картина, чьё видео играет

/*
 * Один коридор-«змейка»: клетки 3.6 м, план MW×MH базовых клеток (сетка
 * (2·MW+1)×(2·MH+1)). Южная грань внешней стены на z = 0, коридор уходит
 * на север (−z), крыльцо — на юг (+z). Вход — одна прорезь в южной стене,
 * у двери начинается коридор; его конец по возвратной линии вдоль западного
 * края снова приходит к двери.
 */
const MAZE_SIZE = YYYY === "2025"
  ? { MW: 8, MH: 14 }  // сетка 17×29 кл., коридор 226 клеток, граней под картины 402
  : { MW: 8, MH: 12 }; // сетка 17×25 кл., коридор 194 клетки, граней под картины 344
const MZ = { cell: 3.6, porch: 6 };    // размер клетки (м), глубина крыльца (м)
const MZ_DOORS = [];                   // [{x, col, kind}] — вход (отладка)
const SPAWN = { x: 0, z: MZ.porch * 0.55 }; // спавн: перед входом (уточняется при сборке)

window.HALL = {
  ready: false, count: 0, previews: 0,
  mp: () => mpDebugInfo(), // диагностика мультиплеера: role/conns/ghosts
  volume: () => (listener ? listener.getMasterVolume() : null),
  audioState: () => (listener ? listener.context.state : "no-context"),
  musicPlaying: () => !!(music && music.isPlaying),
  playing: () => videoElements.filter((v) => !v.paused).length,
  slots: () => currentSlots.map((s) => ({
    file: s.video.file, preview: !!s.previewTex, loaded: !!s.el, playing: s.playing,
    x: +s.group.position.x.toFixed(2), z: +s.group.position.z.toFixed(2), zone: s.zoneName,
    ry: +s.group.rotation.y.toFixed(2), sx: s.group.scale.x,
  })),
  play: (i) => { togglePlayback(currentSlots[i]); return currentSlots[i].playing; },
  pos: () => ({ x: +camera.position.x.toFixed(2), z: +camera.position.z.toFixed(2) }), // отладка
  tp: (x, z, yawRad) => {
    camera.position.set(x, CFG.eyeHeight, z);
    if (typeof yawRad === "number") { yaw = yawRad; camera.rotation.y = yaw; }
    return { x, z };
  },
  rooms: () => [], // комнаты убраны: одна комната-лабиринт
  doors: () => (window.HALL.doors || []).slice(),
  boxes: colliders, // отладка: живой список коллайдеров
  confetti: () => fireConfetti(camera.position.x, camera.position.z), // залп вручную
  // отладка: что видит прицел (кнопки телепорта / клипы)
  rayAt: () => {
    camera.updateMatrixWorld();
    scene.updateMatrixWorld(true);
    raycaster.setFromCamera(CENTER, camera);
    return raycaster.intersectObjects(clickables, false).slice(0, 6).map((h) => ({
      d: +h.distance.toFixed(2),
      teleport: !!h.object.userData.teleport,
      clip: h.object.userData.slot ? h.object.userData.slot.video.file.slice(0, 30) : null,
      at: [+h.point.x.toFixed(2), +h.point.y.toFixed(2), +h.point.z.toFixed(2)],
    }));
  },
};

/* ------------------------------ запуск ------------------------------ */
main().catch((err) => {
  console.error(err);
  statusEl.textContent = "Ошибка: " + err.message;
  startBtn.disabled = true;
});

async function main() {
  initRenderer();

  const data = await fetchJSON("videos-maze.json");
  const videos = data.videos || [];
  window.HALL.count = videos.length;

  buildChannel(videos);
  updateBar(0, currentSlots.length);

  yaw = 0;
  camera.position.set(SPAWN.x, CFG.eyeHeight, SPAWN.z);
  camera.rotation.y = yaw;
  camera.far = 170;
  camera.updateProjectionMatrix();

  ready = true;
  window.HALL.ready = true;

  preparePreviews();
  loadMusic();
}

function initRenderer() {
  try {
    renderer = new THREE.WebGLRenderer({ canvas, antialias: true });
  } catch (e) {
    throw new Error("WebGL недоступен. Включите аппаратное ускорение в браузере.");
  }
  renderer.setSize(innerWidth, innerHeight);
  renderer.setPixelRatio(Math.min(devicePixelRatio, 2));

  scene = new THREE.Scene();
  scene.background = new THREE.Color(0xfff3f6);
  scene.fog = new THREE.Fog(0xfff3f6, 45, 115); // лёгкая дымка вдали

  camera = new THREE.PerspectiveCamera(72, innerWidth / innerHeight, 0.1, 170);
  camera.rotation.order = "YXZ";

  listener = new THREE.AudioListener();
  // для буста до 150% держим наготове компрессор: пики мягко удерживаются,
  // поэтому усиление реально слышно и на видео, и на музыке (без хрипа).
  // Вставляется в цепь только пока громкость > 100%.
  const comp = listener.context.createDynamicsCompressor();
  comp.threshold.value = -18;
  comp.knee.value = 20;
  comp.ratio.value = 12;
  comp.attack.value = 0.003;
  comp.release.value = 0.25;
  listener._boostComp = comp;
  listener.setMasterVolume(CFG.defaultVolume);
  camera.add(listener);
  scene.add(camera);

  // тёплый праздничный свет
  scene.add(new THREE.AmbientLight(0xffffff, 1.6));
  scene.add(new THREE.HemisphereLight(0xfff4e8, 0xffd9e8, 0.9));
  const sun = new THREE.DirectionalLight(0xfff0dd, 0.8);
  sun.position.set(3, 8, 2);
  scene.add(sun);
}

function fetchJSON(url) {
  return fetch(url).then((r) => {
    if (!r.ok) throw new Error("HTTP " + r.status + " от " + url);
    return r.json();
  });
}

/* ============================== ТЕКСТУРЫ ============================== */

function makeCanvasTexture(size, draw, repX, repY) {
  const c = document.createElement("canvas");
  c.width = c.height = size;
  const ctx = c.getContext("2d");
  draw(ctx, size);
  const tex = new THREE.CanvasTexture(c);
  tex.wrapS = tex.wrapT = THREE.RepeatWrapping;
  tex.repeat.set(repX, repY);
  tex.colorSpace = THREE.SRGBColorSpace;
  tex.anisotropy = 8;
  return tex;
}

// нежные стены: пастель + панель снизу + лапки-узор
function wallTexture(len, h) {
  return makeCanvasTexture(256, (ctx, s) => {
    ctx.fillStyle = "#fdeef2"; ctx.fillRect(0, 0, s, s);
    // панель снизу
    ctx.fillStyle = "#ffd9e8"; ctx.fillRect(0, s * 0.72, s, s * 0.28);
    ctx.strokeStyle = "#f7b8d0"; ctx.lineWidth = 4;
    ctx.strokeRect(-2, s * 0.72, s + 4, s * 0.28);
    // лапки
    ctx.fillStyle = "rgba(255,158,192,0.35)";
    for (let i = 0; i < 5; i++) {
      const x = 20 + Math.random() * (s - 40), y = s * 0.1 + Math.random() * s * 0.5;
      const r = 5 + Math.random() * 3;
      ctx.beginPath(); ctx.ellipse(x, y, r, r * 0.85, 0, 0, 7); ctx.fill();
      for (let k = 0; k < 3; k++) {
        ctx.beginPath();
        ctx.ellipse(x - r + k * r, y - r * 1.1, r * 0.38, r * 0.42, 0, 0, 7);
        ctx.fill();
      }
    }
    // звёздочки
    ctx.fillStyle = "rgba(159,220,207,0.5)";
    for (let i = 0; i < 8; i++) {
      const x = Math.random() * s, y = Math.random() * s * 0.7, r = 2 + Math.random() * 3;
      ctx.beginPath(); ctx.arc(x, y, r, 0, 7); ctx.fill();
    }
  }, Math.max(1, Math.round(len / 5)), Math.max(1, Math.round(h / 3)));
}

// кремовый пол с шахматным нежным узором
function floorTexture(repX, repY) {
  return makeCanvasTexture(256, (ctx, s) => {
    const half = s / 2;
    ctx.fillStyle = "#fff6ea"; ctx.fillRect(0, 0, s, s);
    ctx.fillStyle = "#ffeee0"; ctx.fillRect(0, 0, half, half); ctx.fillRect(half, half, half, half);
    ctx.strokeStyle = "rgba(243,216,200,0.9)"; ctx.lineWidth = 3;
    ctx.strokeRect(0, 0, s, s); ctx.strokeRect(0, 0, half, half); ctx.strokeRect(half, half, half, half);
    // редкие сусальные звёздочки
    ctx.fillStyle = "rgba(255,214,122,0.55)";
    for (let i = 0; i < 3; i++) {
      const x = Math.random() * s, y = Math.random() * s, r = 3 + Math.random() * 3;
      ctx.beginPath(); ctx.arc(x, y, r, 0, 7); ctx.fill();
    }
  }, Math.max(1, repX), Math.max(1, repY));
}

function ceilTexture(repX, repY) {
  return makeCanvasTexture(256, (ctx, s) => {
    ctx.fillStyle = "#eafaf7"; ctx.fillRect(0, 0, s, s);
    ctx.strokeStyle = "rgba(190,230,220,0.8)"; ctx.lineWidth = 3;
    ctx.strokeRect(0, 0, s, s);
    // облачка
    ctx.fillStyle = "rgba(255,255,255,0.85)";
    for (let i = 0; i < 3; i++) {
      const x = Math.random() * s, y = Math.random() * s;
      ctx.beginPath();
      ctx.ellipse(x, y, 16 + Math.random() * 12, 8 + Math.random() * 6, 0, 0, 7);
      ctx.ellipse(x + 14, y + 3, 12, 7, 0, 0, 7);
      ctx.fill();
    }
  }, Math.max(1, repX), Math.max(1, repY));
}

function labelText(fileName) {
  let base = fileName.replace(/\.[^.]+$/, "");
  base = base.replace(/^\d+[\s._-]*/, "").trim();
  return base || fileName.replace(/\.[^.]+$/, "");
}

function labelTexture(text) {
  const c = document.createElement("canvas");
  c.width = 640; c.height = 120;
  const ctx = c.getContext("2d");
  ctx.fillStyle = "#fff9fb"; ctx.fillRect(0, 0, c.width, c.height);
  ctx.strokeStyle = "#ff9ec0"; ctx.lineWidth = 6;
  ctx.strokeRect(6, 6, c.width - 12, c.height - 12);
  let px = 60;
  ctx.font = `700 ${px}px "Comic Sans MS", "Segoe UI", system-ui, sans-serif`;
  while (ctx.measureText(text).width > c.width - 52 && px > 18) {
    px -= 4;
    ctx.font = `700 ${px}px "Comic Sans MS", "Segoe UI", system-ui, sans-serif`;
  }
  ctx.fillStyle = "#d94f7e";
  ctx.textAlign = "center"; ctx.textBaseline = "middle";
  ctx.fillText(text, c.width / 2, c.height / 2 + 4);
  const tex = new THREE.CanvasTexture(c);
  tex.colorSpace = THREE.SRGBColorSpace;
  tex.anisotropy = 8;
  return tex;
}

function signTexture(lines, { w = 1024, h = 256, accent = "#ff7fae", font = 88 } = {}) {
  const c = document.createElement("canvas");
  c.width = w; c.height = h;
  const ctx = c.getContext("2d");
  ctx.fillStyle = "#fff9fb"; ctx.fillRect(0, 0, w, h);
  ctx.strokeStyle = accent; ctx.lineWidth = 10;
  ctx.strokeRect(12, 12, w - 24, h - 24);
  ctx.textAlign = "center"; ctx.textBaseline = "middle";
  const n = lines.length;
  lines.forEach((line, i) => {
    let px = font;
    ctx.font = `800 ${px}px "Comic Sans MS", "Segoe UI", system-ui, sans-serif`;
    while (ctx.measureText(line).width > w - 60 && px > 24) {
      px -= 4;
      ctx.font = `800 ${px}px "Comic Sans MS", "Segoe UI", system-ui, sans-serif`;
    }
    ctx.fillStyle = n === 1 ? "#d94f7e" : (i === 0 ? "#d94f7e" : "#8a6a75");
    ctx.fillText(line, w / 2, h * ((i + 0.5) / n));
  });
  const tex = new THREE.CanvasTexture(c);
  tex.colorSpace = THREE.SRGBColorSpace;
  tex.anisotropy = 8;
  return tex;
}

// мордочка кота для спрайтов-гостей (если пригодится) — не используется, но пусть
function catFaceTexture(color = "#e8b98a") {
  const c = document.createElement("canvas");
  c.width = c.height = 128;
  const ctx = c.getContext("2d");
  ctx.fillStyle = color;
  ctx.beginPath(); ctx.ellipse(64, 74, 40, 34, 0, 0, 7); ctx.fill();
  ctx.beginPath(); ctx.moveTo(28, 56); ctx.lineTo(38, 22); ctx.lineTo(52, 46); ctx.closePath(); ctx.fill();
  ctx.beginPath(); ctx.moveTo(100, 56); ctx.lineTo(90, 22); ctx.lineTo(76, 46); ctx.closePath(); ctx.fill();
  ctx.fillStyle = "#333";
  ctx.beginPath(); ctx.arc(50, 70, 5, 0, 7); ctx.fill();
  ctx.beginPath(); ctx.arc(78, 70, 5, 0, 7); ctx.fill();
  ctx.strokeStyle = "#333"; ctx.lineWidth = 2.5;
  ctx.beginPath(); ctx.moveTo(58, 84); ctx.quadraticCurveTo(64, 90, 70, 84); ctx.stroke();
  const tex = new THREE.CanvasTexture(c);
  tex.colorSpace = THREE.SRGBColorSpace;
  return tex;
}

/* ============================== ДЕКОР ============================== */

// воздушный шар на нитке (привязан к потолку, покачивается)
function makeBalloon(x, z, color, h = CFG.H) {
  const g = new THREE.Group();
  const mat = new THREE.MeshLambertMaterial({ color });
  const ball = new THREE.Mesh(new THREE.SphereGeometry(0.32, 20, 16), mat);
  ball.scale.y = 1.2;
  g.add(ball);
  const knot = new THREE.Mesh(new THREE.ConeGeometry(0.05, 0.08, 8), mat);
  knot.position.y = -0.4; knot.rotation.x = Math.PI;
  g.add(knot);
  // нитка до потолка
  const len = h - 0.55;
  const thread = new THREE.Line(
    new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(0, -0.44, 0), new THREE.Vector3(0, -len, 0)]),
    new THREE.LineBasicMaterial({ color: 0xd8c8d0, transparent: true, opacity: 0.7 })
  );
  g.add(thread);
  g.position.set(x, h - 0.35, z);
  scene.add(g);
  balloons.push({ g, baseX: x, baseZ: z, baseY: h - 0.35, phase: Math.random() * 6.28, speed: 0.6 + Math.random() * 0.5 });
}

// торт на тумбе: цифра «3» сверху + 3 свечки
const confettiColors = [0xff9ec0, 0x9fdccf, 0xffd97a, 0xb3d4ff, 0xffb37a, 0xd8b4fe];
function fireConfetti(x, z, count = 90, salute = false) {
  const geo = new THREE.BufferGeometry();
  const pos = new Float32Array(count * 3);
  const col = new Float32Array(count * 3);
  const vel = [];
  const c = new THREE.Color();
  for (let i = 0; i < count; i++) {
    pos[i * 3] = x + (Math.random() - 0.5) * 0.4;
    pos[i * 3 + 1] = 1.4 + Math.random() * 0.4;
    pos[i * 3 + 2] = z + (Math.random() - 0.5) * 0.4;
    c.setHex(confettiColors[i % confettiColors.length]);
    col[i * 3] = c.r; col[i * 3 + 1] = c.g; col[i * 3 + 2] = c.b;
    vel.push({
      vx: (Math.random() - 0.5) * (salute ? 5.5 : 3.2),
      vy: salute ? 4.5 + Math.random() * 3.5 : 3.2 + Math.random() * 2.8,
      vz: (Math.random() - 0.5) * (salute ? 5.5 : 3.2),
      spin: Math.random() * 6.28,
    });
  }
  geo.setAttribute("position", new THREE.BufferAttribute(pos, 3));
  geo.setAttribute("color", new THREE.BufferAttribute(col, 3));
  const mat = new THREE.PointsMaterial({
    size: 0.09, vertexColors: true, transparent: true, opacity: 1, depthWrite: false,
  });
  const pts = new THREE.Points(geo, mat);
  scene.add(pts);
  confettiBursts.push({ pts, vel, life: 0, maxLife: salute ? 6.5 : 4.5 });
}

/* ============================== СТЕНЫ (ОБЪЁМНЫЕ) ============================== */

function wallMat(w, h) {
  return new THREE.MeshLambertMaterial({ map: wallTexture(w, h) });
}

// объёмная стена-перегородка (Box) вдоль Z на координате x
function thickWallZ(x, z0, z1, { doors = [] } = {}) {
  const T = CFG.wallT, H = CFG.H;
  const dh = CFG.doorHalf;
  const segs = [];
  let cur = z0;
  const cuts = doors.slice().sort((a, b) => a - b);
  for (const d of cuts) {
    if (d - dh > cur) segs.push([cur, d - dh]);
    cur = d + dh;
  }
  if (z1 > cur) segs.push([cur, z1]);
  for (const [a, b] of segs) {
    if (b - a < 0.05) continue;
    const m = new THREE.Mesh(
      new THREE.BoxGeometry(T, H, b - a),
      wallMat(b - a, H)
    );
    m.position.set(x, H / 2, (a + b) / 2);
    scene.add(m);
    colliders.push({ minX: x - T / 2, maxX: x + T / 2, minZ: a, maxZ: b });
  }
  // перемычки над дверями
  for (const d of cuts) {
    if (d - dh < z0 || d + dh > z1) continue;
    const m = new THREE.Mesh(
      new THREE.BoxGeometry(T, H - CFG.doorH, dh * 2),
      wallMat(dh * 2, H - CFG.doorH)
    );
    m.position.set(x, CFG.doorH + (H - CFG.doorH) / 2, d);
    scene.add(m);
  }
}

// объёмная стена (Box) вдоль X на координате z
function thickWallX(z, x0, x1, { doors = [] } = {}) {
  const T = CFG.wallT, H = CFG.H;
  const dh = CFG.doorHalf;
  const segs = [];
  let cur = x0;
  const cuts = doors.slice().sort((a, b) => a - b);
  for (const d of cuts) {
    if (d - dh > cur) segs.push([cur, d - dh]);
    cur = d + dh;
  }
  if (x1 > cur) segs.push([cur, x1]);
  for (const [a, b] of segs) {
    if (b - a < 0.05) continue;
    const m = new THREE.Mesh(
      new THREE.BoxGeometry(b - a, H, T),
      wallMat(b - a, H)
    );
    m.position.set((a + b) / 2, H / 2, z);
    scene.add(m);
    colliders.push({ minX: a, maxX: b, minZ: z - T / 2, maxZ: z + T / 2 });
  }
  for (const d of cuts) {
    if (d - dh < x0 || d + dh > x1) continue;
    const m = new THREE.Mesh(
      new THREE.BoxGeometry(dh * 2, H - CFG.doorH, T),
      wallMat(dh * 2, H - CFG.doorH)
    );
    m.position.set(d, CFG.doorH + (H - CFG.doorH) / 2, z);
    scene.add(m);
  }
}

function addBox(minX, maxX, minZ, maxZ) {
  colliders.push({ minX, maxX, minZ, maxZ });
}

function plane(w, h, x, y, z, rotY = 0, mat = null, rotX = 0) {
  const m = new THREE.Mesh(new THREE.PlaneGeometry(w, h), mat);
  m.position.set(x, y, z);
  m.rotation.y = rotY;
  m.rotation.x = rotX;
  scene.add(m);
  return m;
}

/* ============================== КОМНАТА-ЛАБИРИНТ ============================== */

// Один длинный коридор-«змейка»: детерминированная планировка без ветвлений.
// Сетка из блоков: 0 — проход, 1 — стена. Проходы — нечётные строки/столбцы.
// Коридор идёт строками «восток↔запад» через всю площадь, между строками —
// поворотные клетки-соединители, а вдоль западного края — возвратная линия
// к входу: дошёл до конца — снова у двери. Тупиков нет по построению.
function makeCorridor(W, H) {
  const gw = 2 * W + 1, gh = 2 * H + 1;
  const mz = Array.from({ length: gh }, () => Array(gw).fill(1));
  // строки-проходы: блок-столбцы 1..W-1 (сеточные столбцы 3..gw-2)
  for (let k = 0; k < H; k++) {
    const r = 2 * k + 1;
    for (let c = 3; c <= gw - 2; c++) mz[r][c] = 0;
  }
  // поворотные соединители между соседними строками: восток ↔ запад чередуются
  for (let k = 0; k < H - 1; k++) {
    mz[2 * k + 2][k % 2 === 0 ? gw - 2 : 3] = 0;
  }
  // возвратная линия вдоль западного края: конец коридора → к двери
  for (let r = 1; r <= gh - 2; r++) mz[r][1] = 0;
  // стыки: вход соединяет дверь с первой строкой, низ соединяет конец
  // коридора с возвратной линией — цельная петля, ни одного тупика
  mz[1][2] = 0;
  mz[gh - 2][2] = 0;
  return { mz, gw, gh };
}

// Вся «карта» года: один коридор-змейка + крыльцо с единственным входом.
function buildChannel(videos) {
  const H = CFG.H, T = CFG.wallT;
  const CELL = MZ.cell;
  const { MW, MH } = MAZE_SIZE;
  const { mz, gw, gh } = makeCorridor(MW, MH);
  window.HALL.deadEndsFixed = 0; // тупиков нет по построению

  /* --- геометрия: южная грань внешней стены — z = 0, север — в минус --- */
  const x0 = -(gw * CELL) / 2;
  const cellCX = (c) => x0 + (c + 0.5) * CELL;
  const cellCZ = (r) => -(r + 0.5) * CELL;

  /* --- вход: одна прорезь в южной стене ---
   * За прорезью — открытая клетка первой строки: с неё начинается коридор;
   * его конец по возвратной линии вдоль западного края вернётся к ней.
   */
  const entCol = gw - 8; // открытая клетка (1, entCol) — старт коридора
  mz[0][entCol] = 0;
  MZ_DOORS.push({ x: cellCX(entCol), col: entCol, kind: "entrance" });
  window.HALL.doors = MZ_DOORS.map((d) => ({ x: +d.x.toFixed(2), kind: d.kind }));

  /* --- пол и потолок лабиринта --- */
  const mzMinX = x0 - 1, mzMaxX = x0 + gw * CELL + 1;
  const mzMinZ = -gh * CELL - 1, mzMaxZ = 1;
  plane(mzMaxX - mzMinX, mzMaxZ - mzMinZ, (mzMinX + mzMaxX) / 2, 0.001, (mzMinZ + mzMaxZ) / 2, 0,
    new THREE.MeshLambertMaterial({ map: floorTexture((mzMaxX - mzMinX) / 2, (mzMaxZ - mzMinZ) / 2) }), -Math.PI / 2);
  plane(mzMaxX - mzMinX, mzMaxZ - mzMinZ, (mzMinX + mzMaxX) / 2, H, (mzMinZ + mzMaxZ) / 2, 0,
    new THREE.MeshLambertMaterial({ map: ceilTexture((mzMaxX - mzMinX) / 3, (mzMaxZ - mzMinZ) / 3) }), Math.PI / 2);

  /* --- крыльцо: общее для входа и выхода (вход зациклен на выход) --- */
  const pZ0 = 0, pZ1 = MZ.porch;
  plane(mzMaxX - mzMinX, pZ1 - pZ0, (mzMinX + mzMaxX) / 2, 0.001, (pZ0 + pZ1) / 2, 0,
    new THREE.MeshLambertMaterial({ map: floorTexture((mzMaxX - mzMinX) / 2, 2) }), -Math.PI / 2);
  plane(mzMaxX - mzMinX, pZ1 - pZ0, (mzMinX + mzMaxX) / 2, H, (pZ0 + pZ1) / 2, 0,
    new THREE.MeshLambertMaterial({ map: ceilTexture((mzMaxX - mzMinX) / 3, 2) }), Math.PI / 2);
  // бока и южный торец крыльца — объёмные стены (план лабиринта сам закрывает север)
  thickWallZ(mzMinX, pZ0, pZ1, {});
  thickWallZ(mzMaxX, pZ0, pZ1, {});
  thickWallX(pZ1, mzMinX - T / 2, mzMaxX + T / 2, {});

  /* --- стены: соседние стеновые клетки в строке сливаем в длинные боксы --- */
  for (let r = 0; r < gh; r++) {
    let c = 0;
    while (c < gw) {
      if (mz[r][c] !== 1) { c++; continue; }
      let cEnd = c;
      while (cEnd + 1 < gw && mz[r][cEnd + 1] === 1) cEnd++;
      const len = (cEnd - c + 1) * CELL;
      const cxm = (cellCX(c) + cellCX(cEnd)) / 2;
      const m = new THREE.Mesh(
        new THREE.BoxGeometry(len, H, CELL),
        new THREE.MeshLambertMaterial({ map: wallTexture(len, H) })
      );
      m.position.set(cxm, H / 2, cellCZ(r));
      scene.add(m);
      colliders.push({ minX: cxm - len / 2, maxX: cxm + len / 2, minZ: cellCZ(r) - CELL / 2, maxZ: cellCZ(r) + CELL / 2 });
      c = cEnd + 1;
    }
  }

  /* --- табличка над ВХОДОМ (со стороны крыльца) --- */
  const signY = 3.0; // низ 2.63 (под потолком), верх 3.37
  const doorX = cellCX(entCol);
  SPAWN.x = doorX; // спавн прямо перед входом
  const entSign = new THREE.Mesh(
    new THREE.PlaneGeometry(6.4, 1.3),
    new THREE.MeshBasicMaterial({
      map: signTexture([`Все видео за ${YYYY}`, `количество: ${videos.length}`], { w: 2048, h: 520, font: 150, accent: "#ff7fae" }),
    })
  );
  entSign.position.set(doorX, signY, 0.03);
  scene.add(entSign);

  /* --- кнопки-порталы позади входа: переход в коридоры других лет ---
   * Плоскости на южной стене крыльца, лицом к игроку. Клик — переход.
   */
  const portalDefs = YYYY === "2025"
    ? [{ label: "Переместиться в 2026", href: "https://kuromursk.dpdns.org/clips" },
       { label: "Вернуться в 2024", href: "../2024/" }]
    : YYYY === "2026"
    ? [{ label: "Вернуться в 2024", href: "../2024/" },
       { label: "Переместиться в 2025", href: "../2025/" }]
    : [{ label: "Переместиться в 2025", href: "../2025/" },
       { label: "Переместиться в 2026", href: "https://kuromursk.dpdns.org/clips" }];
  portalDefs.forEach((p, i) => {
    const btn = new THREE.Mesh(
      new THREE.PlaneGeometry(4.8, 1.5),
      new THREE.MeshBasicMaterial({
        map: signTexture([p.label], { w: 1024, h: 320, font: 96, accent: i % 2 ? "#7fd1b0" : "#ff7fae" }),
      })
    );
    btn.position.set(doorX + (i === 0 ? -3.4 : 3.4), 1.6, MZ.porch - CFG.wallT / 2 - 0.06);
    btn.rotation.y = Math.PI;
    btn.userData.portal = p.href;
    clickables.push(btn);
    teleportButtons.push(btn); // пульсация кнопок в общей анимации
    scene.add(btn);
  });

  /* --- шарики: «ворота» у каждого входа + по проходам лабиринта --- */
  const balloonColors = [PAL.accent, PAL.accent2, PAL.accent3];
  let balloonCount = 0;
  for (const d of MZ_DOORS) {
    makeBalloon(d.x - 2.4, -1.5, PAL.accent, H);
    makeBalloon(d.x + 2.4, -1.5, PAL.accent2, H);
    makeBalloon(d.x, -0.9, PAL.accent3, H);
    makeBalloon(d.x, pZ1 - 1.2, PAL.accent3, H);
    makeBalloon(d.x - 2.2, pZ1 - 1.6, PAL.accent, H);
    makeBalloon(d.x + 2.2, pZ1 - 1.6, PAL.accent2, H);
    balloonCount += 6;
  }
  // внутри лабиринта: шарик в каждой третьей клетке прохода
  let bi = 0;
  for (let r = 1; r <= gh - 2; r++) {
    for (let c = 1; c < gw - 1; c++) {
      if (mz[r][c] !== 0) continue;
      bi++;
      if (bi % 3 !== 0) continue;
      makeBalloon(cellCX(c), cellCZ(r), balloonColors[bi % 3], H);
      balloonCount++;
    }
  }
  window.HALL.balloonCount = balloonCount;

  /* --- картины: на каждую грань стены, выходящую в проход, вешаем клип --- */
  const lazyZonesRoom = [];
  for (let b = 0; b < 12; b++) {
    lazyZonesRoom.push({ x: 0, z: 0, slots: [], loaded: false, name: "Лабиринт" });
  }
  const zoneOf = (r, c) => {
    const band = Math.min(2, Math.floor((r - 1) / Math.ceil((gh - 2) / 3))); // 0..2 от юга к северу
    const colB = Math.min(3, Math.floor(c / (gw / 4)));                      // 0..3 с запада на восток
    return lazyZonesRoom[band * 4 + colB];
  };
  const wallOff = 0.14; // рамка выступает из стены лабиринта, не утопая в текстуре
  // Собираем ТОЛЬКО грани, за которыми реально есть стена, причём стена
  // тянется минимум на одну клетку в обе стороны вдоль своего направления —
  // рамка висит на сплошной стене, а не на торце столба в развилке.
  const faces = [];
  for (let r = 1; r <= gh - 2; r++) {
    for (let c = 1; c < gw - 1; c++) {
      if (mz[r][c] !== 0) continue;
      const cx = cellCX(c), cz = cellCZ(r);
      // северная грань: стена в ряду r+1, тянущаяся по c-1 и c+1
      if (mz[r + 1][c] === 1 && mz[r + 1][c - 1] === 1 && mz[r + 1][c + 1] === 1)
        faces.push({ r, c, x: cx, z: cz - CELL / 2 + wallOff, rotY: 0 });
      // южная грань: стена в ряду r-1
      if (mz[r - 1][c] === 1 && mz[r - 1][c - 1] === 1 && mz[r - 1][c + 1] === 1)
        faces.push({ r, c, x: cx, z: cz + CELL / 2 - wallOff, rotY: Math.PI });
      // восточная грань: стена в столбце c+1
      if (mz[r][c + 1] === 1 && mz[r - 1][c + 1] === 1 && mz[r + 1][c + 1] === 1)
        faces.push({ r, c, x: cx + CELL / 2 - wallOff, z: cz, rotY: -Math.PI / 2 });
      // западная грань: стена в столбце c-1
      if (mz[r][c - 1] === 1 && mz[r - 1][c - 1] === 1 && mz[r + 1][c - 1] === 1)
        faces.push({ r, c, x: cx - CELL / 2 + wallOff, z: cz, rotY: Math.PI / 2 });
    }
  }
  window.HALL.faces = faces.length;
  // Клипы распределяем по граням равномерно: граней больше, чем клипов,
  // поэтому на каждой «сплошной» стене достаётся минимум одна картина.
  const total = videos.length;
  const step = faces.length / total;
  for (let i = 0; i < total; i++) {
    const f = faces[Math.floor(i * step)];
    const slot = makeFrame(videos[i], f.x, CFG.rowY, f.z, f.rotY, "Лабиринт");
    // рамки уже основных: проход 3.6 м остаётся свободным по бокам
    slot.group.scale.set(0.72, 0.74, 1);
    zoneOf(f.r, f.c).slots.push(currentSlots.length);
    currentSlots.push(slot);
  }

  // центры ленивых зон — по фактическим слотам
  for (const z of lazyZonesRoom) {
    if (!z.slots.length) continue;
    let sx = 0, sz = 0;
    for (const i of z.slots) { sx += currentSlots[i].group.position.x; sz += currentSlots[i].group.position.z; }
    z.x = sx / z.slots.length;
    z.z = sz / z.slots.length;
    lazyZones.push(z);
  }
}

function makeFrame(video, x, y, z, rotY, zoneName) {
  const group = new THREE.Group();
  group.position.set(x, y, z);
  group.rotation.y = rotY;

  // расходим плоскости по Z с запасом ≥2 см: иначе при взгляде издалека
  // копланарные плоскости мерцают (z-fighting) — «живые» мерцающие текстуры
  const frame = new THREE.Mesh(
    new THREE.PlaneGeometry(CFG.videoW + CFG.frameGap * 2, CFG.videoH + CFG.frameGap * 2),
    new THREE.MeshBasicMaterial({ color: PAL.frame })
  );
  frame.position.z = 0;
  group.add(frame);

  const screenMat = new THREE.MeshBasicMaterial({ color: 0x2a2430 });
  const screen = new THREE.Mesh(new THREE.PlaneGeometry(CFG.videoW, CFG.videoH), screenMat);
  screen.position.z = 0.06;
  group.add(screen);

  const label = new THREE.Mesh(
    new THREE.PlaneGeometry(CFG.videoW * 0.48, CFG.videoW * 0.48 * (120 / 640)),
    new THREE.MeshBasicMaterial({ map: labelTexture(labelText(video.file)) })
  );
  label.position.set(0, -CFG.videoH / 2 - 0.20, 0.10); // ниже рамки, ПЕРЕД экраном (без мерцания)
  group.add(label);

  // стрелочка-указатель направления (вперёд от картины)
  const arrowShape = new THREE.Shape();
  arrowShape.moveTo(0, 0.11);
  arrowShape.lineTo(-0.06, -0.05);
  arrowShape.lineTo(0, 0.005);
  arrowShape.lineTo(0.06, -0.05);
  arrowShape.closePath();
  const arrow = new THREE.Mesh(
    new THREE.ShapeGeometry(arrowShape),
    new THREE.MeshBasicMaterial({ color: PAL.accent3, transparent: true, opacity: 0.85, depthWrite: false })
  );
  arrow.position.set(0, 0.06, 0.12); // впереди всех плоскостей картины (не мерцает)
  arrow.rotation.x = -Math.PI / 2;
  group.add(arrow);
  group.userData.arrow = arrow;

  scene.add(group);

  const slot = { video, group, screenMat, zoneName, el: null, previewTex: null, videoTex: null, playing: false };
  screen.userData.slot = slot;
  clickables.push(screen);
  return slot;
}

/* ============================== ПРЕВЬЮ ============================== */

function once(elem, okEv, badEv, timeoutMs) {
  return new Promise((resolve) => {
    let done = false;
    const finish = () => {
      if (done) return;
      done = true;
      elem.removeEventListener(okEv, finish);
      elem.removeEventListener(badEv, finish);
      clearTimeout(timer);
      resolve();
    };
    const timer = setTimeout(finish, timeoutMs);
    elem.addEventListener(okEv, finish);
    elem.addEventListener(badEv, finish);
  });
}

async function makePreview(url) {
  const el = document.createElement("video");
  el.preload = "metadata";
  el.muted = true;
  el.crossOrigin = "anonymous";
  el.src = url;
  await once(el, "loadedmetadata", "error", 12000);
  if (el.readyState < 1) return null;
  const dur = Number.isFinite(el.duration) && el.duration > 0 ? el.duration : 3;
  el.currentTime = Math.min(1.5, dur * 0.25);
  await once(el, "seeked", "error", 8000);
  const vw = el.videoWidth || 640, vh = el.videoHeight || 360;
  const w = Math.min(CFG.previewMaxW, vw);
  const h = Math.round((w * vh) / vw);
  const c = document.createElement("canvas");
  c.width = w; c.height = h;
  c.getContext("2d").drawImage(el, 0, 0, w, h);
  const data = c.toDataURL("image/jpeg", CFG.previewQuality);
  el.removeAttribute("src");
  el.load();
  return data;
}

function applyPreview(slot, dataURL) {
  return new Promise((resolve) => {
    const img = new Image();
    img.onload = () => {
      const tex = new THREE.Texture(img);
      tex.needsUpdate = true;
      tex.colorSpace = THREE.SRGBColorSpace;
      tex.anisotropy = 8;
      slot.previewTex = tex;
      if (!slot.playing) {
        slot.screenMat.map = tex;
        slot.screenMat.color.set(0xffffff);
        slot.screenMat.needsUpdate = true;
      }
      resolve();
    };
    img.onerror = resolve; // не вешаем очередь на битую картинку
    img.src = dataURL;
  });
}

const previewQueue = [];
let previewBusy = false;
let previewsQueued = 0;
let previewsDone = 0;

function enqueuePreviews(idxs) {
  for (const i of idxs) if (!previewQueue.includes(i)) previewQueue.push(i);
  pumpPreviews();
}

async function pumpPreviews() {
  if (previewBusy) return;
  previewBusy = true;
  while (previewQueue.length) {
    const i = previewQueue.shift();
    const slot = currentSlots[i];
    if (!slot || slot.previewTex) continue;
    try {
      if (slot.video.preview && /\.(png|webp)$/.test(slot.video.preview)) {
        // готовое PNG-превью с сервера — мгновенно
        await applyPreview(slot, slot.video.preview);
      } else {
        const data = await makePreview(slot.video.url);
        if (data) applyPreview(slot, data);
        else slot.screenMat.color.set(0xf0d6de);
      }
    } catch (e) {
      console.warn("Превью не получилось:", slot.video.file, e);
      slot.screenMat.color.set(0xf0d6de);
    }
    previewsDone++;
    window.HALL.previews = previewsDone;
    updateBar(previewsDone, previewsQueued);
  }
  previewBusy = false;
}

function updateBar(done, total) {
  barFill.style.width = total ? `${Math.round((done / total) * 100)}%` : "100%";
  if (!currentSlots.length) {
    statusEl.textContent = `На сервере нет видео. Положите файлы в папку ${YYYY}_kuromur.`;
  } else if (total > 0 && done >= total) {
    statusEl.textContent = "Готово! Все превью загружены.";
  } else {
    statusEl.textContent = `Превью загружаются: ${done}/${total || currentSlots.length}`;
  }
  if (started) {
    startBtn.textContent = "Продолжить";
  } else {
    startBtn.textContent = total > 0 && done >= total ? "Войти" : `Войти (превью ${done}/${total || currentSlots.length})`;
  }
}

// Загрузить превью для слота прямо в момент клика (до начала воспроизведения).
// Сначала пытаемся PNG-превью с сервера (мгновенно), иначе захватываем первый кадр локально.
async function preloadPreviewForSlot(slot, cb) {
  if (slot.previewTex) { cb(); return; }
  const img = new Image();
  img.onload = () => {
    const tex = new THREE.Texture(img);
    tex.needsUpdate = true;
    tex.colorSpace = THREE.SRGBColorSpace;
    tex.anisotropy = 8;
    slot.previewTex = tex;
    if (!slot.playing) {
      slot.screenMat.map = tex;
      slot.screenMat.color.set(0xffffff);
      slot.screenMat.needsUpdate = true;
    }
    cb();
  };
  img.onerror = () => {
    slot.screenMat.color.set(0xf0d6de);
    cb();
  };
  if (slot.video.preview && /\.(png|webp)$/.test(slot.video.preview)) {
    img.src = slot.video.preview;
  } else {
    // первый кадр видео без подгрузки самого видеофайла
    const el = document.createElement("video");
    el.preload = "metadata";
    el.muted = true;
    el.crossOrigin = "anonymous";
    el.src = slot.video.url;
    el.addEventListener("loadedmetadata", () => {
      el.currentTime = 0;
    });
    const onSeek = () => {
      el.removeEventListener("seeked", onSeek);
      const vw = el.videoWidth || 640, vh = el.videoHeight || 360;
      const w = Math.min(CFG.previewMaxW, vw);
      const h = Math.round((w * vh) / vw);
      const c = document.createElement("canvas");
      c.width = w; c.height = h;
      c.getContext("2d").drawImage(el, 0, 0, w, h);
      img.src = c.toDataURL("image/jpeg", CFG.previewQuality);
    };
    el.addEventListener("seeked", onSeek);
    el.addEventListener("error", () => { el.removeEventListener("seeked", onSeek); img.onerror(); });
  }
}

function preparePreviews() {
  // превью лёгкие (webp) — грузим ВСЕ сразу при открытии страницы
  pendingFinished = false;
  const all = currentSlots.map((s, i) => i);
  previewsQueued = all.length;
  previewsDone = 0;
  updateBar(0, previewsQueued);
  enqueuePreviews(all);
}

// раньше лабиринт догружался после входа; теперь всё грузится сразу — заглушка.
let pendingFinished = false;
function loadRemainingPreviews() {
  if (pendingFinished) return;
  pendingFinished = true;
  updateBar(previewsDone, currentSlots.length);
}

/* ============================== МИНИКАРТА И БОЛЬШАЯ КАРТА ============================== */

// Рисует план музея (сверху, север вверху) на переданный canvas-контекст.
// Стены берём из colliders — карта всегда соответствует миру.
let mapBounds = null;
function computeMapBounds() {
  if (mapBounds) return mapBounds;
  let minX = 1e9, maxX = -1e9, minZ = 1e9, maxZ = -1e9;
  for (const b of colliders) {
    minX = Math.min(minX, b.minX); maxX = Math.max(maxX, b.maxX);
    minZ = Math.min(minZ, b.minZ); maxZ = Math.max(maxZ, b.maxZ);
  }
  mapBounds = { minX: minX - 2, maxX: maxX + 2, minZ: minZ - 2, maxZ: maxZ + 2 };
  return mapBounds;
}

// подписи зон на картах убраны — только стены, игроки и призраки

function drawMap(ctx, W, Hh) {
  const b = computeMapBounds();
  const pad = 14;
  const scale = Math.min((W - pad * 2) / (b.maxX - b.minX), (Hh - pad * 2) / (b.maxZ - b.minZ));
  const ox = (W - (b.maxX - b.minX) * scale) / 2;
  const oy = (Hh - (b.maxZ - b.minZ) * scale) / 2;
  const X = (x) => ox + (x - b.minX) * scale;
  const Z = (z) => oy + (z - b.minZ) * scale;

  ctx.clearRect(0, 0, W, Hh);
  ctx.fillStyle = "rgba(24,16,28,0.9)";
  ctx.fillRect(0, 0, W, Hh);

  // стены
  ctx.fillStyle = "#d9a8c4";
  for (const bx of colliders) {
    ctx.fillRect(X(bx.minX), Z(bx.minZ), Math.max(1, (bx.maxX - bx.minX) * scale), Math.max(1, (bx.maxZ - bx.minZ) * scale));
  }

  // подписи
  const fs = Math.max(9, Math.round(scale * 5.2));
  ctx.font = `bold ${fs}px system-ui, sans-serif`;
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  ctx.fillStyle = "rgba(255, 240, 246, 0.85)";
  // подписи зон убраны — рисуем компактнее

  // игрок: точка + направление взгляда
  const px = X(camera.position.x), pz = Z(camera.position.z);
  const dir = -yaw - Math.PI / 2; // yaw 0 смотрит на север (вверх на карте)
  ctx.beginPath();
  ctx.moveTo(px, pz);
  ctx.lineTo(px + Math.cos(dir + 0.45) * 12, pz + Math.sin(dir + 0.45) * 12);
  ctx.lineTo(px + Math.cos(dir - 0.45) * 12, pz + Math.sin(dir - 0.45) * 12);
  ctx.closePath();
  ctx.fillStyle = "rgba(255, 220, 120, 0.5)";
  ctx.fill();
  ctx.beginPath();
  ctx.arc(px, pz, 3.2, 0, 7);
  ctx.fillStyle = "#ffd866";
  ctx.fill();
  ctx.strokeStyle = "#7c3f58";
  ctx.lineWidth = 1.5;
  ctx.stroke();

  // призраки других игроков
  if (typeof mpState !== "undefined") {
    ctx.font = `bold ${Math.max(8, Math.round(scale * 4.5))}px system-ui, sans-serif`;
    for (const g of mpState.others.values()) {
      const gx = X(g.x), gz = Z(g.z);
      ctx.beginPath();
      ctx.arc(gx, gz, 3, 0, 7);
      ctx.fillStyle = "rgba(255, 158, 192, 0.9)";
      ctx.fill();
      ctx.fillStyle = "rgba(255, 200, 220, 0.85)";
      ctx.fillText(g.name, gx, gz - 6);
    }
  }
}

const mmCtx = minimap.getContext("2d");
function updateMinimap() {
  drawMap(mmCtx, minimap.width, minimap.height);
}
setInterval(() => { if (started && !bigmapOpen) updateMinimap(); }, 180);

let bigmapOpen = false;
function toggleBigmap(force) {
  bigmapOpen = force !== undefined ? force : !bigmapOpen;
  bigmap.classList.toggle("hidden", !bigmapOpen);
  if (bigmapOpen) drawMap(bigmapCanvas.getContext("2d"), bigmapCanvas.width, bigmapCanvas.height);
}
// большая карта живо обновляется, пока открыта
setInterval(() => { if (started && bigmapOpen) drawMap(bigmapCanvas.getContext("2d"), bigmapCanvas.width, bigmapCanvas.height); }, 180);

/* ============================== ВИДЕО ПО КЛИКУ ============================== */

function duckMusic(on) {
  if (!music || !musicBuffer) return;
  // при видео мелодия полностью выключается, без видео — тихий фон
  music.setVolume(on ? 0 : CFG.musicVolume);
}

function ensureMedia(slot) {
  if (slot.el) {
    // элемент мог быть освобождён в stopPlayback (src снят) — навешиваем заново
    if (!slot.el.getAttribute("src")) {
      slot.el.src = slot.video.url;
      slot.el.load();
    }
    return slot.el;
  }
  const el = document.createElement("video");
  el.src = slot.video.url;
  el.loop = false;
  el.muted = false;
  el.playsInline = true;
  el.preload = "auto";
  el.crossOrigin = "anonymous";
  el.addEventListener("ended", () => stopPlayback(slot));
  slot.el = el;
  videoElements.push(el);

  const audio = new THREE.PositionalAudio(listener);
  audio.setMediaElementSource(el);
  audio.setRefDistance(CFG.audioRef);
  audio.setMaxDistance(CFG.audioMax);
  audio.setDistanceModel("linear");
  audio.setRolloffFactor(1);
  audio.panner.panningModel = "equalpower";
  slot.group.add(audio);
  return el;
}

function startPlayback(slot) {
  // переключение: прошлое видео останавливается
  if (activeSlot && activeSlot !== slot) stopPlayback(activeSlot);
  activeSlot = slot;
  duckMusic(true); // фон тише, пока играет видео

  const el = ensureMedia(slot);
  if (!slot.videoTex) {
    const tex = new THREE.VideoTexture(el);
    tex.colorSpace = THREE.SRGBColorSpace;
    slot.videoTex = tex;
  }
  slot.screenMat.map = slot.videoTex;
  slot.screenMat.color.set(0xffffff);
  slot.screenMat.needsUpdate = true;
  slot.playing = true;

  // публикация в ОБЩУЮ очередь: у всех клиентов это видео просто начнётся с нуля.
  // (персональная очередь как была: один activeSlot, прошлый уже остановлен выше)
  mpSyncPublish(slot);

  // празднование: залп конфетти у картины!
  fireConfetti(slot.group.position.x * 0.9, slot.group.position.z * 0.9, 110);

  const p = el.play();
  if (p && p.catch) p.catch(() => { el.muted = true; el.play().catch(() => {}); });
}

// моё видео попало в общую очередь
function mpSyncPublish(slot) {
  const url = slot.video.url;
  mpState.syncQueue.set(url, { id: mpState.myId, url, slot, mine: true });
  mpSendVPlay(url);
}

function mpSyncStop(slot) {
  const url = slot.video.url;
  if (!mpState.syncQueue.delete(url)) return; // не игралось в общей очереди
  mpSendVStop(url);
}

function stopPlayback(slot) {
  mpSyncStop(slot); // убрать из общей очереди (если там было) и сообщить всем
  if (slot.el) {
    slot.el.pause();
    // полностью освобождаем медиапоток: пауза оставляет Range-запрос открытым,
    // такие «висящие» потоки накапливаются и тормозят следующие видео
    slot.el.removeAttribute("src");
    slot.el.load();
  }
  slot.playing = false;
  if (activeSlot === slot) {
    activeSlot = null;
    duckMusic(false); // музыка возвращается
  }
  if (slot.previewTex) {
    slot.screenMat.map = slot.previewTex;
  } else {
    slot.screenMat.map = null;
    slot.screenMat.color.set(0x2a2430);
  }
  slot.screenMat.needsUpdate = true;
}

function togglePlayback(slot) {
  if (slot.playing) stopPlayback(slot);
  else startPlayback(slot);
}

/* --- приёмная часть: только факт запуска/остановки, рассинхрон игнорируем --- */

// у кого-то началось видео — запускаем у себя с нуля; silent=true из retained-списка,
// (чтобы массовый приём не вызывал лавину пересылок «что играет»)
function mpReceiveVPlay(e, silent) {
  if (e.id === mpState.myId) return; // это наше собственное, уже играет
  const url = String(e.url || "");
  if (!url) return;
  // это видео сейчас играет у нас (наша персональная очередь) — мы источник истины
  const existing = mpState.syncQueue.get(url);
  if (existing && existing.mine) return;
  const entry = { id: e.id, url, slot: null, mine: false };
  const slot = mpSlotByUrl(url);
  if (slot) {
    entry.slot = slot;
    mpState.syncQueue.set(url, entry);
    startSyncVisual(slot);
  } else {
    // слот ещё не построен (ленивая зона) — запомним и попробуем позже
    mpState.pendingVideos.set(url, entry);
  }
  if (!silent) mpPublishNow(); // retained «что играет» — обновляем нашим знанием
}

// визуально включить чужое видео на экране (картинка общего 3D-экрана
// + позиционный звук от места картины)
function startSyncVisual(slot) {
  const el = ensureMedia(slot);
  if (!slot.videoTex) {
    const tex = new THREE.VideoTexture(el);
    tex.colorSpace = THREE.SRGBColorSpace;
    slot.videoTex = tex;
  }
  slot.screenMat.map = slot.videoTex;
  slot.screenMat.color.set(0xffffff);
  slot.screenMat.needsUpdate = true;
  slot.playing = true;
  const p = el.play();
  if (p && p.catch) p.catch(() => { el.muted = true; el.play().catch(() => {}); });
}

// у кого-то остановилось видео — останавливаем у себя
function mpReceiveVStop(m) {
  const url = String(m.url || "");
  mpState.syncQueue.delete(url);
  mpState.pendingVideos.delete(url);
  const slot = mpSlotByUrl(url);
  if (slot) stopPlayback(slot);
  mpPublishNow();
}

// дозапуск отложенных (слоты ленивых зон могли догрузиться), раз в полсекунды
setInterval(() => {
  if (!mpState.connected) return;
  for (const [url, e] of [...mpState.pendingVideos]) {
    const slot = mpSlotByUrl(url);
    if (!slot) continue; // ещё не построен — ждём
    mpState.pendingVideos.delete(url);
    e.slot = slot;
    mpState.syncQueue.set(url, e);
    startSyncVisual(slot);
  }
}, 500);

// кнопка «Конфетти» удалена — вместо неё миникарта; взрыв по клавише E

// Взрыв конфетти вокруг игрока (клавиша E): центр + 8 точек вокруг в радиусе 4 м
function confettiExplosionAt(x, z) {
  fireConfetti(x, z, 200, true);
  for (let a = 0; a < 8; a++) {
    const ang = (a / 8) * Math.PI * 2;
    fireConfetti(x + Math.cos(ang) * 4, z + Math.sin(ang) * 4, 90, true);
  }
}

function confettiExplosion() {
  const p = camera.position;
  confettiExplosionAt(p.x, p.z);
  // сетевой режим: все призраки увидят салют на нашей позиции
  if (mpState.connected) {
    mpSendRaw({ t: "boom", x: p.x, z: p.z });
  }
}

// интеракция по точке экрана (NDC): видео под прицелом / кнопка телепорта.
// Используется и мышью (центр экрана), и тапом на телефоне (точка касания).
function interactAt(ndc) {
  camera.updateMatrixWorld();
  scene.updateMatrixWorld(true);
  raycaster.setFromCamera(ndc, camera);
  const hits = raycaster.intersectObjects(clickables, false);
  if (hits.length) {
    const obj = hits[0].object;
    // кнопка-портал: переход в коридор другого года (../2025/ и т.п.)
    if (obj.userData.portal) {
      fireConfetti(camera.position.x, camera.position.z, 25); // мини-салют у кнопки
      window.location.href = obj.userData.portal;
      return;
    }
    // кнопка телепорта: нажал — перенёсся в случайный проход лабиринта
    if (obj.userData.teleport) {
      fireConfetti(camera.position.x, camera.position.z, 25); // мини-салют у кнопки
      doMazeTeleport();
      return;
    }
    const slot = obj.userData.slot;
    // видео не подгружаем заранее — сначала превью по клику, затем играем
    preloadPreviewForSlot(slot, () => togglePlayback(slot));
  }
}

canvas.addEventListener("pointerdown", (e) => {
  if (!isPlaying()) return;          // на паузе клики не играют видео
  if (isTouch) return;               // на телефоне тап-клик обрабатывает touchend (чтобы отличить от свайпа)
  if (document.pointerLockElement !== canvas) lockPointer(); // при случае захватываем курсор
  interactAt(CENTER);
});

/* ============================== ТЕЛЕПОРТ-КНОПКА ============================== */

// перенос в случайный безопасный проход лабиринта (цель — всегда проходимая клетка)
function doMazeTeleport() {
  if (!mazeSafeCells.length) return;
  if (clock.elapsedTime - lastTeleport < 1) return; // защита от дабл-клика
  lastTeleport = clock.elapsedTime;
  const dest = mazeSafeCells[Math.floor(Math.random() * mazeSafeCells.length)];
  camera.position.set(dest.x, CFG.eyeHeight, dest.z);
  // салют на месте приземления + всем игрокам в мультиплеере
  confettiExplosion();
}

/* ============================== МУЗЫКА ============================== */

let music = null;
let musicBuffer = null;

function loadMusic() {
  new THREE.AudioLoader().load(
    "audio/halloween.mp3",
    (buf) => {
      musicBuffer = buf;
      if (started) playMusic();
    },
    undefined,
    (e) => console.warn("Музыка не загрузилась:", e)
  );
}

function playMusic() {
  if (!musicBuffer) return;
  if (music && music.isPlaying) return;
  if (!music) {
    music = new THREE.Audio(listener);
    music.setBuffer(musicBuffer);
    music.setLoop(true);
    music.setVolume(CFG.musicVolume);
  }
  try {
    music.play();
  } catch (e) {
    console.warn("Музыка не стартовала:", e);
  }
}

function stopMusic() {
  if (music && music.isPlaying) music.pause();
}

/* ============================== ЗВУК ПРИ ПАУЗЕ ============================== */

let soundSuspended = false;

function suspendSound() {
  if (soundSuspended) return;
  soundSuspended = true;
  try { listener.context.suspend(); } catch (e) { /* ignore */ }
}

function resumeSound() {
  if (!soundSuspended) return;
  soundSuspended = false;
  try { listener.context.resume(); } catch (e) { /* ignore */ }
}

// вкладка скрыта / окно не в фокусе — тишина
document.addEventListener("visibilitychange", () => {
  if (document.hidden) suspendSound();
  else if (started && overlay.classList.contains("hidden")) resumeSound();
});
window.addEventListener("blur", () => { if (started) suspendSound(); });
window.addEventListener("focus", () => {
  if (started && overlay.classList.contains("hidden")) resumeSound();
});

/* ============================== МУЛЬТИПЛЕЕР ============================== */

const usernameInput = $("username");
const mpNote = $("mp-note");
const mpCount = $("mp-count");

// всплывший из localStorage ник
try { usernameInput.value = localStorage.getItem("kurumur-name") || ""; } catch {}

// милая котико-аватарка: объёмная группа вращается по направлению взгляда игрока
function ghostSprite(name) {
  const group = new THREE.Group();

  // мягкий пушистый материал — палитра Куромур: лавандово-чернильная шёрстка
  const bodyMat = new THREE.MeshLambertMaterial({ color: 0xb9a8d4 }); // мягкая лаванда («Куро»-фиолет, осветлённый)
  const darkMat = new THREE.MeshLambertMaterial({ color: 0x2b2138 }); // чернильно-фиолетовый фон carrd

  // тельце — пузатая сфера
  const body = new THREE.Mesh(new THREE.SphereGeometry(0.3, 24, 16), bodyMat);
  body.scale.set(1, 1.05, 1);
  body.position.y = -0.18;
  group.add(body);

  // голова — большая и круглая (миниатюрные пропорции: голова крупнее тела)
  const head = new THREE.Mesh(new THREE.SphereGeometry(0.28, 24, 16), bodyMat);
  head.position.y = 0.22;
  group.add(head);

  // ушки — два конуса сверху с тёмными кончиками
  const earGeo = new THREE.ConeGeometry(0.09, 0.16, 12);
  const earL = new THREE.Mesh(earGeo, bodyMat);
  earL.position.set(-0.16, 0.46, 0);
  earL.rotation.z = 0.25;
  group.add(earL);
  const earR = new THREE.Mesh(earGeo, bodyMat);
  earR.position.set(0.16, 0.46, 0);
  earR.rotation.z = -0.25;
  group.add(earR);
  // розовые внутренние ушки — как акценты 🐾 на carrd
  const earInGeo = new THREE.ConeGeometry(0.055, 0.1, 12);
  const earInMat = new THREE.MeshLambertMaterial({ color: 0xffd8e8 }); // тот же розовый, что у таблички
  const earInL = new THREE.Mesh(earInGeo, earInMat);
  earInL.position.set(-0.16, 0.45, 0.03);
  earInL.rotation.z = 0.25;
  group.add(earInL);
  const earInR = new THREE.Mesh(earInGeo, earInMat);
  earInR.position.set(0.16, 0.45, 0.03);
  earInR.rotation.z = -0.25;
  group.add(earInR);
  const tipGeo = new THREE.SphereGeometry(0.035, 8, 6);
  const tipL = new THREE.Mesh(tipGeo, darkMat);
  tipL.position.set(-0.185, 0.53, 0);
  group.add(tipL);
  const tipR = new THREE.Mesh(tipGeo, darkMat);
  tipR.position.set(0.185, 0.53, 0);
  group.add(tipR);

  // хвостик — изогнутая цепочка шариков с тёмным кончиком, торчит назад (—Z)
  const tailSegGeo = new THREE.SphereGeometry(0.055, 10, 8);
  const segs = [
    { p: [0, -0.15, -0.3], s: 1 },
    { p: [0.03, -0.08, -0.36], s: 0.95 },
    { p: [0.08, 0.02, -0.38], s: 0.85 },
  ];
  for (const s of segs) {
    const seg = new THREE.Mesh(tailSegGeo, bodyMat);
    seg.position.set(...s.p);
    seg.scale.setScalar(s.s);
    group.add(seg);
  }
  const tailTip = new THREE.Mesh(new THREE.SphereGeometry(0.05, 10, 8), darkMat);
  tailTip.position.set(0.12, 0.1, -0.37);
  group.add(tailTip);

  // лапки — четыре маленьких шарика у основания
  const pawGeo = new THREE.SphereGeometry(0.07, 10, 8);
  for (const [px, pz] of [[-0.14, 0.14], [0.14, 0.14], [-0.14, -0.12], [0.14, -0.12]]) {
    const paw = new THREE.Mesh(pawGeo, darkMat);
    paw.position.set(px, -0.46, pz);
    paw.scale.set(1, 0.7, 1);
    group.add(paw);
  }

  // глазки смотрят вперёд (+Z группы) — направление взгляда видно всем телом
  const eyeGeo = new THREE.SphereGeometry(0.07, 12, 10);
  const eyeWhite = new THREE.MeshBasicMaterial({ color: 0x2b2138 }); // чернильно-фиолетовые глазки, как фон carrd
  const eyeL = new THREE.Mesh(eyeGeo, eyeWhite);
  eyeL.scale.set(1, 1.3, 0.6);
  eyeL.position.set(-0.11, 0.25, 0.235);
  group.add(eyeL);
  const eyeR = new THREE.Mesh(eyeGeo, eyeWhite);
  eyeR.scale.set(1, 1.3, 0.6);
  eyeR.position.set(0.11, 0.25, 0.235);
  group.add(eyeR);
  // двойной блеск в глазках — «втуберный» способ смотреть
  const shineGeo = new THREE.SphereGeometry(0.022, 8, 6);
  const shineSmall = new THREE.SphereGeometry(0.012, 8, 6);
  const shineMat = new THREE.MeshBasicMaterial({ color: 0xffffff });
  const s1 = new THREE.Mesh(shineGeo, shineMat);
  s1.position.set(-0.085, 0.295, 0.285);
  group.add(s1);
  const s2 = new THREE.Mesh(shineSmall, shineMat);
  s2.position.set(-0.13, 0.215, 0.28);
  group.add(s2);
  const s3 = new THREE.Mesh(shineGeo, shineMat);
  s3.position.set(0.135, 0.295, 0.285);
  group.add(s3);
  const s4 = new THREE.Mesh(shineSmall, shineMat);
  s4.position.set(0.09, 0.215, 0.28);
  group.add(s4);

  // носик + усы
  const nose = new THREE.Mesh(new THREE.SphereGeometry(0.03, 10, 8), new THREE.MeshBasicMaterial({ color: 0xe2647a }));
  nose.position.set(0, 0.15, 0.27);
  nose.scale.set(1.3, 0.8, 0.7);
  group.add(nose);
  const whiskerGeo = new THREE.CylinderGeometry(0.004, 0.004, 0.16, 4);
  const whiskerMat = new THREE.MeshBasicMaterial({ color: 0x2b2138 });
  for (const [side, yOff] of [[-1, 0.13], [1, 0.13], [-1, 0.09], [1, 0.09]]) {
    const w = new THREE.Mesh(whiskerGeo, whiskerMat);
    w.rotation.z = Math.PI / 2;
    w.rotation.y = side * 0.35;
    w.position.set(side * 0.2, yOff + 0.04, 0.2);
    group.add(w);
  }
  // розовые щёчки
  const cheekMat = new THREE.MeshBasicMaterial({ color: 0xffb7ca, transparent: true, opacity: 0.55 });
  const cheekL = new THREE.Mesh(new THREE.CircleGeometry(0.04, 10), cheekMat);
  cheekL.position.set(-0.19, 0.14, 0.22);
  cheekL.rotation.y = -0.4;
  group.add(cheekL);
  const cheekR = new THREE.Mesh(new THREE.CircleGeometry(0.04, 10), cheekMat);
  cheekR.position.set(0.19, 0.14, 0.22);
  cheekR.rotation.y = 0.4;
  group.add(cheekR);

  // табличка с именем — билборд над головой
  const c = document.createElement("canvas");
  c.width = 512; c.height = 128;  // Увеличиваем канвас для длинных имён
  const ctx = c.getContext("2d");
  
  const labelName = `${name} 🐾`;
  
  // Динамически подбираем размер шрифта, чтобы текст влез
  let px = 68;  // Начальный размер шрифта (было 34px, увеличиваем пропорционально канвасу)
  ctx.font = `700 ${px}px system-ui, "Segoe UI", sans-serif`;
  while (ctx.measureText(labelName).width > c.width - 56 && px > 24) {
    px -= 4;
    ctx.font = `700 ${px}px system-ui, "Segoe UI", sans-serif`;
  }
  
  const tw = Math.min(c.width - 56, ctx.measureText(labelName).width + 56);
  
  ctx.fillStyle = "rgba(20,14,28,0.75)";
  ctx.beginPath();
  ctx.roundRect(c.width / 2 - tw / 2, 20, tw, 88, 24);
  ctx.fill();
  
  ctx.fillStyle = "#ffd8e8";
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  ctx.fillText(labelName, c.width / 2, 66);
  
  const tex = new THREE.CanvasTexture(c);
  tex.colorSpace = THREE.SRGBColorSpace;
  
  const label = new THREE.Sprite(new THREE.SpriteMaterial({
    map: tex, transparent: true, opacity: 0.9, depthWrite: false,
  }));
  
  // Масштаб плашки — пропорционально размеру канваса
  const aspect = c.width / c.height;
  label.scale.set(1.6, 1.6 / aspect, 1);
  label.position.y = 0.75;
  group.add(label);

  return group;
}

/* ============================== МУЛЬТИПЛЕЕР ============================== */
/*
 * Транспорт: MQTT-релей поверх публичных брокеров (WebSocket). Замена двух
 * прежних схем: WebSocket-сервера в server.js (/mp) и P2P-PeerJS.
 *
 * Почему MQTT, а не PeerJS: P2P без TURN не пробивается между сетями многих
 * российских провайдеров (похоже, именно это случилось в проде: «друг друга
 * не видно»), а бесплатных публичных TURN почти не осталось. MQTT-брокер —
 * это уже готовый релей: каждый клиент публикует своё состояние и слушает
 * остальных. Нет избрания хоста, нет RTCPeerConnection, всё доходит любых
 * сетей. Объём данных мизерный (позиции и события).
 *
 * Топики (общие для всех, своя «комната» на каждый год):
 *   kuromursk-maze-<год>-b7km41/p    — позиции {t:"p", id, name, x, z, ry} 12 Гц
 *   kuromursk-maze-<год>-b7km41/evt  — события {t:"vplay"|"vstop"|"boom", id, ...}
 *   kuromursk-maze-<год>-b7km41/now  — retained: список «что играет прямо сейчас»
 *     {t:"now", videos:[{id,url},...]} — так что поздний вошедший сразу видит
 *     картину в фильме (замена серверного init.videos).
 * Призраки очищаются локально по lastSeen > 10 с, дубликаты имён — по месту
 * отрисовки (суффикс «Мур 2»).
 */
const MP_BROKERS = [
  "wss://broker.hivemq.com:8884/mqtt",
  "wss://broker.emqx.io:8084/mqtt",
];
// отдельная «комната» на каждый год-проект: гости 2024 (или 2025) не мешают
// гостям музея из основного зала
const MP_ROOM = "kuromursk-maze-" + YYYY + "-b7km41";
const MP_TOPIC_P = MP_ROOM + "/p";
const MP_TOPIC_EVT = MP_ROOM + "/evt";
const MP_TOPIC_NOW = MP_ROOM + "/now";

const mpState = {
  clients: [],          // ПОДКЛЮЧЕНИЯ КО ВСЕМ брокерам: [mqtt.Client | null]
  status: "off",        // off | connecting | on
  myId: null, connected: false, myName: null,
  others: new Map(), // id -> { sprite, name, x, z, ry, tx, tz, try, lastSeen }
  lastSend: 0,
  reconnectTimer: null,
  boomKey: null, boomTime: 0,  // дедупликация «boom» (двойной салют от двух брокеров)
  /* --- синхронизация видео (только факт запуска) --- */
  syncQueue: new Map(),     // url -> { id, url, slot, mine } — ОБЩАЯ очередь: что играет у всех
  pendingVideos: new Map(), // url -> инфо, слот ещё не построен (ленивая зона)
};

function mpDecode(raw) {
  try {
    const s = typeof raw === "string" ? raw : new TextDecoder().decode(raw);
    return JSON.parse(s);
  } catch { return null; }
}

// publish/subscribe на ВСЕ живые брокеры: один клиент MOЖ быть подключён
// только к доступным ему; чтобы любые пары игроков встречались, шину дублируем
function mpEachClient(fn) {
  let alive = 0;
  for (const c of mpState.clients) {
    if (c && c.connected) { alive++; try { fn(c); } catch {} }
  }
  return alive;
}

// Событие в общий топик (включая конфетти и остановки video)
function mpSendRaw(obj) {
  const payload = JSON.stringify({ ...obj, id: mpState.myId });
  mpEachClient((c) => c.publish(MP_TOPIC_EVT, payload));
}

// retained-список «что играет сейчас» — каждый клиент публикует своё знание,
// последний выигрывает; только что вошедший получает его по подписке
function mpPublishNow() {
  const videos = [...mpState.syncQueue.values()].map((e) => ({
    id: e.mine ? mpState.myId : e.id, url: e.url,
  }));
  const payload = JSON.stringify({ t: "now", videos });
  mpEachClient((c) => c.publish(MP_TOPIC_NOW, payload, { retain: true, qos: 0 }));
}

function mpSendVPlay(url) {
  mpSendRaw({ t: "vplay", url });
  mpPublishNow();
}

function mpSendVStop(url) {
  mpSendRaw({ t: "vstop", url });
  mpPublishNow();
}

// диагностическая сводка: смотреть в консоли `window.HALL.mp()`
function mpDebugInfo() {
  return {
    status: mpState.status,
    connected: mpState.connected,
    myId: mpState.myId,
    mqttLoaded: typeof mqtt !== "undefined" || typeof MQTT !== "undefined",
    brokers: MP_BROKERS.map((url, i) => ({
      broker: url.replace("wss://", ""),
      on: !!(mpState.clients[i] && mpState.clients[i].connected),
    })),
    ghosts: [...mpState.others.keys()].map((id) => mpState.others.get(id).name),
  };
}


// найти картину-слот по url видео
function mpSlotByUrl(url) {
  return currentSlots.find((s) => s.video.url === url) || null;
}

// Единая обработка входящих сообщений
function mpHandleMessage(m) {
  if (m.t === "p") {
    if (m.id === mpState.myId) return;
    mpUpdateGhost(m);
    return;
  }
  if (m.id === mpState.myId) return; // свои события не обрабатываем
  if (m.t === "join") { mpAddGhost(m.player); return; }
  if (m.t === "leave") { mpRemoveGhost(m.id); return; }
  if (m.t === "boom") {
    // при мульти-брокерной шине событие приходит дважды — салют дублируем нельзя
    const key = m.id + "|" + (m.x || 0) + "|" + (m.z || 0);
    const now = performance.now();
    if (mpState.boomKey === key && now - mpState.boomTime < 500) return;
    mpState.boomKey = key; mpState.boomTime = now;
    confettiExplosionAt(m.x, m.z);
    return;
  }
  if (m.t === "vplay") { mpReceiveVPlay(m); return; }
  if (m.t === "vstop") { mpReceiveVStop(m); return; }
  if (m.t === "now") {
    for (const e of m.videos || []) mpReceiveVPlay(e, true);
    return;
  }
}

function mpConnect(name) {
  if (typeof mqtt === "undefined" && typeof MQTT === "undefined") {
    console.warn("MQTT не загрузился — мультиплеер недоступен (музей работает без него)");
    return;
  }
  for (const c of mpState.clients) { if (c) { try { c.end(true); } catch {} } }
  mpState.clients = [];
  if (mpState.reconnectTimer) { clearTimeout(mpState.reconnectTimer); mpState.reconnectTimer = null; }
  mpState.myName = name;
  mpState.myId = "km" + Math.random().toString(36).slice(2, 10);
  mpStartAll();
}

// Стартуем ВСЕ брокеры параллельно: иначе разные игроки могут оказаться на
// разных брокерах (у кого-то hivemq не пробился — ротация увела их врозь).
function mpStartAll() {
  mpState.status = "connecting";
  for (let i = 0; i < MP_BROKERS.length; i++) mpStartBroker(i);
}

function mpStartBroker(i) {
  const url = MP_BROKERS[i];
  let client;
  try {
    client = (window.mqtt || window.MQTT).connect(url, {
      clientId: mpState.myId + "b" + i,
      keepalive: 30,
      clean: true,
      connectTimeout: 10000,
      reconnectPeriod: 0,  // авто-реконнект отключаем: сами перезапускаем всех
    });
  } catch (e) {
    console.warn("MQTT недоступен:", e);
    return;
  }
  mpState.clients[i] = client;
  console.info("MP: подключаемся к брокеру", url.replace("wss://", ""));

  client.on("connect", () => {
    if (mpState.clients[i] !== client) return;
    client.subscribe([MP_TOPIC_P, MP_TOPIC_EVT, MP_TOPIC_NOW], { qos: 0 });
    mpState.status = "on";
    mpState.connected = true;
    mpNote.classList.remove("hidden");
    console.info("MP: подключён:", url.replace("wss://", ""), "(брокер", i + 1, "/", MP_BROKERS.length + ")");
    // retained «что играет» придёт по подписке; и сразу публикуем своё знание
    mpPublishNow();
  });

  client.on("message", (topic, payload) => {
    const m = mpDecode(payload);
    if (!m || typeof m !== "object") return;
    mpHandleMessage(m);
  });

  const die = () => {
    if (mpState.clients[i] !== client) return;
    mpState.clients[i] = null;
    try { client.end(true); } catch {}
    mpMaybeRestart();
  };

  client.on("close", die);
  client.on("offline", die);
  client.on("error", (e) => {
    console.warn("MP: брокер недоступен:", (e && e.message) || e);
    die();
  });
}

// Все брокеры молчат — перезапуск всей шины через 15 с
function mpMaybeRestart() {
  if (mpState.clients.some((c) => c)) return; // есть ещё живое соединение
  mpState.connected = false;
  mpState.status = "off";
  if (mpState.reconnectTimer) return;
  if (!started) return;
  console.info("MP: все брокеры молчат — перезапуск через 15 с");
  mpState.reconnectTimer = setTimeout(() => {
    mpState.reconnectTimer = null;
    if (started) { mpState.clients = []; mpStartAll(); }
  }, 15000);
}

// (обрыв обрабатывается целиком через rotate() внутри mpTryBroker)

function mpAddGhost(p) {
  if (p.id === mpState.myId || mpState.others.has(p.id)) return;
  // дубликаты имён — суффикс по месту (раньше делал сервер)
  let name = String(p.name || "Гость");
  for (const g of mpState.others.values()) {
    if (g.name === name) { name = `${name} 2`; }
  }
  const sprite = ghostSprite(name); // теперь Group: тело-билборд + стрелка направления
  sprite.position.set(p.x, 1.35, p.z);
  scene.add(sprite);
  mpState.others.set(p.id, {
    sprite, name,
    x: p.x, z: p.z, ry: p.ry,
    tx: p.x, tz: p.z, try: p.ry,
    phase: Math.random() * 6.28,
    lastSeen: performance.now(),
  });
}

function mpUpdateGhost(p) {
  const g = mpState.others.get(p.id);
  if (!g) { mpAddGhost(p); return; }
  g.tx = p.x; g.tz = p.z; g.try = p.ry;
  g.lastSeen = performance.now();
}

function mpRemoveGhost(id) {
  const g = mpState.others.get(id);
  if (!g) return;
  scene.remove(g.sprite);
  for (const ch of g.sprite.children) {
    if (ch.isSprite) {
      ch.material.map.dispose();
    }
    if (ch.material) ch.material.dispose();
    if (ch.geometry) ch.geometry.dispose();
  }
  mpState.others.delete(id);
}

function mpTick(t, dt) {
  if (!mpState.connected) return;
  // отправляем своё состояние ~12 Гц на все живые брокеры
  if (t - mpState.lastSend > 0.08) {
    mpState.lastSend = t;
    const payload = JSON.stringify({
      t: "p", id: mpState.myId, name: mpState.myName,
      x: camera.position.x, z: camera.position.z, ry: yaw,
    });
    mpEachClient((c) => c.publish(MP_TOPIC_P, payload));
  }
  // призраки без новостей дольше 10 с — удаляем (замена серверного heartbeat)
  for (const [id, g] of [...mpState.others]) {
    if (t - g.lastSeen > 10) mpRemoveGhost(id);
  }
  mpCount.textContent = String(mpState.others.size);
  // интерполяция чужих призраков
  const k = 1 - Math.exp(-8 * dt);
  for (const g of mpState.others.values()) {
    g.x += (g.tx - g.x) * k;
    g.z += (g.tz - g.z) * k;
    // плавный поворот
    let d = g.try - g.ry;
    while (d > Math.PI) d -= Math.PI * 2;
    while (d < -Math.PI) d += Math.PI * 2;
    g.ry += d * k;
    // парение + лёгкое «дыхание» прозрачности
    g.sprite.position.set(
      g.x,
      1.35 + Math.sin(t * 1.6 + g.phase) * 0.09,
      g.z
    );
    // направление взгляда: всё привидение поворачивается лицом, куда смотрит игрок
    g.sprite.rotation.y = g.ry + Math.PI; // глаза на локальной +Z, yaw 0 = взгляд на -Z
    // лёгкое «дыхание» прозрачности всех частей тела
    for (const ch of g.sprite.children) {
      if (ch.isSprite) continue;
      ch.material.opacity = 0.55 + Math.sin(t * 0.9 + g.phase) * 0.08;
    }
  }
}

/* ============================== УПРАВЛЕНИЕ ============================== */

function enter() {
  if (!ready) return;
  if (!started) {
    // имя: обязательное, из поля ввода
    let name = usernameInput.value.trim().slice(0, 16);
    if (!name) {
      usernameInput.classList.add("err");
      usernameInput.focus();
      return;
    }
    usernameInput.classList.remove("err");
    try { localStorage.setItem("kurumur-name", name); } catch {}
    mpState.myName = name;
    playerName.textContent = name;
    playerBadge.classList.remove("hidden");

    started = true;
    crosshair.classList.remove("hidden");
    volHud.classList.remove("hidden");
    hintHud.classList.remove("hidden");
    minimap.classList.remove("hidden");
    mpConnect(name); // мультиплеер: представляемся и начинаем синхронизацию
    loadRemainingPreviews(); // догружаем превью лабиринта в фоне
    // праздничный залп при входе
    setTimeout(() => fireConfetti(SPAWN.x, SPAWN.z - 2.5, 130), 400);
  }
  const ctx = listener.context;
  if (ctx.state !== "running") ctx.resume().catch(() => {});
  resumeSound();
  playMusic();

  overlay.classList.add("hidden");
  btnMain.classList.add("hidden");
  lockPointer();
  // Enter в поле имени тоже входит
}
usernameInput.addEventListener("keydown", (e) => {
  if (e.key === "Enter") { e.preventDefault(); enter(); }
});

let hadPointerLock = false; // захват когда-либо удавался
function lockPointer() {
  try {
    const p = canvas.requestPointerLock({ unadjustedMovement: true });
    if (p && p.catch) {
      p.catch(() => {
        const p2 = canvas.requestPointerLock();
        if (p2 && p2.catch) p2.catch(() => {});
      });
    }
  } catch (e) {
    // pointer lock недоступен — играем в fallback-режиме (обзор при зажатой ЛКМ)
    try { canvas.requestPointerLock(); } catch (e2) { /* ignore */ }
  }
}

document.addEventListener("pointerlockchange", () => {
  if (document.pointerLockElement === canvas) { hadPointerLock = true; return; }
  // пауза по Esc-подобной потере замка — лишь когда замок реально выдавался;
  // без замка играем тихо в fallback-режиме, ничего не выкидывая в меню
  if (started && hadPointerLock) {
    suspendSound(); // пауза — беззвучно
    ovTitle.textContent = "Пауза";
    ovSub.textContent = "Звук выключен. Нажмите «Продолжить», чтобы вернуться на праздник.";
    startBtn.textContent = "Продолжить";
    btnMain.classList.remove("hidden");
    overlay.classList.remove("hidden");
  }
});

document.addEventListener("mousemove", (e) => {
  if (!isPlaying()) return;
  const locked = document.pointerLockElement === canvas;
  // без захвата курсора осматриваемся при удержании левой кнопки мыши
  if (!locked && !(e.buttons & 1)) return;
  yaw -= e.movementX * CFG.mouseSense;
  pitch -= e.movementY * CFG.mouseSense;
  pitch = Math.max(-1.5, Math.min(1.5, pitch));
});

document.addEventListener("wheel", (e) => {
  e.preventDefault();
  const step = e.deltaY < 0 ? 0.05 : -0.05;
  // до 150%: master gain может превышать 1 — честно помечаю, что звук усилен.
  // Усиление > 1 упирается в клиппинг, поэтому пока громкость выше 100% —
  // в цепь включается компрессор (пики мягко удерживаются, тихое громче на слух).
  const vol = Math.max(0, Math.min(1.5, listener.getMasterVolume() + step));
  listener.setMasterVolume(vol);
  try {
    if (vol > 1) listener.setFilter(listener._boostComp);
    else listener.removeFilter();
  } catch (e) { /* старая версия three — усиление работает и так */ }
  volHud.textContent = vol === 0 ? "🔇 громкость выключена"
    : vol > 1 ? `📣 громкость ${Math.round(vol * 100)}% (усилено)` 
    : `🔊 громкость ${Math.round(vol * 100)}%`;
}, { passive: false });

window.addEventListener("keydown", (e) => {
  if (overlay.classList.contains("hidden")) keys.add(e.code);
  // E — большой взрыв конфетти вокруг игрока
  if (e.code === "KeyE" && isPlaying()) {
    confettiExplosion();
  }
  // Space — прыжок: не прокручиваем страницу
  if (e.code === "Space" && isPlaying()) e.preventDefault();
  // M — большая карта (работает и в игре, и на паузе)
  if (e.code === "KeyM" && started) {
    e.preventDefault();
    toggleBigmap();
    return;
  }
  // M/клик закрывает карту
  if (bigmapOpen && (e.code === "Escape" || e.code === "Space")) toggleBigmap(false);
  // Escape — пауза (работает и без pointer lock)
  if (e.code === "Escape" && started && !bigmapOpen && overlay.classList.contains("hidden")) {
    ovTitle.textContent = "Пауза";
    ovSub.textContent = "Звук выключен. Нажмите «Продолжить», чтобы вернуться на праздник.";
    startBtn.textContent = "Продолжить";
    btnMain.classList.remove("hidden");
    overlay.classList.remove("hidden");
    suspendSound();
    return;
  }
  if (e.code === "KeyF" && isPlaying()) {
    if (document.fullscreenElement) document.exitFullscreen().catch(() => {});
    else document.documentElement.requestFullscreen().catch(() => {});
  }
});
bigmap.addEventListener("click", () => toggleBigmap(false));
window.addEventListener("keyup", (e) => keys.delete(e.code));

/* ============================== СЕНСОРНОЕ УПРАВЛЕНИЕ (ТЕЛЕФОН) ============================== */
// Левая нижняя зона — плавающий виртуальный джойстик (аналоговые оси).
// Правая часть экрана — свайп: обзор мышью. Тап (без движения) = клик по картине.
// Кнопки: 🎉 конфетти (как E), 🗺 карта (как M), ⏸ пауза (как Esc).

let touchF = 0; // вперёд/назад  [-1..1]
let touchR = 0; // вправо/влево  [-1..1]
const isTouch = matchMedia("(pointer: coarse)").matches || "ontouchstart" in window;

let touchUI = null;
if (isTouch) {
  touchUI = document.createElement("div");
  touchUI.id = "touch-ui";
  touchUI.innerHTML = `
    <div id="joy-zone"></div>
    <div id="joy-base" class="tx-hidden">
      <div id="joy-stick"></div>
    </div>
    <div class="tx-btns">
      <button id="btn-confetti" class="tx-btn" aria-label="Конфетти">🎉</button>
      <button id="btn-map" class="tx-btn" aria-label="Карта">🗺️</button>
      <button id="btn-vol" class="tx-btn" aria-label="Громкость">🔊</button>
      <button id="btn-jump" class="tx-btn" aria-label="Прыжок">⤒</button>
      <button id="btn-crouch" class="tx-btn" aria-label="Присед">⤓</button>
      <button id="btn-pause" class="tx-btn" aria-label="Пауза">⏸️</button>
    </div>
    <div id="vol-panel" class="tx-hidden">
      <span id="vol-val">🔊 100%</span>
      <input id="vol-range" type="range" min="0" max="150" step="5" value="100" />
    </div>`;
  document.body.appendChild(touchUI);
}

/* --- виртуальный джойстик --- */
const JOY_RADIUS = 56; // px, до края ход стика
const joyZone = document.getElementById("joy-zone");
const joyBase = document.getElementById("joy-base");
const joyStick = document.getElementById("joy-stick");
let joyId = null, joyCx = 0, joyCy = 0;

function joyCenter(e) {
  const t = e.changedTouches[0];
  joyCx = t.clientX; joyCy = t.clientY;
}
function joyUpdate(e) {
  for (const t of e.changedTouches) {
    if (t.identifier !== joyId) continue;
    let dx = t.clientX - joyCx, dy = t.clientY - joyCy;
    const len = Math.hypot(dx, dy);
    if (len > JOY_RADIUS) { dx *= JOY_RADIUS / len; dy *= JOY_RADIUS / len; }
    touchR = dx / JOY_RADIUS;
    touchF = -dy / JOY_RADIUS;
    joyStick.style.transform = `translate(${dx}px, ${dy}px)`;
  }
}
function joyEnd(e) {
  for (const t of e.changedTouches) {
    if (t.identifier !== joyId) continue;
    joyId = null;
    touchF = 0; touchR = 0;
    joyStick.style.transform = "translate(0, 0)";
    joyBase.classList.add("tx-hidden");
  }
}
if (touchUI) {
  joyZone.addEventListener("touchstart", (e) => {
    e.preventDefault();
    if (joyId !== null) return; // один стик за раз
    joyId = e.changedTouches[0].identifier;
    joyCenter(e);
    // база появляется под пальцем (плавающий стик)
    joyBase.style.left = (joyCx - 70) + "px";
    joyBase.style.top = (joyCy - 70) + "px";
    joyBase.classList.remove("tx-hidden");
    joyUpdate(e);
  }, { passive: false });
  joyZone.addEventListener("touchmove", (e) => { e.preventDefault(); joyUpdate(e); }, { passive: false });
  joyZone.addEventListener("touchend", joyEnd);
  joyZone.addEventListener("touchcancel", joyEnd);
}

/* --- обзор свайпом по правой части экрана + тап = клик --- */
const lookTouch = { id: null, x: 0, y: 0, moved: 0, t0: 0 };
const LOOK_SENSE = 0.0045;

canvas.addEventListener("touchstart", (e) => {
  if (!isPlaying()) return;
  for (const t of e.changedTouches) {
    // левую нижнюю зону занимает джойстик, обзор — всё остальное
    if (t.clientX >= innerWidth * 0.3 && lookTouch.id === null) {
      lookTouch.id = t.identifier;
      lookTouch.x = t.clientX; lookTouch.y = t.clientY;
      lookTouch.moved = 0; lookTouch.t0 = performance.now();
    }
  }
}, { passive: true });

canvas.addEventListener("touchmove", (e) => {
  if (!isPlaying() || lookTouch.id === null) return;
  for (const t of e.changedTouches) {
    if (t.identifier !== lookTouch.id) continue;
    const dx = t.clientX - lookTouch.x, dy = t.clientY - lookTouch.y;
    lookTouch.x = t.clientX; lookTouch.y = t.clientY;
    lookTouch.moved += Math.abs(dx) + Math.abs(dy);
    yaw -= dx * LOOK_SENSE;
    pitch -= dy * LOOK_SENSE;
    pitch = Math.max(-1.5, Math.min(1.5, pitch));
  }
}, { passive: true });

canvas.addEventListener("touchend", (e) => {
  for (const t of e.changedTouches) {
    if (t.identifier !== lookTouch.id) continue;
    lookTouch.id = null;
    // короткий тап без движения = клик по картине (точка тапа, не центр экрана)
    if (isPlaying() && lookTouch.moved < 12 && performance.now() - lookTouch.t0 < 400) {
      interactAt(new THREE.Vector2(
        (t.clientX / innerWidth) * 2 - 1,
        -(t.clientY / innerHeight) * 2 + 1));
    }
  }
});

/* --- экранные кнопки --- */
if (touchUI) {
  const pauseLikeEsc = () => {
    if (!started || bigmapOpen) return;
    ovTitle.textContent = "Пауза";
    ovSub.textContent = "Звук выключен. Нажмите «Продолжить», чтобы вернуться на праздник.";
    startBtn.textContent = "Продолжить";
    btnMain.classList.remove("hidden");
    overlay.classList.remove("hidden");
    suspendSound();
  };
  document.getElementById("btn-confetti").addEventListener("touchstart", (e) => { e.preventDefault(); if (isPlaying()) confettiExplosion(); });
  document.getElementById("btn-map").addEventListener("touchstart", (e) => { e.preventDefault(); if (started) toggleBigmap(); });
  document.getElementById("btn-pause").addEventListener("touchstart", (e) => { e.preventDefault(); pauseLikeEsc(); });
  // прыжок: одиночный тап = импульс
  document.getElementById("btn-jump").addEventListener("touchstart", (e) => { e.preventDefault(); touchJump = true; });
  // присед: тумблер (нажал — присел, нажал ещё раз — встал)
  document.getElementById("btn-crouch").addEventListener("touchstart", (e) => { e.preventDefault(); touchCrouch = !touchCrouch; });

  /* --- панель громкости (0-150%) --- */
  const volPanel = document.getElementById("vol-panel");
  const volRange = document.getElementById("vol-range");
  const volVal = document.getElementById("vol-val");

  const volLabel = (vol) => vol === 0 ? "🔇 0%"
    : vol > 1 ? `📣 ${Math.round(vol * 100)}% (усилено)`
    : `🔊 ${Math.round(vol * 100)}%`;

  const applyVolume = (vol) => {
    listener.setMasterVolume(vol);
    try {
      if (vol > 1) listener.setFilter(listener._boostComp);
      else listener.removeFilter();
    } catch (e) { /* старая версия three — усиление работает и так */ }
    volVal.textContent = volLabel(vol);
  };

  document.getElementById("btn-vol").addEventListener("touchstart", (e) => {
    e.preventDefault();
    const vol = Math.min(1.5, Math.max(0, listener.getMasterVolume()));
    volRange.value = String(Math.round(vol * 100));
    volVal.textContent = volLabel(vol);
    volPanel.classList.toggle("tx-hidden");
  });
  volRange.addEventListener("input", () => applyVolume(+volRange.value / 100));
  volRange.addEventListener("touchstart", (e) => e.stopPropagation()); // не трактовать как обзор-свайп
}

window.addEventListener("resize", () => {
  camera.aspect = innerWidth / innerHeight;
  camera.updateProjectionMatrix();
  renderer.setSize(innerWidth, innerHeight);
});
window.addEventListener("contextmenu", (e) => e.preventDefault());

startBtn.addEventListener("click", enter);
btnMain.addEventListener("click", () => { window.location.href = "https://kuromursk.dpdns.org/"; });
// игра стартует ТОЛЬКО по кнопке «Войти» или Enter в поле имени.
// Клики по оверлею (включая подпись/панель) никогда не запускают вход.
usernameInput.addEventListener("keydown", (e) => e.stopPropagation());

/* ============================== ДВИЖЕНИЕ ============================== */

function collide(pos) {
  const r = 0.3;
  for (const b of colliders) {
    if (pos.x > b.minX - r && pos.x < b.maxX + r && pos.z > b.minZ - r && pos.z < b.maxZ + r) {
      const dxL = pos.x - (b.minX - r), dxR = (b.maxX + r) - pos.x;
      const dzT = pos.z - (b.minZ - r), dzB = (b.maxZ + r) - pos.z;
      const m = Math.min(dxL, dxR, dzT, dzB);
      if (m === dxL) pos.x = b.minX - r;
      else if (m === dxR) pos.x = b.maxX + r;
      else if (m === dzT) pos.z = b.minZ - r;
      else pos.z = b.maxZ + r;
    }
  }
}

// играем когда «Войти» нажат и оверлей скрыт — независимо от pointer lock.
// Обзор мышью работает и без захвата курсора (fallback), Escape — пауза.
function isPlaying() {
  return started && overlay.classList.contains("hidden");
}

/* --- состояние прыжка/приседа --- */
let jumpOffset = 0;   // текущее превышение над уровнем глаз (м)
let jumpVy = 0;       // вертикальная скорость (м/с)
let crouching = false;
let eyeLevel = CFG.eyeHeight;
let touchJump = false;   // импульс от тач-кнопки
let touchCrouch = false; // зажат (тумблер) тач-кнопкой приседа

function updateMovement(dt) {
  if (!isPlaying()) {
    velocity.multiplyScalar(Math.exp(-8 * dt));
    return;
  }
  const kf = (keys.has("KeyW") || keys.has("ArrowUp") ? 1 : 0) - (keys.has("KeyS") || keys.has("ArrowDown") ? 1 : 0);
  const kr = (keys.has("KeyD") || keys.has("ArrowRight") ? 1 : 0) - (keys.has("KeyA") || keys.has("ArrowLeft") ? 1 : 0);
  // оси с виртуального джойстика (аналоговые: наклон = доля скорости)
  const f = Math.max(-1, Math.min(1, kf + touchF));
  const r = Math.max(-1, Math.min(1, kr + touchR));

  const target = new THREE.Vector3(r, 0, -f);
  // длина < 1 — идём медленнее (полунаклон джойстика), > 1 — клампим до макс. скорости
  const tLen = target.length();
  if (tLen > 1) target.divideScalar(tLen);
  target.applyAxisAngle(UP, yaw);
  let speed = keys.has("ShiftLeft") || keys.has("ShiftRight") ? CFG.runSpeed : CFG.walkSpeed;
  if (crouching) speed *= CFG.crouchSpeed; // в приседе тише и медленнее (стелс по Куромур)
  target.multiplyScalar(speed);

  velocity.lerp(target, 1 - Math.exp(-CFG.smooth * dt));
  camera.position.addScaledVector(velocity, dt);

  /* --- прыжок и присед --- */
  // прыжок: одиночный импульс, в воздухе ходьба по инерции не мешает
  const onGround = jumpOffset <= 0.001 && Math.abs(jumpVy) < 0.01;
  const wantJump = (keys.has("Space") || touchJump);
  touchJump = false;
  if (wantJump && onGround && !crouching) jumpVy = CFG.jumpSpeed;
  if (jumpOffset > 0 || jumpVy !== 0) {
    jumpOffset += jumpVy * dt;
    jumpVy -= CFG.gravity * dt;
    if (jumpOffset <= 0) { jumpOffset = 0; jumpVy = 0; }
  }
  // присед: удержание C / тач-кнопка; стоя в воздухе приседать нельзя
  crouching = keys.has("KeyC") || touchCrouch;
  if (jumpOffset > 0) { crouching = false; /* прыжок важнее */ }

  // плавная смена высоты глаз: базовая (стоя/присед) + прыжок
  const targetEye = crouching ? CFG.crouchEye : CFG.eyeHeight;
  eyeLevel += (targetEye - eyeLevel) * (1 - Math.exp(-10 * dt));
  camera.position.y = eyeLevel + jumpOffset;
  collide(camera.position);

  camera.rotation.y = yaw;
  camera.rotation.x = pitch;
}

/* ============================== ЦИКЛ ============================== */

const clock = new THREE.Clock();
let confettiTimer = 3;

renderer.setAnimationLoop(() => {
  const dt = Math.min(0.05, clock.getDelta());
  const t = clock.elapsedTime;

  updateMovement(dt);
  mpTick(t, dt); // мультиплеер: отправка позиции + интерполяция призраков

  // шары покачиваются
  for (const b of balloons) {
    b.g.position.x = b.baseX + Math.sin(t * b.speed + b.phase) * 0.12;
    b.g.position.y = b.baseY + Math.sin(t * b.speed * 1.4 + b.phase) * 0.06;
    b.g.rotation.z = Math.sin(t * b.speed + b.phase) * 0.08;
  }

  // огоньки свечей слегка дрожат
  for (const f of candles) {
    f.intensity = 4 + Math.sin(t * 9 + f.position.x) * 0.7 + Math.random() * 0.3;
  }

  // язычки пламени пляшут
  for (const m of flameMeshes) {
    const s = 1 + Math.sin(t * 11 + m.userData.ph) * 0.22 + (Math.random() - 0.5) * 0.12;
    m.scale.set(1, s, 1);
  }

  // кнопки телепорта мягко пульсируют, привлекая взгляд
  for (const b of teleportButtons) {
    b.scale.setScalar(1 + Math.sin(t * 3 + b.position.x * 2 + b.position.z) * 0.07);
  }

  // коты гуляют по своим маршрутам
  for (const c of cats) {
    const s = t * c.speed * 6.28 + c.phase;
    const nx = c.cx + Math.cos(s) * c.rx;
    const nz = c.cz + Math.sin(s) * c.rz;
    // направление движения
    const dx = nx - c.g.position.x, dz = nz - c.g.position.z;
    if (dx * dx + dz * dz > 1e-6) {
      c.g.rotation.y = Math.atan2(dx, dz);
    }
    c.g.position.set(nx, 0, nz);
    // пружинистая походка + виляние хвостом
    c.g.position.y = Math.abs(Math.sin(t * 5 + c.bobPhase)) * 0.05;
    c.tail.rotation.z = Math.sin(t * 4 + c.bobPhase) * 0.5;
  }

  // конфетти: физика частиц
  for (let i = confettiBursts.length - 1; i >= 0; i--) {
    const b = confettiBursts[i];
    b.life += dt;
    const pos = b.pts.geometry.attributes.position;
    for (let j = 0; j < b.vel.length; j++) {
      const v = b.vel[j];
      v.vy -= 2.6 * dt;             // гравитация
      v.vx *= 1 - 0.9 * dt;         // сопротивление воздуха
      v.vz *= 1 - 0.9 * dt;
      pos.array[j * 3] += v.vx * dt;
      pos.array[j * 3 + 1] += v.vy * dt;
      pos.array[j * 3 + 2] += v.vz * dt;
      if (pos.array[j * 3 + 1] < 0.03) { // упало на пол — лежит
        pos.array[j * 3 + 1] = 0.03;
        v.vy = 0; v.vx *= 0.8; v.vz *= 0.8;
      }
    }
    pos.needsUpdate = true;
    b.pts.material.opacity = Math.max(0, 1 - b.life / b.maxLife);
    if (b.life >= b.maxLife) {
      scene.remove(b.pts);
      b.pts.geometry.dispose();
      b.pts.material.dispose();
      confettiBursts.splice(i, 1);
    }
  }

  // периодические залпы конфетти (атмосфера праздника)
  confettiTimer -= dt;
  if (confettiTimer <= 0 && started) {
    confettiTimer = 5 + Math.random() * 4;
    if (confettiBursts.length < 4) {
      const p = camera.position;
      fireConfetti(p.x + (Math.random() - 0.5) * 6, p.z + (Math.random() - 0.5) * 6, 70);
    }
  }


  renderer.render(scene, camera);
});

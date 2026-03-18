const canvas = document.getElementById("game");
const ctx = canvas.getContext("2d");
const overlayEl = document.getElementById("overlay");
const scoreEl = document.getElementById("score");
const livesEl = document.getElementById("lives");

const TILE = 22;
const WIDTH = 23;
const HEIGHT = 23;
const GHOSTS_COUNT = 3;

// Speeds are in "tiles per second".
const PLAYER_TPS = 6;
const GHOST_TPS = 5;

const PLAYER_LIVES = 3;

canvas.width = WIDTH * TILE;
canvas.height = HEIGHT * TILE;

const DIRS = {
  up: { x: 0, y: -1 },
  down: { x: 0, y: 1 },
  left: { x: -1, y: 0 },
  right: { x: 1, y: 0 },
  none: { x: 0, y: 0 },
};

function mulberry32(seed) {
  return function () {
    let t = (seed += 0x6d2b79f5);
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function manhattan(a, b) {
  return Math.abs(a.x - b.x) + Math.abs(a.y - b.y);
}

function dirKey(d) {
  if (d.x === 0 && d.y === -1) return "up";
  if (d.x === 0 && d.y === 1) return "down";
  if (d.x === -1 && d.y === 0) return "left";
  if (d.x === 1 && d.y === 0) return "right";
  return "none";
}

function opposite(d) {
  return { x: -d.x, y: -d.y };
}

function isSameDir(a, b) {
  return a.x === b.x && a.y === b.y;
}

function neighbors4(x, y) {
  return [
    { x: x, y: y - 1, dir: DIRS.up },
    { x: x, y: y + 1, dir: DIRS.down },
    { x: x - 1, y: y, dir: DIRS.left },
    { x: x + 1, y: y, dir: DIRS.right },
  ];
}

function buildMaze(seed = 1) {
  // Tile grid layout is 2*cell + 1 so corridors and walls alternate.
  const cellW = (WIDTH - 1) / 2;
  const cellH = (HEIGHT - 1) / 2;

  const grid = Array.from({ length: HEIGHT }, () => Array.from({ length: WIDTH }, () => "#"));
  const visited = Array.from({ length: cellH }, () => Array.from({ length: cellW }, () => false));

  const rand = mulberry32(seed);

  function toTile(cx, cy) {
    return { x: cx * 2 + 1, y: cy * 2 + 1 };
  }

  // Carve starting cell.
  const start = { cx: 0, cy: 0 };
  let stack = [start];
  visited[start.cy][start.cx] = true;
  {
    const t = toTile(start.cx, start.cy);
    grid[t.y][t.x] = " ";
  }

  while (stack.length) {
    const cur = stack[stack.length - 1];
    const { x: tx, y: ty } = toTile(cur.cx, cur.cy);

    const options = neighbors4(cur.cx, cur.cy)
      .filter((n) => n.x >= 0 && n.x < cellW && n.y >= 0 && n.y < cellH)
      .filter((n) => !visited[n.y][n.x]);

    if (!options.length) {
      stack.pop();
      continue;
    }

    const pick = options[Math.floor(rand() * options.length)];
    // Carve wall between current cell and chosen neighbor.
    const midTile = { x: tx + pick.dir.x, y: ty + pick.dir.y };
    const nextTile = toTile(pick.x, pick.y);
    grid[midTile.y][midTile.x] = " ";
    grid[nextTile.y][nextTile.x] = " ";
    visited[pick.y][pick.x] = true;
    stack.push({ cx: pick.x, cy: pick.y });
  }

  // Convert corridor spaces into pellets.
  for (let y = 0; y < HEIGHT; y++) {
    for (let x = 0; x < WIDTH; x++) {
      if (grid[y][x] === " ") grid[y][x] = ".";
    }
  }

  return grid;
}

function nearestPassable(grid, target) {
  let best = null;
  let bestD = Infinity;
  for (let y = 0; y < HEIGHT; y++) {
    for (let x = 0; x < WIDTH; x++) {
      if (grid[y][x] === "#") continue;
      const d = manhattan({ x, y }, target);
      if (d < bestD) {
        bestD = d;
        best = { x, y };
      }
    }
  }
  return best;
}

function pickFarthestPassable(grid, from, avoidList) {
  let best = null;
  let bestD = -Infinity;
  for (let y = 0; y < HEIGHT; y++) {
    for (let x = 0; x < WIDTH; x++) {
      if (grid[y][x] === "#") continue;
      // Avoid choosing tiles too close to other ghosts.
      let tooClose = false;
      for (const a of avoidList) {
        if (manhattan({ x, y }, a) <= 1) {
          tooClose = true;
          break;
        }
      }
      if (tooClose) continue;

      const d = manhattan({ x, y }, from);
      if (d > bestD) {
        bestD = d;
        best = { x, y };
      } else if (d === bestD && best) {
        // Deterministic tie-break: prefer smaller y, then smaller x.
        if (y < best.y || (y === best.y && x < best.x)) {
          best = { x, y };
        }
      }
    }
  }
  return best;
}

let grid;
let pelletCount = 0;

let player;
let ghosts = [];

let playerSpawn;
let ghostSpawns = [];

let gameState = "ready"; // ready | playing | won | lost
let overlayMessage = "";

let inputDir = DIRS.none;
let nextDir = DIRS.none;

let invulnerableUntil = 0;
let time = 0;

let accPlayer = 0;
let accGhosts = 0;

function canMove(x, y) {
  if (x < 0 || y < 0 || x >= WIDTH || y >= HEIGHT) return false;
  return grid[y][x] !== "#";
}

function tileCenter(tx) {
  return tx * TILE + TILE / 2;
}

function resetRound() {
  const seed = 1; // deterministic layout
  grid = buildMaze(seed);

  pelletCount = 0;
  for (let y = 0; y < HEIGHT; y++) {
    for (let x = 0; x < WIDTH; x++) {
      if (grid[y][x] === ".") pelletCount++;
    }
  }

  playerSpawn = nearestPassable(grid, { x: Math.floor(WIDTH / 2), y: Math.floor(HEIGHT / 2) });
  player = {
    x: playerSpawn.x,
    y: playerSpawn.y,
    dir: DIRS.none,
    nextDir: DIRS.none,
  };
  grid[player.y][player.x] = " "; // no pellet on spawn
  // Recompute pellet count after removing spawn pellet.
  pelletCount = 0;
  for (let y = 0; y < HEIGHT; y++) {
    for (let x = 0; x < WIDTH; x++) {
      if (grid[y][x] === ".") pelletCount++;
    }
  }

  // Spawn ghosts far from player.
  ghostSpawns = [];
  const avoidList = [];
  for (let i = 0; i < GHOSTS_COUNT; i++) {
    const spawn = pickFarthestPassable(grid, playerSpawn, avoidList);
    ghostSpawns.push(spawn);
    avoidList.push(spawn);
  }

  const ghostColors = ["#ff4b6e", "#2ef2b4", "#55a7ff", "#ffcc00", "#b08cff"];
  ghosts = ghostSpawns.map((s, i) => ({
    x: s.x,
    y: s.y,
    dir: DIRS.none,
    color: ghostColors[i % ghostColors.length],
  }));

  // Clear pellets in ghost spawn neighborhood.
  for (const g of ghostSpawns) {
    for (let dy = -1; dy <= 1; dy++) {
      for (let dx = -1; dx <= 1; dx++) {
        const x = g.x + dx;
        const y = g.y + dy;
        if (x < 0 || y < 0 || x >= WIDTH || y >= HEIGHT) continue;
        if (grid[y][x] !== "#") grid[y][x] = " ";
      }
    }
  }

  pelletCount = 0;
  for (let y = 0; y < HEIGHT; y++) {
    for (let x = 0; x < WIDTH; x++) {
      if (grid[y][x] === ".") pelletCount++;
    }
  }

  invulnerableUntil = performance.now() + 1200;

  accPlayer = 0;
  accGhosts = 0;
  inputDir = DIRS.none;
  nextDir = DIRS.none;
  overlayMessage = "Press an arrow key to start";
  updateOverlay();
  gameState = "ready";
}

function updateOverlay() {
  overlayEl.textContent = overlayMessage;
}

function startPlayingIfNeeded() {
  if (gameState === "ready") {
    gameState = "playing";
    overlayMessage = "";
    updateOverlay();
  }
}

function loseLife() {
  if (gameState !== "playing") return;
  const now = performance.now();
  if (now < invulnerableUntil) return;

  // Reset positions but keep remaining lives.
  lives--;
  livesEl.textContent = String(lives);

  if (lives <= 0) {
    gameState = "lost";
    overlayMessage = "Game Over. Press R to restart";
    updateOverlay();
    return;
  }

  player.x = playerSpawn.x;
  player.y = playerSpawn.y;
  player.dir = DIRS.none;
  player.nextDir = DIRS.none;
  inputDir = DIRS.none;
  nextDir = DIRS.none;

  for (let i = 0; i < ghosts.length; i++) {
    ghosts[i].x = ghostSpawns[i].x;
    ghosts[i].y = ghostSpawns[i].y;
    ghosts[i].dir = DIRS.none;
  }

  invulnerableUntil = performance.now() + 1600;
}

function chooseGhostDirection(g) {
  // Decide a direction at every tile step.
  const options = [];
  for (const d of [DIRS.up, DIRS.down, DIRS.left, DIRS.right]) {
    const nx = g.x + d.x;
    const ny = g.y + d.y;
    if (canMove(nx, ny)) options.push(d);
  }
  if (!options.length) return DIRS.none;

  // Prefer not reversing unless forced.
  if (!isSameDir(g.dir, DIRS.none)) {
    const rev = opposite(g.dir);
    if (options.length > 1) {
      const filtered = options.filter((d) => !(d.x === rev.x && d.y === rev.y));
      if (filtered.length) options.splice(0, options.length, ...filtered);
    }
  }

  // Chase sometimes with a bit of randomness.
  const chase = Math.random() < 0.8;
  if (!chase) {
    return options[Math.floor(Math.random() * options.length)];
  }

  let best = options[0];
  let bestD = Infinity;
  for (const d of options) {
    const nx = g.x + d.x;
    const ny = g.y + d.y;
    const dScore = manhattan({ x: nx, y: ny }, { x: player.x, y: player.y });
    if (dScore < bestD) {
      bestD = dScore;
      best = d;
    }
  }
  return best;
}

function stepPlayer() {
  // If the player has a requested direction and it is legal, commit it.
  if (!isSameDir(nextDir, DIRS.none)) {
    const nx = player.x + nextDir.x;
    const ny = player.y + nextDir.y;
    if (canMove(nx, ny)) player.dir = nextDir;
  }

  if (isSameDir(player.dir, DIRS.none)) return;

  const tx = player.x + player.dir.x;
  const ty = player.y + player.dir.y;
  if (!canMove(tx, ty)) return;

  player.x = tx;
  player.y = ty;

  if (grid[player.y][player.x] === ".") {
    grid[player.y][player.x] = " ";
    pelletCount--;
    score++;
    scoreEl.textContent = String(score);

    if (pelletCount <= 0) {
      gameState = "won";
      overlayMessage = "You win! Press R to restart";
      updateOverlay();
    }
  }
}

function stepGhosts() {
  for (const g of ghosts) {
    const nd = chooseGhostDirection(g);
    g.dir = nd;
    if (isSameDir(nd, DIRS.none)) continue;

    const tx = g.x + nd.x;
    const ty = g.y + nd.y;
    if (!canMove(tx, ty)) continue;
    g.x = tx;
    g.y = ty;
  }
}

function checkCollisions() {
  if (gameState !== "playing") return;
  const now = performance.now();
  if (now < invulnerableUntil) return;

  for (const g of ghosts) {
    if (g.x === player.x && g.y === player.y) {
      loseLife();
      break;
    }
  }
}

function drawWalls() {
  ctx.fillStyle = "#f4f7ff";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  for (let y = 0; y < HEIGHT; y++) {
    for (let x = 0; x < WIDTH; x++) {
      if (grid[y][x] !== "#") continue;
      ctx.fillStyle = "#3b82f6";
      const px = x * TILE;
      const py = y * TILE;
      // Slight inset for nicer look.
      ctx.fillRect(px + 1, py + 1, TILE - 2, TILE - 2);
    }
  }
}

function drawPellets() {
  for (let y = 0; y < HEIGHT; y++) {
    for (let x = 0; x < WIDTH; x++) {
      if (grid[y][x] !== ".") continue;
      const cx = tileCenter(x);
      const cy = tileCenter(y);
      ctx.fillStyle = "#ffcc2e";
      ctx.beginPath();
      ctx.arc(cx, cy, Math.max(2, TILE * 0.1), 0, Math.PI * 2);
      ctx.fill();
    }
  }
}

function drawPlayer() {
  const cx = tileCenter(player.x);
  const cy = tileCenter(player.y);

  const r = TILE * 0.42;
  const mouth = 0.35;
  let start = 0;
  let end = Math.PI * 2;

  const d = player.dir;
  if (isSameDir(d, DIRS.left)) {
    start = mouth;
    end = Math.PI * 2 - mouth;
  } else if (isSameDir(d, DIRS.right)) {
    start = Math.PI + mouth;
    end = Math.PI - mouth + Math.PI;
  } else if (isSameDir(d, DIRS.up)) {
    start = Math.PI * 1.5 + mouth;
    end = Math.PI * 1.5 - mouth + Math.PI * 2;
  } else if (isSameDir(d, DIRS.down)) {
    start = Math.PI * 0.5 + mouth;
    end = Math.PI * 0.5 - mouth + Math.PI * 2;
  } else {
    // If not moving, draw full circle.
    start = 0;
    end = Math.PI * 2;
  }

  ctx.fillStyle = "#ffd400";
  ctx.beginPath();
  ctx.moveTo(cx, cy);
  ctx.arc(cx, cy, r, start, end, false);
  ctx.closePath();
  ctx.fill();
}

function drawGhost(g) {
  const cx = tileCenter(g.x);
  const cy = tileCenter(g.y);
  const r = TILE * 0.4;

  // Body.
  ctx.fillStyle = g.color;
  ctx.beginPath();
  // Wavy top to look like a ghost.
  const wave = 6;
  const step = (Math.PI * 2) / wave;
  for (let i = 0; i < wave; i++) {
    // Bottom curve.
    const ang = i * step;
    const x = cx + Math.cos(ang) * r;
    const y = cy + Math.sin(ang) * (r * 0.9);
    if (i === 0) ctx.moveTo(x, y);
    else ctx.lineTo(x, y);
  }
  ctx.closePath();
  ctx.fill();

  // Eyes.
  const eyeOffset = TILE * 0.12;
  const eyeR = TILE * 0.14;
  const dir = g.dir;
  const ex = dir.x === 0 ? 0 : dir.x * eyeOffset;
  const ey = dir.y === 0 ? 0 : dir.y * eyeOffset;

  // Two eyes.
  ctx.fillStyle = "#001018";
  ctx.beginPath();
  ctx.arc(cx - eyeR, cy - eyeR * 0.1 + ey, eyeR, 0, Math.PI * 2);
  ctx.arc(cx + eyeR, cy - eyeR * 0.1 + ey, eyeR, 0, Math.PI * 2);
  ctx.fill();

  // White shine.
  ctx.fillStyle = "rgba(255,255,255,0.9)";
  ctx.beginPath();
  ctx.arc(cx - eyeR * 0.4 + ex, cy - eyeR * 0.25 + ey, eyeR * 0.35, 0, Math.PI * 2);
  ctx.arc(cx + eyeR * 0.4 + ex, cy - eyeR * 0.25 + ey, eyeR * 0.35, 0, Math.PI * 2);
  ctx.fill();
}

function render() {
  drawWalls();
  drawPellets();

  // Ghosts behind player for readability.
  for (const g of ghosts) drawGhost(g);
  drawPlayer();
}

let score = 0;
let lives = PLAYER_LIVES;

function resetHUD() {
  score = 0;
  lives = PLAYER_LIVES;
  scoreEl.textContent = "0";
  livesEl.textContent = String(lives);
}

function resetGame() {
  resetHUD();
  resetRound();
}

let lastTs = performance.now();
function tick(ts) {
  const dt = Math.min(0.05, (ts - lastTs) / 1000);
  lastTs = ts;
  time += dt;

  if (gameState === "playing") {
    accPlayer += dt;
    accGhosts += dt;

    const playerInterval = 1 / PLAYER_TPS;
    const ghostInterval = 1 / GHOST_TPS;

    while (accPlayer >= playerInterval) {
      accPlayer -= playerInterval;
      stepPlayer();
      checkCollisions();
      if (gameState !== "playing") break;
    }

    while (accGhosts >= ghostInterval) {
      accGhosts -= ghostInterval;
      stepGhosts();
      checkCollisions();
      if (gameState !== "playing") break;
    }
  }

  render();

  requestAnimationFrame(tick);
}

function setOverlayForStart() {
  overlayMessage = "Press an arrow key to start";
  updateOverlay();
}

window.addEventListener("keydown", (e) => {
  const key = e.key;
  if (["ArrowUp", "ArrowDown", "ArrowLeft", "ArrowRight", "r", "R"].includes(key)) {
    e.preventDefault();
  }

  if (key === "r" || key === "R") {
    resetGame();
    return;
  }

  if (key === "ArrowUp") nextDir = DIRS.up;
  else if (key === "ArrowDown") nextDir = DIRS.down;
  else if (key === "ArrowLeft") nextDir = DIRS.left;
  else if (key === "ArrowRight") nextDir = DIRS.right;
  else return;

  startPlayingIfNeeded();
});

// Init
resetHUD();
resetRound();
setOverlayForStart();
requestAnimationFrame(tick);


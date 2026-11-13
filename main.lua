-- Rain Walk
-- A moody black-and-white pixel-art stroll: a hooded figure with an
-- umbrella walks a rainy night street lit by dithered lamplight, and
-- splashes through puddles.
--
-- CONTROLS: Arrow keys / WASD walk, Space jumps (land in a puddle for a
-- big splash), M toggles sound, Esc quits.
--
-- Everything is drawn at a tiny internal resolution (192x108) and scaled
-- up 5x with nearest-neighbour filtering, so it all stays crisp pixels.

------------------------------------------------------------
-- 1. CONSTANTS
------------------------------------------------------------
local VW, VH = 192, 108          -- internal resolution
local SCALE = 5                  -- window = 960x540
local WORLD_W = 640              -- the street is ~3.3 screens wide
local WALL_END = 62              -- where the brick wall meets the sidewalk
local CURB_Y = 78                -- sidewalk / road boundary
local LY = 19                    -- height of the lamp light source
local GROUND_MIN_Y, GROUND_MAX_Y = 66, 106   -- where the player may walk
local LIGHT_R = 64               -- half-width of each lamp's light image

local floor, sqrt, abs, sin, cos, pi, max, min =
  math.floor, math.sqrt, math.abs, math.sin, math.cos, math.pi, math.max, math.min

local function clamp(v, a, b)
  if v < a then return a elseif v > b then return b end
  return v
end
local function clip01(v) return clamp(v, 0, 1) end

-- tiny deterministic pseudo-random value from two numbers (no flicker)
local function rand2(a, b)
  local n = sin(a * 127.1 + b * 311.7) * 43758.5453
  return n - floor(n)
end

-- 4x4 ordered-dither threshold: gives the 1-bit "screen door" lamplight
local BAYER = { {0, 8, 2, 10}, {12, 4, 14, 6}, {3, 11, 1, 9}, {15, 7, 13, 5} }
local function thr(x, y)
  return (BAYER[(y % 4) + 1][(x % 4) + 1] + 0.5) / 16
end

------------------------------------------------------------
-- 2. WORLD DATA -- edit these to redesign the street
------------------------------------------------------------
-- x positions of the lamp poles (the lantern hangs 13px to the right)
local LAMP_POLES = { 70, 215, 360, 505 }

-- puddles: centre x/y and radii, in world pixels (road is y 80..108)
local PUDDLES = {
  { cx = 60,  cy = 92, rx = 16, ry = 4 },
  { cx = 120, cy = 97, rx = 11, ry = 3 },
  { cx = 175, cy = 86, rx = 13, ry = 3 },
  { cx = 215, cy = 71, rx = 9,  ry = 2 },
  { cx = 240, cy = 95, rx = 20, ry = 5 },
  { cx = 300, cy = 88, rx = 10, ry = 3 },
  { cx = 355, cy = 99, rx = 15, ry = 4 },
  { cx = 410, cy = 90, rx = 12, ry = 3 },
  { cx = 470, cy = 96, rx = 18, ry = 5 },
  { cx = 530, cy = 87, rx = 11, ry = 3 },
  { cx = 585, cy = 98, rx = 14, ry = 4 },
}

-- windows on the brick wall (lit ones glow)
local WINDOWS = {
  { x = 26,  y = 14, w = 12, h = 18, lit = false },
  { x = 150, y = 14, w = 12, h = 18, lit = true  },
  { x = 292, y = 14, w = 12, h = 18, lit = false },
  { x = 442, y = 14, w = 12, h = 18, lit = true  },
  { x = 580, y = 14, w = 12, h = 18, lit = false },
}

------------------------------------------------------------
-- 3. STATE
------------------------------------------------------------
local canvas, font
local bgImage, lampImage
local lamps = {}
local drops = {}
local ripples = {}
local particles = {}

local gt = 0               -- game time
local camX = 0
local splashes = 0
local hintTimer = 9
local muted = false

local player = {
  x = 30, y = 90,
  jz = 0, jvz = 0,       -- jump height + vertical speed
  facing = 1,
  moving = false,
  stepT = 0.15,
  foot = 0,
  dripT = 0,
}

------------------------------------------------------------
-- 4. LIGHTING MATH
------------------------------------------------------------
-- returns (halo, wall) light amounts from one lamp at world point (wx,wy)
local function lampTerms(lamp, wx, wy)
  local dx, dy = wx - lamp.lx, wy - LY
  local d = sqrt(dx * dx + dy * dy)
  if wy < WALL_END then
    local halo = (clip01(1 - d / 22) ^ 1.8) * 1.3
    local below = clip01((wy - LY + 4) / 12)
    local cone = 0.15 + 0.85 * below
    local wall = (clip01(1 - d / 56) ^ 1.7) * cone
    return halo, wall
  end
  return 0, clip01(1 - abs(dx) / 36) * 0.5
end

-- overall light at a world point (0..~1), used to brighten rain
local function lightAt(wx, wy)
  local best = 0
  for _, lamp in ipairs(lamps) do
    if abs(wx - lamp.lx) < 70 then
      local h, w = lampTerms(lamp, wx, wy)
      best = max(best, h, w)
    end
  end
  return best
end

-- how lit the ground is horizontally (0..1), for the figure and ripples
local function lightG(x)
  local g = 0
  for _, lamp in ipairs(lamps) do
    g = max(g, clip01(1 - abs(x - lamp.lx) / 36))
  end
  return g
end

-- tighter reflection of the lantern, for puddle surfaces
local function lampReflect(x)
  local g = 0
  for _, lamp in ipairs(lamps) do
    g = max(g, (clip01(1 - abs(x - lamp.lx) / 30) ^ 1.5) * lamp.flick)
  end
  return g
end

local function brickInfo(x, y)
  local row = floor(y / 4)
  local off = (row % 2) * 4
  local mortar = (y % 4 == 3) or (((x + off) % 8) == 7)
  local col = floor((x + off) / 8)
  local tone = 0.78 + 0.22 * rand2(row, col)
  return mortar, tone
end

------------------------------------------------------------
-- 5. PRE-RENDERED IMAGES (built once at load)
------------------------------------------------------------
local function fillRect(id, x, y, w, h, v)
  for yy = y, y + h - 1 do
    for xx = x, x + w - 1 do
      if xx >= 0 and xx < id:getWidth() and yy >= 0 and yy < id:getHeight() then
        id:setPixel(xx, yy, v, v, v, 1)
      end
    end
  end
end

local function buildBackground()
  local id = love.image.newImageData(WORLD_W, VH)
  for y = 0, VH - 1 do
    for x = 0, WORLD_W - 1 do
      local v = 0
      if y < WALL_END then
        local mortar, tone = brickInfo(x, y)
        if not mortar then v = 0.045 * tone end
      elseif y < CURB_Y then
        v = 0.02
        if x % 16 == 0 then v = 0.06 end
        if y == WALL_END then v = 0.10 end
      elseif y == CURB_Y then
        v = 0.22
      elseif y == CURB_Y + 1 then
        v = 0.07
      else
        if rand2(x * 1.7, y * 2.3) < 0.06 then v = 0.055 end
      end
      id:setPixel(x, y, v, v, v, 1)
    end
  end

  -- windows
  for _, w in ipairs(WINDOWS) do
    fillRect(id, w.x - 1, w.y - 1, w.w + 2, w.h + 2, 0.22)   -- frame
    for yy = w.y, w.y + w.h - 1 do
      for xx = w.x, w.x + w.w - 1 do
        local v = 0.015
        if w.lit then v = (((xx + yy) % 2) == 0) and 0.90 or 0.62 end
        id:setPixel(xx, yy, v, v, v, 1)
      end
    end
    local mx = w.x + floor(w.w / 2)
    local my = w.y + floor(w.h / 2)
    local barV = w.lit and 0.08 or 0.18
    fillRect(id, mx, w.y, 1, w.h, barV)                        -- mullions
    fillRect(id, w.x, my, w.w, 1, barV)
    fillRect(id, w.x - 2, w.y + w.h + 1, w.w + 4, 2, 0.30)    -- sill
  end
  local img = love.graphics.newImage(id)
  img:setFilter("nearest", "nearest")
  return img
end

-- the lamp post, arm and lantern shell (glass is drawn live, for flicker).
-- Local x = (world x - pole x) + 4, so pole x maps to column 4.
local function buildLampSprite()
  local id = love.image.newImageData(27, 74)
  local function S(dx, y, v)
    local lx = dx + 4
    if lx >= 0 and lx < 27 and y >= 0 and y < 74 then id:setPixel(lx, y, v, v, v, 1) end
  end
  -- pole: shade, body, lit edge (brighter near the lamp)
  for y = 18, 65 do
    S(-2, y, (y < 40) and 0.35 or 0.16)
    S(-1, y, 0.07)
    S(0, y, (55 + 150 * max(0, 1 - (y - 18) / 70)) / 255)
  end
  -- base and collar
  for y = 66, 72 do
    for dx = -3, 2 do S(dx, y, 0.14) end
    S(2, y, 0.35)
  end
  for dx = -3, 2 do S(dx, 66, 0.35) end
  for dx = -2, 1 do S(dx, 58, 0.20); S(dx, 59, 0.10) end
  -- gooseneck arm: a quarter circle from the pole top to above the lantern
  for k = 0, 199 do
    local ang = pi + (pi / 2) * k / 199
    for _, rc in ipairs({ {13, 0.12}, {12, 0.55} }) do
      local dx = floor(13 + rc[1] * cos(ang) + 0.5)
      local y = floor(18 + rc[1] * sin(ang) + 0.5)
      S(dx, y, rc[2])
    end
  end
  for y = 5, 9 do S(13, y, 0.16) end                          -- hanger rod
  local cap = { [10] = {12, 14}, [11] = {11, 15}, [12] = {9, 17}, [13] = {8, 18} }
  for y, r in pairs(cap) do
    for dx = r[1], r[2] do S(dx, y, (y < 13) and 0.16 or 0.27) end
  end
  for y = 14, 23 do                                            -- lantern frame bars
    S(9, y, 0.12); S(17, y, 0.12)
  end
  for dx = 9, 17 do S(dx, 24, 0.18) end                        -- bottom plate
  S(13, 25, 0.18)                                              -- finial
  local img = love.graphics.newImage(id)
  img:setFilter("nearest", "nearest")
  return img
end

-- dithered light cast by one lamp onto the wall, the sidewalk and the curb
local function buildLampLight(lamp)
  local id = love.image.newImageData(LIGHT_R * 2, VH)
  local x0 = lamp.lx - LIGHT_R
  for iy = 0, VH - 1 do
    for ix = 0, LIGHT_R * 2 - 1 do
      local wx = x0 + ix
      if wx >= 0 and wx < WORLD_W then
        local t = thr(wx, iy)
        if iy < WALL_END then
          local halo, wall = lampTerms(lamp, wx, iy)
          local mortar, tone = brickInfo(wx, iy)
          local wallI = wall * (mortar and 0.38 or 1) * tone
          if halo > t then
            id:setPixel(ix, iy, 0.92, 0.92, 0.92, 1)
          elseif wallI > t then
            id:setPixel(ix, iy, 0.59, 0.59, 0.59, 1)
          end
        elseif iy < CURB_Y then
          local ig = (clip01(1 - abs(wx - lamp.lx) / 36) ^ 1.2) * 0.6
          if ig > t then id:setPixel(ix, iy, 0.44, 0.44, 0.44, 1) end
        elseif iy == CURB_Y then
          local lit = max(0, 1 - abs(wx - lamp.lx) / 30)
          local v = 0.22 + 0.65 * lit
          id:setPixel(ix, iy, v, v, v, 1)
        end
      end
    end
  end
  local img = love.graphics.newImage(id)
  img:setFilter("nearest", "nearest")
  return img
end

------------------------------------------------------------
-- 6. AUDIO (synthesised, no files needed; all wrapped in pcall)
------------------------------------------------------------
local splashSounds = {}
local rainSource = nil

local function makeNoise(len, rate, attack, decayPow, cutoff, gain, loopable)
  local n = floor(len * rate)
  local sd = love.sound.newSoundData(n, rate, 16, 1)
  local lp1, lp2 = 0, 0
  for i = 0, n - 1 do
    local t = i / n
    local env = 1
    if not loopable then
      env = (1 - t) ^ decayPow
      if t < attack then env = env * (t / attack) end
    end
    local noise = math.random() * 2 - 1
    lp1 = lp1 + (noise - lp1) * cutoff
    lp2 = lp2 + (lp1 - lp2) * cutoff
    sd:setSample(i, clamp(lp2 * env * gain, -1, 1))
  end
  return sd
end

local function initAudio()
  pcall(function()
    for i = 1, 3 do
      local sd = makeNoise(0.20 + i * 0.03, 22050, 0.03, 2.2, 0.30 + i * 0.06, 2.6, false)
      splashSounds[i] = love.audio.newSource(sd, "static")
    end
    local rain = makeNoise(2.0, 22050, 0, 0, 0.55, 1.6, true)
    rainSource = love.audio.newSource(rain, "static")
    rainSource:setLooping(true)
    rainSource:setVolume(0.22)
    rainSource:play()
  end)
end

local function playSplash(vol)
  if muted or #splashSounds == 0 then return end
  pcall(function()
    local s = splashSounds[math.random(#splashSounds)]:clone()
    s:setVolume(vol)
    s:setPitch(0.85 + math.random() * 0.35)
    s:play()
  end)
end

------------------------------------------------------------
-- 7. SPLASHES, RIPPLES, PUDDLES
------------------------------------------------------------
local PART_G = 240

local function addRipple(x, y, maxR, life)
  if #ripples >= 90 then table.remove(ripples, 1) end
  table.insert(ripples, { x = x, y = y, age = 0, life = life, maxR = maxR })
end

local function splashAt(x, y, count, power)
  for i = 1, count do
    local a = -pi * (0.15 + 0.7 * math.random())
    local sp = (35 + math.random() * 55) * power
    table.insert(particles, {
      x = x + (math.random() - 0.5) * 3, y = y,
      vx = cos(a) * sp * 0.6, vy = sin(a) * sp,
      life = 0.55, maxLife = 0.55,
      landY = y + math.random() * 1.5, kind = "splash",
    })
  end
end

local function puddleAt(x, y)
  for _, p in ipairs(PUDDLES) do
    local ex, ey = (x - p.cx) / p.rx, (y - p.cy) / p.ry
    if ex * ex + ey * ey <= 1 then return p end
  end
  return nil
end

local function onStep()
  player.foot = 1 - player.foot
  local fx = player.x + ((player.foot == 0) and -3 or 3)
  if puddleAt(fx, player.y) then
    splashAt(fx, player.y, 7, 0.7)
    addRipple(fx, player.y, 3.5, 0.5)
    splashes = splashes + 1
    playSplash(0.45)
  end
end

local function onLand()
  if puddleAt(player.x, player.y) then
    splashAt(player.x - 3, player.y, 10, 1.2)
    splashAt(player.x + 3, player.y, 10, 1.2)
    addRipple(player.x, player.y, 8, 0.7)
    addRipple(player.x, player.y, 5, 0.5)
    splashes = splashes + 3
    playSplash(0.9)
  end
end

------------------------------------------------------------
-- 8. RAIN
------------------------------------------------------------
local function respawnDrop(d, anywhere)
  d.x = math.random() * (VW + 60) - 20
  d.y = anywhere and (math.random() * VH) or -(math.random() * 30)
  d.land = math.random(GROUND_MIN_Y, GROUND_MAX_Y)
end

local function initRain()
  drops = {}
  for i = 1, 150 do
    local near = (i % 3 == 0)
    local d = {
      sp = near and (270 + math.random() * 30) or (150 + math.random() * 20),
      len = near and 5 or 3,
      dark = near and 0.40 or 0.22,
      lit = near and 1.0 or 0.80,
    }
    respawnDrop(d, true)
    table.insert(drops, d)
  end
end

-- the umbrella: world-space dome centre / base used for rain collision
local function canopy()
  local cxw = player.x + player.facing * 3.5
  local baseY = player.y - player.jz - 26
  return cxw, baseY
end

local function updateRain(dt)
  local cxw, baseY = canopy()
  for _, d in ipairs(drops) do
    d.y = d.y + d.sp * dt
    d.x = d.x - d.sp * 0.25 * dt

    -- umbrella catches the rain
    local wx = d.x + camX
    local ddx = (wx - cxw) / 14
    if abs(ddx) < 1 and d.y < baseY then
      local top = 8 * sqrt(1 - ddx * ddx)
      if d.y >= baseY - top then
        if math.random() < 0.4 then
          table.insert(particles, {
            x = wx, y = baseY - top,
            vx = (math.random() - 0.5) * 40, vy = -(10 + math.random() * 20),
            life = 0.2, maxLife = 0.2, landY = 1e9, kind = "tick",
          })
        end
        respawnDrop(d, false)
      end
    end

    if d.y >= d.land then
      if d.land >= CURB_Y + 3 and math.random() < 0.45 then
        addRipple(d.x + camX, d.land, 2.6, 0.38)
      end
      respawnDrop(d, false)
    end
  end
end

------------------------------------------------------------
-- 9. UPDATE
------------------------------------------------------------
local function updateLamps()
  for _, lamp in ipairs(lamps) do
    if gt >= lamp.nextFlick then
      lamp.flickEnd = gt + 0.12
      lamp.nextFlick = gt + 2.5 + math.random() * 4.5
    end
    lamp.flick = (gt < lamp.flickEnd) and 0.8 or 1
  end
end

local function updatePlayer(dt)
  local left  = love.keyboard.isDown("left")  or love.keyboard.isDown("a")
  local right = love.keyboard.isDown("right") or love.keyboard.isDown("d")
  local up    = love.keyboard.isDown("up")    or love.keyboard.isDown("w")
  local down  = love.keyboard.isDown("down")  or love.keyboard.isDown("s")
  local dx, dy = 0, 0
  if left then dx = dx - 1 end
  if right then dx = dx + 1 end
  if up then dy = dy - 1 end
  if down then dy = dy + 1 end

  player.moving = (dx ~= 0 or dy ~= 0)
  if dx ~= 0 then player.facing = dx end

  local hs = (dy ~= 0) and 42 or 52
  player.x = clamp(player.x + dx * hs * dt, 10, WORLD_W - 10)
  player.y = clamp(player.y + dy * 34 * dt, GROUND_MIN_Y, GROUND_MAX_Y)

  -- jumping
  if player.jz > 0 or player.jvz > 0 then
    player.jvz = player.jvz - 480 * dt
    player.jz = player.jz + player.jvz * dt
    if player.jz <= 0 then
      player.jz, player.jvz = 0, 0
      onLand()
    end
  end

  -- footsteps
  if player.moving and player.jz == 0 then
    player.stepT = player.stepT + dt
    if player.stepT >= 0.2 then
      player.stepT = 0
      onStep()
    end
  else
    player.stepT = 0.15
  end

  -- drips running off the umbrella rim
  player.dripT = player.dripT - dt
  if player.dripT <= 0 then
    player.dripT = 0.14 + math.random() * 0.1
    local cxw, baseY = canopy()
    local side = (math.random() < 0.5) and -13 or 13
    table.insert(particles, {
      x = cxw + side, y = baseY + 1, vx = 0, vy = 0,
      life = 2, maxLife = 2,
      landY = clamp(player.y + math.random(-2, 4), GROUND_MIN_Y, VH - 1),
      kind = "drip",
    })
  end
end

local function updateParticles(dt)
  for i = #particles, 1, -1 do
    local q = particles[i]
    q.life = q.life - dt
    if q.kind == "tick" then
      q.x = q.x + q.vx * dt
      q.y = q.y + q.vy * dt
    else
      q.vy = q.vy + PART_G * dt
      q.x = q.x + q.vx * dt
      q.y = q.y + q.vy * dt
      if q.vy > 0 and q.y >= q.landY then
        if math.random() < 0.3 then addRipple(q.x, q.landY, 2, 0.3) end
        q.life = 0
      end
    end
    if q.life <= 0 then table.remove(particles, i) end
  end
end

local function updateRipples(dt)
  for i = #ripples, 1, -1 do
    local r = ripples[i]
    r.age = r.age + dt
    if r.age >= r.life then table.remove(ripples, i) end
  end

  -- ambient rain ripples: more on puddles, some on the open road
  if math.random() < dt * 9 then
    local cands = {}
    for _, p in ipairs(PUDDLES) do
      if p.cx + p.rx > camX and p.cx - p.rx < camX + VW then table.insert(cands, p) end
    end
    if #cands > 0 then
      local p = cands[math.random(#cands)]
      addRipple(p.cx + (math.random() * 2 - 1) * p.rx * 0.8,
                p.cy + (math.random() * 2 - 1) * p.ry * 0.8, 3, 0.5)
    end
  end
  if math.random() < dt * 5 then
    addRipple(camX + math.random() * VW, CURB_Y + 4 + math.random() * (VH - CURB_Y - 6), 2.4, 0.4)
  end
end

function love.update(dt)
  dt = min(dt, 1 / 30)
  gt = gt + dt
  if hintTimer > 0 then hintTimer = hintTimer - dt end

  updateLamps()
  updatePlayer(dt)

  local target = clamp(player.x - VW / 2, 0, WORLD_W - VW)
  camX = camX + (target - camX) * min(1, 6 * dt)

  updateRain(dt)
  updateParticles(dt)
  updateRipples(dt)
end

------------------------------------------------------------
-- 10. INPUT
------------------------------------------------------------
function love.keypressed(key)
  if key == "space" then
    if player.jz == 0 and player.jvz == 0 then player.jvz = 135 end
  elseif key == "m" then
    muted = not muted
    if rainSource then
      pcall(function()
        if muted then rainSource:pause() else rainSource:play() end
      end)
    end
  elseif key == "escape" then
    love.event.quit()
  end
end

------------------------------------------------------------
-- 11. DRAWING
------------------------------------------------------------
local gLM, gA = 1, 1   -- lighting multiplier / alpha used by the figure

local function R(x, y, w, h, v)
  love.graphics.setColor(v * gLM, v * gLM, v * gLM, gA)
  love.graphics.rectangle("fill", x, y, w, h)
end

local function RW(x, y, w, h, v)   -- ignores lighting (glowing eyes)
  love.graphics.setColor(v, v, v, gA)
  love.graphics.rectangle("fill", x, y, w, h)
end

-- The hooded figure with an umbrella. Local coords: feet at (0,0), y up is
-- negative, drawn facing right and flipped for left. `mirror` draws the
-- upside-down reflection in the wet ground.
local function drawFigure(px, py, facing, mirror, alpha, lm, moving, foot, bob)
  gLM, gA = lm, alpha
  love.graphics.push()
  love.graphics.translate(floor(px + 0.5), floor(py + 0.5))
  love.graphics.scale(facing, mirror and -1 or 1)

  -- boots (the stepping foot lifts a pixel)
  local lift1 = (moving and foot == 0) and 1 or 0
  local lift2 = (moving and foot == 1) and 1 or 0
  R(-5, -2 - lift1, 4, 2, 0.10)
  R(1, -2 - lift2, 4, 2, 0.10)
  R(-5, -2 - lift1, 4, 1, 0.38)
  R(1, -2 - lift2, 4, 1, 0.38)

  love.graphics.translate(0, bob)

  -- robe: flared trapezoid with lighter edges
  for r = 0, 11 do
    local y = -3 - r
    local hw = floor(6.5 - r * 0.28 + 0.5)
    R(-hw, y, hw * 2 + 1, 1, 0.20)
    R(-hw, y, 1, 1, 0.52)
    R(hw, y, 1, 1, 0.52)
  end
  for x = -7, 7, 3 do R(x, -3, 1, 1, 0.04) end      -- ragged hem
  R(-5, -9, 11, 1, 0.50)                             -- rope belt
  R(1, -8, 2, 2, 0.85)                               -- belt knot
  R(-2, -5, 1, 4, 0.12)                              -- fabric folds
  R(2, -5, 1, 4, 0.12)

  -- arm + umbrella handle/pole
  R(4, -36, 1, 25, 0.62)
  R(2, -15, 3, 4, 0.18)
  R(3, -12, 3, 3, 0.82)

  -- hood with a dark face and two glowing eyes
  for dy = -5, 5 do
    local hw = floor(sqrt(25 - dy * dy) + 0.5)
    local y = -17 + dy
    R(-hw, y, hw * 2 + 1, 1, 0.14)
    R(-hw, y, 1, 1, 0.50)
    R(hw, y, 1, 1, 0.50)
    if dy == -5 then R(-hw, y, hw * 2 + 1, 1, 0.50) end
  end
  R(0, -23, 1, 1, 0.50)
  for dy = -3, 3 do
    local hw = floor(sqrt(9 - dy * dy) + 0.5)
    R(1 - hw, -17 + dy, hw * 2 + 1, 1, 0.01)
  end
  RW(0, -17, 1, 1, 1)
  RW(3, -17, 1, 1, 1)

  -- umbrella canopy: dark dome, pale rim, ribs, scalloped edge
  local cxl, hgt, baseY = 3, 8, -26
  for dx = -11, 16 do
    local t = (dx - cxl + 0.5) / 14
    local hh = floor(hgt * sqrt(max(0, 1 - t * t)) + 0.5)
    if hh > 0 then
      local top = baseY - hh + 1
      R(dx, top, 1, hh, 0.13)
      if ((dx - cxl) % 5 == 0) and hh > 2 then R(dx, top + 1, 1, hh - 1, 0.36) end
      R(dx, top, 1, 1, 0.80)
    end
  end
  R(-11, baseY, 28, 1, 0.72)
  for dx = -11, 16 do
    if (dx + 11) % 4 < 2 then R(dx, baseY + 1, 1, 1, 0.72) end
  end
  R(3, baseY - hgt - 2, 1, 2, 0.75)                  -- finial

  love.graphics.pop()
  love.graphics.setColor(1, 1, 1, 1)
end

local function drawPuddle(pd)
  local y0 = math.ceil(pd.cy - pd.ry)
  local y1 = floor(pd.cy + pd.ry)
  for y = y0, y1 do
    local dy = (y - pd.cy) / pd.ry
    if abs(dy) <= 1 then
      local half = pd.rx * sqrt(1 - dy * dy)
      local xa = math.ceil(pd.cx - half)
      local xb = floor(pd.cx + half)
      for x = xa, xb do
        local g = lampReflect(x)
        local v = 0.07
        if g * 0.95 > thr(x, y) then
          v = 0.78
        elseif x == xa or x == xb or y == y0 then
          v = 0.18 + 0.5 * g
        end
        love.graphics.setColor(v, v, v, 1)
        love.graphics.rectangle("fill", x, y, 1, 1)
      end
    end
  end
end

-- shimmering dithered reflection of a lantern on the wet pavement/road
local function drawLampReflection(lamp)
  local y0 = WALL_END + 1
  for y = y0, VH - 1 do
    local rel = (y - y0) / (VH - 1 - y0)
    local wob = 1.6 * sin(2 * pi * (gt * 1.2 + y / 11))
    local width = 2.5 + rel * 3.2
    local fade = 1 - 0.55 * rel
    local shimmer = 0.65 + 0.35 * sin(2 * pi * (y / 4 - gt * 1.7))
    for x = lamp.lx - 10, lamp.lx + 10 do
      local shape = max(0, 1 - abs(x - (lamp.lx + wob)) / width)
      local val = shape * fade * shimmer * 1.15 * lamp.flick
      if val > thr(x, y) then
        love.graphics.setColor(0.88, 0.88, 0.88, 1)
        love.graphics.rectangle("fill", x, y, 1, 1)
      end
    end
  end
end

local function drawRipple(r)
  local p = r.age / r.life
  local rx = 0.6 + p * r.maxR
  local ry = max(0.4, rx * 0.4)
  local v = (0.25 + 0.75 * lightG(r.x)) * ((1 - p) ^ 1.2)
  v = max(v, 0.10)
  love.graphics.setColor(v, v, v, 1)
  local n = max(4, floor(rx * 7))
  for k = 0, n - 1 do
    local ang = 2 * pi * k / n
    love.graphics.rectangle("fill",
      floor(r.x + rx * cos(ang) + 0.5), floor(r.y + ry * sin(ang) + 0.5), 1, 1)
  end
end

local function drawLamp(lamp, idx)
  love.graphics.setColor(1, 1, 1, 1)
  love.graphics.draw(lampImage, lamp.p - 4, 0)
  local g = (lamp.flick < 1) and 0.92 or 1
  love.graphics.setColor(g, g, g, 1)
  love.graphics.rectangle("fill", lamp.p + 10, 14, 7, 10)
  -- drips running off the lantern
  for side = 0, 1 do
    local a = (gt * 8 + side * 6 + idx * 3) % 12
    local y = 26 + floor(a * a * 0.3)
    if y < WALL_END + 8 then
      love.graphics.setColor(0.96, 0.96, 0.96, 1)
      love.graphics.rectangle("fill", lamp.p + (side == 0 and 10 or 16), y, 1, 1)
    end
  end
  love.graphics.setColor(1, 1, 1, 1)
end

local function drawParticles()
  for _, q in ipairs(particles) do
    local a = clamp(q.life / q.maxLife * 1.4, 0, 1)
    if q.kind == "drip" then a = 1 end
    love.graphics.setColor(1, 1, 1, a)
    love.graphics.rectangle("fill", floor(q.x), floor(q.y), 1, 1)
  end
  love.graphics.setColor(1, 1, 1, 1)
end

local function drawRain(camI)
  for _, d in ipairs(drops) do
    local hx, hy = floor(d.x), floor(d.y)
    local light = clip01(lightAt(hx + camI, clamp(hy, 0, VH - 1)) * 3.2)
    local c = d.dark + (d.lit - d.dark) * light
    for i = 0, d.len - 1 do
      local px = floor(d.x + 0.25 * i)
      local py = floor(d.y - i)
      if py >= 0 and py <= d.land and px >= 0 and px < VW then
        local cc = (i >= d.len - 2) and (c * 0.6) or c
        love.graphics.setColor(cc, cc, cc, 1)
        love.graphics.rectangle("fill", px, py, 1, 1)
      end
    end
  end
  love.graphics.setColor(1, 1, 1, 1)
end

local function drawHud()
  love.graphics.setFont(font)
  love.graphics.setColor(1, 1, 1, 0.75)
 -- love.graphics.print(string.format("SPLASHES %03d", splashes), 4, 3)
  if hintTimer > 0 then
    love.graphics.setColor(1, 1, 1, clip01(hintTimer / 2) * 0.8)
    love.graphics.printf("There are puddles to splash in.", 0, VH - 12, VW, "center")
  end
  love.graphics.setColor(1, 1, 1, 1)
end

function love.draw()
  local camI = floor(camX)
  love.graphics.setCanvas(canvas)
  love.graphics.clear(0, 0, 0, 1)

  love.graphics.push()
  love.graphics.translate(-camI, 0)

  -- background, lamp light, ground details
  love.graphics.setColor(1, 1, 1, 1)
  love.graphics.draw(bgImage, 0, 0)

  local visible = {}
  for i, lamp in ipairs(lamps) do
    if lamp.lx + LIGHT_R > camI and lamp.lx - LIGHT_R < camI + VW then
      table.insert(visible, i)
    end
  end

  for _, i in ipairs(visible) do
    local lamp = lamps[i]
    love.graphics.setColor(1, 1, 1, lamp.flick)
    love.graphics.draw(lamp.lightImg, lamp.lx - LIGHT_R, 0)
  end
  love.graphics.setColor(1, 1, 1, 1)

  for _, pd in ipairs(PUDDLES) do
    if pd.cx + pd.rx > camI and pd.cx - pd.rx < camI + VW then drawPuddle(pd) end
  end
  for _, i in ipairs(visible) do drawLampReflection(lamps[i]) end
  for _, r in ipairs(ripples) do
    if r.x > camI - 12 and r.x < camI + VW + 12 then drawRipple(r) end
  end

  -- the figure's reflection in the wet ground
  local lm = 0.62 + 0.38 * clip01(lightG(player.x) * 1.3)
  local bob = (player.moving and player.jz == 0 and (floor(gt * 10) % 2 == 0)) and -1 or 0
  drawFigure(player.x, player.y + player.jz, player.facing, true, 0.20, lm,
             player.moving, player.foot, 0)

  -- lamps behind the figure, then the figure, then lamps in front
  for _, i in ipairs(visible) do
    if 72 <= player.y then drawLamp(lamps[i], i) end
  end
  drawFigure(player.x, player.y - player.jz, player.facing, false, 1, lm,
             player.moving, player.foot, bob)
  for _, i in ipairs(visible) do
    if 72 > player.y then drawLamp(lamps[i], i) end
  end

  drawParticles()
  love.graphics.pop()

  drawRain(camI)
  drawHud()

  love.graphics.setCanvas()
  love.graphics.setColor(1, 1, 1, 1)
  love.graphics.draw(canvas, 0, 0, 0, SCALE, SCALE)
end

------------------------------------------------------------
-- 12. LOAD
------------------------------------------------------------
function love.load()
  love.window.setTitle("Rain Walk")
  love.graphics.setDefaultFilter("nearest", "nearest")
  math.randomseed(os.time())
  math.random(); math.random()

  canvas = love.graphics.newCanvas(VW, VH)
  canvas:setFilter("nearest", "nearest")
  font = love.graphics.newFont(8, "mono")
  font:setFilter("nearest", "nearest")
  love.graphics.setFont(font)

  for _, p in ipairs(LAMP_POLES) do
    table.insert(lamps, {
      p = p, lx = p + 13, flick = 1,
      flickEnd = 0, nextFlick = 1 + math.random() * 4,
    })
  end

  bgImage = buildBackground()
  lampImage = buildLampSprite()
  for _, lamp in ipairs(lamps) do lamp.lightImg = buildLampLight(lamp) end

  initRain()
  initAudio()
end

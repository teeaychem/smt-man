#pragma once

#include <stdint.h>

constexpr uint32_t FPS = 60;

constexpr uint64_t NS_PER_FRAME = 1000000000 / FPS;

constexpr int32_t TILE_PIXELS = 8;

constexpr int UI_SCALE = 4;

constexpr uint32_t SPRITE_BUFFER_SIZE = TILE_PIXELS * 4;

constexpr uint32_t RENDER_TOP = 3;

constexpr uint32_t RENDER_BOT = 2;

constexpr uint32_t MAZE_INDENT = TILE_PIXELS / 2;

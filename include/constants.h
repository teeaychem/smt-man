#pragma once

#include <pthread.h>
#include <stdint.h>

#include "generic/pairs.h"

constexpr uint8_t ANIMA_COUNT = 4;

constexpr uint8_t PERSONA_COUNT = 1;

constexpr uint32_t FPS = 60;

constexpr uint64_t NS_PER_FRAME = 1000000000 / FPS;

constexpr Pair_uint32 STANDARD_TILE_DIMENSIONS = {.x = 28, .y = 31};

constexpr int32_t TILE_PIXELS = 8;

constexpr int UI_SCALE = 4;

extern pthread_t ANIMA_THREADS[ANIMA_COUNT];

constexpr int32_t SPRITE_VELOCITY = 1;

constexpr uint32_t SPRITE_BUFFER_SIZE = TILE_PIXELS * 4;

constexpr uint32_t RENDER_TOP = 3;

constexpr uint32_t RENDER_BOT = 2;

constexpr uint32_t MAZE_INDENT = TILE_PIXELS / 2;

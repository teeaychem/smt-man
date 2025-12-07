#pragma once

#include <pthread.h>
#include <stdint.h>

#include <SDL3/SDL_render.h>

#include "pairs.h"

constexpr uint8_t ANIMA_COUNT = 2;

/* constexpr int32_t TILE_EDGE_SIZE = 8; */

constexpr Pair_uint32 TILE_COUNTS = {.x = 28, .y = 31};

constexpr int32_t TILE_SCALE = 16;

constexpr Pair_uint32 PIXEL_DIMENSIONS = {.x = TILE_COUNTS.x * TILE_SCALE, .y = TILE_COUNTS.y * TILE_SCALE};

constexpr Pair_uint32 PAIR_SPRITE_EDGE = {.x = TILE_SCALE, .y = TILE_SCALE};

constexpr int UI_SCALE = 3;
constexpr uint32_t FPS_COUNT = 15;

constexpr Uint64 NS_PER_FRAME = 1000000000 / FPS_COUNT;

extern pthread_t ANIMA_THREADS[ANIMA_COUNT];
extern pthread_mutex_t MTX_SOLVER;

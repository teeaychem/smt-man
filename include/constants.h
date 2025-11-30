#pragma once

#include <stdint.h>

#include <SDL3/SDL_render.h>

#include "utils/pairs.h"

constexpr size_t ANIMA_COUNT = 2;
static char *ANIMA_NAMES[2] = {"gottlob", "bertrand"};

/* constexpr int32_t TILE_EDGE_SIZE = 8; */

constexpr PairI32 TILE_COUNTS = {.x = 28, .y = 31};

constexpr int32_t TILE_SCALE = 16;

constexpr PairI32 PIXEL_COUNTS = {.x = TILE_COUNTS.x * TILE_SCALE, .y = TILE_COUNTS.y * TILE_SCALE};

constexpr PairI32 PAIR_SPRITE_EDGE = {.x = TILE_SCALE, .y = TILE_SCALE};

constexpr int UI_SCALE = 2;
constexpr uint32_t FPS_COUNT = 15;

constexpr Uint64 NS_PER_FRAME = 1000000000 / FPS_COUNT;

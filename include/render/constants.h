#pragma once

#include <stdint.h>

#include <SDL3/SDL_render.h>

#include "utils/pairs.h"

constexpr size_t ANIMA_COUNT = 2;
static const char *ANIMA_NAMES[2] = {"gottlob", "bertrand"};

static const int32_t TILE_EDGE_SIZE = 8;
static const int32_t SPRITE_EDGE_SIZE = TILE_EDGE_SIZE * 2;
static const PairI32 kTILES = {.x = 28, .y = 31};
static const PairI32 kPIXELS = {.x = kTILES.x * SPRITE_EDGE_SIZE, .y = kTILES.y * SPRITE_EDGE_SIZE};
static const PairI32 PAIR_SPRITE_EDGE = {.x = SPRITE_EDGE_SIZE, .y = SPRITE_EDGE_SIZE};

static const int kSCALE = 2;
static const uint32_t kSCREEN_FPS = 15;

static const Uint64 kNS_PER_FRAME = 1000000000 / kSCREEN_FPS;

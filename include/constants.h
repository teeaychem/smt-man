#pragma once

#include <pthread.h>
#include <stdint.h>

#include "generic/pairs.h"

constexpr uint8_t ANIMA_COUNT = 4;

constexpr uint32_t FPS = 30;

constexpr uint64_t NS_PER_FRAME = 1000000000 / FPS;

constexpr Pair_uint32 STANDARD_TILE_DIMENSIONS = {.x = 28, .y = 36};

constexpr int32_t TILE_PIXELS = 8;

constexpr int UI_SCALE = 4;

extern pthread_t ANIMA_THREADS[ANIMA_COUNT];

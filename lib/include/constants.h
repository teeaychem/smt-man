#pragma once

#include <pthread.h>
#include <stdint.h>

#include "generic/pairs.h"

constexpr uint8_t ANIMA_COUNT = 1;

constexpr uint8_t PERSONA_COUNT = 1;

constexpr Pair_uint32 STANDARD_TILE_DIMENSIONS = {.x = 28, .y = 31};

constexpr int32_t SPRITE_VELOCITY = 1;

constexpr int32_t TILE_PIXELS = 8;

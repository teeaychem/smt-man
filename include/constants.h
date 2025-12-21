#pragma once

#include <pthread.h>
#include <stdint.h>

constexpr uint8_t ANIMA_COUNT = 4;

constexpr int32_t TILE_PIXELS = 8;

extern pthread_t ANIMA_THREADS[ANIMA_COUNT];

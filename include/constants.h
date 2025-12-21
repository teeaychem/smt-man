#pragma once

#include <pthread.h>
#include <stdint.h>

constexpr uint8_t ANIMA_COUNT = 4;

constexpr int32_t TILE_PIXELS = 8;

constexpr int UI_SCALE = 6;
constexpr uint32_t FPS_COUNT = 12;

constexpr uint64_t NS_PER_FRAME = 1000000000 / FPS_COUNT;

extern pthread_t ANIMA_THREADS[ANIMA_COUNT];
extern pthread_mutex_t MTX_SOLVER;

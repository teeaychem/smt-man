#pragma once

#include <stdint.h>

#include <SDL3/SDL_render.h>

#include "utils/pairs.h"

static const int32_t kTILE = 8;
static const int32_t kSPRITE = kTILE * 2;
static const PairI32 kTILES = {.x = 28, .y = 31};
static const PairI32 kPIXELS = {.x = kTILES.x * kSPRITE, .y = kTILES.y * kSPRITE};

static const int kSCALE = 2;
static const uint32_t kSCREEN_FPS = 30;

static const Uint64 kNS_PER_FRAME = 1000000000 / kSCREEN_FPS;

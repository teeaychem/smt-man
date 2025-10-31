#include "utils/pairs.h"
#include <SDL3/SDL_render.h>
#include <stdint.h>

const int32_t kTILE = 16;
const PairI32 kTILES = {.x = 28, .y = 36};
const PairI32 kPIXELS = {.x = kTILES.x * kTILE, .y = kTILES.y * kTILE};

const int kSCALE = 2;
const int kSCREEN_FPS = 30;

const Uint64 kNS_PER_FRAME = 1000000000 / kSCREEN_FPS;

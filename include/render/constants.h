#include "utils/pairs.h"
#include <SDL3/SDL_render.h>
#include <stdint.h>

const int32_t kTile = 16;
const PairI32 dTiles = {.x = 28, .y = 36};
const PairI32 dPixels = {.x = dTiles.x * kTile, .y = dTiles.y * kTile};

const int kScale = 2;
const int kScreenFps = 30;

const Uint64 nsPerFrame = 1000000000 / kScreenFps;

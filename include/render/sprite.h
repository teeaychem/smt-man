#pragma once

#include "surface.h"

#include "utils/pairs.h"

typedef struct sprite_info_t SpriteInfo;
struct sprite_info_t {
  PairI32 size;
  Surface surface;
  PairI32 surface_offset;
  uint32_t tick;
};

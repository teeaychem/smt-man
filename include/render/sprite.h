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

static inline uint32_t SpriteInfo_pixel_at_point(SpriteInfo *self, uint32_t col, uint32_t row) {
  return (self->surface_offset.y + col) * self->surface.size.x + self->surface_offset.x + row;
}

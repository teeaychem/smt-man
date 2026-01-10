#pragma once

#include <stdint.h>

#include <SDL3/SDL.h>
#include <png.h>

#include "SML/maze.h"
#include "generic/pairs.h"
#include "render/palette.h"

struct surface_t {
  Pair_uint32 size;
  uint32_t *pixels;
};
typedef struct surface_t Surface;

/// Methods

void Surface_from_path(Surface *self, const char *path);

void Surface_drop(Surface *self);

void Surface_char_projection(const Surface *self, char *destination, size_t *length);

void Surface_mirror(Surface *self, const uint32_t size);

void Surface_transpose(Surface *self, const uint32_t size);

void Surface_apply_pallete(Surface *self, const uint32_t size, const Pallete pallete);

void Surface_fill_tile(Surface *self, const Pair_uint32 destination, const uint32_t size, const uint32_t colour);

void Surface_tile_line(Surface *self, const uint32_t x, const uint32_t y, const Plane plane, const uint32_t length, const uint32_t colour);

void Surface_circle_draw(Surface *self, const Pair_uint32 *origin, const Pair_uint32 *offset, const Quadrant quadrant, const uint32_t colour);

// INVARIANT: The tile has an even number of pixels, and the origin is given by: (x += width/2, y += height/2).
void Surface_tile_arc(Surface *self, const Pair_uint32 origin, const uint32_t radius, const Quadrant quadrant, const uint32_t colour);

void Surface_tile_fixed_arc(Surface *self, const Pair_uint32 origin, const TileData *tile_data, const uint32_t colour);

/// Static inline

static inline uint32_t Surface_offset(const Surface *self, const uint32_t col, const uint32_t row) {
  return (row * self->size.x) + col;
}

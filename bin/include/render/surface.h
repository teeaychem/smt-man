#pragma once

#include <stdint.h>
#include <stdlib.h>

#include <SDL3/SDL.h>
#include <png.h>

#include "generic/pairs.h"

#include "SML/maze.h"

#include "render/palette.h"

struct surface_t {
  Pair_uint32 dimensions;
  uint32_t *pixels;
};
typedef struct surface_t surface_s;

/// Methods

void surface_ctor(surface_s *self, const char *path);

void surface_dtor(surface_s *self);

void surface_char_projection(const surface_s *self, char **destination, size_t *length);

void surface_stdout(const surface_s *self);

void surface_mirror(surface_s *self, const uint32_t size);

void surface_transpose(surface_s *self, const uint32_t size);

void surface_apply_pallete(surface_s *self, const uint32_t size, const Pallete pallete);

void surface_fill_tile(surface_s *self, const Pair_uint32 destination, const uint32_t size, const uint32_t colour);

void surface_tile_line(surface_s *self, const uint32_t x, const uint32_t y, const plane_e plane, const uint32_t length, const uint32_t colour);

void surface_circle_draw(surface_s *self, const Pair_uint32 *origin, const Pair_uint32 *offset, const quadrant_e quadrant, const uint32_t colour);

// INVARIANT: The tile has an even number of pixels, and the origin is given by: (x += width/2, y += height/2).
void surface_tile_arc(surface_s *self, const Pair_uint32 origin, const uint32_t radius, const quadrant_e quadrant, const uint32_t colour);

void surface_tile_fixed_arc(surface_s *self, const Pair_uint32 origin, const tile_data_s *tile_data, const uint32_t colour);

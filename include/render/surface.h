#pragma once

#include <stdint.h>

#include <SDL3/SDL.h>
#include <png.h>

#include "generic/pairs.h"
#include "render/palette.h"

struct surface_t {
  Pair_uint32 size;
  uint32_t *pixels;
};
typedef struct surface_t Surface;

/// Methods

void Surface_from_path(Surface *self, const char *path);

void Surface_destroy(Surface *self);

void Surface_char_projection(const Surface *self, char *destination, size_t *length);

void Surface_mirror_mut(Surface *self, const uint32_t size);

void Surface_transpose_mut(Surface *self, const uint32_t size);

void Surface_pallete_mut(Surface *self, const uint32_t size, Pallete pallete);

void Surface_fill_tile(Surface *self, const Pair_uint32 destination, const uint32_t size, const uint32_t colour);

/// Static inline

static inline uint32_t Surface_offset(const Surface *self, const uint32_t col, const uint32_t row) {
  return (row * self->size.x) + col;
}

#pragma once

#include <stdint.h>

#include <SDL3/SDL.h>
#include <png.h>

#include "generic/pairs.h"

struct surface_t {
  Pair_uint32 size;
  uint32_t *pixels;
};
typedef struct surface_t Surface;

void Surface_from_path(Surface *self, char *path);

void Surface_destroy(Surface *self);

void Surface_char_projection(Surface *self, char *dest, size_t *len);

uint32_t Surface_offset(Surface *self, uint32_t col, uint32_t row);

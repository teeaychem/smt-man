#pragma once

#include "pairs.h"
#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include <stdint.h>
#include <png.h>

struct surface_t {
  Pair_uint32 size;
  uint32_t *pixels;
};
typedef struct surface_t Surface;

Surface Surface_from_path(char *path);

void Surface_destroy(Surface *self);

int Surface_char_projection(Surface *self, char *dest, size_t *len);

static inline uint32_t Surface_pixel_offset(Surface *self, uint32_t col, uint32_t row) {
  return (row * self->size.x) + col;
}

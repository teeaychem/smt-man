#pragma once

#include "utils/pairs.h"
#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include <png.h>

struct surface_t {
  PairI32 size;

  int32_t *pixels;
};

typedef struct surface_t Surface;

Surface Surface_from_path(char *path);

void Surface_destroy(Surface *self);

int Surface_char_projection(Surface *surface, char *dest, size_t *len);

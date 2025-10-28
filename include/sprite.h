#pragma once

#include "utils/pairs.h"
#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include <png.h>

struct sprite_t {
  PairI32 size;
  PairI32 pos;

  int32_t *pixels;
};

typedef struct sprite_t Sprite;

Sprite Sprite_create(char *path);
void Sprite_destroy(Sprite *self);

int Sprite_char_projection(Sprite *sprite, char *dest, size_t *len);

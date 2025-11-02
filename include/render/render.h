#pragma once

#include "sprite.h"
#include "utils/pairs.h"
#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include <stddef.h>

struct renderer_t {
  PairI32 dPixels;

  SDL_Renderer *renderer;
  int32_t *frameBuffer;
  SDL_Texture *texture;
};

typedef struct renderer_t Renderer;

Renderer Renderer_create(SDL_Window *window, PairI32 dPixels);

void Renderer_update(Renderer *self);

void Renderer_draw_sprite(Renderer *self, Sprite const *sprite);

void Renderer_fill_tile(Renderer *self, PairI32 pos, int32_t colour);

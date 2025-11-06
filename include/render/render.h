#pragma once

#include "surface.h"
#include "utils/pairs.h"
#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include <stddef.h>

struct renderer_t {
  SDL_Window *gWindow;

  SDL_Renderer *renderer;
  int32_t *frameBuffer;
  SDL_Texture *texture;
};

typedef struct renderer_t Renderer;

Renderer Renderer_create();

void Renderer_destroy(Renderer *self);

void Renderer_update(Renderer *self);

void Renderer_draw_surface(Renderer *self,
                           PairI32 const *position,
                           Surface const *surface,
                           PairI32 const *origin, PairI32 const *size);

void Renderer_erase_surface(Renderer *self,
                           PairI32 const *position,
                           Surface const *surface,
                           PairI32 const *origin, PairI32 const *size);

void Renderer_fill_tile(Renderer *self, PairI32 pos, int32_t colour);

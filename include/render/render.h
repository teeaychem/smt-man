#pragma once

#include "anima.h"
#include "logic.h"
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

void Renderer_draw_sprite(Renderer *self,
                          PairI32 const *location,
                          SpriteInfo *sprite_info);

void Renderer_erase_sprite(Renderer *self,
                           PairI32 const *location,
                           SpriteInfo *sprite_info);

void Renderer_fill_tile(Renderer *self, PairI32 pos, int32_t colour);

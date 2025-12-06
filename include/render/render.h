#pragma once

#include <stddef.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "render/sprite.h"
#include "utils/pairs.h"

typedef struct renderer_t Renderer;
struct renderer_t {
  SDL_Window *window;

  SDL_Renderer *renderer;
  int32_t *frame_buffer;
  SDL_Texture *texture;
};

Renderer Renderer_create();

void Renderer_destroy(Renderer *self);

void Renderer_update(Renderer *self);

void Renderer_draw_sprite(Renderer *self,
                          PairI32 location,
                          SpriteInfo *sprite_info);

void Renderer_erase_sprite(Renderer *self,
                           PairI32 location,
                           SpriteInfo *sprite_info);

void Renderer_fill_tile(Renderer *self, PairI32 pos, int32_t colour);

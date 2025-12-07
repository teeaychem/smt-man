#pragma once

#include <stddef.h>
#include <stdint.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "constants.h"
#include "maze.h"
#include "pairs.h"
#include "render/surface.h"

typedef struct sprite_info_t SpriteInfo;
struct sprite_info_t {
  Pair_uint32 size;
  Surface surface;
  Pair_uint32 surface_offset;
  uint32_t tick;
};

static inline uint32_t SpriteInfo_pixel_at_point(SpriteInfo *self, uint32_t col, uint32_t row) {
  return (self->surface_offset.y + col) * self->surface.size.x + self->surface_offset.x + row;
}

typedef struct renderer_t Renderer;
struct renderer_t {
  Pair_uint32 dimensions;
  SDL_Window *window;

  SDL_Renderer *renderer;
  uint32_t *frame_buffer;
  SDL_Texture *texture;

  SpriteInfo anima_sprites[ANIMA_COUNT];
};

Renderer Renderer_create(const Pair_uint32 dimensions);

void Renderer_destroy(Renderer *self);

void Renderer_update(Renderer *self);

void Renderer_draw_sprite(Renderer *self, Pair_uint32 location, SpriteInfo *sprite_info);

void Renderer_erase_sprite(Renderer *self, Pair_uint32 location, SpriteInfo *sprite_info);

void Renderer_fill_tile(Renderer *self, Pair_uint32 pos, uint32_t colour);

static inline uint32_t Renderer_pixel_at_point(Renderer *self, uint32_t col, uint32_t row) {
  return col * self->dimensions.x + row;
}

void Renderer_read_maze(Renderer *self, Maze *maze);

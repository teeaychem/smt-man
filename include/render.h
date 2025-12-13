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

struct sheet_offets_t {
  struct {
    uint32_t size;
    Pair_uint32 rt[2];
    Pair_uint32 dn[2];
    Pair_uint32 lt[2];
    Pair_uint32 up[2];

  } anima;
};
typedef struct sheet_offets_t Sheetoffsets;

extern Sheetoffsets sheet_offsets;

typedef Surface Sheet;

typedef struct renderer_t Renderer;
struct renderer_t {
  Pair_uint32 dimensions;
  SDL_Window *window;

  SDL_Renderer *renderer;
  uint32_t *frame_buffer;
  SDL_Texture *texture;

  Surface sheet;
  SpriteInfo anima_sprites[ANIMA_COUNT];
};

Renderer Renderer_create(const Pair_uint32 dimensions, Surface sheet);

void Renderer_destroy(Renderer *self);

void Renderer_update(Renderer *self);

static inline uint32_t Renderer_pixel_at_point(Renderer *self, uint32_t col, uint32_t row) {
  return (row * self->dimensions.x) + col;
}

void Renderer_fill_tile(Renderer *self, Pair_uint32 pos, uint32_t colour);

void Renderer_read_maze(Renderer *self, Maze *maze);

static inline uint32_t Surface_pixel_offset(Surface *self, uint32_t col, uint32_t row) {
  return (row * self->size.x) + col;
}

void Renderer_draw_from_sheet(Renderer *self, Pair_uint32 location, uint32_t size, Pair_uint32 *offset);

void Renderer_erase_from_sheet(Renderer *self, Pair_uint32 location, uint32_t size, Pair_uint32 *offset);

// TODO: Remove
typedef struct sprite_info_t SpriteInfo;
struct sprite_info_t {
  Pair_uint32 size;
  Surface surface;
  Pair_uint32 surface_offset;
  uint32_t tick;
};

static inline uint32_t Sprite_pixel_at_point(SpriteInfo *self, uint32_t col, uint32_t row) {
  return (row * self->surface.size.x) + col;
}

void Renderer_draw_sprite(Renderer *self, Pair_uint32 location, SpriteInfo *sprite_info);
void Renderer_erase_sprite(Renderer *self, Pair_uint32 position, SpriteInfo *sprite_info);

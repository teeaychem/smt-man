#pragma once

#include <stddef.h>
#include <stdint.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>
#include <stdio.h>

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

typedef Surface Sheet;

static inline uint32_t Sprite_pixel_at_point(SpriteInfo *self, uint32_t col, uint32_t row) {
  return (row * self->surface.size.x) + col;
}

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

static void Renderer_draw_sprite(Renderer *self, Pair_uint32 location, SpriteInfo *sprite_info) {
  for (uint32_t row = 0; row < sprite_info->size.y; ++row) {
    for (uint32_t col = 0; col < sprite_info->size.x; ++col) {

      uint32_t pixel_fb = Renderer_pixel_at_point(self, location.x + col, location.y + row);

      if ((self->frame_buffer[pixel_fb] | 0x00000000) == 0x00000000) {

        uint32_t pixel_s = Sprite_pixel_at_point(sprite_info, col, row);

        self->frame_buffer[pixel_fb] = sprite_info->surface.pixels[pixel_s];
      }
    }
  }
}

static void Renderer_erase_sprite(Renderer *self, Pair_uint32 position, SpriteInfo *sprite_info) {
  for (uint32_t row = 0; row < sprite_info->size.y; ++row) {
    for (uint32_t col = 0; col < sprite_info->size.x; ++col) {

      uint32_t pixel_fb = Renderer_pixel_at_point(self, position.x + col, position.y + row);
      uint32_t pixel_s = Sprite_pixel_at_point(sprite_info, col, row);

      if (self->frame_buffer[pixel_fb] == sprite_info->surface.pixels[pixel_s]) {
        self->frame_buffer[pixel_fb] = 0x00000000;
      }
    }
  }
}

void Renderer_fill_tile(Renderer *self, Pair_uint32 pos, uint32_t colour);

void Renderer_read_maze(Renderer *self, Maze *maze);

static inline uint32_t Surface_pixel_offset(Surface *self, uint32_t col, uint32_t row) {
  return (row * self->size.x) + col;
}

static void Sheet_anima_right(Pair_uint32 *size, Pair_uint32 *offset) {
  assert(size != nullptr);
  assert(offset != nullptr);

  size->x = 16;
  size->y = 16;
  offset->x = 1;
  offset->y = 83;
}

static void Render_write(Renderer *self, Pair_uint32 location, Pair_uint32 *size, Pair_uint32 *offset) {
  for (uint32_t row = 0; row < size->y; ++row) {
    for (uint32_t col = 0; col < size->x; ++col) {

      uint32_t pixel_fb = Renderer_pixel_at_point(self, location.x + col, location.y + row);

      /* if ((self->frame_buffer[pixel_fb] | 0x00000000) == 0x00000000) { */

      uint32_t pixel_s = Surface_pixel_offset(&self->sheet, offset->x + col, offset->y + row);

      self->frame_buffer[pixel_fb] = self->sheet.pixels[pixel_s];
      /* self->frame_buffer[pixel_fb] = 0xFFFFFFFF; */
      /* } */
    }
  }
}

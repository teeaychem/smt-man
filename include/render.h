#pragma once

#include <stdint.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "constants.h"
#include "enums.h"
#include "generic/pairs.h"
#include "maze.h"
#include "render/palette.h"
#include "render/surface.h"

typedef struct renderer_t Renderer;
struct renderer_t {
  Surface sheet;
  Surface frame_buffer;

  SDL_Window *window;
  SDL_Renderer *renderer;
  SDL_Texture *texture;
};

void Renderer_create(Renderer *renderer, const Pair_uint8 maze_size, const char *sheet_path);

void Renderer_destroy(Renderer *self);

static inline uint32_t Renderer_buffer_index(const Renderer *self, uint32_t x, uint32_t y) {
  return (y * self->frame_buffer.size.x) + x;
}

void Renderer_render_frame_buffer(Renderer *self);

void Renderer_tile_fill(Renderer *self, const Pair_uint32 pos, uint32_t colour);

void Renderer_read_maze(Renderer *self, const Maze *maze);

void Renderer_draw_from_sheet(Renderer *self, Pair_uint32 destination, uint32_t size, Pair_uint32 source, Turn turn, Pallete pallete);

void Renderer_erase_from_sheet(Renderer *self, Pair_uint32 destination, uint32_t size, Pair_uint32 source, Turn turn, Pallete pallete);

void Renderer_tile_line(Renderer *self, uint32_t x, uint32_t y, Plane plane, uint32_t length, uint32_t colour);

// INVARIANT: The tile has an even number of pixels, and the origin is given by: (x += width/2, y += height/2).
void Renderer_tile_arc(Renderer *self, Pair_uint32 origin, uint32_t radius, Quadrant quadrant, uint32_t colour);

// Calculates the pixels to offset a render by in order for the render to be centred on a tile.
static inline uint32_t Renderer_centre_offset(uint32_t size) {
  // Cache a handful of common cases
  if (size == TILE_PIXELS * 2) {
    return TILE_PIXELS / 2;
  }
  if (size == TILE_PIXELS) {
    return 0;
  }

  return size > TILE_PIXELS ? (size - TILE_PIXELS) / 2 : 0;
}

static inline bool Renderer_u32_location_is_tile(Pair_uint32 location) {
  return location.x % TILE_PIXELS == 0 && location.y % TILE_PIXELS == 0;
}

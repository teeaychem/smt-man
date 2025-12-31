#pragma once

#include <stdint.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "constants.h"
#include "enums.h"
#include "generic/pairs.h"
#include "logic/situation.h"
#include "lyf/anima.h"
#include "lyf/persona.h"
#include "maze.h"
#include "render/palette.h"
#include "render/surface.h"

typedef struct renderer_t Renderer;
struct renderer_t {
  Surface sheet;
  Surface frame_buffer;
  Surface sprite_buffer;

  SDL_Window *window;
  SDL_Renderer *renderer;
  SDL_Texture *texture;
};

enum renderer_action_e {
  RENDER_DRAW,
  RENDER_ERASE,
};
typedef enum renderer_action_e RenderAction;

void Renderer_create(Renderer *renderer, const Pair_uint8 maze_size, const char *sheet_path);

void Renderer_drop(Renderer *self);

void Renderer_read_maze(Renderer *self, Maze *maze);

void Renderer_write_maze(Renderer *self, const Maze *maze);

void Renderer_render_frame_buffer(Renderer *self);

void Renderer_tile_fill(Renderer *self, const Pair_uint32 pos, const uint32_t colour);

void Renderer_draw_from_sheet(Renderer *self, const Pair_uint32 destination, const uint32_t size, const Pair_uint32 source, const Pallete pallete);

void Renderer_tile_line(Renderer *self, const uint32_t x, const uint32_t y, const Plane plane, const uint32_t length, const uint32_t colour);

// INVARIANT: The tile has an even number of pixels, and the origin is given by: (x += width/2, y += height/2).
void Renderer_tile_arc(Renderer *self, const Pair_uint32 origin, const uint32_t radius, const Quadrant quadrant, const uint32_t colour);

void Renderer_anima(Renderer *self, const Anima animas[ANIMA_COUNT], const uint8_t id, const RenderAction action);

void Renderer_persona(Renderer *self, const Persona *persona, const Situation *situation, const RenderAction action);

void Renderer_sprite_fill(Renderer *self, const Pair_uint32 location, const uint32_t size, const uint32_t colour);

void Renderer_draw_from_sprite_buffer(Renderer *self, const Pair_uint32 destination, const uint32_t size);

void Renderer_sprite_buffer_map_to(Renderer *self, const Pair_uint32 sprite_offset, const uint8_t size);

/// Static inline

/// Calculates the pixels to offset a render by in order for the render to be centred on a tile.
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

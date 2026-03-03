#pragma once

#include <stdint.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "SML/logic/situation.h"
#include "SML/maze.h"

#include "generic/pairs.h"
#include "render/palette.h"
#include "render/sprite.h"
#include "render/surface.h"
#include "sprite/anima.h"
#include "sprite/persona.h"

struct renderer_t {
  Surface sheet;
  Surface frame_buffer;
  Surface sprite_buffer;

  SDL_Window *window;
  SDL_Renderer *renderer;
  SDL_Texture *texture;
};
typedef struct renderer_t renderer_s;

enum renderer_action_t {
  RENDER_DRAW,
  RENDER_ERASE,
};
typedef enum renderer_action_t renderer_action_e;

void renderer_ctor(renderer_s *renderer, const Pair_uint8 maze_size, const char *sheet_path);

void renderer_dtor(renderer_s *self);

void renderer_clear(renderer_s *self);

void renderer_anima(renderer_s *self, const anima_s *anima, const situation_s *situation, Sprite *sprite, const renderer_action_e action);

void renderer_draw_from_sprite_buffer(renderer_s *self, const Pair_uint32 destination, const uint32_t size);

void renderer_draw_maze(renderer_s *self, const maze_s *maze);

void renderer_drawn_from_sheet(renderer_s *self, const Pair_uint32 destination, const uint32_t size, const Pair_uint32 source, const Pallete pallete);

void renderer_persona(renderer_s *self, const persona_s *persona, Sprite *sprite, const situation_s *situation, const renderer_action_e action);

void renderer_render_frame_buffer(renderer_s *self);

void renderer_sprite_buffer_map_to(renderer_s *self, const Pair_uint32 sprite_offset, const uint8_t size);

void renderer_sprite_fill(renderer_s *self, const Pair_uint32 location, const uint32_t size, const uint32_t colour, const bool edge);

/// Static inline

/// Calculates the pixels to offset a render by in order for the render to be centred on a tile.
static inline uint32_t renderer_centre_offset(uint32_t size) {
  // Cache a handful of common cases
  if (size == TILE_PIXELS * 2) {
    return TILE_PIXELS / 2;
  }
  if (size == TILE_PIXELS) {
    return 0;
  }

  return size > TILE_PIXELS ? (size - TILE_PIXELS) / 2 : 0;
}

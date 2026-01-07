#pragma once

#include <stdint.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "constants.h"
#include "generic/pairs.h"
#include "logic/situation.h"
#include "maze.h"
#include "render/palette.h"
#include "render/sprite.h"
#include "render/surface.h"
#include "sprites/anima.h"
#include "sprites/persona.h"

constexpr uint32_t FPS = 60;

constexpr uint64_t NS_PER_FRAME = 1000000000 / FPS;

/* constexpr int32_t TILE_PIXELS = 8; */

constexpr int UI_SCALE = 4;

constexpr uint32_t SPRITE_BUFFER_SIZE = TILE_PIXELS * 4;

constexpr uint32_t RENDER_TOP = 3;

constexpr uint32_t RENDER_BOT = 2;

constexpr uint32_t MAZE_INDENT = TILE_PIXELS / 2;

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

void Renderer_draw_maze(Renderer *self, const Maze *maze);

void Renderer_render_frame_buffer(Renderer *self);

void Renderer_draw_from_sheet(Renderer *self, const Pair_uint32 destination, const uint32_t size, const Pair_uint32 source, const Pallete pallete);

void Renderer_anima(Renderer *self, const Anima *anima, Sprite *sprite, const RenderAction action);

void Renderer_persona(Renderer *self, const Persona *persona, Sprite *sprite, const Situation *situation, const RenderAction action);

void Renderer_sprite_fill(Renderer *self, const Pair_uint32 location, const uint32_t size, const uint32_t colour, const bool edge);

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

#pragma once

#include <SDL3/SDL_events.h>

#include "consts.h"
#include "generic/pairs.h"
#include "maze.h"
#include "sprites/anima.h"
#include "sprites/persona.h"
#include <stdatomic.h>
#include <stdint.h>

constexpr int32_t SPRITE_VELOCITY = 1;

struct sprite_t {
  /// Size of the associated sprite, as a square
  uint8_t size;
  /// Location of the sprite sprite
  Pair_uint32 location;
};
typedef struct sprite_t Sprite;

struct sprites_t {
  size_t anima_count;
  Sprite *animas;
  Sprite persona;
};
typedef struct sprites_t Sprites;

/// Methods

static inline void Sprite_init(Sprite *self, const uint8_t sprite_size, const Pair_uint8 location, uint32_t offset_n) {
  self->size = sprite_size,
  self->location = (Pair_uint32){.x = ((uint32_t)(location.x)) * TILE_PIXELS,
                                 .y = ((uint32_t)location.y + offset_n) * TILE_PIXELS};
}

static inline bool Sprite_is_centered_on_tile(Pair_uint32 location, uint32_t tile_pixels) {
  return location.x % tile_pixels == 0 && location.y % tile_pixels == 0;
}

static inline Pair_uint8 Sprite_location_to_abstract(const Pair_uint32 *sprite_location, uint32_t tile_pixels, uint32_t offset_n) {

  uint32_t x_mod = sprite_location->x % tile_pixels;
  uint32_t y_mod = sprite_location->y % tile_pixels;

  Pair_uint8 maze_location = {};

  if (x_mod < tile_pixels / 2) {
    maze_location.x = (uint8_t)((sprite_location->x - x_mod) / tile_pixels);
  } else {
    maze_location.x = (uint8_t)((sprite_location->x + (tile_pixels - x_mod)) / tile_pixels);
  }

  if (y_mod < tile_pixels / 2) {
    maze_location.y = (uint8_t)((sprite_location->y - y_mod) / tile_pixels);
  } else {
    maze_location.y = (uint8_t)((sprite_location->y + (tile_pixels - y_mod)) / tile_pixels);
  }

  maze_location.y -= offset_n;

  return maze_location;
}

/// Rendering related sprite methods

/// Anima

void Anima_on_tile(Anima *self, Sprite *sprite, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n);

void Anima_on_frame(Anima *self, Sprite *sprite, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n);

void Anima_handle_event(Anima *self, const SDL_Event *event);

/// Persona

void Persona_on_tile(Persona *self, Sprite *sprite, Situation *situation, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n);

void Persona_off_tile(Persona *self, Sprite *sprite, Situation *situation, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n);

void Persona_on_frame(Persona *self, Sprite *sprite, const Maze *maze, Situation *situation, uint32_t tile_pixels, uint32_t offset_n);

void Persona_handle_event(Persona *self, const Maze *maze, Situation *situation, const SDL_Event *event);

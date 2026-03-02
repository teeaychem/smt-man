#pragma once

#include <stdatomic.h>
#include <stdint.h>

#include <SDL3/SDL_events.h>

#include "SML/maze.h"



#include "consts.h"
#include "generic/pairs.h"
#include "sprite/anima.h"
#include "sprite/persona.h"

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

static inline void Sprite_init(Sprite *self, const uint8_t sprite_size, const Pair_uint8 maze_location, uint32_t offset) {
  self->size = sprite_size,
  self->location = (Pair_uint32){
      .x = (((uint32_t)maze_location.x) + offset) * TILE_PIXELS,
      .y = (uint32_t)maze_location.y * TILE_PIXELS,
  };
}

static inline bool Sprite_is_centered_on_tile(Pair_uint32 location, uint32_t tile_pixels) {
  return location.x % tile_pixels == 0 && location.y % tile_pixels == 0;
}

static inline Pair_uint8 Sprite_maze_location(const Pair_uint32 *sprite_location, uint32_t tile_pixels, uint32_t offset_n) {

  uint32_t x_mod = sprite_location->x % tile_pixels;

  Pair_uint8 maze_location = {};

  { // x
    if (x_mod < tile_pixels / 2) {
      maze_location.x = (uint8_t)((sprite_location->x - x_mod) / tile_pixels);
    } else {
      maze_location.x = (uint8_t)((sprite_location->x + (tile_pixels - x_mod)) / tile_pixels);
    }
    maze_location.x -= offset_n;
  }

  { // y
    uint32_t y_mod = sprite_location->y % tile_pixels;
    if (y_mod < tile_pixels / 2) {
      maze_location.y = (uint8_t)((sprite_location->y - y_mod) / tile_pixels);
    } else {
      maze_location.y = (uint8_t)((sprite_location->y + (tile_pixels - y_mod)) / tile_pixels);
    }
  }

  return maze_location;
}

/// Rendering related sprite methods

/// Anima

void anima_on_frame(anima_s *self, Sprite *sprite, const maze_s *maze, uint32_t tile_pixels, uint32_t offset_n);

void anima_handle_event(anima_s *self, const SDL_Event *event);

/// Persona

void persona_on_frame(persona_s *self, Sprite *sprite, const maze_s *maze, Situation *situation, uint32_t tile_pixels, uint32_t offset_n);

void persona_handle_event(persona_s *self, Situation *situation, const SDL_Event *event);

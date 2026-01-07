#pragma once

#include <stdint.h>

#include "constants.h"
#include "generic/pairs.h"

static inline bool Sprite_is_centered_on_tile(Pair_uint32 location) {
  return location.x % TILE_PIXELS == 0 && location.y % TILE_PIXELS == 0;
}

static inline Pair_uint8 Sprite_location_to_abstract(const Pair_uint32 *sprite_location) {

  uint32_t x_mod = sprite_location->x % TILE_PIXELS;
  uint32_t y_mod = sprite_location->y % TILE_PIXELS;

  Pair_uint8 maze_location = {};

  if (x_mod < TILE_PIXELS / 2) {
    maze_location.x = (uint8_t)((sprite_location->x - x_mod) / TILE_PIXELS);
  } else {
    maze_location.x = (uint8_t)((sprite_location->x + (TILE_PIXELS - x_mod)) / TILE_PIXELS);
  }

  if (y_mod < TILE_PIXELS / 2) {
    maze_location.y = (uint8_t)((sprite_location->y - y_mod) / TILE_PIXELS);
  } else {
    maze_location.y = (uint8_t)((sprite_location->y + (TILE_PIXELS - y_mod)) / TILE_PIXELS);
  }

  maze_location.y -= RENDER_TOP;

  return maze_location;
}

#pragma once

#include <stdint.h>

#include "generic/pairs.h"

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

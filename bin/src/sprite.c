
#include "render/sprite.h"
#include "consts.h"

void sprite_ctor(sprite_s *self, const uint8_t sprite_size, const Pair_uint8 maze_location) {

  *self = (sprite_s){
      .size = sprite_size,
      .location = {
          .x = (((uint32_t)maze_location.x) + RENDER_TOP) * TILE_PIXELS,
          .y = (uint32_t)maze_location.y * TILE_PIXELS,
      },
  };
}

bool sprite_is_centered_on_tile(Pair_uint32 location, uint32_t tile_pixels) {
  return location.x % tile_pixels == 0 && location.y % tile_pixels == 0;
}

Pair_uint8 sprite_maze_location(const Pair_uint32 *sprite_location, uint32_t tile_pixels, uint32_t offset_n) {

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

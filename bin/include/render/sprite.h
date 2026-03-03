#pragma once

#include <stdatomic.h>
#include <stdint.h>

#include <SDL3/SDL_events.h>

#include "generic/pairs.h"

constexpr int32_t SPRITE_FRAME_VELOCITY = 1;

struct sprite_t {
  /// Size of the associated sprite, as a square
  uint8_t size;
  /// Location of the sprite sprite
  Pair_uint32 location;
};
typedef struct sprite_t sprite_s;

/// Methods

void sprite_ctor(sprite_s *self, const uint8_t sprite_size, const Pair_uint8 maze_location, uint32_t offset);

bool sprite_is_centered_on_tile(Pair_uint32 location, uint32_t tile_pixels);

Pair_uint8 sprite_maze_location(const Pair_uint32 *sprite_location, uint32_t tile_pixels, uint32_t offset_n);

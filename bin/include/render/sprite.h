#pragma once

#include "constants.h"
#include "generic/bitvec.h"
#include "generic/pairs.h"
#include "sprites/anima.h"
#include "sprites/persona.h"
#include "sprites/sprite.h"
#include <stdatomic.h>
#include <stdint.h>

struct sprite_t {
  /// Size of the associated sprite, as a square
  uint8_t sprite_size;
  /// Location of the sprite sprite
  Pair_uint32 sprite_location;
};
typedef struct sprite_t Sprite;

struct sprites_t {
  Sprite anima[ANIMA_COUNT];
  Sprite persona;
};
typedef struct sprites_t Sprites;

static inline void Sprite_init(Sprite *self, const uint8_t sprite_size, const Pair_uint8 location, uint32_t offset_n) {
  self->sprite_size = sprite_size,
  self->sprite_location = (Pair_uint32){.x = ((uint32_t)(location.x)) * TILE_PIXELS,
                                        .y = ((uint32_t)location.y + offset_n) * TILE_PIXELS};
}

static inline bool Sprite_is_centered_on_tile(Pair_uint32 location, uint32_t tile_pixels) {
  return location.x % tile_pixels == 0 && location.y % tile_pixels == 0;
}

static inline void Anima_on_tile(Anima *self, Sprite *sprite, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n) {

  Pair_uint8 location = Sprite_location_to_abstract(&sprite->sprite_location, tile_pixels, offset_n);
  /// Update location
  atomic_store(&self->mind.view.anima[self->id].location, location);

  /// Update direction
  if (Maze_tile_in_direction_is_path(maze, location, self->mind.direction_intent)) {
    atomic_store(&self->mind.view.anima[self->id].direction_actual, self->mind.direction_intent);
  } else {
    atomic_store(&self->mind.view.anima[self->id].direction_actual, DIRECTION_NONE);
  }
}

static inline void Anima_on_frame(Anima *self, Sprite *sprite, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n) {

  uint32_t movement = atomic_load(&self->mind.view.anima[self->id].movement_pattern);
  movement = uint32_rotl1(movement);
  atomic_store(&self->mind.view.anima[self->id].movement_pattern, movement);

  if ((movement & 0x10000000) == 0) {
    return;
  }

  self->tick_action += 1;

  // Ensure coherence
  Anima_instinct(self);

  if (Sprite_is_centered_on_tile(sprite->sprite_location, tile_pixels)) {
    Anima_on_tile(self, sprite, maze, tile_pixels, offset_n);
  }

  switch (atomic_load(&self->mind.view.anima[self->id].direction_actual)) {
  case DIRECTION_NONE: {
    // Do nothing
  } break;
  case DIRECTION_N: {
    sprite->sprite_location.y -= SPRITE_VELOCITY;
  } break;
  case DIRECTION_E: {
    sprite->sprite_location.x += SPRITE_VELOCITY;
  } break;
  case DIRECTION_S: {
    sprite->sprite_location.y += SPRITE_VELOCITY;
  } break;
  case DIRECTION_W: {
    sprite->sprite_location.x -= SPRITE_VELOCITY;
  } break;
  }
}

static inline void Persona_on_tile(Persona *self, Sprite *sprite, Situation *situation, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n) {

  Pair_uint8 location = Sprite_location_to_abstract(&sprite->sprite_location, tile_pixels, offset_n);
  /// Update location
  atomic_store(&situation->persona.location, location);

  /// Update direction
  if (Maze_tile_in_direction_is_path(maze, location, self->direction_intent)) {
    atomic_store(&situation->persona.direction_actual, self->direction_intent);
  } else if (Maze_tile_in_direction_is_path(maze, location, situation->persona.direction_actual)) {
    // Keep current direction.
  } else {
    atomic_store(&situation->persona.direction_actual, DIRECTION_NONE);
  }
}

static inline void Persona_off_tile(Persona *self, Sprite *sprite, Situation *situation, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n) {

  Pair_uint8 location = Sprite_location_to_abstract(&sprite->sprite_location, tile_pixels, offset_n);

  if ((self->direction_intent | situation->persona.direction_actual) == (DIRECTION_E | DIRECTION_W) ||
      (self->direction_intent | situation->persona.direction_actual) == (DIRECTION_S | DIRECTION_N)) {
    /// Update direction
    if (Maze_tile_in_direction_is_path(maze, location, self->direction_intent)) {
      atomic_store(&situation->persona.direction_actual, self->direction_intent);
    } else if (Maze_tile_in_direction_is_path(maze, location, situation->persona.direction_actual)) {
      // Keep current direction.
    } else {
      atomic_store(&situation->persona.direction_actual, DIRECTION_NONE);
    }
  }
}

static inline void Persona_on_frame(Persona *self, Sprite *sprite, const Maze *maze, Situation *situation, uint32_t tile_pixels, uint32_t offset_n) {

  uint32_t movement = atomic_load(&situation->persona.movement_pattern);
  movement = uint32_rotl1(movement);
  atomic_store(&situation->persona.movement_pattern, movement);

  if ((movement & 0x10000000) == 0) {
    return;
  }

  self->tick_action += 1;

  if (Sprite_is_centered_on_tile(sprite->sprite_location, tile_pixels)) {
    Persona_on_tile(self, sprite, situation, maze, tile_pixels, offset_n);
  } else {
    Persona_off_tile(self, sprite, situation, maze, tile_pixels, offset_n);
  }

  switch (atomic_load(&situation->persona.direction_actual)) {
  case DIRECTION_NONE: {
    // Do nothing
  } break;
  case DIRECTION_N: {
    sprite->sprite_location.y -= SPRITE_VELOCITY;
  } break;
  case DIRECTION_E: {
    sprite->sprite_location.x += SPRITE_VELOCITY;
  } break;
  case DIRECTION_S: {
    sprite->sprite_location.y += SPRITE_VELOCITY;
  } break;
  case DIRECTION_W: {
    sprite->sprite_location.x -= SPRITE_VELOCITY;
  } break;
  }
}

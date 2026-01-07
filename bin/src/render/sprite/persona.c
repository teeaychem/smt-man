#include "generic/bitvec.h"
#include "render/sprite.h"

void Persona_on_tile(Persona *self, Sprite *sprite, Situation *situation, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n) {

  Pair_uint8 location = Sprite_location_to_abstract(&sprite->location, tile_pixels, offset_n);
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

void Persona_off_tile(Persona *self, Sprite *sprite, Situation *situation, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n) {

  Pair_uint8 location = Sprite_location_to_abstract(&sprite->location, tile_pixels, offset_n);

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

void Persona_on_frame(Persona *self, Sprite *sprite, const Maze *maze, Situation *situation, uint32_t tile_pixels, uint32_t offset_n) {

  uint32_t movement = atomic_load(&situation->persona.movement_pattern);
  movement = uint32_rotl1(movement);
  atomic_store(&situation->persona.movement_pattern, movement);

  if ((movement & 0x10000000) == 0) {
    return;
  }

  self->tick_action += 1;

  if (Sprite_is_centered_on_tile(sprite->location, tile_pixels)) {
    Persona_on_tile(self, sprite, situation, maze, tile_pixels, offset_n);
  } else {
    Persona_off_tile(self, sprite, situation, maze, tile_pixels, offset_n);
  }

  switch (atomic_load(&situation->persona.direction_actual)) {
  case DIRECTION_NONE: {
    // Do nothing
  } break;
  case DIRECTION_N: {
    sprite->location.y -= SPRITE_VELOCITY;
  } break;
  case DIRECTION_E: {
    sprite->location.x += SPRITE_VELOCITY;
  } break;
  case DIRECTION_S: {
    sprite->location.y += SPRITE_VELOCITY;
  } break;
  case DIRECTION_W: {
    sprite->location.x -= SPRITE_VELOCITY;
  } break;
  }
}

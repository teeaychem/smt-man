#include "generic/bitvec.h"

#include "render/sprite.h"

void Anima_on_tile(Anima *self, Sprite *sprite, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n) {

  Pair_uint8 location = Sprite_location_to_abstract(&sprite->location, tile_pixels, offset_n);
  /// Update location
  atomic_store(&self->situation.animas[self->id].location, location);

  /// Update direction
  if (Maze_tile_in_direction_is_path(maze, location, self->direction_intent)) {
    atomic_store(&self->situation.animas[self->id].direction_actual, self->direction_intent);
  } else {
    atomic_store(&self->situation.animas[self->id].direction_actual, DIRECTION_NONE);
  }
}

void Anima_on_frame(Anima *self, Sprite *sprite, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n) {

  uint32_t movement = atomic_load(&self->situation.animas[self->id].movement_pattern);
  movement = uint32_rotl1(movement);
  atomic_store(&self->situation.animas[self->id].movement_pattern, movement);

  if ((movement & 0x10000000) == 0) {
    return;
  }

  self->tick_action += 1;

  // Ensure coherence
  Anima_instinct(self);

  if (Sprite_is_centered_on_tile(sprite->location, tile_pixels)) {
    Anima_on_tile(self, sprite, maze, tile_pixels, offset_n);
  }

  switch (atomic_load(&self->situation.animas[self->id].direction_actual)) {
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

void Anima_handle_event(Anima *self, const SDL_Event *event) {
  assert(self != nullptr && event != nullptr);
}

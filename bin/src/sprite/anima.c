#include "generic/bitvec.h"

#include "random.h"
#include "render/sprite.h"

void Anima_on_tile(Anima *self, Sprite *sprite, const Maze *maze, Pair_uint8 maze_location) {

  /// Update location
  atomic_store(&self->smt.situation.animas[self->id].location, maze_location);
}

void Anima_update_direction(Anima *self, const Maze *maze, Pair_uint8 maze_location) {

  /// Update direction
}

void Anima_on_frame(Anima *self, Sprite *sprite, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n) {

  uint32_t movement = atomic_load(&self->smt.situation.animas[self->id].movement_pattern);
  movement = uint32_rotl1(movement);
  atomic_store(&self->smt.situation.animas[self->id].movement_pattern, movement);

  if ((movement & 0x10000000) == 0) {
    return;
  }

  self->tick_action += 1;

  // Ensure coherence
  Anima_instinct(self);

  if (Sprite_is_centered_on_tile(sprite->location, tile_pixels)) {
    Pair_uint8 maze_location = Sprite_maze_location(&sprite->location, tile_pixels, offset_n);

    Anima_on_tile(self, sprite, maze, maze_location);

    if (Maze_is_intersection(maze, maze_location.x, maze_location.y)) {
      atomic_store(&self->smt.situation.animas[self->id].direction_actual, self->direction_intent);
    }

    if (atomic_load(&self->smt.situation.animas[self->id].direction_actual) == CARDINAL_NONE) {
      int random_c = random_in_range(0, 4);
      switch (random_c) {
      case 0: {
        atomic_store(&self->smt.situation.animas[self->id].direction_actual, CARDINAL_N);
      } break;
      case 1: {
        atomic_store(&self->smt.situation.animas[self->id].direction_actual, CARDINAL_E);
      } break;
      case 2: {
        atomic_store(&self->smt.situation.animas[self->id].direction_actual, CARDINAL_S);
      } break;
      case 3: {
        atomic_store(&self->smt.situation.animas[self->id].direction_actual, CARDINAL_W);
      } break;
      default: {
      };
      }
    }

    if (!Maze_tile_in_direction_is_path(maze, maze_location, self->direction_intent)) {

      atomic_store(&self->smt.situation.animas[self->id].direction_actual, CARDINAL_NONE);
    }

    Anima_update_direction(self, maze, maze_location);
  }

  switch (atomic_load(&self->smt.situation.animas[self->id].direction_actual)) {
  case CARDINAL_NONE: {
    // Do nothing
  } break;
  case CARDINAL_N: {
    sprite->location.y -= SPRITE_VELOCITY;
  } break;
  case CARDINAL_E: {
    sprite->location.x += SPRITE_VELOCITY;
  } break;
  case CARDINAL_S: {
    sprite->location.y += SPRITE_VELOCITY;
  } break;
  case CARDINAL_W: {
    sprite->location.x -= SPRITE_VELOCITY;
  } break;
  }
}

void Anima_handle_event(Anima *self, const SDL_Event *event) {
  assert(self != nullptr && event != nullptr);
}

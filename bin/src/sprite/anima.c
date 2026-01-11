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

    pthread_mutex_lock(&self->path.mutex);

    Z3_ast path_tile = MazePath_at(&self->path, maze_location);
    Cardinal direction_actual = atomic_load(&self->smt.situation.animas[self->id].direction_actual);

    if (Maze_is_intersection(maze, maze_location.x, maze_location.y)) {
      if (self->smt.language.path.token.o_n == path_tile) {
        self->direction_intent = CARDINAL_N;
        printf("\tON");
      } else if (self->smt.language.path.token.o_e == path_tile) {
        self->direction_intent = CARDINAL_E;
        printf("\tOE");
      } else if (self->smt.language.path.token.o_s == path_tile) {
        self->direction_intent = CARDINAL_S;
        printf("\tOS");
      } else if (self->smt.language.path.token.o_w == path_tile) {
        self->direction_intent = CARDINAL_W;
        printf("\tOW");
      }

      else if (self->smt.language.path.token.n_s == path_tile) {
        printf("\tNS");
        // Continue in same direction
      } else if (self->smt.language.path.token.e_w == path_tile) {
        printf("\tEW");
        // Continue in same direction
      }

      else if (self->smt.language.path.token.n_e == path_tile) {
        printf("\tNE");
        if (direction_actual == CARDINAL_S) {
          direction_actual = CARDINAL_E;
        } else {
          direction_actual = CARDINAL_N;
        }
      } else if (self->smt.language.path.token.s_e == path_tile) {
        printf("\tSE");
        if (direction_actual == CARDINAL_N) {
          direction_actual = CARDINAL_E;
        } else {
          direction_actual = CARDINAL_S;
        }
      } else if (self->smt.language.path.token.s_w == path_tile) {
        printf("\tSW");
        if (direction_actual == CARDINAL_N) {
          direction_actual = CARDINAL_W;
        } else {
          direction_actual = CARDINAL_S;
        }
      } else if (self->smt.language.path.token.n_w == path_tile) {
        printf("\tNW");
        if (direction_actual == CARDINAL_S) {
          direction_actual = CARDINAL_W;
        } else {
          direction_actual = CARDINAL_N;
        }
      }

      else if (self->smt.language.path.token.x_x == path_tile) {
        printf("Anima %d is not on a path!\n", self->id);
      }

      else {
        printf("Anima %d is not on a path!\n", self->id);
      }

      atomic_store(&self->smt.situation.animas[self->id].direction_actual, direction_actual);

      MazePath_display(&self->path, &self->smt.language);
      printf("Direction: ");
      Cardinal_print(direction_actual);
      printf("\n");
      printf("Anima @ %dx%d\n", maze_location.x, maze_location.y);
      /* getc(stdin); */

      pthread_mutex_unlock(&self->path.mutex);
    }

    if (direction_actual == CARDINAL_NONE || !Maze_tile_in_direction_is_path(maze, maze_location, direction_actual)) {
      int random_c = random_in_range(0, 4);
      switch (random_c) {
      case 0: {
        direction_actual = CARDINAL_N;
      } break;
      case 1: {
        direction_actual = CARDINAL_E;
      } break;
      case 2: {
        direction_actual = CARDINAL_S;
      } break;
      case 3: {
        direction_actual = CARDINAL_W;
      } break;
      default: {
      };
      }
    }

    atomic_store(&self->smt.situation.animas[self->id].direction_actual, direction_actual);

    // TODO: Empty fn
    /* Anima_update_direction(self, maze, maze_location); */
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

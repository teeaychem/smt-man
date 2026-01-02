#include <stdatomic.h>
#include <stdint.h>

#include "enums.h"
#include "generic/bitvec.h"
#include "generic/pairs.h"
#include "logic.h"
#include "lyf/anima.h"
#include "maze.h"
#include "render.h"

void Anima_default(Anima *anima, const uint8_t id, const uint8_t sprite_size, const Pair_uint8 location, const Direction direction) {
  g_log(nullptr, G_LOG_LEVEL_INFO, "Creating anima: %d", id);

  *anima = (Anima){
      .id = id,

      .sprite_size = sprite_size,
      .sprite_location = {.x = ((uint32_t)(location.x)) * TILE_PIXELS,
                          .y = ((uint32_t)location.y + RENDER_TOP) * TILE_PIXELS},

      .tick_action = 0,

      .contact = {
          .cond_resume = PTHREAD_COND_INITIALIZER,
          .mtx_suspend = PTHREAD_MUTEX_INITIALIZER,
      },

      .mind = {},
  };

  Mind_default(&anima->mind, id, location, direction);

  atomic_init(&anima->contact.flag_suspend, false);
}

void Anima_destroy(Anima *self) {
  assert(self != nullptr);
}

void Anima_handle_event(Anima *self, const SDL_Event *event) {
  assert(self != nullptr && event != nullptr);
}

void Anima_on_frame(Anima *self, const Maze *maze) {

  uint32_t movement = atomic_load(&self->mind.view.anima[self->id].movement_pattern);
  movement = uint32_rotl1(movement);
  atomic_store(&self->mind.view.anima[self->id].movement_pattern, movement);

  if ((movement & 0x10000000) == 0) {
    return;
  }

  self->tick_action += 1;

  // Ensure coherence
  Anima_instinct(self);

  if (Sprite_is_centered_on_tile(self->sprite_location)) {
    Anima_on_tile(self, maze);
  }

  switch (atomic_load(&self->mind.view.anima[self->id].direction_actual)) {
  case DIRECTION_NONE: {
    // Do nothing
  } break;
  case DIRECTION_N: {
    self->sprite_location.y -= SPRITE_VELOCITY;
  } break;
  case DIRECTION_E: {
    self->sprite_location.x += SPRITE_VELOCITY;
  } break;
  case DIRECTION_S: {
    self->sprite_location.y += SPRITE_VELOCITY;
  } break;
  case DIRECTION_W: {
    self->sprite_location.x -= SPRITE_VELOCITY;
  } break;
  }
}

void Anima_on_tile(Anima *self, const Maze *maze) {

  Pair_uint8 location = Sprite_location_to_abstract(&self->sprite_location);
  /// Update location
  atomic_store(&self->mind.view.anima[self->id].location, location);

  /// Update direction
  if (Maze_tile_in_direction_is_path(maze, location, self->mind.direction_intent)) {
    atomic_store(&self->mind.view.anima[self->id].direction_actual, self->mind.direction_intent);
  } else {
    atomic_store(&self->mind.view.anima[self->id].direction_actual, DIRECTION_NONE);
  }
}

void Anima_instinct(Anima *self) {
  assert(self != nullptr);
}

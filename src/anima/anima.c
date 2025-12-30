#include <stdatomic.h>
#include <stdint.h>

#include "enums.h"
#include "generic/bitvec.h"
#include "generic/pairs.h"
#include "logic.h"
#include "lyf/anima.h"
#include "maze.h"
#include "render.h"

void Anima_default(Anima *anima, uint8_t id, uint8_t sprite_size, Pair_uint8 location, Direction direction) {
  g_log(nullptr, G_LOG_LEVEL_INFO, "Creating anima: %d", id);

  Z3_context ctx = z3_mk_anima_ctx();
  Z3_optimize optimizer = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, optimizer);

  *anima = (Anima){
      .id = id,

      .sprite_size = sprite_size,
      .sprite_location = {.x = ((uint32_t)location.x) * TILE_PIXELS,
                          .y = ((uint32_t)location.y) * TILE_PIXELS},

      .tick_action = 0,

      .contact = {
          .cond_resume = PTHREAD_COND_INITIALIZER,
          .mtx_suspend = PTHREAD_MUTEX_INITIALIZER,
      },

      .mind = {
          .ctx = ctx,
          .solver = optimizer,
          .lang = {},
          .view = {},
      },
  };

  Mind_default(&anima->mind, id, location, direction);

  atomic_init(&anima->contact.flag_suspend, false);
}

void Anima_destroy(Anima *self) {
  assert(self != nullptr);
}

void Anima_handle_event(Anima *self, SDL_Event *event) {
  assert(self != nullptr && event != nullptr);
}

void Anima_on_frame(Anima *self, Maze *maze) {

  uint32_t movement = atomic_load(&self->mind.view.anima[self->id].movement_pattern);
  movement = uint32_rotl1(movement);
  atomic_store(&self->mind.view.anima[self->id].movement_pattern, movement);

  if ((movement & 0x10000000) == 0) {
    return;
  }

  self->tick_action += 1;

  // Ensure coherence
  Anima_instinct(self);

  if (Renderer_u32_location_is_tile(self->sprite_location)) {
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

void Anima_on_tile(Anima *self, Maze *maze) {

  Pair_uint8 location = Maze_location_from_sprite(&self->sprite_location);
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

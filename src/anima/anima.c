#include <stdatomic.h>
#include <stdint.h>

#include "enums.h"
#include "generic/bitvec.h"
#include "generic/pairs.h"
#include "logic.h"
#include "lyf/anima.h"
#include "maze.h"

void Anima_default(Anima *anima, uint8_t id, uint8_t scale, Pair_uint8 location, Direction direction) {
  g_log(nullptr, G_LOG_LEVEL_INFO, "Creating anima: %d", id);

  Z3_context ctx = z3_mk_anima_ctx();
  Z3_optimize optimizer = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, optimizer);

  *anima = (Anima){
      .id = id,
      .pixel_size = scale,
      .tick.actions = 0,
      .momentum = direction,

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

  if (event->type == SDL_EVENT_KEY_DOWN && !event->key.repeat) {

    switch (event->key.key) {
    case SDLK_UP: {
      atomic_store(&self->mind.view.anima[self->id].intent, NORTH);
    } break;
    case SDLK_DOWN: {
      atomic_store(&self->mind.view.anima[self->id].intent, SOUTH);
    } break;
    case SDLK_LEFT: {
      atomic_store(&self->mind.view.anima[self->id].intent, WEST);
    } break;
    case SDLK_RIGHT: {
      atomic_store(&self->mind.view.anima[self->id].intent, EAST);
    } break;
    }
  }
}

void Anima_sync_abstract(Anima *self, Maze *maze, Pair_uint32 *sprite_location) {
  /// Scale sprite location
  Pair_uint8 location = {.x = (uint8_t)(sprite_location->x / TILE_PIXELS),
                         .y = (uint8_t)(sprite_location->y / TILE_PIXELS)};

  Direction intent = atomic_load(&self->mind.view.anima[self->id].intent);
  uint8_t velocity = atomic_load(&self->mind.view.anima[self->id].velocity);

  bool intent_ok = false;
  switch (intent) {
  case NORTH: {
    intent_ok = (location.y != Maze_first_row(maze)) && Maze_abstract_is_path(maze, location.x, location.y - 1);
  } break;
  case EAST: {
    intent_ok = (location.x + 2 < maze->size.x) && Maze_abstract_is_path(maze, location.x + 1, location.y);
  } break;
  case SOUTH: {
    intent_ok = (location.y != Maze_last_row(maze)) && Maze_abstract_is_path(maze, location.x, location.y + 1);
  } break;
  case WEST: {
    intent_ok = (0 < location.x) && Maze_abstract_is_path(maze, location.x - 1, location.y);
  } break;
  }

  if (intent_ok) {
    velocity = 1;
  } else {
    velocity = 0;
  }

  { // Store block
    self->momentum = intent;
    atomic_store(&self->mind.view.anima[self->id].momentum, intent);
    atomic_store(&self->mind.view.anima[self->id].velocity, velocity);
    atomic_store(&self->mind.view.anima[self->id].location, location);
  }
}

void Anima_on_frame(Anima *self, Maze *maze, Pair_uint32 *sprite_location) {

  uint32_t movement = atomic_load(&self->mind.view.anima[self->id].movement);
  movement = uint32_rotl1(movement);
  atomic_store(&self->mind.view.anima[self->id].movement, movement);

  if ((movement & 0x10000000) == 0) {
    return;
  }

  self->tick.actions += 1;

  bool centred = sprite_location->x % TILE_PIXELS == 0 && sprite_location->y % TILE_PIXELS == 0;

  // Ensure coherence
  Anima_instinct(self);

  if (centred) {
    Anima_sync_abstract(self, maze, sprite_location);
  }

  uint8_t velocity = atomic_load(&self->mind.view.anima[self->id].velocity);
  auto momentum = atomic_load(&self->mind.view.anima[self->id].momentum);

  switch (momentum) {
  case NORTH: {
    sprite_location->y -= velocity;
  } break;
  case EAST: {
    sprite_location->x += velocity;
  } break;
  case SOUTH: {
    sprite_location->y += velocity;
  } break;
  case WEST: {
    sprite_location->x -= velocity;
  } break;
  }

  atomic_store(&self->mind.view.anima[self->id].velocity, velocity);
}

void Anima_instinct(Anima *self) {
  assert(self != nullptr);
}

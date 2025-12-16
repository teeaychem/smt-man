#include <stdatomic.h>
#include <stdint.h>

#include "anima.h"
#include "generic/pairs.h"
#include "logic.h"
#include "maze.h"
#include "utils.h"

void Anima_default(Anima *anima, uint8_t id, uint8_t scale, Pair_uint8 location, Direction direction) {
  g_log(nullptr, G_LOG_LEVEL_INFO, "Creating anima: %d", id);

  Z3_context ctx = z3_mk_anima_ctx();
  Z3_optimize optimizer = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, optimizer);

  *anima = (Anima){
      .id = id,
      .scale = scale,
      .tick = 0,
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
      atomic_store(&self->mind.view.anima[self->id].intent, UP);
    } break;
    case SDLK_DOWN: {
      atomic_store(&self->mind.view.anima[self->id].intent, DOWN);
    } break;
    case SDLK_LEFT: {
      atomic_store(&self->mind.view.anima[self->id].intent, LEFT);
    } break;
    case SDLK_RIGHT: {
      atomic_store(&self->mind.view.anima[self->id].intent, RIGHT);
    } break;
    }
  }
}

void Anima_sync_abstract(Anima *self, Maze *maze) {
  Pair_uint8 abstract_location = atomic_load(&self->mind.view.anima[self->id].location);

  Direction intent = atomic_load(&self->mind.view.anima[self->id].intent);
  atomic_store(&self->mind.view.anima[self->id].momentum, intent);
  self->momentum = intent;

  Pair_uint8 destination = steps_in_direction(&abstract_location, intent, 1);

  bool path_ok = Maze_abstract_is_path(maze, destination.x, destination.y);

  uint8_t velocity = atomic_load(&self->mind.view.anima[self->id].velocity);
  if (path_ok) {
    velocity = 1;
  } else {
    velocity = 0;
  }
  atomic_store(&self->mind.view.anima[self->id].velocity, velocity);

  switch (atomic_load(&self->mind.view.anima[self->id].momentum)) {
  case UP: {
    abstract_location.y -= velocity;
  } break;
  case RIGHT: {
    abstract_location.x += velocity;
  } break;
  case DOWN: {
    abstract_location.y += velocity;
  } break;
  case LEFT: {
    abstract_location.x -= velocity;
  } break;
  }

  atomic_store(&self->mind.view.anima[self->id].location, abstract_location);
}

void Anima_on_frame(Anima *self, Maze *maze, Pair_uint32 *sprite_location) {

  // Ensure coherence
  Anima_instinct(self);

  self->tick += 1;

  if (sprite_location->x % self->scale == 0 && sprite_location->y % self->scale == 0) {
    Anima_sync_abstract(self, maze);
  }

  uint8_t velocity = atomic_load(&self->mind.view.anima[self->id].velocity);
  switch (atomic_load(&self->mind.view.anima[self->id].momentum)) {
  case UP: {
    sprite_location->y -= velocity;
  } break;
  case RIGHT: {
    sprite_location->x += velocity;
  } break;
  case DOWN: {
    sprite_location->y += velocity;
  } break;
  case LEFT: {
    sprite_location->x -= velocity;
  } break;
  }
}

void Anima_instinct(Anima *self) {
  assert(self != nullptr);
}

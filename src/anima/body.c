#include <stdatomic.h>
#include <stdint.h>

#include "anima.h"
#include "constants.h"
#include "logic.h"
#include "maze.h"
#include "utils.h"
#include "utils/pairs.h"

Anima Anima_create(uint8_t id, PairI32 location, Direction intent, Direction momentum, PairI32 sprite_size) {
  static const char *ANIMA_NAMES[2] = {"gottlob", "bertrand"};
  g_log(nullptr, G_LOG_LEVEL_INFO, "Creating anima: %s", ANIMA_NAMES[id]);

  Anima self = {
      .id = id,
      .name = ANIMA_NAMES[id],
      .pov = {},

      .sprite_size = sprite_size,
      .sprite_location = PairI32_scale(&location, TILE_SCALE),

      .sync = {
          .cond_resume = PTHREAD_COND_INITIALIZER,
          .mtx_suspend = PTHREAD_MUTEX_INITIALIZER,
      },

  };

  atomic_init(&self.pov.anima[self.id].intent, intent);
  atomic_init(&self.pov.anima[self.id].momentum, momentum);
  atomic_init(&self.pov.anima[self.id].location, location);
  atomic_init(&self.pov.anima[self.id].status, ANIMA_STATUS_SEARCH);
  atomic_init(&self.pov.anima[self.id].velocity, 1);

  atomic_init(&self.sync.flag_suspend, false);

  return self;
}

void Anima_destroy(Anima *self) {
  assert(self != nullptr);
}

void Anima_handle_event(Anima *self, SDL_Event *event) {

  if (event->type == SDL_EVENT_KEY_DOWN && !event->key.repeat) {

    switch (event->key.key) {
    case SDLK_UP: {
      atomic_store(&self->pov.anima[self->id].intent, UP);
    } break;
    case SDLK_DOWN: {
      atomic_store(&self->pov.anima[self->id].intent, DOWN);
    } break;
    case SDLK_LEFT: {
      atomic_store(&self->pov.anima[self->id].intent, LEFT);
    } break;
    case SDLK_RIGHT: {
      atomic_store(&self->pov.anima[self->id].intent, RIGHT);
    } break;
    }
  }
}

void Anima_move(Anima *self, Maze *maze) {

  auto velocity = atomic_load(&self->pov.anima[self->id].velocity);

  if (self->sprite_location.x % TILE_SCALE == 0 && self->sprite_location.y % TILE_SCALE == 0) {

    auto abstract_location = atomic_load(&self->pov.anima[self->id].location);
    auto intent = atomic_load(&self->pov.anima[self->id].intent);

    atomic_store(&self->pov.anima[self->id].momentum, intent);

    PairI32 destination = steps_in_direction(&abstract_location, intent, 1);

    auto path_ok = Maze_abstract_is_path(maze, destination.x, destination.y);

    if (path_ok) {
      velocity = 1;
    } else {
      velocity = 0;
    }

    switch (atomic_load(&self->pov.anima[self->id].momentum)) {
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

    atomic_store(&self->pov.anima[self->id].location, abstract_location);
  }

  switch (atomic_load(&self->pov.anima[self->id].momentum)) {
  case UP: {
    self->sprite_location.y -= velocity;
  } break;
  case RIGHT: {
    self->sprite_location.x += velocity;
  } break;
  case DOWN: {
    self->sprite_location.y += velocity;
  } break;
  case LEFT: {
    self->sprite_location.x -= velocity;
  } break;
  }

  atomic_store(&self->pov.anima[self->id].velocity, velocity);
}

void Anima_instinct(Anima *self) {
  assert(self != nullptr);
}

#include "anima.h"
#include "logic.h"

#include "constants.h"
#include "utils.h"
#include "utils/pairs.h"
#include <stdatomic.h>
#include <stdint.h>

Anima Anima_default(uint8_t id, PairI32 position, PairI32 sprite_size) {
  return Anima_create(id, position, DOWN, DOWN, sprite_size);
}

Anima Anima_create(uint8_t id, PairI32 location, Direction intent, Direction momentum, PairI32 sprite_size) {
  printf("Creating anima: %s", ANIMA_NAMES[id]);

  Anima self = {
      .id = id,
      .pov = {},
      .sprite_size = sprite_size,

      .sync = {
          .cond_resume = PTHREAD_COND_INITIALIZER,
          .mtx_suspend = PTHREAD_MUTEX_INITIALIZER,
      },

      .velocity = 1,
  };

  atomic_init(&self.pov.anima[self.id].intent, intent);
  atomic_init(&self.pov.anima[self.id].momentum, momentum);
  atomic_init(&self.pov.anima[self.id].location, location);
  atomic_init(&self.pov.anima[self.id].status, ANIMA_STATUS_SEARCH);

  atomic_init(&self.sync.flag_suspend, false);

  return self;
}

void Anima_destroy(Anima *self) {
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

  Direction momentum = atomic_load(&self->pov.anima[self->id].momentum);

  auto current_location = atomic_load(&self->pov.anima[self->id].location);

  if (current_location.x % SPRITE_EDGE_SIZE == 0 && current_location.y % SPRITE_EDGE_SIZE == 0) {
    momentum = atomic_load(&self->pov.anima[self->id].intent);
    atomic_store(&self->pov.anima[self->id].momentum, momentum);

    PairI32 destination;

    steps_in_direction(&current_location, momentum, SPRITE_EDGE_SIZE, &destination);

    if (Maze_is_open(maze, &destination)) {
      self->velocity = 1;
    } else {
      self->velocity = 0;
    }
  }

  switch (momentum) {
  case UP: {
    current_location.y -= self->velocity;
  } break;
  case RIGHT: {
    current_location.x += self->velocity;
  } break;
  case DOWN: {
    current_location.y += self->velocity;
  } break;
  case LEFT: {
    current_location.x -= self->velocity;
  } break;
  }

  atomic_store(&self->pov.anima[self->id].location, current_location);
}

void Anima_instinct(Anima *self) {
}

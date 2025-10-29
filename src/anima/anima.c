#include "anima.h"
#include "logic.h"
#include "maze.h"
#include "sprite.h"
#include "utils.h"
#include "utils/pairs.h"

Anima Anima_default(Sprite sprite) {
  return Anima_create(PairI32_create(1, 1), DOWN, DOWN, sprite);
}

Anima Anima_create(PairI32 pos, Direction intent, Direction momentum, Sprite sprite) {
  Anima self = {.pos = pos,
                .intent = intent,
                .momentum = momentum,
                .mVel = 2,
                .sprite = sprite,
                .mind = cvc5_mind_default()};

  self.sprite.pos = PairI32_create(self.pos.x * sprite.size.x, self.pos.y * sprite.size.y);

  return self;
}

void Anima_destory(Anima *self) {
  Sprite_destroy(&self->sprite);
}

void Anima_handleEvent(Anima *self, SDL_Event *event) {

  if (event->type == SDL_EVENT_KEY_DOWN && !event->key.repeat) {

    switch (event->key.key) {
    case SDLK_UP:
      self->intent = UP;
      break;
    case SDLK_DOWN:
      self->intent = DOWN;
      break;
    case SDLK_LEFT:
      self->intent = LEFT;
      break;
    case SDLK_RIGHT:
      self->intent = RIGHT;
      break;
    }
  }
}

void Anima_moveWithin(Anima *self, Maze *maze) {

  if (self->sprite.pos.x % self->sprite.size.x == 0 && self->sprite.pos.y % self->sprite.size.y == 0) {
    self->pos.x = self->sprite.pos.x / 16;
    self->pos.y = self->sprite.pos.y / 16;

    self->momentum = self->intent;

    PairI32 destination;

    steps_in_direction(&self->pos, self->momentum, 1, &destination);

    if (Maze_isOpen(maze, &destination)) {
      self->mVel = 1;
    } else {
      self->mVel = 0;
    }
  }

  switch (self->momentum) {
  case UP: {
    self->sprite.pos.y -= self->mVel;
  } break;
  case RIGHT: {
    self->sprite.pos.x += self->mVel;
  } break;
  case DOWN: {
    self->sprite.pos.y += self->mVel;
  } break;
  case LEFT: {
    self->sprite.pos.x -= self->mVel;
  } break;
  }
}

#include "anima.h"
#include "maze.h"
#include "sprite.h"
#include "utils.h"

Anima Anima_default(Sprite sprite) {
  return Anima_create(1, 1, down, down, sprite);
}

Anima Anima_create(int32_t pos_x, int32_t pos_y, Direction intent, Direction momentum, Sprite sprite) {
  Anima creature = {.pos_x = pos_x, .pos_y = pos_y, .intent = intent, .momentum = momentum, .mVel = 1, .sprite = sprite, .kAnimaVelocity = 2};
  creature.sprite.pos_x = creature.pos_x * sprite.size_w;
  creature.sprite.pos_y = creature.pos_y * sprite.size_h;

  return creature;
}

void Anima_destory(Anima *self) {
  Sprite_destroy(&self->sprite);
}

void Anima_handleEvent(Anima *self, SDL_Event *event) {

  if (event->type == SDL_EVENT_KEY_DOWN && !event->key.repeat) {

    switch (event->key.key) {
    case SDLK_UP:
      self->intent = up;
      break;
    case SDLK_DOWN:
      self->intent = down;
      break;
    case SDLK_LEFT:
      self->intent = left;
      break;
    case SDLK_RIGHT:
      self->intent = right;
      break;
    }
  }
}

void Anima_moveWithin(Anima *self, Maze *maze) {

  if (self->sprite.pos_x % self->sprite.size_w == 0 && self->sprite.pos_y % self->sprite.size_h == 0) {
    self->pos_x = self->sprite.pos_x / 16;
    self->pos_y = self->sprite.pos_y / 16;

    self->momentum = self->intent;

    int32_t step_x;
    int32_t step_y;

    steps_in_direction(self->pos_x, self->pos_y, self->momentum, 1, &step_x, &step_y);

    if (Maze_isOpen(maze, step_x, step_y)) {
      self->mVel = 1;
    } else {
      self->mVel = 0;
    }
  }

  switch (self->momentum) {
  case up: {
    self->sprite.pos_y -= self->mVel;
  } break;
  case right: {
    self->sprite.pos_x += self->mVel;
  } break;
  case down: {
    self->sprite.pos_y += self->mVel;
  } break;
  case left: {
    self->sprite.pos_x -= self->mVel;
  } break;
  }
}

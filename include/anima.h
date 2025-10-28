
#pragma once

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "maze.h"
#include "sprite.h"
#include "utils.h"

struct anima_t {

  PairI32 pos;

  Direction intent;
  Direction momentum;

  int mVel;

  Sprite sprite;
};

typedef struct anima_t Anima;

#ifdef __cplusplus
extern "C" {
#endif

Anima Anima_default(Sprite sprite);

Anima Anima_create(PairI32 pos, Direction intent, Direction momentum, Sprite sprite);

void Anima_destory(Anima *self);

void Anima_handleEvent(Anima *self, SDL_Event *event);

void Anima_moveWithin(Anima *self, Maze *maze);
#ifdef __cplusplus
}
#endif

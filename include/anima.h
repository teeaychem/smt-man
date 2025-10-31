
#pragma once

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "cvc5/c/cvc5.h"
#include "maze.h"
#include "sprite.h"
#include "utils.h"


struct l_local {
  Cvc5Term facing_u;
  Cvc5Term facing_r;
  Cvc5Term facing_d;
  Cvc5Term facing_l;
};

struct anima_t {

  char *name;

  Cvc5Term term;
  struct l_local terms;

  PairI32 pos;

  Direction intent;
  Direction momentum;

  int mVel;

  Sprite sprite;

  Cvc5 *mind;
};

typedef struct anima_t Anima;

Anima Anima_default(char* name, Sprite sprite);

Anima Anima_create(char* name, PairI32 pos, Direction intent, Direction momentum, Sprite sprite);

void Anima_destory(Anima *self);

void Anima_handle_event(Anima *self, SDL_Event *event);

void Anima_move_within(Anima *self, Maze *maze);

void Anima_deduction_known(Anima *self);

void Anima_deduct(Anima *self);

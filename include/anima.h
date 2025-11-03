#pragma once

#include <pthread.h>
#include <stdatomic.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "maze.h"
#include "sprite.h"
#include "utils.h"

#include "cvc5/c/cvc5.h"
#include "cvc5/c/cvc5_parser.h"

#include "logic.h"

struct mind_t {
  Cvc5 *solver;
  Cvc5TermManager *tm;
  Cvc5SymbolManager *sm;
  Cvc5InputParser *parser;

  AnimaTerms terms;
};

typedef struct mind_t Mind;

Mind Mind_default();

struct l_local {
  Cvc5Term facing_u;
  Cvc5Term facing_r;
  Cvc5Term facing_d;
  Cvc5Term facing_l;
};

struct anima_t {

  _Atomic(char *) name;

  PairI32 pos;

  _Atomic Direction intent;
  _Atomic Direction momentum;

  int mVel;

  Sprite sprite;

  pthread_mutex_t mtx_suspend;
  _Atomic bool flag_suspend;
  pthread_cond_t cond_resume;
};

typedef struct anima_t Anima;

Anima Anima_default(char *name, PairI32 position, Sprite sprite);

Anima Anima_create(char *name, PairI32 pos, Direction intent, Direction momentum, Sprite sprite);

void Anima_destroy(Anima *self);

void Anima_touch(Anima *self, Mind *mind);

void Anima_handle_event(Anima *self, SDL_Event *event);

void Anima_move_within(Anima *self, Maze *maze);

void Anima_mind_innate(Anima *self, Mind *mind);

void Anima_deduct(Anima *self, Mind *mind);

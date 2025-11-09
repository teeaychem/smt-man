#pragma once

#include <pthread.h>
#include <stdatomic.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "maze.h"
#include "surface.h"
#include "utils.h"

#include "cvc5/c/cvc5.h"
#include "cvc5/c/cvc5_parser.h"

#include "logic.h"
#include "utils/pairs.h"

// Minds

typedef struct mind_t Mind;
struct mind_t {
  Cvc5 *solver;
  Cvc5TermManager *tm;
  Cvc5SymbolManager *sm;
  Cvc5InputParser *parser;

  SmtLot lot;
};

Mind Mind_default();

// Animas

typedef struct anima_t Anima;
struct anima_t {

  char *name;

  uint8_t id;

  _Atomic(Direction) intent;
  _Atomic(Direction) momentum;

  _Atomic(AnimaStatus) status;

  PairI32 location;
  PairI32 size;

  int mVel;

  Surface surface;
  PairI32 surface_offset;

  uint32_t status_tick;

  _Atomic(bool) flag_suspend;
  pthread_mutex_t mtx_suspend;
  pthread_cond_t cond_resume;
};

Anima Anima_default(uint8_t id, char *name, PairI32 position, Surface surface);

Anima Anima_create(uint8_t id, char *name, PairI32 pos, Direction intent, Direction momentum, Surface surface);

void Anima_destroy(Anima *self);

void Anima_touch(Anima *self, Mind *mind);

void Anima_fresh_tick(Anima *self);

void Anima_update_surface_offset(Anima *self);

void Anima_handle_event(Anima *self, SDL_Event *event);

void Anima_move(Anima *self, Maze *maze);

void Anima_mind_innate(Anima *self, Mind *mind);

void Anima_instinct(Anima *self);

void Anima_deduct(Anima *self, Mind *mind);

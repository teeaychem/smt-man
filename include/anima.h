#pragma once

#include <pthread.h>

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

typedef struct sprite_info_t SpriteInfo;
struct sprite_info_t {
  PairI32 size;
  Surface surface;
  PairI32 surface_offset;
  uint32_t tick;
};

typedef struct anima_sync_t AnimaSync;
struct anima_sync_t {
  _Atomic(bool) flag_suspend;
  pthread_mutex_t mtx_suspend;
  pthread_cond_t cond_resume;
};

typedef struct anima_t Anima;
struct anima_t {

  uint8_t id;

  char *name;

  PairI32 abstract_location;
  PairI32 sprite_location;

  SmtWorld pov;

  PairI32 sprite_size;

  AnimaSync sync;
};

Anima Anima_create(uint8_t id, PairI32 location, Direction intent, Direction momentum, PairI32 sprite_size);

void Anima_destroy(Anima *self);

void Anima_touch(Anima *self, Mind *mind);

void Anima_handle_event(Anima *self, SDL_Event *event);

void Anima_move(Anima *self, Maze *maze);

void Anima_LoT_direction(Anima *self, Mind *mind);

void Anima_instinct(Anima *self);

void Anima_deduct(Anima *self, Mind *mind);

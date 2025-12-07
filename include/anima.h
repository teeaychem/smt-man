#pragma once

#include <pthread.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "pairs.h"
#include "utils.h"

#include "logic.h"
#include "pairs.h"

// Minds

typedef struct mind_t Mind;
struct mind_t {
  Z3_optimize solver;
  Z3_context ctx;
  struct z3_lang lang;
};

Mind Mind_default();

// Animas

typedef struct anima_sync_t AnimaSync;
struct anima_sync_t {
  _Atomic(bool) flag_suspend;
  pthread_mutex_t mtx_suspend;
  pthread_cond_t cond_resume;
};

typedef struct anima_t Anima;
struct anima_t {

  uint8_t id;

  const char *name;

  Pair_uint8 abstract_location;
  Pair_uint32 sprite_location;

  SmtWorld pov;

  Pair_uint32 sprite_size;

  AnimaSync sync;
};

Anima Anima_create(uint8_t id, Pair_uint8 location, Direction intent, Direction momentum, Pair_uint32 sprite_size);

void Anima_destroy(Anima *self);

void Anima_touch(Anima *self, Mind *mind);

void Anima_handle_event(Anima *self, SDL_Event *event);

void Anima_move(Anima *self, Maze *maze);

void Anima_instinct(Anima *self);

void Anima_deduct(Anima *self, Mind *mind);

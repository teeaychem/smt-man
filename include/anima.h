#pragma once

#include <pthread.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "generic/pairs.h"
#include "logic.h"
#include "logic/situation.h"
#include "utils.h"

// Minds

struct mind_t {
  Z3_optimize solver;
  Z3_context ctx;
  struct z3_lang lang;
};
typedef struct mind_t Mind;

//

void Mind_default(Mind *mind);

// Animas

//
struct anima_sync_t {
  _Atomic(bool) flag_suspend;
  pthread_mutex_t mtx_suspend;
  pthread_cond_t cond_resume;
};
typedef struct anima_sync_t AnimaSync;

//
struct anima_t {

  uint8_t id;

  Situation pov;

  AnimaSync sync;
};
typedef struct anima_t Anima;

//

void Anima_default(Anima *anima, uint8_t id, Pair_uint8 location, Direction direction);

void Anima_destroy(Anima *self);

void Anima_touch(Anima *self, Mind *mind);

void Anima_handle_event(Anima *self, SDL_Event *event);

void Anima_move(Anima *self, Maze *maze, Pair_uint32 *sprite_location);

void Anima_instinct(Anima *self);

void Anima_deduct(Anima *self, Mind *mind);

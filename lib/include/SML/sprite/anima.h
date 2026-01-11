#pragma once

#include <pthread.h>
#include <stdint.h>
#include <z3.h>

#include "SML/logic.h"
#include "generic/enums.h"
#include "generic/pairs.h"

/// Tools for contacting the anima from a different thread
struct anima_contact_t {
  _Atomic(bool) flag_suspend;

  pthread_mutex_t mtx_suspend;

  pthread_cond_t cond_resume;
};
typedef struct anima_contact_t AnimaContact;

struct anima_t {
  /// Uniqie identifier in [0..ANIMA_COUNT]
  uint8_t id;
  /// Incremented on each tick an action is performed
  uint8_t tick_action;

  Cardinal direction_intent;
  /// Point of view, on the situation

  AnimaContact contact;

  struct {
    Situation situation;

    Z3_context ctx;

    Z3_optimize opz;

    Lang lang;
  } smt;
};
typedef struct anima_t Anima;

// Methods

void Anima_default(Anima *anima, const uint8_t id, const Pair_uint8 location, const Cardinal direction);

void Anima_destroy(Anima *self);

void Anima_instinct(Anima *self);

void Anima_touch(Anima *self, const Maze *maze, size_t anima_count);

void Anima_deduct(Anima *self, const Maze *maze);

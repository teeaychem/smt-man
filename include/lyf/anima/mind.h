#pragma once

#include "logic.h"

// Structs

struct mind_t {
  uint8_t id;

  Z3_context ctx;

  Z3_optimize solver;

  struct z3_lang lang;

  // Point of view, on the situation
  Situation view;
};
typedef struct mind_t Mind;

// Methods

void Mind_default(Mind *mind, uint8_t id, Pair_uint8 location, Direction direction);

void Mind_touch(Mind *self);

void Mind_deduct(Mind *self);

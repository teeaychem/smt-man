#pragma once

#include <z3.h>

#include "enums.h"
#include "generic/pairs.h"
#include "logic.h"
#include "logic/situation.h"
#include "maze.h"

// Structs

struct mind_t {
  uint8_t id;

  Z3_context ctx;

  Z3_optimize opz;

  struct z3_lang lang;

  Direction direction_intent;
  /// Point of view, on the situation
  Situation view;
};
typedef struct mind_t Mind;

// Methods

void Mind_default(Mind *mind, uint8_t id, Pair_uint8 location, Direction direction);

void Mind_touch(Mind *self, const Maze* maze);

void Mind_deduct(Mind *self, const Maze *maze);

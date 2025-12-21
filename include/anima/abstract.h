#pragma once

#include "anima/enums.h"
#include "generic/pairs.h"
#include "utils.h"

struct abstract_anima_t {
  _Atomic(Pair_uint8) location;

  _Atomic(Direction) intent;
  _Atomic(Direction) momentum;

  _Atomic(AnimaStatus) status;

  _Atomic(uint8_t) velocity;
};
typedef struct abstract_anima_t AbstractAnima;

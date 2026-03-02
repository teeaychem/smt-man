#pragma once

#include <stddef.h>

#include "generic/enums.h"
#include "generic/pairs.h"

#include "SML/logic/enums.h"

struct situation_t {
  struct {
    size_t count;
    struct anima_state_t {
      _Atomic(Cardinal) direction_actual;

      _Atomic(Pair_uint8) location;

      _Atomic(uint32_t) movement_pattern;

      _Atomic(anima_status_e) status;

    } *states;
  } animas;

  struct persona_state_t {
    _Atomic(Cardinal) direction_actual;

    _Atomic(Pair_uint8) location;

    _Atomic(uint32_t) movement_pattern;
  } persona;
};
typedef struct situation_t Situation;

// Methods

void situation_ctor(Situation *self, size_t anima_count);

void situation_dtor(Situation *self);

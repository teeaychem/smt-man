#pragma once

#include "SML/logic/enums.h"
#include "generic/enums.h"
#include "generic/pairs.h"

/// Animas
struct anima_state_t {
  _Atomic(Pair_uint8) location;

  _Atomic(Cardinal) direction_actual;

  _Atomic(AnimaStatus) status;

  _Atomic(uint32_t) movement_pattern;
};
typedef struct anima_state_t AnimaState;

/// Persona
struct persona_state_t {
  _Atomic(Pair_uint8) location;

  _Atomic(Cardinal) direction_actual;

  _Atomic(uint32_t) movement_pattern;
};
typedef struct persona_state_t PersonaState;

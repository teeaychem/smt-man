#pragma once

#include "SML/enums.h"
#include "SML/logic/enums.h"
#include "generic/pairs.h"

/// Animas
struct abstract_anima_t {
  _Atomic(Pair_uint8) location;

  _Atomic(Cardinal) direction_actual;

  _Atomic(AnimaStatus) status;

  _Atomic(uint32_t) movement_pattern;
};
typedef struct abstract_anima_t AbstractAnima;

/// Persona
struct abstract_persona_t {
  _Atomic(Pair_uint8) location;

  _Atomic(Cardinal) direction_actual;

  _Atomic(uint32_t) movement_pattern;
};
typedef struct abstract_persona_t AbstractPersona;

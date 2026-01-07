#pragma once

#include "enums.h"
#include "generic/pairs.h"
#include "logic/enums.h"

/// Animas
struct abstract_anima_t {
  _Atomic(Pair_uint8) location;

  _Atomic(Direction) direction_actual;

  _Atomic(AnimaStatus) status;

  _Atomic(uint32_t) movement_pattern;
};
typedef struct abstract_anima_t AbstractAnima;

/// Persona
struct abstract_persona_t {
  _Atomic(Pair_uint8) location;

  _Atomic(Direction) direction_actual;

  _Atomic(uint32_t) movement_pattern;
};
typedef struct abstract_persona_t AbstractPersona;

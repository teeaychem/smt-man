#pragma once

#include <stdint.h>

#include "SML/logic/situation.h"
#include "generic/enums.h"

struct persona_t {
  /// Incremented on each tick an action is performed
  uint8_t tick_action;

  cardinal_e direction_intent;
};
typedef struct persona_t Persona;

void Persona_ctor(Persona *persona, Situation *situation);

void Persona_dtor(Persona *self);

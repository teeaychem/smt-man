#pragma once

#include <stdint.h>

#include "enums.h"
#include "logic/situation.h"

struct persona_t {
  /// Incremented on each tick an action is performed
  uint8_t tick_action;

  Direction direction_intent;
};
typedef struct persona_t Persona;

void Persona_default(Persona *persona, Situation *situation);

void Persona_drop(Persona *self);

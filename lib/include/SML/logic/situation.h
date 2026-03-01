#pragma once

#include <stddef.h>

#include "SML/logic/abstractions.h"

struct situation_t {
  struct {
    size_t count;
    AnimaState *states;
  } animas;
  PersonaState persona;
};
typedef struct situation_t Situation;

// Methods

#pragma once

#include "constants.h"
#include "logic/abstractions.h"

struct situation_t {
  AbstractAnima anima[ANIMA_COUNT];
  AbstractPersona persona;
};
typedef struct situation_t Situation;

// Methods

#pragma once

#include "anima/abstract.h"
#include "constants.h"

struct situation_t {
  AbstractAnima anima[ANIMA_COUNT];
};
typedef struct situation_t Situation;

// Methods

#pragma once

#include <stddef.h>

#include "logic/abstractions.h"

struct situation_t {
  size_t anima_count;
  AbstractAnima *animas;
  AbstractPersona persona;
};
typedef struct situation_t Situation;

// Methods

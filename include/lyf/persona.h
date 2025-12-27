#pragma once

#include <stdint.h>

#include "enums.h"
#include "generic/pairs.h"
#include "lyf/tick.h"

struct persona_t {
  uint8_t pixel_size;
  Tick tick;

  Direction direction;
  Pair_uint8 location;
};
typedef struct persona_t Persona;

void Persona_default(Persona *persona, uint8_t pixel_size, Pair_uint8 location, Direction direction);

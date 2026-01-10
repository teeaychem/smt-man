#pragma once

// TODO: Relocate
#include "SML/enums.h"
#include <stdint.h>

#define TYPE uint32_t
#define SUFFIX uint32
#include "generic/templates/pair_template.h"
#undef SUFFIX
#undef TYPE

#define TYPE uint8_t
#define SUFFIX uint8
#include "templates/pair_template.h"

Pair_uint8 Pair_uint8_steps_in_direction(const Pair_uint8 *origin, Cardinal direction, uint8_t steps);

#ifdef PAIR_IMPLEMENTATION

Pair_uint8 Pair_uint8_steps_in_direction(const Pair_uint8 *origin, Cardinal direction, uint8_t steps) {

  Pair_uint8 destination = {.x = origin->x, .y = origin->y};

  switch (direction) {
  case CARDINAL_NONE: {
    // No change
  } break;

  case CARDINAL_N: {
    destination.y = (steps <= origin->y) ? (origin->y - steps) : 0;
  } break;

  case CARDINAL_W: {
    destination.x = (steps <= (UINT8_MAX - origin->x)) ? origin->x + steps : UINT8_MAX;
  } break;

  case CARDINAL_S: {
    destination.y = (steps <= (UINT8_MAX - origin->y)) ? origin->y + steps : UINT8_MAX;
  } break;

  case CARDINAL_E: {
    destination.x = (steps <= origin->x) ? (origin->x - steps) : 0;
  } break;
  }

  return destination;
}

#endif

#undef SUFFIX
#undef TYPE

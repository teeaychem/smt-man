#include "utils.h"
#include "utils/pairs.h"
#include <stdio.h>

void steps_in_direction(PairI32 *origin, Direction direction, int32_t steps, PairI32 *destination) {

  *destination = *origin;

  switch (direction) {
  case up: {
    destination->y = (steps <= origin->y) ? (origin->y - steps) : 0;
  } break;

  case right: {
    destination->x = (steps <= (INT32_MAX - origin->x)) ? origin->x + steps : INT32_MAX;
  } break;

  case down: {
    destination->y = (steps <= (INT32_MAX - origin->y)) ? origin->y + steps : INT32_MAX;
  } break;

  case left: {
    destination->x = (steps <= origin->x) ? (origin->x - steps) : 0;
  } break;
  }
}

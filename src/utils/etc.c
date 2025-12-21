#include <stdlib.h>

#include "generic/pairs.h"
#include "utils.h"

Pair_uint8 steps_in_direction(const Pair_uint8 *origin, Direction direction, uint8_t steps) {

  Pair_uint8 destination = {.x = origin->x, .y = origin->y};

  switch (direction) {
  case UP: {
    destination.y = (steps <= origin->y) ? (origin->y - steps) : 0;
  } break;

  case RIGHT: {
    destination.x = (steps <= (INT8_MAX - origin->x)) ? origin->x + steps : INT8_MAX;
  } break;

  case DOWN: {
    destination.y = (steps <= (INT8_MAX - origin->y)) ? origin->y + steps : INT8_MAX;
  } break;

  case LEFT: {
    destination.x = (steps <= origin->x) ? (origin->x - steps) : 0;
  } break;
  }

  return destination;
}

int random_in_range(int min, int max) {
  return min + rand() / (RAND_MAX / (max - min + 1) + 1);
}

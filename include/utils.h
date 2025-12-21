#pragma once

#include <stdint.h>

#include "generic/pairs.h"

enum direction_e {
  UP,
  RIGHT,
  DOWN,
  LEFT,
};
typedef enum direction_e Direction;

enum quadrant_e {
  FIRST,
  SECOND,
  THIRD,
  FOURTH,
};
typedef enum quadrant_e Quadrant;

Pair_uint8 steps_in_direction(const Pair_uint8 *origin, Direction direction, uint8_t steps);

int random_in_range(int min, int max);

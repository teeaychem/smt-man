#pragma once

#include <stdint.h>

#include "pairs.h"

enum direction_e {
  UP,
  RIGHT,
  DOWN,
  LEFT,
};

typedef enum direction_e Direction;

Pair_uint32 steps_in_direction(Pair_uint8 *origin, Direction direction, uint32_t steps);

int random_in_range(int min, int max);

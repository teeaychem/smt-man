#pragma once

#include "utils/pairs.h"
#include <stdint.h>

enum direction_e {
  UP,
  RIGHT,
  DOWN,
  LEFT,
};

typedef enum direction_e Direction;

PairI32 steps_in_direction(PairI32 *origin, Direction direction, int32_t steps);

int random_in_range(int min, int max);

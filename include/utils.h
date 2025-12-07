#pragma once

#include <stdint.h>

#include "utils/pairs.h"

enum direction_e {
  UP,
  RIGHT,
  DOWN,
  LEFT,
};

typedef enum direction_e Direction;

PairI32 steps_in_direction(PairI32 *origin, Direction direction, uint32_t steps);

int random_in_range(int min, int max);

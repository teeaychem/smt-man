#pragma once

#include "utils/pairs.h"
#include <stdint.h>
#include <stdlib.h>

enum direction_e {
  UP,
  RIGHT,
  DOWN,
  LEFT,
};

typedef enum direction_e Direction;

void steps_in_direction(PairI32 *origin, Direction direction, int32_t steps, PairI32 *destination);

int random_in_range(int min, int max);

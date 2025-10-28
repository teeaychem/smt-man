#pragma once

#include "utils/pairs.h"
#include <stdint.h>
#include <stdlib.h>

enum direction_e {
  up,
  right,
  down,
  left,
};

typedef enum direction_e Direction;

#ifdef __cplusplus
extern "C" {
#endif

void steps_in_direction(PairI32 *origin, Direction direction, int32_t steps, PairI32 *destination);

#ifdef __cplusplus
}
#endif

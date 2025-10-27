#pragma once

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

void steps_in_direction(int32_t origin_x, int32_t origin_y, Direction direction, int32_t steps, int32_t *step_x, int32_t *step_y);

inline int random_in_range(int min, int max) {
  return min + rand() / (RAND_MAX / (max - min + 1) + 1);
}

#ifdef __cplusplus
}
#endif

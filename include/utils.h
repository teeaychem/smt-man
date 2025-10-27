#pragma once

#include <stdint.h>

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
#ifdef __cplusplus
}
#endif

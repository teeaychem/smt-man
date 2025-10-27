#include "utils.h"

void nvec_direction_steps(int32_t origin_x, int32_t origin_y, Direction direction, int32_t steps, int32_t *step_x, int32_t *step_y) {

  *step_x = origin_x;
  *step_y = origin_y;

  switch (direction) {
  case up: {
    *step_y = (steps <= origin_y) ? (origin_y - steps) : 0;
  } break;

  case right: {
    *step_x = (steps <= (INT32_MAX - origin_x)) ? origin_x + steps : INT32_MAX;
  } break;

  case down: {
    *step_y = (steps <= (INT32_MAX - origin_y)) ? origin_y + steps : INT32_MAX;
  } break;

  case left: {
    *step_x = (steps <= origin_x) ? (origin_x - steps) : 0;
  } break;
  }
}

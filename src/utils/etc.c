#include "toys.h"
#include "utils.h"
#include "utils/pairs.h"
#include <stdlib.h>

PairI32 steps_in_direction(PairI32 *origin, Direction direction, uint32_t steps) {

  PairI32 destination = {.x = origin->x, .y = origin->y};

  switch (direction) {
  case UP: {
    destination.y = (steps <= origin->y) ? (origin->y - steps) : 0;
  } break;

  case RIGHT: {
    destination.x = (steps <= (INT32_MAX - origin->x)) ? origin->x + steps : INT32_MAX;
  } break;

  case DOWN: {
    destination.y = (steps <= (INT32_MAX - origin->y)) ? origin->y + steps : INT32_MAX;
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

void rgbVM_advance(rgbVM *self) {
  int current = random_in_range(0, 2);

  if (self->state[current].value == UINT8_MAX) {
    self->state[current].momentum = false;
  } else if (self->state[current].value == 0) {
    self->state[current].momentum = true;
  }

  if (self->state[current].momentum) {
    self->state[current].value = (self->state[current].value + 1);
  } else {
    self->state[current].value = (self->state[current].value - 1);
  }
}

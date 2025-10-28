#include "utils/pairs.h"

PairI32 PairI32_create(int32_t x, int32_t y) {
  PairI32 pair = {.x = x, .y = y};
  return pair;
}

int32_t PairI32_area(PairI32 *self) {
  return self->x * self->y;
}

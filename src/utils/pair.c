#include "utils/pairs.h"

PairI32 PairI32_create(int32_t x, int32_t y) {
  PairI32 pair = {.x = x, .y = y};
  return pair;
}

int32_t PairI32_area(const PairI32 *self) {
  return self->x * self->y;
}

PairI32 PairI32_abstract_by(const PairI32 *self, const int32_t interval) {
  return (PairI32){.x = (self->x / interval),
                   .y = (self->y / interval)};
}

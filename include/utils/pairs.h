#pragma once

#include <stdint.h>
struct pair_u32 {
  uint32_t x;
  uint32_t y;
};

typedef struct pair_u32 PairI32;

static inline PairI32 PairI32_create(uint32_t x, uint32_t y) {
  return (PairI32){.x = x, .y = y};
}

static inline uint32_t PairI32_area(const PairI32 *self) {
  return self->x * self->y;
}

static inline PairI32 PairI32_scale(const PairI32 *self, const uint32_t factor) {
  return (PairI32){.x = (self->x * factor),
                   .y = (self->y * factor)};
}

static inline PairI32 PairI32_abstract_by(const PairI32 *self, const uint32_t interval) {
  return (PairI32){.x = (self->x / interval),
                   .y = (self->y / interval)};
}

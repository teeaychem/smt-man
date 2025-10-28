#pragma once

#include <stdint.h>
struct pair_i32_t {
  int32_t x;
  int32_t y;
};

typedef struct pair_i32_t PairI32;

PairI32 PairI32_create(int32_t x, int32_t y);

int32_t PairI32_area(PairI32 *self);

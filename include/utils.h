#pragma once

#include <stdlib.h>

static inline int random_in_range(int min, int max) {
  return min + rand() / (RAND_MAX / (max - min + 1) + 1);
}

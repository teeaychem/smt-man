#pragma once

#include <stdint.h>

struct tick_t {
  /// Increments each time an action is taken.
  uint8_t actions;
};
typedef struct tick_t Tick;

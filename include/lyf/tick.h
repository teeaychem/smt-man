#pragma once

#include <stdint.h>

struct tick_t {
  /// Increments each time an action is taken.
  uint8_t actions;
  /// Increments on each frame.
  uint8_t frames;
  /// The number of actions to take, per frame.
  uint8_t frames_per_action;
};
typedef struct tick_t Tick;

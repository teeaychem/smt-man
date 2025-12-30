#pragma once

#include <stdint.h>

/// Cardinal directions
// Directions are flags
enum direction_e : uint8_t {
  DIRECTION_NONE = 0,
  DIRECTION_N = 1,
  DIRECTION_E = 1 << 1,
  DIRECTION_S = 1 << 2,
  DIRECTION_W = 1 << 3,
};
typedef enum direction_e Direction;

/// Quadrants of a circle
enum quadrant_e {
  QUADRANT_FIRST,
  QUADRANT_SECOND,
  QUADRANT_THIRD,
  QUADRANT_FOURTH,
};
typedef enum quadrant_e Quadrant;

/// Turns
enum turn_e {
  TURN_QUARTER,
  TURN_HALF,
  TURN_THREE_QUARTER,
  TURN_ONE,
};
typedef enum turn_e Turn;

/// The horizontal or vertical plane
enum plane_e {
  PLANE_HORIZONTAL,
  PLANE_VERTICAL,
};
typedef enum plane_e Plane;

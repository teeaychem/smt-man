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
  QUADRANT_1,
  QUADRANT_2,
  QUADRANT_3,
  QUADRANT_4,
};
typedef enum quadrant_e Quadrant;

/// Turns
enum turn_e {
  TURN_0Q,
  TURN_1Q,
  TURN_2Q,
  TURN_3Q,
};
typedef enum turn_e Turn;

/// The horizontal or vertical plane
enum plane_e {
  PLANE_H, // HORIZONTAL
  PLANE_V, // VERTICAL
};
typedef enum plane_e Plane;

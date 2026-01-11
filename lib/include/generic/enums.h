#pragma once

#include <stdint.h>

/// Cardinal directions
// Directions are flags
enum cardinal_e : uint8_t {
  CARDINAL_NONE = 0,
  CARDINAL_N = 1,
  CARDINAL_E = 1 << 1,
  CARDINAL_S = 1 << 2,
  CARDINAL_W = 1 << 3,
};
typedef enum cardinal_e Cardinal;

/// Quadrants of a circle
enum quadrant_e {
  QUADRANT_1,
  QUADRANT_2,
  QUADRANT_3,
  QUADRANT_4,
};
typedef enum quadrant_e Quadrant;

/// The horizontal or vertical plane
enum plane_e {
  PLANE_H, // HORIZONTAL
  PLANE_V, // VERTICAL
};
typedef enum plane_e Plane;

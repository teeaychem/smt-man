#pragma once

#include <stdint.h>

/// Cardinal directions
// Directions are flags
enum cardinat_t : uint8_t {
  CARDINAL_NONE = 0,
  CARDINAL_N = 1,
  CARDINAL_E = 1 << 1,
  CARDINAL_S = 1 << 2,
  CARDINAL_W = 1 << 3,
};
typedef enum cardinat_t cardinal_e;

static inline char cardinal_to_char(cardinal_e self) {
  switch (self) {

  case CARDINAL_NONE: {
    return 'X';
  } break;
  case CARDINAL_N: {
    return 'N';
  } break;
  case CARDINAL_E: {
    return 'E';
  } break;
  case CARDINAL_S: {
    return 'S';
  } break;
  case CARDINAL_W: {
    return 'W';
  } break;
  }
}

/// Quadrants of a circle
enum quadrant_t {
  QUADRANT_1,
  QUADRANT_2,
  QUADRANT_3,
  QUADRANT_4,
};
typedef enum quadrant_t quadrant_e;

/// The horizontal or vertical plane
enum plane_t {
  PLANE_H, // HORIZONTAL
  PLANE_V, // VERTICAL
};
typedef enum plane_t plane_e;

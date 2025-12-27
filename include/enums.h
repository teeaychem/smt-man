#pragma once

/// Cardinal directions
enum direction_e {
  NORTH,
  EAST,
  SOUTH,
  WEST,
};
typedef enum direction_e Direction;

/// Quadrants of a circle
enum quadrant_e {
  FIRST,
  SECOND,
  THIRD,
  FOURTH,
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
  HORIZONTAL,
  VERTICAL,
};
typedef enum plane_e Plane;

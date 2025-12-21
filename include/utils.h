#pragma once

enum direction_e {
  UP,
  RIGHT,
  DOWN,
  LEFT,
};
typedef enum direction_e Direction;

enum quadrant_e {
  FIRST,
  SECOND,
  THIRD,
  FOURTH,
};
typedef enum quadrant_e Quadrant;

int random_in_range(int min, int max);

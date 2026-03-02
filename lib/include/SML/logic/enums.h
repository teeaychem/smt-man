#pragma once

#include <stdint.h>

enum anima_status_t {
  ANIMA_STATUS_SEARCH,
};
typedef enum anima_status_t anima_status_e;

/// The path value of a tile, given by some map.
enum path_t : uint8_t {
  /// Empty
  PATH_X = 0,
  /// North / East
  PATH_A,
  /// South / West
  PATH_B,
  /// Origin
  PATH_O,
};
typedef enum path_t path_e;

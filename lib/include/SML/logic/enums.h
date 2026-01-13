#pragma once

#include <stdint.h>

enum anima_status_t {
  ANIMA_STATUS_SEARCH,
};
typedef enum anima_status_t AnimaStatus;

/// The path value of a tile, given by some map.
enum path_e : uint8_t {
  /// Empty
  PATH_X = 0,
  /// North / East
  PATH_A,
  /// South / West
  PATH_B,
  /// Origin
  PATH_O,
};

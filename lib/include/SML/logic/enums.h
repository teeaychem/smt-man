#pragma once

//
enum anima_status_t {
  ANIMA_STATUS_SEARCH,
};
typedef enum anima_status_t AnimaStatus;

/// The path value of a tile, given by some map.
enum path_e {
  /// Origin north
  PATH_ON,
  /// Origin east
  PATH_OE,
  /// Origin south
  PATH_OS,
  /// Origin west
  PATH_OW,

  /// North south
  PATH_NS,
  /// East west
  PATH_EW,

  /// Nort east
  PATH_NE,
  /// South east
  PATH_SE,
  /// South east
  PATH_SW,
  /// North west
  PATH_NW,

  /// Empty
  PATH_XX,
};

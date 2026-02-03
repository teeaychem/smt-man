#pragma once

#include <assert.h>
#include <stddef.h>
#include <stdint.h>

#include "err.h"
#include "generic/enums.h"
#include "generic/pairs.h"

constexpr Pair_uint32 STANDARD_MAZE_DIMENSIONS = {.x = 31, .y = 28};

struct tile_edge_data_t {

  enum : uint8_t {
    TILE_LINES_P = 1,
    TILE_LINES_M = 2,
  } lines;

  enum {
    TILE_STYLE_NONE,
    TILE_STYLE_LINE,
    TILE_STYLE_ARC,
  } edge_style;

  union {
    Plane edge_line_plane;
    Quadrant edge_arc_quadrant;
  };
};

struct tile_path_data_t {
  enum {
    ITEM_NONE,
    ITEM_PELLET,
    ITEM_POWERUP,
  } item;
};

// Tile representation data
struct tile_data_t {
  enum {
    TILE_EDGE,
    TILE_EMPTY,
    TILE_INFO,
    TILE_PATH,
  } type;

  union {
    struct tile_edge_data_t edge_value;
    struct tile_path_data_t path_value;
  } value;
};
typedef struct tile_data_t TileData;

static inline char TileData_as_char(TileData *self) {
  switch (self->type) {
  case TILE_EDGE: {
    return '#';
  } break;
  case TILE_EMPTY: {
    return '_';
  } break;
  case TILE_INFO: {
    return 'X';
  } break;
  case TILE_PATH: {
    return ' ';
  } break;
    break;
  }
}

/// Maze

struct maze_t {
  Pair_uint8 size;
  TileData *tiles;
};
typedef struct maze_t Maze;

/// Methods

Result Maze_from_path(Maze *maze, const char *path);

Result Maze_detail(Maze *self);

void Maze_drop(Maze *self);

bool Maze_tile_in_direction_is_path(const Maze *self, const Pair_uint8 location, const Cardinal direction);

void Maze_complete_line_data(const Maze *self, TileData *tile_data, const uint8_t row, const uint8_t col);

Result Maze_complete_data(const Maze *self);

/// Static inline

static inline size_t Maze_tile_index(const Maze *self, const uint8_t row, const uint8_t col) {
  return Pair_uint8_flatten(&self->size, row, col);
}

static inline TileData *Maze_tile_data_at(const Maze *self, const uint8_t row, const uint8_t col) {
  return &self->tiles[Maze_tile_index(self, row, col)];
}

static inline bool Maze_is_path(const Maze *self, const uint8_t row, const uint8_t col) {
  return Maze_tile_data_at(self, row, col)->type == TILE_PATH;
}

static inline bool Maze_is_intersection(const Maze *self, const uint8_t row, const uint8_t col) {
  // clang-format off
  bool path_n = row > 0                && Maze_is_path(self, row - 1, col);
  bool path_e = col + 1 < self->size.x && Maze_is_path(self, row, col + 1);
  bool path_s = row + 1 < self->size.y && Maze_is_path(self, row + 1, col);
  bool path_w = col > 0                && Maze_is_path(self, row, col - 1);
  // clang-format on

  return (path_n || path_s) && (path_e || path_w);
}

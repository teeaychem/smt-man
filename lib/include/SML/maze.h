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
    plane_e edge_line_plane;
    quadrant_e edge_arc_quadrant;
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
typedef struct tile_data_t tile_data_s;

static inline char tile_data_as_char(tile_data_s *self) {
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
  Pair_uint8 dimensions;
  tile_data_s *tiles;
};
typedef struct maze_t maze_s;

/// Methods

Result maze_ctor(maze_s *maze);

Result maze_ctor_from_path(maze_s *maze, const char *path);

void maze_dtor(maze_s *self);

Result maze_read_from_path(maze_s *maze, const char *path);

Result maze_detail(maze_s *self);

char *maze_as_string(const maze_s *self);

bool maze_tile_in_direction_is_path(const maze_s *self, const Pair_uint8 location, const cardinal_e direction);

void maze_complete_line_data(const maze_s *self, tile_data_s *tile_data, const uint8_t row, const uint8_t col);

/// Static inline

static inline size_t maze_tile_index(const maze_s *self, const uint8_t row, const uint8_t col) {
  return Pair_uint8_flatten(&self->dimensions, row, col);
}

static inline tile_data_s *maze_tile_data_at(const maze_s *self, const uint8_t row, const uint8_t col) {
  return &self->tiles[maze_tile_index(self, row, col)];
}

static inline bool maze_is_path(const maze_s *self, const uint8_t row, const uint8_t col) {
  return maze_tile_data_at(self, row, col)->type == TILE_PATH;
}

static inline bool maze_is_intersection(const maze_s *self, const uint8_t row, const uint8_t col) {
  // clang-format off
  bool path_n = row > 0                && maze_is_path(self, row - 1, col);
  bool path_e = col + 1 < self->dimensions.x && maze_is_path(self, row, col + 1);
  bool path_s = row + 1 < self->dimensions.y && maze_is_path(self, row + 1, col);
  bool path_w = col > 0                && maze_is_path(self, row, col - 1);
  // clang-format on

  return (path_n || path_s) && (path_e || path_w);
}

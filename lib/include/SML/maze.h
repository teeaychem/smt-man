#pragma once

#include <assert.h>
#include <stddef.h>
#include <stdint.h>

#include "SML/enums.h"
#include "err.h"
#include "generic/pairs.h"

constexpr Pair_uint32 STANDARD_MAZE_DIMENSIONS = {.x = 28, .y = 31};

struct tile_edge_data_t {

  enum : uint8_t {
    TILE_LINES_INNER = 1,
    TILE_LINES_OUTER = 2,
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

struct maze_t {
  Pair_uint8 size;
  TileData *tiles;
};
typedef struct maze_t Maze;

// Methods

Result Maze_create(Maze *maze, const char *path);

Result Maze_detail(Maze *self);

void Maze_drop(Maze *self);

bool Maze_tile_in_direction_is_path(const Maze *self, const Pair_uint8 location, const Direction direction);

void Maze_complete_line_data(const Maze *self, TileData *tile_data, const uint8_t col, const uint8_t row);

Result Maze_complete_data(const Maze *self);

/// Satic inline

static inline size_t Maze_tile_offset(const Maze *self, const uint8_t col, const uint8_t row) {
  assert(col < self->size.x && "Invalid col");
  assert(row < self->size.y && "Invalid row");

  return ((size_t)row * self->size.x) + (size_t)col;
}

static inline TileData *Maze_tile_data_at(const Maze *self, const uint8_t col, const uint8_t row) {
  return &self->tiles[Maze_tile_offset(self, col, row)];
}

static inline bool Maze_is_path(const Maze *self, const uint8_t col, const uint8_t row) {
  return Maze_tile_data_at(self, col, row)->type == TILE_PATH;
}

static inline bool Maze_is_intersection(const Maze *self, const uint8_t col, const uint8_t row) {

  // clang-format off
  bool path_n = row != 0               && Maze_is_path(self, col, row - 1);
  bool path_e = col + 2 < self->size.x && Maze_is_path(self, col + 1, row);
  bool path_s = row + 2 < self->size.y && Maze_is_path(self, col, row + 1);
  bool path_w = col != 0               && Maze_is_path(self, col - 1, row);
  // clang-format on

  if (path_n || path_s) {
    return path_e || path_w;
  }

  if ((path_e) || (path_w)) {
    return path_n || path_s;
  }

  return false;
}

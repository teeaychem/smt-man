#pragma once

#include <assert.h>
#include <stdint.h>

#include "enums.h"
#include "generic/pairs.h"
#include "glib.h"
#include "utils.h"

struct tile_edge_data_t {

  enum {
    TILE_LINES_ONE = 0,
    TILE_LINES_TWO,
  } lines;

  enum {
    TILE_STYLE_LINE,
    TILE_STYLE_ARC,
  } edge_style;

  union {
    Direction edge_line_value;
    Quadrant edge_arc_value;
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
  uint8_t padding_top;
  uint8_t padding_bot;
};
typedef struct maze_t Maze;

// Methods

void Maze_create(Maze *maze, char *path);

void Maze_detail(Maze *self);

void Maze_destroy(Maze *self);

static inline TileData *Maze_abstract_at(const Maze *self, uint8_t col, uint8_t row) {
  if (!(col < self->size.x)) {
    g_log(nullptr, G_LOG_LEVEL_CRITICAL, "Invalid col: %d", col);
    pause_panic();
  }

  if (!(row < self->size.y)) {
    g_log(nullptr, G_LOG_LEVEL_CRITICAL, "Invalid row: %d", row);
    pause_panic();
  }

  return &self->tiles[(row * self->size.x) + col];
}

static inline bool Maze_abstract_is_path(const Maze *self, uint8_t col, uint8_t row) {
  return Maze_abstract_at(self, col, row)->type == TILE_PATH;
}

static inline bool Maze_first_row(const Maze *self) {
  return self->padding_top;
}

static inline bool Maze_last_row(const Maze *self) {
  return self->size.y - (self->padding_bot + 1);
}

#pragma once

#include <assert.h>
#include <stdint.h>

#include "enums.h"
#include "generic/pairs.h"

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

static inline TileData *Maze_abstract_at(const Maze *self, uint8_t x, uint8_t y) {
  assert(x < self->size.x);
  assert(y < self->size.y);
  return &self->tiles[(y * self->size.x) + x];
}

static inline bool Maze_abstract_is_path(const Maze *self, uint8_t x, uint8_t y) {
  return self->tiles[(y * self->size.x) + x].type == TILE_PATH;
  ;
}

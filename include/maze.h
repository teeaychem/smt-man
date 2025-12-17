#pragma once

#include <assert.h>
#include <stdint.h>

#include "generic/pairs.h"

// Tile representation data
struct tile_data_t {
  enum {
    TILE_EDGE,
    TILE_EMPTY,
    TILE_INFO,
    TILE_PATH,
  } type;

  union {

    struct {
      enum {
        TILE_EDGE_UP = 0,
        TILE_EDGE_RT,
        TILE_EDGE_DN,
        TILE_EDGE_LT,
      } offset;

      enum {
        TILE_LINES_ONE = 0,
        TILE_LINES_TWO,
      } lines;

      enum {
        TILE_STYLE_STRAIGHT = 0,
        TILE_STYLE_CURVED,
      } style;
    } edge_value;

    struct {
      enum {
        ITEM_NONE,
        ITEM_PELLET,
        ITEM_POWERUP,
      } item;

    } path_value;
  } value;
};
typedef struct tile_data_t TileData;

struct maze_t {
  Pair_uint8 size;
  TileData *tiles;
};
typedef struct maze_t Maze;

void Maze_create(Maze *maze, char *path);

void Maze_destroy(Maze *self);

static inline TileData Maze_abstract_at(Maze *self, uint8_t x, uint8_t y) {
  assert(x < self->size.x);
  assert(y < self->size.y);
  return self->tiles[(y * self->size.x) + x];
}

static inline bool Maze_abstract_is_path(Maze *self, uint8_t x, uint8_t y) {
  return self->tiles[(y * self->size.x) + x].type == TILE_PATH;
  ;
}

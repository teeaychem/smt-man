#pragma once

#include <assert.h>
#include <stdint.h>

#include <glib.h>

#include "constants.h"
#include "enums.h"
#include "generic/pairs.h"

struct tile_edge_data_t {

  uint32_t indent;

  enum : uint8_t {
    TILE_LINES_NONE = 0,
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

void Maze_create(Maze *maze, const char *path);

void Maze_detail(Maze *self);

void Maze_destroy(Maze *self);

bool Maze_tile_in_direction_is_path(const Maze *self, const Pair_uint8 location, const Direction direction);

void Maze_complete_line_data(const Maze *self, TileData *tile_data, const uint8_t col, const uint8_t row);

void Maze_complete_data(const Maze *self);

/// Satic inline

static inline TileData *Maze_abstract_at(const Maze *self, const uint8_t col, const uint8_t row) {
  if (!(col < self->size.x)) {
    g_log(nullptr, G_LOG_LEVEL_CRITICAL, "Invalid col: %d", col);
    exit(-2);
  }

  if (!(row < self->size.y)) {
    g_log(nullptr, G_LOG_LEVEL_CRITICAL, "Invalid row: %d", row);
    exit(-2);
  }

  return &self->tiles[(row * self->size.x) + col];
}

static inline bool Maze_abstract_is_path(const Maze *self, const uint8_t col, const uint8_t row) {
  return Maze_abstract_at(self, col, row)->type == TILE_PATH;
}

static inline Pair_uint8 Maze_location_from_sprite(const Pair_uint32 *sprite_location) {

  uint32_t x_mod = sprite_location->x % TILE_PIXELS;
  uint32_t y_mod = sprite_location->y % TILE_PIXELS;

  Pair_uint8 maze_location = {};

  if (x_mod < TILE_PIXELS / 2) {
    maze_location.x = (uint8_t)((sprite_location->x - x_mod) / TILE_PIXELS);
  } else {
    maze_location.x = (uint8_t)((sprite_location->x + (TILE_PIXELS - x_mod)) / TILE_PIXELS);
  }

  if (y_mod < TILE_PIXELS / 2) {
    maze_location.y = (uint8_t)((sprite_location->y - y_mod) / TILE_PIXELS);
  } else {
    maze_location.y = (uint8_t)((sprite_location->y + (TILE_PIXELS - y_mod)) / TILE_PIXELS);
  }

  return maze_location;
}

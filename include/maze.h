#pragma once

#include <assert.h>
#include <stdint.h>

#include <glib.h>

#include "constants.h"
#include "enums.h"
#include "generic/pairs.h"
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

bool Maze_tile_in_direction_is_path(Maze *self, Pair_uint8 location, Direction direction);

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

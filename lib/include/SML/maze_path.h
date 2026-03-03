#pragma once

#include <pthread.h>
#include <stddef.h>
#include <z3.h>

#include "SML/lexicon.h"
#include "generic/pairs.h"

struct maze_tile_t {
  path_e h;
  path_e v;
};
typedef struct maze_tile_t maze_tile_s;

/// Maze path

struct maze_path_t {
  pthread_mutex_t access_mutex;

  Pair_uint8 dimensions;

  struct {
    size_t count;
    maze_tile_s *data;
  } tiles;
};
typedef struct maze_path_t maze_path_s;

/// Methods

void maze_path_ctor(maze_path_s *self, const Pair_uint8 size);

void maze_path_dtor(maze_path_s *self);

void maze_path_clear(maze_path_s *self);

void maze_path_read(maze_path_s *self, const lexicon_s *lexicon, const Z3_context ctx, const Z3_model model, const maze_s *maze);

void maze_path_display(maze_path_s *self);

static inline maze_tile_s maze_path_at(maze_path_s *self, const Pair_uint8 location) {

  size_t tile_idx = Pair_uint8_flatten(&self->dimensions, location.x, location.y);
  assert(tile_idx < self->tiles.count);

  return self->tiles.data[tile_idx];
}

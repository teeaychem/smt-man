#pragma once

#include <pthread.h>
#include <stddef.h>
#include <z3.h>

#include "generic/pairs.h"

#include "SML/logic.h"

struct maze_tile_t {
  path_e h;
  path_e v;
};
typedef struct maze_tile_t maze_tile_s;

/// Maze path

struct maze_path_t {
  pthread_mutex_t mutex;
  Pair_uint8 size;
  size_t tile_count;
  maze_tile_s *tiles;
};
typedef struct maze_path_t maze_path_s;

/// Methods

void maze_path_ctor(maze_path_s *self, const Pair_uint8 size);

void maze_path_dtor(maze_path_s *self);

void maze_path_clear(maze_path_s *self);

void maze_path_read(maze_path_s *self, const Lexicon *lexicon, const Z3_context ctx, const Z3_model model, const Maze *maze);

void maze_path_display(maze_path_s *self, const Lexicon *lexicon);

static inline maze_tile_s maze_path_at(maze_path_s *self, const Pair_uint8 location) {

  size_t tile_idx = Pair_uint8_flatten(&self->size, location.x, location.y);
  assert(tile_idx < self->tile_count);

  return self->tiles[tile_idx];
}

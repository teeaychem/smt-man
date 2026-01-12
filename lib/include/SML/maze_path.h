#pragma once

#include <pthread.h>
#include <stddef.h>
#include <z3.h>

#include "SML/logic.h"
#include "generic/pairs.h"

struct maze_tile_t {
  Z3_ast h;
  Z3_ast v;
};
typedef struct maze_tile_t MazeTile;

/// Maze path

struct maze_path_t {
  pthread_mutex_t mutex;
  Pair_uint8 size;
  size_t tile_count;
  MazeTile *tiles;
};
typedef struct maze_path_t MazePath;

/// Methods

void MazePath_init(MazePath *self, const Pair_uint8 size);

void MazePath_clear(MazePath *self);

void MazePath_read(MazePath *self, const Language *language, const Z3_context ctx, const Z3_model model, const Maze *maze);

void MazePath_display(MazePath *self, const Language *language);

void MazePath_display(MazePath *self, const Language *language);

MazeTile MazePath_at(MazePath *self, const Pair_uint8 location);

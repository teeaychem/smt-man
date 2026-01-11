#pragma once

#include <stddef.h>
#include <z3.h>

#include "SML/logic.h"
#include "generic/pairs.h"

/// Maze path

struct maze_path_t {
  Pair_uint8 size;
  size_t tile_count;
  Z3_ast *tiles;
};
typedef struct maze_path_t MazePath;

/// Methods

void MazePath_init(MazePath *self, Pair_uint8 size);

void MazePath_clear(MazePath *self);

void MazePath_read(MazePath *self, const Language *lang, const Z3_context ctx, const Z3_model model, const Maze *maze);

void MazePath_display(MazePath *self, const Language *lang);

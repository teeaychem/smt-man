#pragma once

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <sys/syslog.h>

#include "pairs.h"

struct maze_t {
  Pair_uint32 size;
  char *abstract;
};

typedef struct maze_t Maze;

Maze Maze_create(char *path);

void Maze_destroy(Maze *self);

static inline char Maze_abstract_at(Maze *self, uint32_t x, uint32_t y) {
  assert(x < self->size.x);
  assert(y < self->size.y);
  return self->abstract[(y * self->size.x) + x];
}

static inline bool Maze_abstract_is_path(Maze *self, uint32_t x, uint32_t y) {
  return self->abstract[(y * self->size.x) + x] == '#';
}

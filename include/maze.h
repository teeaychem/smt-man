#pragma once

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <sys/syslog.h>

#include "generic/pairs.h"

struct maze_t {
  Pair_uint8 size;
  char *tiles;
};
typedef struct maze_t Maze;

void Maze_create(Maze *maze, char *path);

void Maze_destroy(Maze *self);

static inline char Maze_abstract_at(Maze *self, uint8_t x, uint8_t y) {
  assert(x < self->size.x);
  assert(y < self->size.y);
  return self->tiles[(y * self->size.x) + x];
}

static inline bool Maze_abstract_is_path(Maze *self, uint8_t x, uint8_t y) {
  return self->tiles[(y * self->size.x) + x] == '#';
}

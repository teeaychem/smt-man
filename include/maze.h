#pragma once

#include "utils/pairs.h"
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <sys/syslog.h>

#include "constants.h"

struct maze_t {

  PairI32 size;

  char *abstract;
  uint8_t *pixels;
};

typedef struct maze_t Maze;

Maze Maze_create(char *path);

void Maze_destroy(Maze *self);

bool Maze_is_open(Maze *self, PairI32 *tile);

static inline uint8_t Maze_pixel_at_point(Maze *self, PairI32 point) {
  return self->pixels[(point.y * PIXEL_COUNTS.x) + point.x];
}

static inline char Maze_abstract_at(Maze *self, int32_t x, int32_t y) {
  assert(x < self->size.x);
  assert(y < self->size.y);
  return self->abstract[(y * self->size.x) + x];
}

static inline bool Maze_abstract_is_path(Maze *self, int32_t x, int32_t y) {
  return self->abstract[(y * self->size.x) + x] == '#';
}

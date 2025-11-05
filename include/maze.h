#pragma once

#include "utils/pairs.h"
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/syslog.h>

struct maze_t {

  PairI32 size;

  char *pixels;
};

typedef struct maze_t Maze;

Maze Maze_create(char *path);

void Maze_destroy(Maze *self);

bool Maze_is_open(Maze *self, PairI32 *tile);

uint8_t Maze_at_point(Maze *self, PairI32 tile);

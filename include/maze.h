#pragma once

#include "utils/pairs.h"
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/syslog.h>

struct maze_t {

  PairI32 size;

  char *tiles;
};

typedef struct maze_t Maze;

Maze Maze_create(char *path);

void Maze_destroy(Maze *self);

bool Maze_isOpen(Maze *self, PairI32 *tile);

uint8_t Maze_tileAt(Maze *self, PairI32 *tile);

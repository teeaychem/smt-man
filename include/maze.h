#pragma once

#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syslog.h>

struct maze_t {

  int32_t size_x;
  int32_t size_y;
  char *tiles;
};

typedef struct maze_t Maze;

#ifdef __cplusplus
extern "C" {
#endif

Maze Maze_create(char *path);

void Maze_destroy(Maze *self);

bool Maze_isOpen(Maze *self, int32_t x, int32_t y);

uint8_t Maze_tileAt(Maze *self, int32_t x, int32_t y);
#ifdef __cplusplus
}
#endif

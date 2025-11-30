#include <assert.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "constants.h"
#include "maze.h"
#include "utils/pairs.h"

void next_line(FILE *file) {
  char c;
  while (c != EOF && c != '\n') {
    c = fgetc(file);
  }
}

Maze Maze_create(char *path) {

  Maze self = {.size = {},
               .pixels = NULL};

  size_t tile_count = 0;
  bool preamble_ok = true;

  FILE *file = fopen(path, "r");
  if (!file) {
    printf("%p ? %d", file, file == NULL);
    printf("%s\n", path);
    printf("Failed to open maze from: %s", path);
    exit(1);
  }

  char read;

  while (read != EOF) {
    read = fgetc(file);

    switch (read) {
    case EOF:
      break;

    case 'c': {
    } break;

    case 'w': {
      if (!fscanf(file, "%" SCNu32, &(self.size.x))) {
        printf("Failed to read maze width");
        preamble_ok = false;
      };
    } break;

    case 'h': {
      if (!fscanf(file, "%" SCNu32, &(self.size.y))) {
        printf("Failed to read maze height");
        preamble_ok = false;
      };
    } break;

    case 'm': {
      ungetc(read, file);
      read = EOF;
    } break;

    default: {
    } break;
    }

    if (read != EOF) {
      next_line(file);
    }
  }

  if ((self.size.x % TILE_COUNTS.x) != 0 | (self.size.y % TILE_COUNTS.y) != 0) {
    printf("Maze dimension %dx%d is not an integer scale of %dx%d",
           self.size.x, self.size.y,
           TILE_COUNTS.x, TILE_COUNTS.y);
    preamble_ok = false;
  }

  if (!preamble_ok) {
    printf("Failed to construct maze");
    exit(1);
  }

  self.abstract = malloc(PairI32_area(&self.size) * sizeof(*self.abstract));
  self.pixels = malloc(PairI32_area(&PIXEL_COUNTS) * sizeof(*self.pixels));
  memset(self.pixels, '\0', PairI32_area(&PIXEL_COUNTS));

  int32_t x_scale = PIXEL_COUNTS.x / self.size.x;
  int32_t y_scale = PIXEL_COUNTS.y / self.size.y;

  int32_t pos_x = 0;
  int32_t pos_y = 0;

  int32_t tile_idx = 0;

  while ((read = fgetc(file)) != EOF) {
    switch (read) {
    case 'c': {
      next_line(file);
    } break;

    case 'm': {
      pos_x = 0;
    } break;

    case '\n': {
      if (pos_x != self.size.x) {
        printf("x_x"), exit(-1);
      }
      pos_y += 1;
    } break;

    default: {
      self.abstract[pos_y * self.size.x + pos_x] = read;
      for (size_t pxl_y = 0; pxl_y < TILE_SCALE; ++pxl_y) {
        for (size_t pxl_x = 0; pxl_x < TILE_SCALE; ++pxl_x) {
          self.pixels[(((pos_y * TILE_SCALE) + pxl_y) * PIXEL_COUNTS.x) + pxl_x + (pos_x * TILE_SCALE)] = read;
        }
      }

      pos_x += 1;

      if (read == '#') {
        ++tile_count;
      }
    }
    }
  }

  if (pos_y != self.size.y) {
    printf("y_y"), exit(-1);
  }

  printf("Constructed maze %dx%d (%zu)", self.size.x, self.size.y, tile_count);

  return self;
}

void Maze_destroy(Maze *self) {
  free(self->abstract);
  free(self->pixels);
}

bool Maze_is_open(Maze *self, PairI32 *point) {
  bool yOk = 0 <= point->y && point->y < PIXEL_COUNTS.y;
  bool xOk = 0 <= point->x && point->x < PIXEL_COUNTS.x;
  bool locationOk = Maze_pixel_at_point(self, *point) == (uint8_t)'#';

  return yOk && xOk && locationOk;
}

void Maze_pixel_stdout(Maze *self) {
  for (size_t y = 0; y < PIXEL_COUNTS.y; ++y) {
    for (size_t x = 0; x < PIXEL_COUNTS.x; ++x) {
      printf("%c", self->pixels[(y * PIXEL_COUNTS.x) + x]);
    }

    if (y + TILE_SCALE < PIXEL_COUNTS.y) {
      printf("\n");
    }
  }
}

void Maze_abstract_stdout(Maze *self) {
  for (int32_t c = 0; c < self->size.y; ++c) {
    for (int32_t r = 0; r < self->size.x; ++r) {
      printf("%c", Maze_abstract_at(self, r, c));
    }
    printf("\n");
  }
}

#include <assert.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "constants.h"
#include "glib.h"
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

  FILE *file_ptr = fopen(path, "r");
  if (file_ptr == NULL) {
    g_log(NULL, G_LOG_LEVEL_CRITICAL, "Failed to open maze from: %s", path);
    exit(1);
  }

  char read = ' ';
  while (read != EOF) {
    read = fgetc(file_ptr);

    switch (read) {
    case EOF:
      break;

    case 'c': {
    } break;

    case 'w': {
      if (!fscanf(file_ptr, "%" SCNu32, &(self.size.x))) {
        printf("Failed to read maze width");
        preamble_ok = false;
      };
    } break;

    case 'h': {
      if (!fscanf(file_ptr, "%" SCNu32, &(self.size.y))) {
        printf("Failed to read maze height");
        preamble_ok = false;
      };
    } break;

    case 'm': {
      ungetc(read, file_ptr);
      read = EOF;
    } break;

    default: {
    } break;
    }

    if (read != EOF) {
      next_line(file_ptr);
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
    fclose(file_ptr);
    exit(1);
  }

  self.abstract = malloc(PairI32_area(&self.size) * sizeof(*self.abstract));
  self.pixels = malloc(PairI32_area(&PIXEL_DIMENSIONS) * sizeof(*self.pixels));
  memset(self.pixels, '\0', PairI32_area(&PIXEL_DIMENSIONS));

  int32_t x_scale = PIXEL_DIMENSIONS.x / self.size.x;
  int32_t y_scale = PIXEL_DIMENSIONS.y / self.size.y;

  int32_t pos_x = 0;
  int32_t pos_y = 0;

  int32_t tile_idx = 0;

  while ((read = fgetc(file_ptr)) != EOF) {
    switch (read) {
    case 'c': {
      next_line(file_ptr);
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
          self.pixels[(((pos_y * TILE_SCALE) + pxl_y) * PIXEL_DIMENSIONS.x) + pxl_x + (pos_x * TILE_SCALE)] = read;
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

  fclose(file_ptr);

  printf("Constructed maze %dx%d (%zu)", self.size.x, self.size.y, tile_count);

  return self;
}

void Maze_destroy(Maze *self) {
  free(self->abstract);
  free(self->pixels);
}

void Maze_pixel_stdout(Maze *self) {
  for (size_t y = 0; y < PIXEL_DIMENSIONS.y; ++y) {
    for (size_t x = 0; x < PIXEL_DIMENSIONS.x; ++x) {
      printf("%c", self->pixels[(y * PIXEL_DIMENSIONS.x) + x]);
    }

    if (y + TILE_SCALE < PIXEL_DIMENSIONS.y) {
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

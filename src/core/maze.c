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
  char c = ' ';
  while (c != EOF && c != '\n') {
    c = (char)fgetc(file);
  }
}

Maze Maze_create(char *path) {

  Maze self = {
      .size = {},
  };

  size_t tile_count = 0;
  bool preamble_ok = true;

  FILE *file_ptr = fopen(path, "r");
  if (file_ptr == NULL) {
    g_log(NULL, G_LOG_LEVEL_CRITICAL, "Failed to open maze from: %s", path);
    exit(1);
  }

  char read = ' ';
  while (read != EOF) {
    read = (char)fgetc(file_ptr);

    switch (read) {
    case EOF:
      break;

    case 'c': {
    } break;

    case 'w': {
      if (!fscanf(file_ptr, "%" SCNu32, &(self.size.x))) {
        g_log(NULL, G_LOG_LEVEL_WARNING, "Failed to read maze width: %s", path);
        preamble_ok = false;
      };
    } break;

    case 'h': {
      if (!fscanf(file_ptr, "%" SCNu32, &(self.size.y))) {
        g_log(NULL, G_LOG_LEVEL_WARNING, "Failed to read maze height: %s", path);
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
    g_log(NULL,
          G_LOG_LEVEL_WARNING,
          "Maze dimension %dx%d is not an integer scale of %dx%d", self.size.x, self.size.y, TILE_COUNTS.x, TILE_COUNTS.y);

    preamble_ok = false;
  }

  if (!preamble_ok) {
    fclose(file_ptr);
    g_log(NULL, G_LOG_LEVEL_CRITICAL, "Failed to construct maze: %s", path);
    exit(1);
  }

  self.abstract = malloc(PairI32_area(&self.size) * sizeof(*self.abstract));

  uint32_t pos_x = 0;
  uint32_t pos_y = 0;

  while ((read = (char)fgetc(file_ptr)) != EOF) {
    switch (read) {
    case 'c': {
      next_line(file_ptr);
    } break;

    case 'm': {
      pos_x = 0;
    } break;

    case '\n': {
      if (pos_x != self.size.x) {
        g_log(NULL, G_LOG_LEVEL_CRITICAL, "Invalid row width: %s", path);
        exit(-1);
      }
      pos_y += 1;
    } break;

    default: {
      self.abstract[pos_y * self.size.x + pos_x] = read;

      pos_x += 1;

      if (read == '#') {
        ++tile_count;
      }
    }
    }
  }

  if (pos_y != self.size.y) {
    g_log(NULL, G_LOG_LEVEL_CRITICAL, "Invalid col height: %s", path);
    exit(-1);
  }

  fclose(file_ptr);

  g_log(NULL, G_LOG_LEVEL_INFO, "Constructed maze %dx%d (%zu)", self.size.x, self.size.y, tile_count);

  return self;
}

void Maze_destroy(Maze *self) {
  free(self->abstract);
}

void Maze_abstract_stdout(Maze *self) {
  for (uint32_t c = 0; c < self->size.y; ++c) {
    for (uint32_t r = 0; r < self->size.x; ++r) {
      putchar(Maze_abstract_at(self, r, c));
    }
    putchar('\n');
  }
}

#include <assert.h>
#include <stdint.h>

#include "constants.h"
#include "generic/pairs.h"
#include "glib.h"
#include "maze.h"

void next_line(FILE *file) {
  char chx = ' ';
  while (chx != EOF && chx != '\n') {
    chx = (char)fgetc(file);
  }
}

void Maze_create(Maze *maze, char *path) {

  *maze = (Maze){
      .size = {},
  };

  size_t tile_count = 0;
  bool preamble_ok = true;

  FILE *file_ptr = fopen(path, "r");
  if (file_ptr == nullptr) {
    g_log(nullptr, G_LOG_LEVEL_CRITICAL, "Failed to open maze from: %s", path);
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
      if (!fscanf(file_ptr, "%" SCNu8, &(maze->size.x))) {
        g_log(nullptr, G_LOG_LEVEL_WARNING, "Failed to read maze width: %s", path);
        preamble_ok = false;
      };
    } break;

    case 'h': {
      if (!fscanf(file_ptr, "%" SCNu8, &(maze->size.y))) {
        g_log(nullptr, G_LOG_LEVEL_WARNING, "Failed to read maze height: %s", path);
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

  if ((maze->size.x % TILE_COUNTS.x) != 0 | (maze->size.y % TILE_COUNTS.y) != 0) {
    g_log(nullptr,
          G_LOG_LEVEL_WARNING,
          "Maze dimension %dx%d is not an integer scale of %dx%d", maze->size.x, maze->size.y, TILE_COUNTS.x, TILE_COUNTS.y);

    preamble_ok = false;
  }

  if (!preamble_ok) {
    fclose(file_ptr);
    g_log(nullptr, G_LOG_LEVEL_CRITICAL, "Failed to construct maze: %s", path);
    exit(1);
  }

  maze->tiles = malloc((size_t)maze->size.x * (size_t)maze->size.y * sizeof(*maze->tiles));

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
      if (pos_x != maze->size.x) {
        g_log(nullptr, G_LOG_LEVEL_CRITICAL, "Invalid row width: %s", path);
        exit(-1);
      }
      pos_y += 1;
    } break;

    default: {
      maze->tiles[pos_y * maze->size.x + pos_x] = read;

      pos_x += 1;

      if (read == '#') {
        ++tile_count;
      }
    }
    }
  }

  if (pos_y != maze->size.y) {
    g_log(nullptr, G_LOG_LEVEL_CRITICAL, "Invalid col height: %s", path);
    exit(-1);
  }

  fclose(file_ptr);

  g_log(nullptr, G_LOG_LEVEL_INFO, "Constructed maze %dx%d (%zu)", maze->size.x, maze->size.y, tile_count);
}

void Maze_destroy(Maze *self) {
  free(self->tiles);
}

void Maze_abstract_stdout(Maze *self) {
  for (uint8_t c = 0; c < self->size.y; ++c) {
    for (uint8_t r = 0; r < self->size.x; ++r) {
      putchar(Maze_abstract_at(self, r, c));
    }
    putchar('\n');
  }
}

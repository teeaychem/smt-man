
#include <inttypes.h>
#include <string.h>

#include "maze.h"
#include "stumpless/log.h"
#include "utils/pairs.h"

void next_line(FILE *file) {
  char c;
  while (c != EOF && c != '\n') {
    c = fgetc(file);
  }
}

Maze Maze_create(char *path) {

  Maze self = {.size.x = 0, .size.y = 0, .tiles = NULL};

  bool preambleOk = true;

  FILE *file = fopen(path, "r");
  if (file == NULL) {
    stumplog(LOG_ERR, "Failed to open maze");
    preambleOk = false;
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
        stumplog(LOG_ERR, "Failed to read maze width");
        preambleOk = false;
      };
    } break;

    case 'h': {
      if (!fscanf(file, "%" SCNu32, &(self.size.y))) {
        stumplog(LOG_ERR, "Failed to read maze height");
        preambleOk = false;
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

  if (!preambleOk) {
    stumplog(LOG_INFO, path);
    stumplog(LOG_CRIT, "Failed to construct maze");
    exit(1);
  }

  self.tiles = (char *)malloc(PairI32_area(&self.size));
  memset(self.tiles, '\0', PairI32_area(&self.size));

  int32_t tile_idx = 0;

  while ((read = fgetc(file)) != EOF) {
    switch (read) {
    case 'c': {
      next_line(file);
    } break;

    case 'm': {
    } break;

    case '\n': {
      while (tile_idx % self.size.x != 0 || tile_idx == 0) {
        ++tile_idx;
      }
    } break;

    default: {
      self.tiles[tile_idx] = read;
      ++tile_idx;
    }
    }
  }

  return self;
}

void Maze_destroy(Maze *self) {
  free(self->tiles);
}

bool Maze_isOpen(Maze *self, PairI32 *tile) {
  bool yOk = 0 <= tile->y && tile->y < self->size.y;
  bool xOk = 0 <= tile->x && tile->x < self->size.x;
  bool locationOk = Maze_tileAt(self, tile) == '#';

  return yOk && xOk && locationOk;
}

uint8_t Maze_tileAt(Maze *self, PairI32 *tile) {
  return self->tiles[tile->y * self->size.x + tile->x];
}

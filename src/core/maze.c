#include "maze.h"
#include "stumpless/log.h"

void next_line(FILE *file) {
  char c;
  while (c != EOF && c != '\n') {
    c = fgetc(file);
  }
}

Maze Maze_create(char *path) {

  Maze self = {.size_x = 0, .size_y = 0, .tiles = NULL};

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
      if (!fscanf(file, "%" SCNu32, &self.size_x)) {
        stumplog(LOG_ERR, "Failed to read maze width");
        preambleOk = false;
      };
    } break;

    case 'h': {
      if (!fscanf(file, "%" SCNu32, &self.size_y)) {
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

  self.tiles = (char *)malloc(self.size_x * self.size_y);
  memset(self.tiles, '\0', self.size_x * self.size_y);

  int32_t tile_idx = 0;

  while ((read = fgetc(file)) != EOF) {
    switch (read) {
    case 'c': {
      next_line(file);
    } break;

    case 'm': {
    } break;

    case '\n': {
      while (tile_idx % self.size_x != 0 || tile_idx == 0) {
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

bool Maze_isOpen(Maze *self, int32_t x, int32_t y) {
  bool yOk = 0 <= y && y < self->size_y;
  bool xOk = 0 <= x && x < self->size_x;
  bool locationOk = Maze_tileAt(self, x, y) == '#';

  return yOk && xOk && locationOk;
}

uint8_t Maze_tileAt(Maze *self, int32_t x, int32_t y) {
  return self->tiles[y * self->size_x + x];
}

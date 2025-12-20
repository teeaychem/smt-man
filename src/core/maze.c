#include <assert.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

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

  constexpr Pair_uint32 standard_tile_dimensions = {.x = 28, .y = 36};
  if ((maze->size.x % standard_tile_dimensions.x) != 0 | (maze->size.y % standard_tile_dimensions.y) != 0) {
    g_log(nullptr,
          G_LOG_LEVEL_WARNING,
          "Maze dimension %dx%d is not an integer scale of %dx%d", maze->size.x, maze->size.y, standard_tile_dimensions.x, standard_tile_dimensions.y);

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

      TileData data = {};

      switch (read) {

      case ' ': {
        data.type = TILE_PATH;
        data.value.path_value.item = ITEM_NONE;
      } break;

      case '-': {
        data.type = TILE_PATH;
        data.value.path_value.item = ITEM_PELLET;
      } break;

      case '+': {
        data.type = TILE_PATH;
        data.value.path_value.item = ITEM_POWERUP;
      } break;

      case 'H': {
        data.type = TILE_EDGE;
      } break;

      case '|': {
        data.type = TILE_EDGE;
      } break;

      case '_': {
        data.type = TILE_EMPTY;
      } break;

      case 'X': {
        data.type = TILE_INFO;
      } break;
      }

      maze->tiles[pos_y * maze->size.x + pos_x] = data;

      pos_x += 1;

      if (read == '-') {
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
      switch (Maze_abstract_at(self, r, c)->type) {

      case TILE_EDGE: {
        putchar('#');
      } break;
      case TILE_EMPTY: {
        putchar('_');
      } break;
      case TILE_INFO: {
        putchar('X');
      } break;
      case TILE_PATH: {
        putchar(' ');
      } break;
        break;
      }
    }
    putchar('\n');
  }
}

void Tile_set_arc(TileData *tile, Quadrant quadrant) {
  tile->value.edge_value.edge_style = TILE_STYLE_ARC;
  tile->value.edge_value.edge_arc_value = quadrant;
}

void Maze_detail_arc_outer(Maze *self) {

  { // LEFT
    uint8_t col = 0;
    TileData *tile;

    { // TOP
      tile = Maze_abstract_at(self, col, 3);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, SECOND);
      }
    }

    { // BOTTOM
      tile = Maze_abstract_at(self, col, self->size.y - 3);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, THIRD);
      }
    }

    { // INTERMEDIATE
      for (uint8_t row = 4; row < self->size.y - 3; ++row) {
        tile = Maze_abstract_at(self, col, row);
        if (tile->type == TILE_EDGE) {
          if (Maze_abstract_at(self, col + 1, row)->type == TILE_EDGE) {

            if ((Maze_abstract_at(self, col, row - 1)->type == TILE_EDGE) &&
                (Maze_abstract_at(self, col, row + 1)->type == TILE_EDGE)) {
              if (Maze_abstract_at(self, col + 1, row - 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, THIRD);
              } else if (Maze_abstract_at(self, col + 1, row + 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, SECOND);
              }
            }

            if ((Maze_abstract_at(self, col, row - 1)->type != TILE_EDGE) &&
                (Maze_abstract_at(self, col, row + 1)->type == TILE_EDGE)) {
              Tile_set_arc(tile, SECOND);
            }

            if ((Maze_abstract_at(self, col, row - 1)->type == TILE_EDGE) &&
                (Maze_abstract_at(self, col, row + 1)->type != TILE_EDGE)) {
              Tile_set_arc(tile, THIRD);
            }
          }
        }
      }
    }
  }

  { // RIGHT
    uint8_t col = self->size.x - 1;
    TileData *tile;

    { // TOP
      tile = Maze_abstract_at(self, col, 3);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, FIRST);
      }
    }

    { // BOTTOM
      tile = Maze_abstract_at(self, col, self->size.y - 3);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, FOURTH);
      }
    }

    { // INTERMEDIATE
      for (uint8_t row = 4; row < self->size.y - 3; ++row) {
        tile = Maze_abstract_at(self, col, row);
        if (tile->type == TILE_EDGE) {
          if (Maze_abstract_at(self, col - 1, row)->type == TILE_EDGE) {

            if ((Maze_abstract_at(self, col, row - 1)->type == TILE_EDGE) &&
                (Maze_abstract_at(self, col, row + 1)->type == TILE_EDGE)) {
              if (Maze_abstract_at(self, col - 1, row - 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, FOURTH);
              } else if (Maze_abstract_at(self, col - 1, row + 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, FIRST);
              }
            }

            if ((Maze_abstract_at(self, col, row - 1)->type != TILE_EDGE) &&
                (Maze_abstract_at(self, col, row + 1)->type == TILE_EDGE)) {
              Tile_set_arc(tile, FIRST);
            }

            if ((Maze_abstract_at(self, col, row - 1)->type == TILE_EDGE) &&
                (Maze_abstract_at(self, col, row + 1)->type != TILE_EDGE)) {
              Tile_set_arc(tile, FOURTH);
            }
          }
        }
      }
    }
  }
}

/* void Maze_detail_arc_inner(Maze *self) { */
/*   for (uint8_t c = 0; c < self->size.y; ++c) { */
/*     for (uint8_t r = 0; r < self->size.x; ++r) { */
/*       TileData *tile = Maze_abstract_at(self, c, r); */
/*       if (tile->type == TILE_EDGE) { */
/*         if (c == 0 && r == 0) { */
/*           tile->value.edge_value.edge_style = TILE_STYLE_ARC; */
/*           tile->value.edge_value.edge_arc_value = FIRST; */
/*         } */

/*         if (c == 0 && r + 1 == self->size.y) { */
/*           tile->value.edge_value.edge_style = TILE_STYLE_ARC; */
/*           tile->value.edge_value.edge_arc_value = THIRD; */
/*         } */
/*       } */
/*     } */
/*   } */
/* } */

void Maze_detail(Maze *self) {
  Maze_detail_arc_outer(self);
}

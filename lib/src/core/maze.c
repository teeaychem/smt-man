#include <assert.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

#include <slog.h>
#include <stdlib.h>

#include "generic/pairs.h"

#include "SML/maze.h"

void next_line(FILE *file) {
  char chx = ' ';
  while (chx != EOF && chx != '\n') {
    chx = (char)fgetc(file);
  }
}

Result Maze_create(Maze *maze, const char *path) {

  *maze = (Maze){
      .tiles = nullptr,
      .size = {},
  };

  size_t tile_count = 0;
  bool preamble_ok = true;

  FILE *file_ptr = fopen(path, "r");
  assert(file_ptr != nullptr && "Failed to open maze");

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
        printf("Failed to read maze width: %s", path);
        preamble_ok = false;
      };
    } break;

    case 'h': {
      if (!fscanf(file_ptr, "%" SCNu8, &(maze->size.y))) {
        printf("Failed to read maze height: %s", path);
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

  if ((maze->size.x % STANDARD_MAZE_DIMENSIONS.x) != 0 | (maze->size.y % STANDARD_MAZE_DIMENSIONS.y) != 0) {
    slog_display(SLOG_WARN, 0,
                 "Maze dimension %dx%d is not an integer scale of %dx%d\n", maze->size.x, maze->size.y, STANDARD_MAZE_DIMENSIONS.x, STANDARD_MAZE_DIMENSIONS.y);

    preamble_ok = false;
  }

  if (!preamble_ok) {
    fclose(file_ptr);
    printf("Failed to construct maze from: %s\n", path);
    exit(1);
  }

  maze->tiles = malloc((size_t)maze->size.x * (size_t)maze->size.y * sizeof(*maze->tiles));

  uint8_t pos_x = 0;
  uint8_t pos_y = 0;

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
        slog_display(SLOG_ERROR, 0, "Invalid width.\n\tHave: %d\n\tExpected: %d\n\tRow: %d\n\tMaze: %s\n", pos_x, maze->size.x, pos_y, path);
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
        data.value.edge_value.edge_style = TILE_STYLE_LINE;
      } break;

      case '|': {
        data.type = TILE_EDGE;
        data.value.edge_value.edge_style = TILE_STYLE_LINE;
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
    assert(pos_y != maze->size.y);
    slog_display(SLOG_ERROR, 0,
                 "Invalid height.\n\tHave: %d\n\tExpected: %d\n\tMaze: %s\n", pos_y, maze->size.y, path);
    exit(-1);
  }

  fclose(file_ptr);

  slog_display(SLOG_INFO, 0, "Constructed maze %dx%d (%zu)\n", maze->size.x, maze->size.y, tile_count);
  return RESULT_OK;
}

void Maze_drop(Maze *self) {
  free(self->tiles);
  self->tiles = nullptr;
  self->size.x = 0;
  self->size.y = 0;
}

void Maze_abstract_stdout(Maze *self) {
  for (uint8_t c = 0; c < self->size.y; ++c) {
    for (uint8_t r = 0; r < self->size.x; ++r) {
      switch (Maze_tile_data_at(self, r, c)->type) {

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
  tile->value.edge_value.edge_arc_quadrant = quadrant;
}

void Maze_detail_arc_outer(Maze *self) {

  { // LEFT
    uint8_t col = 0;
    TileData *tile = nullptr;

    { // TOP
      tile = Maze_tile_data_at(self, col, 0);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_2);
        tile->value.edge_value.lines = TILE_LINES_OUTER;
      }
    }

    { // BOTTOM
      tile = Maze_tile_data_at(self, col, self->size.y - 1);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_3);
        tile->value.edge_value.lines = TILE_LINES_OUTER;
      }
    }

    { // INTERMEDIATE
      for (uint8_t row = 4; row < self->size.y - 1; ++row) {
        tile = Maze_tile_data_at(self, col, row);
        if (tile->type == TILE_EDGE) {
          if (Maze_tile_data_at(self, col + 1, row)->type == TILE_EDGE) {

            if ((Maze_tile_data_at(self, col, row - 1)->type == TILE_EDGE) &&
                (Maze_tile_data_at(self, col, row + 1)->type == TILE_EDGE)) {
              if (Maze_tile_data_at(self, col + 1, row - 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_3);
                tile->value.edge_value.lines = TILE_LINES_OUTER;
              } else if (Maze_tile_data_at(self, col + 1, row + 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_2);
                tile->value.edge_value.lines = TILE_LINES_OUTER;
              }
            }

            if ((Maze_tile_data_at(self, col, row - 1)->type != TILE_EDGE) &&
                (Maze_tile_data_at(self, col, row + 1)->type == TILE_EDGE)) {
              Tile_set_arc(tile, QUADRANT_2);
              tile->value.edge_value.lines = TILE_LINES_OUTER;
            }

            if ((Maze_tile_data_at(self, col, row - 1)->type == TILE_EDGE) &&
                (Maze_tile_data_at(self, col, row + 1)->type != TILE_EDGE)) {
              Tile_set_arc(tile, QUADRANT_3);
              tile->value.edge_value.lines = TILE_LINES_OUTER;
            }
          }
        }
      }
    }
  }

  { // RIGHT
    uint8_t col = self->size.x - 1;
    TileData *tile = nullptr;

    { // TOP
      tile = Maze_tile_data_at(self, col, 0);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_1);
        tile->value.edge_value.lines = TILE_LINES_OUTER;
      }
    }

    { // BOTTOM
      tile = Maze_tile_data_at(self, col, self->size.y - 1);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_4);
        tile->value.edge_value.lines = TILE_LINES_OUTER;
      }
    }

    { // INTERMEDIATE
      for (uint8_t row = 4; row < self->size.y - 1; ++row) {
        tile = Maze_tile_data_at(self, col, row);
        if (tile->type == TILE_EDGE) {
          if (Maze_tile_data_at(self, col - 1, row)->type == TILE_EDGE) {

            if ((Maze_tile_data_at(self, col, row - 1)->type == TILE_EDGE) &&
                (Maze_tile_data_at(self, col, row + 1)->type == TILE_EDGE)) {
              if (Maze_tile_data_at(self, col - 1, row - 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_4);
                tile->value.edge_value.lines = TILE_LINES_OUTER;
              } else if (Maze_tile_data_at(self, col - 1, row + 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_1);
                tile->value.edge_value.lines = TILE_LINES_OUTER;
              }
            }

            if ((Maze_tile_data_at(self, col, row - 1)->type != TILE_EDGE) &&
                (Maze_tile_data_at(self, col, row + 1)->type == TILE_EDGE)) {
              Tile_set_arc(tile, QUADRANT_1);
              tile->value.edge_value.lines = TILE_LINES_OUTER;
            }

            if ((Maze_tile_data_at(self, col, row - 1)->type == TILE_EDGE) &&
                (Maze_tile_data_at(self, col, row + 1)->type != TILE_EDGE)) {
              Tile_set_arc(tile, QUADRANT_4);
              tile->value.edge_value.lines = TILE_LINES_OUTER;
            }
          }
        }
      }
    }
  }

  { // TOP
    uint8_t row = 0;
    TileData *tile = nullptr;

    { // LEFT
      tile = Maze_tile_data_at(self, 0, row);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_2);
        tile->value.edge_value.lines = TILE_LINES_OUTER;
      }
    }

    { // RIGHT
      tile = Maze_tile_data_at(self, self->size.x - 1, row);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_1);
        tile->value.edge_value.lines = TILE_LINES_OUTER;
      }
    }

    { // INTERMEDIATE
      for (uint8_t col = 1; col < self->size.x - 1; ++col) {
        tile = Maze_tile_data_at(self, col, row);
        if (tile->type == TILE_EDGE) {
          if (Maze_tile_data_at(self, col, row + 1)->type == TILE_EDGE) {

            if ((Maze_tile_data_at(self, col - 1, row)->type == TILE_EDGE) &&
                (Maze_tile_data_at(self, col + 1, row)->type == TILE_EDGE)) {
              if (Maze_tile_data_at(self, col + 1, row + 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_2);
                tile->value.edge_value.lines = TILE_LINES_OUTER;
              } else if (Maze_tile_data_at(self, col - 1, row + 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_1);
                tile->value.edge_value.lines = TILE_LINES_OUTER;
              }
            }
          }
        }
      }
    }
  }

  { // BOTTOM
    uint8_t row = self->size.y - 1;
    TileData *tile = nullptr;

    { // LEFT
      tile = Maze_tile_data_at(self, 0, row);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_3);
        tile->value.edge_value.lines = TILE_LINES_OUTER;
      }
    }

    { // RIGHT
      tile = Maze_tile_data_at(self, self->size.x - 1, row);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_4);
        tile->value.edge_value.lines = TILE_LINES_OUTER;
      }
    }

    { // INTERMEDIATE
      for (uint8_t col = 1; col < self->size.x - 1; ++col) {
        tile = Maze_tile_data_at(self, col, row);
        if (tile->type == TILE_EDGE) {
          if (Maze_tile_data_at(self, col, row - 1)->type == TILE_EDGE) {

            if ((Maze_tile_data_at(self, col - 1, row)->type == TILE_EDGE) &&
                (Maze_tile_data_at(self, col + 1, row)->type == TILE_EDGE)) {
              if (Maze_tile_data_at(self, col + 1, row - 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_3);
                tile->value.edge_value.lines = TILE_LINES_OUTER;
              } else if (Maze_tile_data_at(self, col - 1, row - 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_4);
                tile->value.edge_value.lines = TILE_LINES_OUTER;
              }
            }
          }
        }
      }
    }
  }
}

void Maze_detail_arc_inner(Maze *self) {
  for (uint8_t col = 1; col < self->size.x - 1; ++col) {
    for (uint8_t row = 1; row < self->size.y - 1; ++row) {
      TileData *tile = Maze_tile_data_at(self, col, row);
      if (tile->type == TILE_EDGE) {

        bool up_is_edge = (Maze_tile_data_at(self, col, row - 1)->type == TILE_EDGE);
        bool left_is_edge = Maze_tile_data_at(self, col - 1, row)->type == TILE_EDGE;
        bool right_is_edge = (Maze_tile_data_at(self, col + 1, row)->type == TILE_EDGE);
        bool down_is_edge = Maze_tile_data_at(self, col, row + 1)->type == TILE_EDGE;

        if ((left_is_edge && down_is_edge) && (!right_is_edge && !up_is_edge)) {
          Tile_set_arc(tile, QUADRANT_1);
          tile->value.edge_value.lines = TILE_LINES_INNER;
        }

        else if ((left_is_edge && down_is_edge) && (Maze_tile_data_at(self, col - 1, row + 1)->type == TILE_PATH)) {
          Tile_set_arc(tile, QUADRANT_1);
          tile->value.edge_value.lines = TILE_LINES_OUTER;
        }

        else if ((right_is_edge && down_is_edge) && (!left_is_edge && !up_is_edge)) {
          Tile_set_arc(tile, QUADRANT_2);
          tile->value.edge_value.lines = TILE_LINES_INNER;
        }

        else if ((right_is_edge && down_is_edge) && (Maze_tile_data_at(self, col + 1, row + 1)->type == TILE_PATH)) {
          Tile_set_arc(tile, QUADRANT_2);
          tile->value.edge_value.lines = TILE_LINES_OUTER;
        }

        else if ((right_is_edge && up_is_edge) && (!left_is_edge && !down_is_edge)) {
          Tile_set_arc(tile, QUADRANT_3);
          tile->value.edge_value.lines = TILE_LINES_INNER;
        }

        else if ((right_is_edge && up_is_edge) && (Maze_tile_data_at(self, col + 1, row - 1)->type == TILE_PATH)) {
          Tile_set_arc(tile, QUADRANT_3);
          tile->value.edge_value.lines = TILE_LINES_OUTER;
        }

        else if ((left_is_edge && up_is_edge) && (!right_is_edge && !down_is_edge)) {
          Tile_set_arc(tile, QUADRANT_4);
          tile->value.edge_value.lines = TILE_LINES_INNER;
        }

        else if ((left_is_edge && up_is_edge) && (Maze_tile_data_at(self, col - 1, row - 1)->type != TILE_EDGE)) {
          Tile_set_arc(tile, QUADRANT_4);
          tile->value.edge_value.lines = TILE_LINES_OUTER;
        }
      }
    }
  }
}

Result Maze_detail(Maze *self) {
  Maze_detail_arc_outer(self);
  Maze_detail_arc_inner(self);
  return RESULT_OK;
}

bool Maze_tile_in_direction_is_path(const Maze *self, const Pair_uint8 location, const Direction direction) {
  switch (direction) {
  case DIRECTION_NONE: {
    return true;
  } break;
  case DIRECTION_N: {
    return (location.y != 0 && Maze_is_path(self, location.x, location.y - 1));
  } break;
  case DIRECTION_E: {
    return (location.x + 2 < self->size.x) && Maze_is_path(self, location.x + 1, location.y);
  } break;
  case DIRECTION_S: {
    return (location.y != (self->size.y - 1)) && Maze_is_path(self, location.x, location.y + 1);
  } break;
  case DIRECTION_W: {
    return (0 < location.x) && Maze_is_path(self, location.x - 1, location.y);
  } break;
  }
}

void Maze_complete_line_data(const Maze *self, TileData *tile_data, const uint8_t col, const uint8_t row) {

  assert(tile_data->type == TILE_EDGE);
  assert(tile_data->value.edge_value.edge_style == TILE_STYLE_LINE);

  // Top row
  if (row == 0) {
    tile_data->value.edge_value.lines = TILE_LINES_INNER;
    tile_data->value.edge_value.edge_line_plane = PLANE_H;
  }
  // Bottom row
  else if (row == (self->size.y - 1)) {
    tile_data->value.edge_value.lines = TILE_LINES_OUTER;
    tile_data->value.edge_value.edge_line_plane = PLANE_H;
  }
  // Intermediate rows
  else {
    // Above path
    if (Maze_tile_data_at(self, col, row + 1)->type == TILE_PATH) {
      tile_data->value.edge_value.lines = TILE_LINES_INNER;
      tile_data->value.edge_value.edge_line_plane = PLANE_H;
    }
    // Below path
    else if (Maze_tile_data_at(self, col, row - 1)->type == TILE_PATH) {
      tile_data->value.edge_value.lines = TILE_LINES_OUTER;
      tile_data->value.edge_value.edge_line_plane = PLANE_H;
    }
    // Left of path
    else if (col + 1 < self->size.x && Maze_tile_data_at(self, col + 1, row)->type == TILE_PATH) {
      tile_data->value.edge_value.lines = TILE_LINES_INNER;
      tile_data->value.edge_value.edge_line_plane = PLANE_V;
    }
    // Right of path
    else if (0 < col && Maze_tile_data_at(self, col - 1, row)->type == TILE_PATH) {
      tile_data->value.edge_value.lines = TILE_LINES_OUTER;
      tile_data->value.edge_value.edge_line_plane = PLANE_V;
    }
    // An issue
    else {
      // printf("??? %d %d\n", row, col);
    }
  }
}

Result Maze_complete_data(const Maze *self) {
  // For each tile...

  for (uint8_t col = 0; col < self->size.x; ++col) {
    for (uint8_t row = 0; row < self->size.y; ++row) {

      TileData *tile_data = Maze_tile_data_at(self, col, row);

      switch (tile_data->type) {

      case TILE_EDGE: {

        switch (tile_data->value.edge_value.edge_style) {
        case TILE_STYLE_NONE: {
        } break;

        case TILE_STYLE_LINE: {
          Maze_complete_line_data(self, tile_data, col, row);
        } break;

        case TILE_STYLE_ARC: {
          // No action
        } break;
        }

      } break;

      case TILE_EMPTY: {
        // Do nothing
      } break;

      case TILE_INFO: {
        // Do nothing
      } break;
      case TILE_PATH: {
        // Do nothing
      } break;
      }
    }
  }
  return RESULT_OK;
}

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

Result maze_ctor(maze_s *maze) {

  *maze = (maze_s){
      .tiles = nullptr,
      .dimensions = {.x = 0, .y = 0},
  };

  return RESULT_OK;
}

Result maze_ctor_from_path(maze_s *maze, const char *path) {

  ensure(maze_ctor(maze));
  ensure(maze_read_from_path(maze, path));
  ensure(maze_detail(maze));

  return RESULT_OK;
}

void maze_dtor(maze_s *self) {
  free(self->tiles);
  self->tiles = nullptr;
  self->dimensions.x = 0;
  self->dimensions.y = 0;
}

Result maze_read_from_path(maze_s *maze, const char *path) {

  assert(Pair_uint8_eq(&maze->dimensions, &(Pair_uint8){0, 0}));
  assert(maze->tiles == nullptr);

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
      if (!fscanf(file_ptr, "%" SCNu8, &(maze->dimensions.y))) {
        slog_display(SLOG_ERROR, 0, "Failed to read maze width: %s", path);
        preamble_ok = false;
      };
    } break;

    case 'h': {
      if (!fscanf(file_ptr, "%" SCNu8, &(maze->dimensions.x))) {
        slog_display(SLOG_ERROR, 0, "Failed to read maze height: %s", path);
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

  if ((maze->dimensions.x % STANDARD_MAZE_DIMENSIONS.x) != 0 | (maze->dimensions.y % STANDARD_MAZE_DIMENSIONS.y) != 0) {
    slog_display(SLOG_WARN, 0,
                 "Maze dimension %dx%d is not an integer scale of %dx%d\n", maze->dimensions.x, maze->dimensions.y, STANDARD_MAZE_DIMENSIONS.x, STANDARD_MAZE_DIMENSIONS.y);

    preamble_ok = false;
  }

  if (!preamble_ok) {
    fclose(file_ptr);
    slog_display(SLOG_ERROR, 0, "Failed to construct maze from: %s\n", path);
    return RESULT_KO;
  }

  maze->tiles = malloc((size_t)maze->dimensions.x * (size_t)maze->dimensions.y * sizeof(*maze->tiles));

  uint8_t row = 0;
  uint8_t col = 0;

  while ((read = (char)fgetc(file_ptr)) != EOF) {
    switch (read) {
    case 'c': {
      next_line(file_ptr);
    } break;

    case 'm': {
      col = 0;
    } break;

    case '\n': {
      if (col != maze->dimensions.y) {
        slog_display(SLOG_ERROR, 0, "Invalid width.\n\tHave: %d\n\tExpected: %d\n\tRow: %d\n\tMaze: %s\n", row, maze->dimensions.y, col, path);
        return RESULT_KO;
      }
      row += 1;
    } break;

    default: {

      tile_data_s data = {
          .type = TILE_EMPTY

      };

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

      maze->tiles[maze_tile_index(maze, row, col)] = data;

      col += 1;

      if (read == '-') {
        ++tile_count;
      }
    }
    }
  }

  if (row != maze->dimensions.x) {
    slog_display(SLOG_ERROR, 0,
                 "Invalid height.\n\tHave: %d\n\tExpected: %d\n\tMaze: %s\n", row, maze->dimensions.y, path);
    return RESULT_KO;
  }

  fclose(file_ptr);

  slog_display(SLOG_INFO, 0, "Constructed maze %dx%d (%zu)\n", maze->dimensions.x, maze->dimensions.y, tile_count);
  return RESULT_OK;
}

char *maze_as_string(const maze_s *self) {

  char *string = malloc((self->dimensions.x * (self->dimensions.y + 1)) * sizeof(*string));

  for (uint8_t row = 0; row < self->dimensions.x; ++row) {
    for (uint8_t col = 0; col < self->dimensions.y; ++col) {
      string[(row * (self->dimensions.y + 1)) + col] = tile_data_as_char(maze_tile_data_at(self, row, col));
    }
    string[(row * (self->dimensions.y + 1)) + self->dimensions.y] = '\n';
  }

  return string;
}

void Tile_set_arc(tile_data_s *tile, quadrant_e quadrant) {
  tile->value.edge_value.edge_style = TILE_STYLE_ARC;
  tile->value.edge_value.edge_arc_quadrant = quadrant;
}

void Maze_detail_arc_outer(maze_s *self) {

  { // LEFT
    uint8_t col = 0;
    tile_data_s *tile = nullptr;

    { // TOP
      tile = maze_tile_data_at(self, 0, col);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_2);
        tile->value.edge_value.lines = TILE_LINES_M;
      }
    }

    { // BOTTOM
      tile = maze_tile_data_at(self, self->dimensions.x - 1, col);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_3);
        tile->value.edge_value.lines = TILE_LINES_M;
      }
    }

    { // INTERMEDIATE
      for (uint8_t row = 4; row < self->dimensions.x - 1; ++row) {
        tile = maze_tile_data_at(self, row, col);
        if (tile->type == TILE_EDGE) {
          if (maze_tile_data_at(self, row, col + 1)->type == TILE_EDGE) {

            if ((maze_tile_data_at(self, row - 1, col)->type == TILE_EDGE) &&
                (maze_tile_data_at(self, row + 1, col)->type == TILE_EDGE)) {
              if (maze_tile_data_at(self, row - 1, col + 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_3);
                tile->value.edge_value.lines = TILE_LINES_M;
              } else if (maze_tile_data_at(self, row + 1, col + 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_2);
                tile->value.edge_value.lines = TILE_LINES_M;
              }
            }

            if ((maze_tile_data_at(self, row - 1, col)->type != TILE_EDGE) &&
                (maze_tile_data_at(self, row + 1, col)->type == TILE_EDGE)) {
              Tile_set_arc(tile, QUADRANT_2);
              tile->value.edge_value.lines = TILE_LINES_M;
            }

            if ((maze_tile_data_at(self, row - 1, col)->type == TILE_EDGE) &&
                (maze_tile_data_at(self, row + 1, col)->type != TILE_EDGE)) {
              Tile_set_arc(tile, QUADRANT_3);
              tile->value.edge_value.lines = TILE_LINES_M;
            }
          }
        }
      }
    }
  }

  { // RIGHT
    uint8_t col = self->dimensions.y - 1;
    tile_data_s *tile = nullptr;

    { // TOP
      tile = maze_tile_data_at(self, 0, col);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_1);
        tile->value.edge_value.lines = TILE_LINES_M;
      }
    }

    { // BOTTOM
      tile = maze_tile_data_at(self, self->dimensions.x - 1, col);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_4);
        tile->value.edge_value.lines = TILE_LINES_M;
      }
    }

    { // INTERMEDIATE
      for (uint8_t row = 4; row < self->dimensions.x - 1; ++row) {
        tile = maze_tile_data_at(self, row, col);
        if (tile->type == TILE_EDGE) {
          if (maze_tile_data_at(self, row, col - 1)->type == TILE_EDGE) {

            if ((maze_tile_data_at(self, row - 1, col)->type == TILE_EDGE) &&
                (maze_tile_data_at(self, row + 1, col)->type == TILE_EDGE)) {
              if (maze_tile_data_at(self, row - 1, col - 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_4);
                tile->value.edge_value.lines = TILE_LINES_M;
              } else if (maze_tile_data_at(self, row + 1, col - 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_1);
                tile->value.edge_value.lines = TILE_LINES_M;
              }
            }

            if ((maze_tile_data_at(self, row - 1, col)->type != TILE_EDGE) &&
                (maze_tile_data_at(self, row + 1, col)->type == TILE_EDGE)) {
              Tile_set_arc(tile, QUADRANT_1);
              tile->value.edge_value.lines = TILE_LINES_M;
            }

            if ((maze_tile_data_at(self, row - 1, col)->type == TILE_EDGE) &&
                (maze_tile_data_at(self, row + 1, col)->type != TILE_EDGE)) {
              Tile_set_arc(tile, QUADRANT_4);
              tile->value.edge_value.lines = TILE_LINES_M;
            }
          }
        }
      }
    }
  }

  { // TOP
    uint8_t row = 0;
    tile_data_s *tile = nullptr;

    { // LEFT
      tile = maze_tile_data_at(self, row, 0);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_2);
        tile->value.edge_value.lines = TILE_LINES_M;
      }
    }

    { // RIGHT
      tile = maze_tile_data_at(self, row, self->dimensions.y - 1);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_1);
        tile->value.edge_value.lines = TILE_LINES_M;
      }
    }

    { // INTERMEDIATE
      for (uint8_t col = 1; col < self->dimensions.y - 1; ++col) {
        tile = maze_tile_data_at(self, row, col);
        if (tile->type == TILE_EDGE) {
          if (maze_tile_data_at(self, row + 1, col)->type == TILE_EDGE) {

            if ((maze_tile_data_at(self, row, col - 1)->type == TILE_EDGE) &&
                (maze_tile_data_at(self, row, col + 1)->type == TILE_EDGE)) {
              if (maze_tile_data_at(self, row + 1, col + 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_2);
                tile->value.edge_value.lines = TILE_LINES_M;
              } else if (maze_tile_data_at(self, row + 1, col - 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_1);
                tile->value.edge_value.lines = TILE_LINES_M;
              }
            }
          }
        }
      }
    }
  }

  { // BOTTOM
    uint8_t row = self->dimensions.x - 1;
    tile_data_s *tile = nullptr;

    { // LEFT
      tile = maze_tile_data_at(self, row, 0);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_3);
        tile->value.edge_value.lines = TILE_LINES_M;
      }
    }

    { // RIGHT
      tile = maze_tile_data_at(self, row, self->dimensions.y - 1);
      if (tile->type == TILE_EDGE) {
        Tile_set_arc(tile, QUADRANT_4);
        tile->value.edge_value.lines = TILE_LINES_M;
      }
    }

    { // INTERMEDIATE
      for (uint8_t col = 1; col < self->dimensions.y - 1; ++col) {
        tile = maze_tile_data_at(self, row, col);
        if (tile->type == TILE_EDGE) {
          if (maze_tile_data_at(self, row - 1, col)->type == TILE_EDGE) {

            if ((maze_tile_data_at(self, row, col - 1)->type == TILE_EDGE) &&
                (maze_tile_data_at(self, row, col + 1)->type == TILE_EDGE)) {
              if (maze_tile_data_at(self, row - 1, col + 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_3);
                tile->value.edge_value.lines = TILE_LINES_M;
              } else if (maze_tile_data_at(self, row - 1, col - 1)->type != TILE_EDGE) {
                Tile_set_arc(tile, QUADRANT_4);
                tile->value.edge_value.lines = TILE_LINES_M;
              }
            }
          }
        }
      }
    }
  }
}

void Maze_detail_arc_inner(maze_s *self) {
  for (uint8_t row = 1; row < self->dimensions.x - 1; ++row) {
    for (uint8_t col = 1; col < self->dimensions.y - 1; ++col) {

      tile_data_s *tile = maze_tile_data_at(self, row, col);
      if (tile->type == TILE_EDGE) {

        bool edge_n = (maze_tile_data_at(self, row - 1, col)->type == TILE_EDGE);
        bool edge_e = (maze_tile_data_at(self, row, col + 1)->type == TILE_EDGE);
        bool edge_s = maze_tile_data_at(self, row + 1, col)->type == TILE_EDGE;
        bool edge_w = maze_tile_data_at(self, row, col - 1)->type == TILE_EDGE;

        if ((edge_w && edge_s) && (!edge_e && !edge_n)) {
          Tile_set_arc(tile, QUADRANT_1);
          tile->value.edge_value.lines = TILE_LINES_P;
        }

        else if ((edge_w && edge_s) && (maze_tile_data_at(self, row + 1, col - 1)->type == TILE_PATH)) {
          Tile_set_arc(tile, QUADRANT_1);
          tile->value.edge_value.lines = TILE_LINES_M;
        }

        else if ((edge_e && edge_s) && (!edge_w && !edge_n)) {
          Tile_set_arc(tile, QUADRANT_2);
          tile->value.edge_value.lines = TILE_LINES_P;
        }

        else if ((edge_e && edge_s) && (maze_tile_data_at(self, row + 1, col + 1)->type == TILE_PATH)) {
          Tile_set_arc(tile, QUADRANT_2);
          tile->value.edge_value.lines = TILE_LINES_M;
        }

        else if ((edge_e && edge_n) && (!edge_w && !edge_s)) {
          Tile_set_arc(tile, QUADRANT_3);
          tile->value.edge_value.lines = TILE_LINES_P;
        }

        else if ((edge_e && edge_n) && (maze_tile_data_at(self, row - 1, col + 1)->type == TILE_PATH)) {
          Tile_set_arc(tile, QUADRANT_3);
          tile->value.edge_value.lines = TILE_LINES_M;
        }

        else if ((edge_w && edge_n) && (!edge_e && !edge_s)) {
          Tile_set_arc(tile, QUADRANT_4);
          tile->value.edge_value.lines = TILE_LINES_P;
        }

        else if ((edge_w && edge_n) && (maze_tile_data_at(self, row - 1, col - 1)->type != TILE_EDGE)) {
          Tile_set_arc(tile, QUADRANT_4);
          tile->value.edge_value.lines = TILE_LINES_M;
        }
      }
    }
  }
}

Result maze_detail(maze_s *self) {
  Maze_detail_arc_outer(self);
  Maze_detail_arc_inner(self);

  // Complete tile related details
  for (uint8_t row = 0; row < self->dimensions.x; ++row) {
    for (uint8_t col = 0; col < self->dimensions.y; ++col) {

      tile_data_s *tile_data = maze_tile_data_at(self, row, col);

      switch (tile_data->type) {

      case TILE_EDGE: {

        switch (tile_data->value.edge_value.edge_style) {
        case TILE_STYLE_NONE: {
          // No action
        } break;

        case TILE_STYLE_LINE: {
          maze_complete_line_data(self, tile_data, row, col);
        } break;

        case TILE_STYLE_ARC: {
          // No action
        } break;
        }

      } break;

      case TILE_EMPTY: {
        // No action
      } break;

      case TILE_INFO: {
        // No action
      } break;
      case TILE_PATH: {
        // No action
      } break;
      }
    }
  }
  return RESULT_OK;

  return RESULT_OK;
}

bool maze_tile_in_direction_is_path(const maze_s *self, const Pair_uint8 location, const cardinal_e direction) {
  switch (direction) {
  case CARDINAL_NONE: {
    return true;
  } break;
  case CARDINAL_N: {
    return (0 < location.x) && maze_is_path(self, location.x - 1, location.y);
  } break;
  case CARDINAL_E: {
    return (location.y + 1 < self->dimensions.y) && maze_is_path(self, location.x, location.y + 1);
  } break;
  case CARDINAL_S: {
    return (location.x + 1 < self->dimensions.x) && maze_is_path(self, location.x + 1, location.y);
  } break;
  case CARDINAL_W: {
    return (0 < location.y) && maze_is_path(self, location.x, location.y - 1);
  } break;
  }
}

void maze_complete_line_data(const maze_s *self, tile_data_s *tile_data, const uint8_t row, const uint8_t col) {

  assert(tile_data->type == TILE_EDGE);
  assert(tile_data->value.edge_value.edge_style == TILE_STYLE_LINE);

  // Top row
  if (row == 0) {
    tile_data->value.edge_value.lines = TILE_LINES_M;
    tile_data->value.edge_value.edge_line_plane = PLANE_H;
  }
  // Bottom row
  else if (row == (self->dimensions.x - 1)) {
    tile_data->value.edge_value.lines = TILE_LINES_P;
    tile_data->value.edge_value.edge_line_plane = PLANE_H;
  }
  // Intermediate rows
  else {
    // South of path
    if (maze_tile_data_at(self, row - 1, col)->type == TILE_PATH) {
      tile_data->value.edge_value.lines = TILE_LINES_P;
      tile_data->value.edge_value.edge_line_plane = PLANE_H;
    }
    // North of path
    else if (maze_tile_data_at(self, row + 1, col)->type == TILE_PATH) {
      tile_data->value.edge_value.lines = TILE_LINES_M;
      tile_data->value.edge_value.edge_line_plane = PLANE_H;
    }
    // East of path
    else if (col + 1 < self->dimensions.y && maze_tile_data_at(self, row, col + 1)->type == TILE_PATH) {
      tile_data->value.edge_value.lines = TILE_LINES_M;
      tile_data->value.edge_value.edge_line_plane = PLANE_V;
    }
    // West of path
    else if (0 < col && maze_tile_data_at(self, row, col - 1)->type == TILE_PATH) {
      tile_data->value.edge_value.lines = TILE_LINES_P;
      tile_data->value.edge_value.edge_line_plane = PLANE_V;
    }
    // An issue
    else {
      // printf("??? %d %d\n", row, col);
    }
  }
}

#include <memory.h>
#include <stdio.h>
#include <stdlib.h>

#include "SML/maze_path.h"

void maze_path_ctor(maze_path_s *self, const Pair_uint8 size) {
  /* assert(self->tiles == nullptr && "oh"); */
  size_t tile_count = (size_t)size.x * (size_t)size.y;

  *self = (maze_path_s){
      .access_mutex = PTHREAD_MUTEX_INITIALIZER,
      .dimensions = size,
      .tiles = {
          .count = tile_count,
          .data = malloc(tile_count * sizeof(*self->tiles.data)),
      },

  };
  maze_path_clear(self);
}

void maze_path_clear(maze_path_s *self) {
  assert(self->tiles.data != nullptr);
  for (size_t idx = 0; idx < self->tiles.count; ++idx) {
    self->tiles.data[idx].h = PATH_X;
    self->tiles.data[idx].v = PATH_X;
  }
}

void maze_path_dtor(maze_path_s *self) {
  free(self->tiles.data);
  self->tiles.data = nullptr;
  self->tiles.count = 0;
  self->dimensions = (Pair_uint8){.x = 0, .y = 0};
}

void maze_path_display(maze_path_s *self, const Lexicon *lexicon) {

  char *line_buffer = malloc(self->dimensions.y * sizeof(*line_buffer));

  for (uint8_t row = 0; row < self->dimensions.x; ++row) {
    for (uint8_t col = 0; col < self->dimensions.y; ++col) {

      maze_tile_s val = self->tiles.data[Pair_uint8_flatten(&self->dimensions, row, col)];

      if (val.h == PATH_A && val.v == PATH_A) { // NE
        line_buffer[col] = '\\';
      } else if (val.h == PATH_A && val.v == PATH_B) { //
        line_buffer[col] = '/';
      } else if (val.h == PATH_A && val.v == PATH_O) { //
        line_buffer[col] = 'V';
      } else if (val.h == PATH_A && val.v == PATH_X) { //
        line_buffer[col] = '-';
      } else if (val.h == PATH_B && val.v == PATH_A) { //
        line_buffer[col] = '/';
      } else if (val.h == PATH_B && val.v == PATH_B) { //
        line_buffer[col] = '\\';
      } else if (val.h == PATH_B && val.v == PATH_O) { //
        line_buffer[col] = 'V';
      } else if (val.h == PATH_B && val.v == PATH_X) { //
        line_buffer[col] = '-';
      } else if (val.h == PATH_O && val.v == PATH_A) { //
        line_buffer[col] = 'H';
      } else if (val.h == PATH_O && val.v == PATH_B) { //
        line_buffer[col] = 'H';
      } else if (val.v == PATH_A || val.v == PATH_B) { //
        line_buffer[col] = '|';
      } else { //
        line_buffer[col] = ' ';
      }
    }
    printf("%s|%d\n", line_buffer, row);
  }

  free(line_buffer);
}

void maze_path_read(maze_path_s *self, const Lexicon *lexicon, const Z3_context ctx, const Z3_model model, const maze_s *maze) {
  // Read the interpretation to the path buffer
  pthread_mutex_lock(&self->access_mutex);

  { // fn h
    Z3_func_interp path_h_f = Z3_model_get_func_interp(ctx, model, lexicon->path.tile_h_f);
    Z3_func_interp_inc_ref(ctx, path_h_f);

    unsigned int entries_h = Z3_func_interp_get_num_entries(ctx, path_h_f);

    for (unsigned int idx = 0; idx < entries_h; ++idx) {
      Z3_func_entry entry = Z3_func_interp_get_entry(ctx, path_h_f, idx);

      size_t tile_index;
      { // Get the tile index
        uint8_t args_row_col[2];
        assert(Z3_func_entry_get_num_args(ctx, entry) == 2);
        unsigned int z3_unsigned_tmp;

        for (unsigned int arg_idx = 0; arg_idx < 2; ++arg_idx) {
          Z3_ast arg = Z3_func_entry_get_arg(ctx, entry, arg_idx);

          Z3_get_numeral_uint(ctx, arg, &z3_unsigned_tmp);
          assert(z3_unsigned_tmp < UINT8_MAX);
          args_row_col[arg_idx] = (uint8_t)z3_unsigned_tmp;
        }
        tile_index = maze_tile_index(maze, args_row_col[0], args_row_col[1]);
      }

      Z3_ast value = Z3_func_entry_get_value(ctx, entry);

      if (value == lexicon->path.token.a) {
        self->tiles.data[tile_index].h = PATH_A;
      } else if (value == lexicon->path.token.b) {
        self->tiles.data[tile_index].h = PATH_B;
      } else if (value == lexicon->path.token.o) {
        self->tiles.data[tile_index].h = PATH_O;
      } else {
        self->tiles.data[tile_index].h = PATH_X;
      }
    }
    Z3_func_interp_dec_ref(ctx, path_h_f);
  }

  { // fn v
    Z3_func_interp path_v_f = Z3_model_get_func_interp(ctx, model, lexicon->path.tile_v_f);
    Z3_func_interp_inc_ref(ctx, path_v_f);
    unsigned int entries_v = Z3_func_interp_get_num_entries(ctx, path_v_f);
    for (unsigned int idx = 0; idx < entries_v; ++idx) {
      Z3_func_entry entry = Z3_func_interp_get_entry(ctx, path_v_f, idx);

      size_t tile_index;
      { // Get the tile index
        uint8_t args_row_col[2];
        assert(Z3_func_entry_get_num_args(ctx, entry) == 2);
        unsigned int z3_unsigned_tmp;

        for (unsigned int arg_idx = 0; arg_idx < 2; ++arg_idx) {
          Z3_ast arg = Z3_func_entry_get_arg(ctx, entry, arg_idx);

          Z3_get_numeral_uint(ctx, arg, &z3_unsigned_tmp);
          assert(z3_unsigned_tmp < UINT8_MAX);
          args_row_col[arg_idx] = (uint8_t)z3_unsigned_tmp;
        }
        tile_index = maze_tile_index(maze, args_row_col[0], args_row_col[1]);
      }

      Z3_ast value = Z3_func_entry_get_value(ctx, entry);

      if (value == lexicon->path.token.a) {
        self->tiles.data[tile_index].v = PATH_A;
      } else if (value == lexicon->path.token.b) {
        self->tiles.data[tile_index].v = PATH_B;
      } else if (value == lexicon->path.token.o) {
        self->tiles.data[tile_index].v = PATH_O;
      } else if (value == lexicon->path.token.x) {
        self->tiles.data[tile_index].v = PATH_X;
      } else {
        slog_display(SLOG_ERROR, 0, "Unexpected token\n");
      }
    }
    Z3_func_interp_dec_ref(ctx, path_v_f);
  }

  pthread_mutex_unlock(&self->access_mutex);
}

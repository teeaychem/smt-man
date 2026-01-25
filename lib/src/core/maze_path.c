#include <memory.h>
#include <stdio.h>
#include <stdlib.h>

#include "SML/maze_path.h"

void MazePath_init(MazePath *self, const Pair_uint8 size) {
  /* assert(self->tiles == nullptr && "oh"); */
  size_t tile_count = (size_t)size.x * (size_t)size.y;

  *self = (MazePath){
      .mutex = PTHREAD_MUTEX_INITIALIZER,
      .size = size,
      .tile_count = tile_count,
      .tiles = malloc(tile_count * sizeof(*self->tiles)),
  };
  MazePath_clear(self);
}

void MazePath_clear(MazePath *self) {
  assert(self->tiles != nullptr);
  for (size_t idx = 0; idx < self->tile_count; ++idx) {
    self->tiles[idx].h = PATH_X;
    self->tiles[idx].v = PATH_X;
  }
}

void MazePath_drop(MazePath *self) {
  free(self->tiles);
  self->tiles = nullptr;
  self->tile_count = 0;
  self->size = (Pair_uint8){.x = 0, .y = 0};
}

void MazePath_display(MazePath *self, const Lexicon *lexicon) {

  char *line_buffer = malloc(self->size.y * sizeof(*line_buffer));

  for (uint8_t row = 0; row < self->size.x; ++row) {
    for (uint8_t col = 0; col < self->size.y; ++col) {

      MazeTile val = self->tiles[Pair_uint8_flatten(&self->size, row, col)];

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

void MazePath_read(MazePath *self, const Lexicon *lexicon, const Z3_context ctx, const Z3_model model, const Maze *maze) {
  // Read the interpretation to the path buffer
  pthread_mutex_lock(&self->mutex);

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
        tile_index = Maze_tile_index(maze, args_row_col[0], args_row_col[1]);
      }

      Z3_ast value = Z3_func_entry_get_value(ctx, entry);

      if (value == lexicon->path.token.a) {
        self->tiles[tile_index].h = PATH_A;
      } else if (value == lexicon->path.token.b) {
        self->tiles[tile_index].h = PATH_B;
      } else if (value == lexicon->path.token.o) {
        self->tiles[tile_index].h = PATH_O;
      } else {
        self->tiles[tile_index].h = PATH_X;
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
        tile_index = Maze_tile_index(maze, args_row_col[0], args_row_col[1]);
      }

      Z3_ast value = Z3_func_entry_get_value(ctx, entry);

      if (value == lexicon->path.token.a) {
        self->tiles[tile_index].v = PATH_A;
      } else if (value == lexicon->path.token.b) {
        self->tiles[tile_index].v = PATH_B;
      } else if (value == lexicon->path.token.o) {
        self->tiles[tile_index].v = PATH_O;
      } else if (value == lexicon->path.token.x) {
        self->tiles[tile_index].v = PATH_X;
      } else {
        slog_display(SLOG_ERROR, 0, "Unexpected token\n");
      }
    }
    Z3_func_interp_dec_ref(ctx, path_v_f);
  }

  pthread_mutex_unlock(&self->mutex);
}

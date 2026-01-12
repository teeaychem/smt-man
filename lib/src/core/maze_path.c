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
      .tiles = calloc(tile_count, sizeof(*self->tiles)),
  };
}

void MazePath_clear(MazePath *self) {
  assert(self->tiles != nullptr);
  for (size_t idx = 0; idx < self->tile_count; ++idx) {
    self->tiles[idx].h = nullptr;
    self->tiles[idx].v = nullptr;
  }
}

void MazePath_drop(MazePath *self) {
  free(self->tiles);
  self->tiles = nullptr;
  self->tile_count = 0;
  self->size = (Pair_uint8){.x = 0, .y = 0};
}

void MazePath_display(MazePath *self, const Language *language) {
  for (uint8_t row = 0; row < self->size.y; row++) {
    for (uint8_t col = 0; col < self->size.x; col++) {

      MazeTile val = self->tiles[Pair_uint8_flatten(&self->size, col, row)];

      if (val.h != nullptr || val.v != nullptr) {

        if (val.h == language->path.token.o || val.v == language->path.token.o) {
          printf("O");
        }

        else if (val.h != language->path.token.x || val.v != language->path.token.x) {
          printf("x");
        }



        /* else if (language->path.token.x == val.h && language->path.token.x != val.v) { */
        /*   printf("-"); */
        /* } */

        else  {
          printf(" ");
        }
      }

      else {
        printf(" ");
      }
    }
    printf("|%d\n", row);
  }
}

void MazePath_read(MazePath *self, const Language *lang, const Z3_context ctx, const Z3_model model, const Maze *maze) {
  // Read the interpretation to the path buffer
  pthread_mutex_lock(&self->mutex);

  {
    Z3_func_interp path_h_f = Z3_model_get_func_interp(ctx, model, lang->path.tile_h_f);
    Z3_func_interp_inc_ref(ctx, path_h_f);

    unsigned int entries_h = Z3_func_interp_get_num_entries(ctx, path_h_f);

    for (unsigned int idx = 0; idx < entries_h; ++idx) {
      Z3_func_entry entry = Z3_func_interp_get_entry(ctx, path_h_f, idx);
      uint8_t args_col_row[2];

      { // Get arguments
        assert(Z3_func_entry_get_num_args(ctx, entry) == 2);
        Z3_ast arg;
        unsigned int z3_unsigned_tmp;

        for (unsigned int arg_idx = 0; arg_idx < 2; ++arg_idx) {
          arg = Z3_func_entry_get_arg(ctx, entry, arg_idx);

          Z3_get_numeral_uint(ctx, arg, &z3_unsigned_tmp);
          assert(z3_unsigned_tmp < UINT8_MAX);
          args_col_row[arg_idx] = (uint8_t)z3_unsigned_tmp;
        }
      }

      Z3_ast value = Z3_func_entry_get_value(ctx, entry);
      self->tiles[Maze_tile_index(maze, args_col_row[0], args_col_row[1])].h = value;
    }
    Z3_func_interp_dec_ref(ctx, path_h_f);
  }

  {
    Z3_func_interp path_v_f = Z3_model_get_func_interp(ctx, model, lang->path.tile_v_f);
    Z3_func_interp_inc_ref(ctx, path_v_f);
    unsigned int entries_v = Z3_func_interp_get_num_entries(ctx, path_v_f);
    for (unsigned int idx = 0; idx < entries_v; ++idx) {
      Z3_func_entry entry = Z3_func_interp_get_entry(ctx, path_v_f, idx);
      uint8_t args_col_row[2];

      { // Get arguments
        assert(Z3_func_entry_get_num_args(ctx, entry) == 2);
        Z3_ast arg;
        unsigned int z3_unsigned_tmp;

        for (unsigned int arg_idx = 0; arg_idx < 2; ++arg_idx) {
          arg = Z3_func_entry_get_arg(ctx, entry, arg_idx);

          Z3_get_numeral_uint(ctx, arg, &z3_unsigned_tmp);
          assert(z3_unsigned_tmp < UINT8_MAX);
          args_col_row[arg_idx] = (uint8_t)z3_unsigned_tmp;
        }
      }

      Z3_ast value = Z3_func_entry_get_value(ctx, entry);
      self->tiles[Maze_tile_index(maze, args_col_row[0], args_col_row[1])].v = value;
    }
    Z3_func_interp_dec_ref(ctx, path_v_f);
  }

  pthread_mutex_unlock(&self->mutex);
}

MazeTile MazePath_at(MazePath *self, const Pair_uint8 location) {
  return self->tiles[Pair_uint8_flatten(&self->size, location.x, location.y)];
}

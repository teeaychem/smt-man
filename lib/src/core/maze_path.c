#include <memory.h>
#include <stdio.h>
#include <stdlib.h>

#include "SML/maze_path.h"

void MazePath_init(MazePath *self, const Pair_uint8 size) {
  assert(self->tiles != nullptr);

  self->size = size;
  self->tile_count = (size_t)size.x * (size_t)size.y;
  self->tiles = calloc(self->tile_count, sizeof(*self->tiles));
}

void MazePath_clear(MazePath *self) {
  assert(self->tiles != nullptr);
  for (size_t idx = 0; idx < self->tile_count; ++idx) {
    self->tiles[idx] = nullptr;
  }
}

void MazePath_drop(MazePath *self) {
  free(self->tiles);
  self->tiles = nullptr;
  self->tile_count = 0;
  self->size = (Pair_uint8){.x = 0, .y = 0};
}

void MazePath_display(MazePath *self, const Language *lang) {
  for (uint8_t row = 0; row < self->size.y; row++) {
    for (uint8_t col = 0; col < self->size.x; col++) {

      Z3_ast val = self->tiles[Pair_uint8_flatten(&self->size, col, row)];

      if (lang->path.token.o_n == val) {
        printf("O");
      } else if (lang->path.token.o_e == val) {
        printf("O");
      } else if (lang->path.token.o_s == val) {
        printf("O");
      } else if (lang->path.token.o_w == val) {
        printf("O");
      }

      else if (lang->path.token.n_s == val) {
        printf("|");
      } else if (lang->path.token.e_w == val) {
        printf("-");
      }

      else if (lang->path.token.n_e == val) {
        printf("X");
      } else if (lang->path.token.s_e == val) {
        printf("X");
      } else if (lang->path.token.s_w == val) {
        printf("X");
      } else if (lang->path.token.n_w == val) {
        printf("X");
      }

      else if (lang->path.token.x_x == val) {
        printf(" ");
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

  Z3_func_interp path_f = Z3_model_get_func_interp(ctx, model, lang->path.tile_is_f);
  Z3_func_interp_inc_ref(ctx, path_f);

  unsigned int entries = Z3_func_interp_get_num_entries(ctx, path_f);

  for (unsigned int idx = 0; idx < entries; ++idx) {
    Z3_func_entry entry = Z3_func_interp_get_entry(ctx, path_f, idx);
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
    self->tiles[Maze_tile_index(maze, args_col_row[0], args_col_row[1])] = value;
  }
  Z3_func_interp_dec_ref(ctx, path_f);

  pthread_mutex_unlock(&self->mutex);
}

Z3_ast MazePath_at(MazePath *self, const Pair_uint8 location) {
  return self->tiles[Pair_uint8_flatten(&self->size, location.x, location.y)];
}

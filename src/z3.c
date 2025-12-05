
#include "constants.h"
#include "logic.h"
#include "maze.h"
#include "misc.h"
#include "smt_z3.h"

#include "utils/pairs.h"
#include "z3_api.h"
#include "z3_optimization.h"

#include <assert.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

void z3_display_path(struct z3_lang *lang, Z3_context ctx, Z3_model model, Maze *maze) {
  Z3_ast u8_cr[2] = {};

  Z3_ast tile_path = NULL;

  for (int32_t r = 0; r < maze->size.y; r++) {
    u8_cr[1] = Z3_mk_int(ctx, r, lang->u8_sort);
    for (int32_t c = 0; c < maze->size.x; c++) {
      u8_cr[0] = Z3_mk_int(ctx, c, lang->u8_sort);

      Z3_model_eval(ctx, model, Z3_mk_app(ctx, lang->path.tile_is_f, 2, u8_cr), false, &tile_path);
      if (tile_path == lang->path.no_no) {
        printf(" ");
      } else {
        printf("x");
      }
    }
    printf("\n");
  }
}

void z3_tmp(Maze *maze, SmtWorld *world) {
  Z3_context ctx = z3_mk_anima_ctx();

  struct z3_lang lang = {};

  Z3_optimize optimizer = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, optimizer);

  lang.u8_sort = Z3_mk_bv_sort(ctx, 8);
  Lang_path_setup(&lang, ctx);
  Lang_anima_setup(&lang, ctx);

  Lang_assert_path_empty_hints(&lang, ctx, optimizer, maze);
  Lang_assert_path_non_empty_hints(&lang, ctx, optimizer, maze);

  Lang_assert_all_non_anima_are_non_origin(&lang, ctx, optimizer, world, maze);
  Lang_assert_all_anima_tiles_are_origin_tiles(&lang, ctx, optimizer, world, maze);

  Lang_assert_anima_locations(&lang, ctx, optimizer, world);

  // Checks
  switch (Z3_optimize_check(ctx, optimizer, 0, NULL)) {
  case Z3_L_FALSE: {
    printf("UNSAT\n");
  } break;
  case Z3_L_UNDEF: {
    printf("UNKNOWN\n");
  } break;
  case Z3_L_TRUE: {
    printf("SAT\n");
  } break;
  }

  auto model = Z3_optimize_get_model(ctx, optimizer);
  Z3_model_inc_ref(ctx, model);

  /* INFO("\nModel:\n%s\n", Z3_model_to_string(ctx, model)); */
  z3_display_path(&lang, ctx, model, maze);

  // Cleanup

  Z3_model_dec_ref(ctx, model);
  Z3_optimize_dec_ref(ctx, optimizer);
  Z3_del_context(ctx);
}

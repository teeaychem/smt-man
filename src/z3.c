#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>

#include <glib.h>

#include "logic.h"
#include "maze.h"
#include "temp.h"

void z3_display_path(const Lang *lang, Z3_context ctx, Z3_model model, const Maze *maze) {
  Z3_ast u8_cr[2] = {};

  Z3_ast tile_path = nullptr;

  for (uint32_t row = 0; row < maze->size.y; row++) {
    u8_cr[1] = Z3_mk_int(ctx, (int)row, lang->u8.sort);
    for (uint32_t col = 0; col < maze->size.x; col++) {
      u8_cr[0] = Z3_mk_int(ctx, (int)col, lang->u8.sort);

      Z3_model_eval(ctx, model, Z3_mk_app(ctx, lang->path.tile_is_f, 2, u8_cr), false, &tile_path);
      if (tile_path == lang->path.et_et) {
        putchar(' ');
      } else {
        putchar('x');
      }
    }
    printf("|%d\n", row);
  }
}

void z3_tmp(Maze *maze, Situation *situation) {
  Z3_context ctx = z3_mk_anima_ctx();

  struct z3_lang lang = {};

  Z3_optimize optimizer = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, optimizer);

  uint8_t anima_id = 2;

  Lang_setup_base(&lang, ctx);
  Lang_setup_path(&lang, ctx);
  Lang_setup_animas(&lang, ctx);
  Lang_setup_persona(&lang, ctx);

  Lang_anima_tile_is_origin(&lang, ctx, optimizer, anima_id);
  Lang_persona_tile_is_origin(&lang, ctx, optimizer);

  Lang_assert_link_reqs(&lang, ctx, optimizer, situation, maze, anima_id);

  Lang_assert_shortest_path_empty_hints(&lang, ctx, optimizer, maze);
  Lang_assert_path_non_empty_hints(&lang, ctx, optimizer, maze);

  Lang_assert_anima_location(&lang, ctx, optimizer, situation, anima_id);
  Lang_assert_persona_location(&lang, ctx, optimizer, situation);

  // Checks
  switch (Z3_optimize_check(ctx, optimizer, 0, nullptr)) {
  case Z3_L_FALSE: {
    g_message("UNSAT");
  } break;
  case Z3_L_UNDEF: {
    g_message("UNKNOWN");
  } break;
  case Z3_L_TRUE: {
    g_message("SAT");
  } break;
  }

  Z3_model model = Z3_optimize_get_model(ctx, optimizer);
  Z3_model_inc_ref(ctx, model);

  g_log(nullptr, G_LOG_LEVEL_INFO, "\nModel:\n%s", Z3_model_to_string(ctx, model));
  z3_display_path(&lang, ctx, model, maze);

  // Cleanup

  Z3_model_dec_ref(ctx, model);
  Z3_optimize_dec_ref(ctx, optimizer);
  Z3_del_context(ctx);
}

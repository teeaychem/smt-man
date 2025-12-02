
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
#include <stdio.h>

Z3_context z3_mk_anima_ctx() {
  Z3_config cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "model", "true");

  Z3_context ctx = Z3_mk_context(cfg);
  Z3_set_error_handler(ctx, error_handler);

  Z3_del_config(cfg);
  return ctx;
}

void z3_tmp(Maze *maze, SmtWorld world) {
  Z3_context ctx = z3_mk_anima_ctx();

  Z3_optimize optimizer = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, optimizer);

  Z3_sort u8_s = Z3_mk_bv_sort(ctx, 8);

  Z3_ast u8_0 = Z3_mk_numeral(ctx, "0", u8_s);
  Z3_ast u8_1 = Z3_mk_numeral(ctx, "1", u8_s);
  Z3_ast u8_2 = Z3_mk_numeral(ctx, "2", u8_s);
  Z3_ast u8_3 = Z3_mk_numeral(ctx, "3", u8_s);

  // Paths

  constexpr size_t PATH_VARIANTS = 11;

  Z3_symbol path_e_names[PATH_VARIANTS] = {
      Z3_mk_string_symbol(ctx, "origin_up"),
      Z3_mk_string_symbol(ctx, "origin_right"),
      Z3_mk_string_symbol(ctx, "origin_down"),
      Z3_mk_string_symbol(ctx, "origin_left"),

      Z3_mk_string_symbol(ctx, "up_down"),
      Z3_mk_string_symbol(ctx, "right_left"),

      Z3_mk_string_symbol(ctx, "up_right"),
      Z3_mk_string_symbol(ctx, "down_right"),
      Z3_mk_string_symbol(ctx, "down_left"),
      Z3_mk_string_symbol(ctx, "up_left"),

      Z3_mk_string_symbol(ctx, "empty"),
  };

  Z3_func_decl path_e_consts[PATH_VARIANTS];
  Z3_func_decl path_e_testers[PATH_VARIANTS];

  Z3_sort tile_path_s = Z3_mk_enumeration_sort(ctx,
                                               Z3_mk_string_symbol(ctx, "path"),
                                               PATH_VARIANTS,
                                               path_e_names,
                                               path_e_consts,
                                               path_e_testers);

  Z3_ast origin_up = Z3_mk_app(ctx, path_e_consts[0], 0, 0);
  Z3_ast origin_right = Z3_mk_app(ctx, path_e_consts[1], 0, 0);
  Z3_ast origin_down = Z3_mk_app(ctx, path_e_consts[2], 0, 0);
  Z3_ast origin_left = Z3_mk_app(ctx, path_e_consts[3], 0, 0);

  Z3_ast up_down = Z3_mk_app(ctx, path_e_consts[4], 0, 0);
  Z3_ast right_left = Z3_mk_app(ctx, path_e_consts[5], 0, 0);

  Z3_ast up_right = Z3_mk_app(ctx, path_e_consts[6], 0, 0);
  Z3_ast down_right = Z3_mk_app(ctx, path_e_consts[7], 0, 0);
  Z3_ast down_left = Z3_mk_app(ctx, path_e_consts[8], 0, 0);
  Z3_ast up_left = Z3_mk_app(ctx, path_e_consts[9], 0, 0);

  Z3_ast no_path = Z3_mk_app(ctx, path_e_consts[10], 0, 0);

  //

  Z3_func_decl tile_path_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "path_choice"), 2, (Z3_sort[2]){u8_s, u8_s}, tile_path_s);

  //
  char u8_buff[20] = {};

  Z3_ast u8_cr[2] = {};

  for (int32_t r = 0; r < maze->size.y; ++r) {
    sprintf(u8_buff, "%d", r);
    u8_cr[1] = Z3_mk_numeral(ctx, u8_buff, u8_s);
    for (int32_t c = 0; c < maze->size.x; ++c) {
      sprintf(u8_buff, "%d", c);
      u8_cr[0] = Z3_mk_numeral(ctx, u8_buff, u8_s);

      if (Maze_abstract_is_path(maze, c, r)) {
        Z3_optimize_assert_soft(ctx, optimizer, Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, u8_cr), no_path), "1", NULL);
      } else {
        Z3_optimize_assert(ctx, optimizer, Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, u8_cr), no_path));
      }
    }
  }

  // Animas

  Z3_symbol anima_e_names[ANIMA_COUNT] = {
      Z3_mk_string_symbol(ctx, "gottlob"),
      Z3_mk_string_symbol(ctx, "bertrand"),
      /* Z3_mk_string_symbol(ctx, "smt-man") */
  };

  Z3_func_decl anima_e_consts[ANIMA_COUNT];
  Z3_func_decl anima_e_testers[ANIMA_COUNT];

  Z3_sort anima_s = Z3_mk_enumeration_sort(ctx,
                                           Z3_mk_string_symbol(ctx, "anima"),
                                           ANIMA_COUNT,
                                           anima_e_names,
                                           anima_e_consts,
                                           anima_e_testers);

  Z3_ast anima_gottlob = Z3_mk_app(ctx, anima_e_consts[0], 0, 0);
  Z3_ast anima_bertrand = Z3_mk_app(ctx, anima_e_consts[1], 0, 0);

  // Anima locations

  Z3_func_decl anima_tile_row_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "anima_loc_row"), 1, (Z3_sort[1]){anima_s}, u8_s);
  Z3_func_decl anima_tile_col_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "anima_loc_col"), 1, (Z3_sort[1]){anima_s}, u8_s);

  PairI32 gottlob_location = atomic_load(&world.anima[0].abstract_location);
  sprintf(u8_buff, "%d", gottlob_location.y);
  Z3_optimize_assert(ctx, optimizer, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, anima_tile_row_f, anima_gottlob), Z3_mk_numeral(ctx, u8_buff, u8_s)));
  sprintf(u8_buff, "%d", gottlob_location.x);
  Z3_optimize_assert(ctx, optimizer, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, anima_tile_col_f, anima_gottlob), Z3_mk_numeral(ctx, u8_buff, u8_s)));

  PairI32 bertrand_location = atomic_load(&world.anima[1].abstract_location);
  sprintf(u8_buff, "%d", bertrand_location.y);
  Z3_optimize_assert(ctx, optimizer, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, anima_tile_row_f, anima_bertrand), Z3_mk_numeral(ctx, u8_buff, u8_s)));
  sprintf(u8_buff, "%d", bertrand_location.x);
  Z3_optimize_assert(ctx, optimizer, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, anima_tile_col_f, anima_bertrand), Z3_mk_numeral(ctx, u8_buff, u8_s)));

  for (int32_t r = 0; r < maze->size.y; r++) {
    sprintf(u8_buff, "%d", r);
    u8_cr[1] = Z3_mk_numeral(ctx, u8_buff, u8_s);
    for (int32_t c = 0; c < maze->size.x; c++) {
      sprintf(u8_buff, "%d", c);
      u8_cr[0] = Z3_mk_numeral(ctx, u8_buff, u8_s);

      Z3_ast tile_path_value = Z3_mk_app(ctx, tile_path_f, 2, u8_cr);

      if (Maze_abstract_is_path(maze, c, r)) {

        Z3_ast up_tile[2] = {};
        if (0 < r) {
          sprintf(u8_buff, "%d", c);
          up_tile[0] = Z3_mk_numeral(ctx, u8_buff, u8_s);
          sprintf(u8_buff, "%d", r - 1);
          up_tile[1] = Z3_mk_numeral(ctx, u8_buff, u8_s);
        }

        Z3_ast rt_tile[2] = {};
        if (c + 1 < maze->size.x) {
          sprintf(u8_buff, "%d", c + 1);
          rt_tile[0] = Z3_mk_numeral(ctx, u8_buff, u8_s);
          sprintf(u8_buff, "%d", r);
          rt_tile[1] = Z3_mk_numeral(ctx, u8_buff, u8_s);
        }

        Z3_ast dn_tile[2] = {};
        if (r + 1 < maze->size.y) {
          sprintf(u8_buff, "%d", c);
          dn_tile[0] = Z3_mk_numeral(ctx, u8_buff, u8_s);
          sprintf(u8_buff, "%d", r + 1);
          dn_tile[1] = Z3_mk_numeral(ctx, u8_buff, u8_s);
        }

        Z3_ast lt_tile[2] = {};
        if (0 < c) {
          sprintf(u8_buff, "%d", c - 1);
          lt_tile[0] = Z3_mk_numeral(ctx, u8_buff, u8_s);
          sprintf(u8_buff, "%d", r);
          lt_tile[1] = Z3_mk_numeral(ctx, u8_buff, u8_s);
        }

        size_t up_tile_reqs = 0;
        Z3_ast up_tile_req[4] = {};
        if (0 < r) {
          up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, up_tile), origin_down);
          up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, up_tile), up_down);
          up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, up_tile), down_right);
          up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, up_tile), down_left);
        }

        size_t rt_tile_reqs = 0;
        Z3_ast rt_tile_req[4] = {};
        if (c + 1 < maze->size.x) {
          rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, rt_tile), origin_left);
          rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, rt_tile), right_left);
          rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, rt_tile), down_left);
          rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, rt_tile), up_left);
        }

        size_t dn_tile_reqs = 0;
        Z3_ast dn_tile_req[4] = {};
        if (r + 1 < maze->size.y) {
          dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, dn_tile), origin_up);
          dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, dn_tile), up_down);
          dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, dn_tile), up_right);
          dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, dn_tile), up_left);
        }

        size_t lt_tile_reqs = 0;
        Z3_ast lt_tile_req[4] = {};
        if (0 < c) {
          lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, lt_tile), origin_right);
          lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, lt_tile), right_left);
          lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, lt_tile), down_right);
          lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, lt_tile), up_right);
        }

        Z3_ast up_tile_or = Z3_mk_or(ctx, up_tile_reqs, up_tile_req);
        Z3_ast rt_tile_or = Z3_mk_or(ctx, rt_tile_reqs, rt_tile_req);
        Z3_ast dn_tile_or = Z3_mk_or(ctx, dn_tile_reqs, dn_tile_req);
        Z3_ast lt_tile_or = Z3_mk_or(ctx, lt_tile_reqs, lt_tile_req);

        if (up_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, origin_up), up_tile_or));
        }

        if (rt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, origin_right), rt_tile_or));
        }

        if (dn_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, origin_down), dn_tile_or));
        }

        if (lt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, origin_left), lt_tile_or));
        }

        // up down
        if (up_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, up_down), up_tile_or));
        }
        if (dn_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, up_down), dn_tile_or));
        }

        // right left
        if (lt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, right_left), lt_tile_or));
        }
        if (rt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, right_left), rt_tile_or));
        }

        // up right
        if (up_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, up_right), up_tile_or));
        }
        if (rt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, up_right), rt_tile_or));
        }

        // down right
        if (dn_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, down_right), dn_tile_or));
        }
        if (rt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, down_right), rt_tile_or));
        }

        // up left
        if (up_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, up_left), up_tile_or));
        }
        if (lt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, up_left), lt_tile_or));
        }

        // down left
        if (dn_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, down_left), dn_tile_or));
        }
        if (lt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, down_left), lt_tile_or));
        }
      }
    }
  }

  for (int32_t r = 0; r < maze->size.y; r++) {
    sprintf(u8_buff, "%d", r);
    u8_cr[1] = Z3_mk_numeral(ctx, u8_buff, u8_s);
    for (int32_t c = 0; c < maze->size.x; c++) {
      sprintf(u8_buff, "%d", c);
      u8_cr[0] = Z3_mk_numeral(ctx, u8_buff, u8_s);

      Z3_ast some_anima_location = Z3_mk_or(ctx,
                                            2,
                                            (Z3_ast[2]){
                                                Z3_mk_and(ctx, 2, (Z3_ast[2]){Z3_mk_eq(ctx, z3_mk_unary_app(ctx, anima_tile_col_f, anima_gottlob), u8_cr[0]), Z3_mk_eq(ctx, z3_mk_unary_app(ctx, anima_tile_row_f, anima_gottlob), u8_cr[1])}),
                                                Z3_mk_and(ctx, 2, (Z3_ast[2]){Z3_mk_eq(ctx, z3_mk_unary_app(ctx, anima_tile_col_f, anima_bertrand), u8_cr[0]), Z3_mk_eq(ctx, z3_mk_unary_app(ctx, anima_tile_row_f, anima_bertrand), u8_cr[1])})});

      Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, u8_cr), origin_up), some_anima_location));
      Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, u8_cr), origin_right), some_anima_location));
      Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, u8_cr), origin_down), some_anima_location));
      Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, Z3_mk_app(ctx, tile_path_f, 2, u8_cr), origin_left), some_anima_location));
    }
  }

  Z3_ast anima_location_gottlob = Z3_mk_app(ctx, tile_path_f, 2, (Z3_ast[2]){z3_mk_unary_app(ctx, anima_tile_col_f, anima_gottlob), z3_mk_unary_app(ctx, anima_tile_row_f, anima_gottlob)});
  Z3_optimize_assert(ctx,
                     optimizer,
                     Z3_mk_or(ctx,
                              4,
                              (Z3_ast[4]){Z3_mk_eq(ctx, anima_location_gottlob, origin_up),
                                          Z3_mk_eq(ctx, anima_location_gottlob, origin_right),
                                          Z3_mk_eq(ctx, anima_location_gottlob, origin_down),
                                          Z3_mk_eq(ctx, anima_location_gottlob, origin_left)}));

  Z3_ast anima_location_bertrand = Z3_mk_app(ctx, tile_path_f, 2, (Z3_ast[2]){z3_mk_unary_app(ctx, anima_tile_col_f, anima_bertrand), z3_mk_unary_app(ctx, anima_tile_row_f, anima_bertrand)});
  Z3_optimize_assert(ctx,
                     optimizer,
                     Z3_mk_or(ctx,
                              4,
                              (Z3_ast[4]){Z3_mk_eq(ctx, anima_location_bertrand, origin_up),
                                          Z3_mk_eq(ctx, anima_location_bertrand, origin_right),
                                          Z3_mk_eq(ctx, anima_location_bertrand, origin_down),
                                          Z3_mk_eq(ctx, anima_location_bertrand, origin_left)}));

  // Hm

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

  Z3_ast tile_path = NULL;
  for (int32_t r = 0; r < maze->size.y; r++) {
    sprintf(u8_buff, "%d", r);
    u8_cr[1] = Z3_mk_numeral(ctx, u8_buff, u8_s);
    for (int32_t c = 0; c < maze->size.x; c++) {
      sprintf(u8_buff, "%d", c);
      u8_cr[0] = Z3_mk_numeral(ctx, u8_buff, u8_s);

      Z3_model_eval(ctx, model, Z3_mk_app(ctx, tile_path_f, 2, u8_cr), false, &tile_path);
      if (tile_path == no_path) {
        printf(" ");
      } else {
        printf("x");
      }
    }
    printf("\n");
  }

  // Cleanup

  Z3_model_dec_ref(ctx, model);
  Z3_optimize_dec_ref(ctx, optimizer);
  Z3_del_context(ctx);
}

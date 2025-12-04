
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

constexpr size_t PATH_VARIANTS = 11;
struct z3_lang {
  Z3_sort u8_sort;

  struct anima {
    Z3_sort sort;

    Z3_symbol enum_names[ANIMA_COUNT];
    Z3_func_decl enum_consts[ANIMA_COUNT];
    Z3_func_decl enum_testers[ANIMA_COUNT];

    Z3_func_decl tile_row_f;
    Z3_func_decl tile_col_f;
  } anima;

  struct path {
    Z3_sort tile_enum_sort;

    Z3_symbol enum_names[PATH_VARIANTS];
    Z3_func_decl enum_consts[PATH_VARIANTS];
    Z3_func_decl enum_testers[PATH_VARIANTS];

    Z3_ast og_up;
    Z3_ast og_rt;
    Z3_ast og_dn;
    Z3_ast og_lt;

    Z3_ast up_dn;
    Z3_ast rt_lt;

    Z3_ast up_rt;
    Z3_ast dn_rt;
    Z3_ast dn_lt;
    Z3_ast up_lt;

    Z3_ast no_no;

    Z3_func_decl tile_is_f;
  } path;
};

// Path fns

void Lang_path_setup(struct z3_lang *lang, Z3_context ctx) {

  lang->path.enum_names[0] = Z3_mk_string_symbol(ctx, "origin_up");
  lang->path.enum_names[1] = Z3_mk_string_symbol(ctx, "origin_right");
  lang->path.enum_names[2] = Z3_mk_string_symbol(ctx, "origin_down");
  lang->path.enum_names[3] = Z3_mk_string_symbol(ctx, "origin_left");

  lang->path.enum_names[4] = Z3_mk_string_symbol(ctx, "up_down");
  lang->path.enum_names[5] = Z3_mk_string_symbol(ctx, "right_left");

  lang->path.enum_names[6] = Z3_mk_string_symbol(ctx, "up_right");
  lang->path.enum_names[7] = Z3_mk_string_symbol(ctx, "down_right");
  lang->path.enum_names[8] = Z3_mk_string_symbol(ctx, "down_left");
  lang->path.enum_names[9] = Z3_mk_string_symbol(ctx, "up_left");

  lang->path.enum_names[10] = Z3_mk_string_symbol(ctx, "empty");

  lang->path.tile_enum_sort = Z3_mk_enumeration_sort(ctx, Z3_mk_string_symbol(ctx, "path"), PATH_VARIANTS, lang->path.enum_names, lang->path.enum_consts, lang->path.enum_testers);

  lang->path.og_up = Z3_mk_app(ctx, lang->path.enum_consts[0], 0, 0);
  lang->path.og_rt = Z3_mk_app(ctx, lang->path.enum_consts[1], 0, 0);
  lang->path.og_dn = Z3_mk_app(ctx, lang->path.enum_consts[2], 0, 0);
  lang->path.og_lt = Z3_mk_app(ctx, lang->path.enum_consts[3], 0, 0);

  lang->path.up_dn = Z3_mk_app(ctx, lang->path.enum_consts[4], 0, 0);
  lang->path.rt_lt = Z3_mk_app(ctx, lang->path.enum_consts[5], 0, 0);

  lang->path.up_rt = Z3_mk_app(ctx, lang->path.enum_consts[6], 0, 0);
  lang->path.dn_rt = Z3_mk_app(ctx, lang->path.enum_consts[7], 0, 0);
  lang->path.dn_lt = Z3_mk_app(ctx, lang->path.enum_consts[8], 0, 0);
  lang->path.up_lt = Z3_mk_app(ctx, lang->path.enum_consts[9], 0, 0);

  lang->path.no_no = Z3_mk_app(ctx, lang->path.enum_consts[10], 0, 0);

  lang->path.tile_is_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "path_choice"), 2, (Z3_sort[2]){lang->u8_sort, lang->u8_sort}, lang->path.tile_enum_sort);
}

void Lang_assert_path_empty_hints(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, Maze *maze) {
  Z3_ast u8_cr[2] = {};
  char u8_buffer[20] = {};

  for (int32_t r = 0; r < maze->size.y; ++r) {
    sprintf(u8_buffer, "%d", r);
    u8_cr[1] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);
    for (int32_t c = 0; c < maze->size.x; ++c) {
      sprintf(u8_buffer, "%d", c);
      u8_cr[0] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);

      if (Maze_abstract_is_path(maze, c, r)) {
        Z3_optimize_assert_soft(ctx, optimizer, Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, u8_cr), lang->path.no_no), "1", NULL);
      } else {
        Z3_optimize_assert(ctx, optimizer, Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, u8_cr), lang->path.no_no));
      }
    }
  }
}

void Lang_assert_path_non_empty_hints(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, Maze *maze) {
  Z3_ast u8_cr[2] = {};
  char u8_buffer[20] = {};

  for (int32_t r = 0; r < maze->size.y; r++) {
    sprintf(u8_buffer, "%d", r);
    u8_cr[1] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);

    for (int32_t c = 0; c < maze->size.x; c++) {
      sprintf(u8_buffer, "%d", c);
      u8_cr[0] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);

      Z3_ast tile_path_value = Z3_mk_app(ctx, lang->path.tile_is_f, 2, u8_cr);

      if (Maze_abstract_is_path(maze, c, r)) {

        Z3_ast up_tile[2] = {};
        if (0 < r) {
          sprintf(u8_buffer, "%d", c);
          up_tile[0] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);
          sprintf(u8_buffer, "%d", r - 1);
          up_tile[1] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);
        }

        Z3_ast rt_tile[2] = {};
        if (c + 1 < maze->size.x) {
          sprintf(u8_buffer, "%d", c + 1);
          rt_tile[0] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);
          sprintf(u8_buffer, "%d", r);
          rt_tile[1] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);
        }

        Z3_ast dn_tile[2] = {};
        if (r + 1 < maze->size.y) {
          sprintf(u8_buffer, "%d", c);
          dn_tile[0] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);
          sprintf(u8_buffer, "%d", r + 1);
          dn_tile[1] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);
        }

        Z3_ast lt_tile[2] = {};
        if (0 < c) {
          sprintf(u8_buffer, "%d", c - 1);
          lt_tile[0] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);
          sprintf(u8_buffer, "%d", r);
          lt_tile[1] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);
        }

        size_t up_tile_reqs = 0;
        Z3_ast up_tile_or = NULL;
        {
          Z3_ast up_tile_req[4] = {};
          if (0 < r) {
            up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, up_tile), lang->path.og_dn);
            up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, up_tile), lang->path.up_dn);
            up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, up_tile), lang->path.dn_rt);
            up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, up_tile), lang->path.dn_lt);
          }
          up_tile_or = Z3_mk_or(ctx, up_tile_reqs, up_tile_req);
        }

        size_t rt_tile_reqs = 0;
        Z3_ast rt_tile_or = NULL;

        {
          Z3_ast rt_tile_req[4] = {};
          if (c + 1 < maze->size.x) {
            rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, rt_tile), lang->path.og_lt);
            rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, rt_tile), lang->path.rt_lt);
            rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, rt_tile), lang->path.dn_lt);
            rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, rt_tile), lang->path.up_lt);
          }
          rt_tile_or = Z3_mk_or(ctx, rt_tile_reqs, rt_tile_req);
        }

        size_t dn_tile_reqs = 0;
        Z3_ast dn_tile_or = NULL;
        {
          Z3_ast dn_tile_req[4] = {};
          if (r + 1 < maze->size.y) {
            dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, dn_tile), lang->path.og_up);
            dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, dn_tile), lang->path.up_dn);
            dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, dn_tile), lang->path.up_rt);
            dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, dn_tile), lang->path.up_lt);
          }
          dn_tile_or = Z3_mk_or(ctx, dn_tile_reqs, dn_tile_req);
        }

        size_t lt_tile_reqs = 0;
        Z3_ast lt_tile_or = NULL;
        {
          Z3_ast lt_tile_req[4] = {};
          if (0 < c) {
            lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, lt_tile), lang->path.og_rt);
            lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, lt_tile), lang->path.rt_lt);
            lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, lt_tile), lang->path.dn_rt);
            lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, lt_tile), lang->path.up_rt);
          }
          lt_tile_or = Z3_mk_or(ctx, lt_tile_reqs, lt_tile_req);
        }

        if (up_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.og_up), up_tile_or));
        }

        if (rt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.og_rt), rt_tile_or));
        }

        if (dn_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.og_dn), dn_tile_or));
        }

        if (lt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.og_lt), lt_tile_or));
        }

        // up down
        if (up_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.up_dn), up_tile_or));
        }
        if (dn_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.up_dn), dn_tile_or));
        }

        // right left
        if (lt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.rt_lt), lt_tile_or));
        }
        if (rt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.rt_lt), rt_tile_or));
        }

        // up right
        if (up_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.up_rt), up_tile_or));
        }
        if (rt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.up_rt), rt_tile_or));
        }

        // down right
        if (dn_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.dn_rt), dn_tile_or));
        }
        if (rt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.dn_rt), rt_tile_or));
        }

        // up left
        if (up_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.up_lt), up_tile_or));
        }
        if (lt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.up_lt), lt_tile_or));
        }

        // down left
        if (dn_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.dn_lt), dn_tile_or));
        }
        if (lt_tile_reqs != 0) {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.dn_lt), lt_tile_or));
        }
      }
    }
  }
}

// Anima fns

void Lang_anima_setup(struct z3_lang *lang, Z3_context ctx) {
  lang->anima.enum_names[0] = Z3_mk_string_symbol(ctx, "gottlob");
  lang->anima.enum_names[1] = Z3_mk_string_symbol(ctx, "bertrand");

  lang->anima.sort = Z3_mk_enumeration_sort(ctx,
                                            Z3_mk_string_symbol(ctx, "anima"),
                                            ANIMA_COUNT,
                                            lang->anima.enum_names,
                                            lang->anima.enum_consts,
                                            lang->anima.enum_testers);

  lang->anima.tile_row_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "anima_loc_row"), 1, (Z3_sort[1]){lang->anima.sort}, lang->u8_sort);
  lang->anima.tile_col_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "anima_loc_col"), 1, (Z3_sort[1]){lang->anima.sort}, lang->u8_sort);
}

void Lang_assert_anima_locations(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, SmtWorld *world) {
  char u8_buffer[20] = {};

  for (size_t anima_idx = 0; anima_idx < ANIMA_COUNT; ++anima_idx) {

    PairI32 anima_location = atomic_load(&world->anima[anima_idx].abstract_location);
    Z3_ast anima_ast = Z3_mk_app(ctx, lang->anima.enum_consts[anima_idx], 0, 0);

    sprintf(u8_buffer, "%d", anima_location.y);
    Z3_optimize_assert(ctx, optimizer, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, lang->anima.tile_row_f, anima_ast), Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort)));
    sprintf(u8_buffer, "%d", anima_location.x);
    Z3_optimize_assert(ctx, optimizer, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, lang->anima.tile_col_f, anima_ast), Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort)));
  }
}

// Require a non-origin tile on non-anima tiles
void Lang_assert_all_non_anima_are_non_origin(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, SmtWorld *world, Maze *maze) {
  Z3_ast u8_cr[2] = {};
  char u8_buffer[20] = {};

  for (int32_t r = 0; r < maze->size.y; r++) {
    sprintf(u8_buffer, "%d", r);
    u8_cr[1] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);
    for (int32_t c = 0; c < maze->size.x; c++) {
      sprintf(u8_buffer, "%d", c);
      u8_cr[0] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);

      for (size_t anima_idx = 0; anima_idx < ANIMA_COUNT; ++anima_idx) {
        auto location = atomic_load(&world->anima[anima_idx].abstract_location);
        if (location.x == c && location.y == r) {
          goto skip_tile_assertion;
        }
      }

      Z3_ast tile_path_value = Z3_mk_app(ctx, lang->path.tile_is_f, 2, u8_cr);

      Z3_optimize_assert(ctx, optimizer, Z3_mk_or(ctx, 7, (Z3_ast[7]){
                                                              Z3_mk_eq(ctx, tile_path_value, lang->path.up_dn),
                                                              Z3_mk_eq(ctx, tile_path_value, lang->path.rt_lt),
                                                              Z3_mk_eq(ctx, tile_path_value, lang->path.up_rt),
                                                              Z3_mk_eq(ctx, tile_path_value, lang->path.dn_rt),
                                                              Z3_mk_eq(ctx, tile_path_value, lang->path.up_lt),
                                                              Z3_mk_eq(ctx, tile_path_value, lang->path.dn_lt),
                                                              Z3_mk_eq(ctx, tile_path_value, lang->path.no_no),
                                                          }));
    skip_tile_assertion:
    }
  }
}

void Lang_assert_all_anima_tiles_are_origin_tiles(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, SmtWorld *world, Maze *maze) {
  for (size_t anima_idx = 0; anima_idx < ANIMA_COUNT; ++anima_idx) {
    Z3_ast anima_ast = Z3_mk_app(ctx, lang->anima.enum_consts[anima_idx], 0, 0);

    Z3_ast anima_tile_location = Z3_mk_app(ctx, lang->path.tile_is_f, 2, (Z3_ast[2]){z3_mk_unary_app(ctx, lang->anima.tile_col_f, anima_ast), z3_mk_unary_app(ctx, lang->anima.tile_row_f, anima_ast)});

    Z3_ast tile_choices[4] = {Z3_mk_eq(ctx, anima_tile_location, lang->path.og_up),
                              Z3_mk_eq(ctx, anima_tile_location, lang->path.og_rt),
                              Z3_mk_eq(ctx, anima_tile_location, lang->path.og_dn),
                              Z3_mk_eq(ctx, anima_tile_location, lang->path.og_lt)};

    Z3_optimize_assert(ctx, optimizer, Z3_mk_or(ctx, 4, tile_choices));
  }
}

// Unused
void Lang_assert_all_origin_are_anima(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, SmtWorld *world, Maze *maze) {
  Z3_ast u8_cr[2] = {};
  char u8_buffer[20] = {};

  for (int32_t r = 0; r < maze->size.y; r++) {
    sprintf(u8_buffer, "%d", r);
    u8_cr[1] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);
    for (int32_t c = 0; c < maze->size.x; c++) {
      sprintf(u8_buffer, "%d", c);
      u8_cr[0] = Z3_mk_numeral(ctx, u8_buffer, lang->u8_sort);

      Z3_ast anima_ands[ANIMA_COUNT];
      for (size_t anima_idx = 0; anima_idx < ANIMA_COUNT; ++anima_idx) {
        Z3_ast anima_ast = Z3_mk_app(ctx, lang->anima.enum_consts[anima_idx], 0, 0);

        Z3_ast anima_row_col_eq[2] = {Z3_mk_eq(ctx, z3_mk_unary_app(ctx, lang->anima.tile_col_f, anima_ast), u8_cr[0]),
                                      Z3_mk_eq(ctx, z3_mk_unary_app(ctx, lang->anima.tile_row_f, anima_ast), u8_cr[1])};

        anima_ands[anima_idx] = Z3_mk_and(ctx, 2, anima_row_col_eq);
      }

      Z3_ast some_anima_location = Z3_mk_or(ctx, ANIMA_COUNT, anima_ands);

      Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, u8_cr), lang->path.og_up), some_anima_location));
      Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, u8_cr), lang->path.og_rt), some_anima_location));
      Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, u8_cr), lang->path.og_dn), some_anima_location));
      Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, u8_cr), lang->path.og_lt), some_anima_location));
    }
  }
}

Z3_context z3_mk_anima_ctx() {
  Z3_config cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "model", "true");

  Z3_context ctx = Z3_mk_context(cfg);
  Z3_set_error_handler(ctx, error_handler);

  Z3_del_config(cfg);
  return ctx;
}

void z3_tmp(Maze *maze, SmtWorld *world) {
  Z3_context ctx = z3_mk_anima_ctx();

  struct z3_lang lang = {};
  lang.u8_sort = Z3_mk_bv_sort(ctx, 8);

  Z3_optimize optimizer = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, optimizer);

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

  Z3_ast u8_cr[2] = {};
  char u8_buffer[20] = {};

  Z3_ast tile_path = NULL;

  for (int32_t r = 0; r < maze->size.y; r++) {
    sprintf(u8_buffer, "%d", r);
    u8_cr[1] = Z3_mk_numeral(ctx, u8_buffer, lang.u8_sort);
    for (int32_t c = 0; c < maze->size.x; c++) {
      sprintf(u8_buffer, "%d", c);
      u8_cr[0] = Z3_mk_numeral(ctx, u8_buffer, lang.u8_sort);

      Z3_model_eval(ctx, model, Z3_mk_app(ctx, lang.path.tile_is_f, 2, u8_cr), false, &tile_path);
      if (tile_path == lang.path.no_no) {
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

#include <stdatomic.h>
#include <stdint.h>

#include "generic/pairs.h"
#include "logic.h"
#include "macro.h"

Z3_context z3_mk_anima_ctx() {

  Z3_config cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "model", "true");

  Z3_context ctx = Z3_mk_context(cfg);
  Z3_set_error_handler(ctx, error_handler);

  Z3_del_config(cfg);

  return ctx;
}

void Lang_base_setup(struct z3_lang *lang, Z3_context ctx) {
  lang->u8.sort = Z3_mk_bv_sort(ctx, 8);
}

// Path fns

void Lang_path_setup(struct z3_lang *lang, Z3_context ctx) {

  {
    lang->path.enum_names[0] = Z3_mk_string_symbol(ctx, "og_up");
    lang->path.enum_names[1] = Z3_mk_string_symbol(ctx, "og_rt");
    lang->path.enum_names[2] = Z3_mk_string_symbol(ctx, "og_dn");
    lang->path.enum_names[3] = Z3_mk_string_symbol(ctx, "og_lt");

    lang->path.enum_names[4] = Z3_mk_string_symbol(ctx, "up_dn");
    lang->path.enum_names[5] = Z3_mk_string_symbol(ctx, "rt_lt");

    lang->path.enum_names[6] = Z3_mk_string_symbol(ctx, "up_rt");
    lang->path.enum_names[7] = Z3_mk_string_symbol(ctx, "dn_rt");
    lang->path.enum_names[8] = Z3_mk_string_symbol(ctx, "dn_lt");
    lang->path.enum_names[9] = Z3_mk_string_symbol(ctx, "up_lt");

    lang->path.enum_names[10] = Z3_mk_string_symbol(ctx, "et_et");
  }

  lang->path.sort = Z3_mk_enumeration_sort(ctx, Z3_mk_string_symbol(ctx, "path"), PATH_VARIANTS, lang->path.enum_names, lang->path.enum_consts, lang->path.enum_testers);

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

  lang->path.et_et = Z3_mk_app(ctx, lang->path.enum_consts[10], 0, 0);

  Z3_sort u8col_u8row[2] = {lang->u8.sort, lang->u8.sort};
  lang->path.tile_is_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "path_choice"), ARRAY_LEN(u8col_u8row), u8col_u8row, lang->path.sort);

  lang->path.penatly = Z3_mk_string_symbol(ctx, "path_penatly");
}

/***
 * Shortest paths are found by placing a penatly on the assignment of a non empty path value to each potentiial path tile.
 * So long as a path is required and optimisation is enforced, no shorter path can exist on SAT.
 */
void Lang_assert_shortest_path_empty_hints(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, Maze *maze) {

  Z3_ast u8_col_row[2] = {};

  for (uint8_t r = 0; r < maze->size.y; ++r) {
    u8_col_row[1] = Z3_mk_int(ctx, (int)r, lang->u8.sort);

    for (uint8_t c = 0; c < maze->size.x; ++c) {
      u8_col_row[0] = Z3_mk_int(ctx, (int)c, lang->u8.sort);

      if (Maze_abstract_is_path(maze, c, r)) {
        Z3_optimize_assert_soft(ctx, optimizer, Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, ARRAY_LEN(u8_col_row), u8_col_row), lang->path.et_et), "1", lang->path.penatly);
      } else {
        Z3_optimize_assert(ctx, optimizer, Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, ARRAY_LEN(u8_col_row), u8_col_row), lang->path.et_et));
      }
    }
  }
}

void Lang_assert_path_non_empty_hints(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, Maze *maze) {

  Z3_ast u8_col_row[2] = {};

  for (uint8_t r = 0; r < maze->size.y; r++) {
    u8_col_row[1] = Z3_mk_int(ctx, (int)r, lang->u8.sort);

    for (uint8_t c = 0; c < maze->size.x; c++) {
      u8_col_row[0] = Z3_mk_int(ctx, (int)c, lang->u8.sort);

      if (Maze_abstract_is_path(maze, c, r)) {
        Z3_ast tile_path_value = Z3_mk_app(ctx, lang->path.tile_is_f, 2, u8_col_row);

        if (0 < r) {
          Z3_ast up_tile[2] = {
              Z3_mk_int(ctx, (int)c, lang->u8.sort),
              Z3_mk_int(ctx, (int)(r - 1), lang->u8.sort),
          };

          uint32_t up_tile_reqs = 0;
          Z3_ast up_tile_req[4] = {};

          up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, up_tile), lang->path.og_dn);
          up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, up_tile), lang->path.up_dn);
          up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, up_tile), lang->path.dn_rt);
          up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, up_tile), lang->path.dn_lt);

          if (0 < up_tile_reqs) {
            Z3_ast up_tile_or = Z3_mk_or(ctx, up_tile_reqs, up_tile_req);

            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.og_up), up_tile_or));
            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.up_lt), up_tile_or));
            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.up_dn), up_tile_or));
            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.up_rt), up_tile_or));
          }
        }

        if (c + 1 < maze->size.x) {
          Z3_ast rt_tile[2] = {
              Z3_mk_int(ctx, (int)(c + 1), lang->u8.sort),
              Z3_mk_int(ctx, (int)r, lang->u8.sort),
          };

          uint32_t rt_tile_reqs = 0;
          Z3_ast rt_tile_req[4] = {};

          rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, rt_tile), lang->path.og_lt);
          rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, rt_tile), lang->path.rt_lt);
          rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, rt_tile), lang->path.dn_lt);
          rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, rt_tile), lang->path.up_lt);

          if (0 < rt_tile_reqs) {
            Z3_ast rt_tile_or = Z3_mk_or(ctx, rt_tile_reqs, rt_tile_req);

            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.og_rt), rt_tile_or));
            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.rt_lt), rt_tile_or));
            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.up_rt), rt_tile_or));
            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.dn_rt), rt_tile_or));
          }
        }

        if (r + 1 < maze->size.y) {
          Z3_ast dn_tile[2] = {
              Z3_mk_int(ctx, (int)c, lang->u8.sort),
              Z3_mk_int(ctx, (int)(r + 1), lang->u8.sort),
          };

          uint32_t dn_tile_reqs = 0;
          Z3_ast dn_tile_req[4] = {};

          dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, dn_tile), lang->path.og_up);
          dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, dn_tile), lang->path.up_dn);
          dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, dn_tile), lang->path.up_rt);
          dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, dn_tile), lang->path.up_lt);

          if (0 < dn_tile_reqs) {
            Z3_ast dn_tile_or = Z3_mk_or(ctx, dn_tile_reqs, dn_tile_req);

            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.og_dn), dn_tile_or));
            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.up_dn), dn_tile_or));
            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.dn_rt), dn_tile_or));
            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.dn_lt), dn_tile_or));
          }
        }

        if (0 < c) {
          Z3_ast lt_tile[2] = {
              Z3_mk_int(ctx, (int)(c - 1), lang->u8.sort),
              Z3_mk_int(ctx, (int)r, lang->u8.sort),
          };

          uint32_t lt_tile_reqs = 0;
          Z3_ast lt_tile_req[4] = {};

          lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, lt_tile), lang->path.og_rt);
          lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, lt_tile), lang->path.rt_lt);
          lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, lt_tile), lang->path.dn_rt);
          lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, lt_tile), lang->path.up_rt);

          if (0 < lt_tile_reqs) {
            Z3_ast lt_tile_or = Z3_mk_or(ctx, lt_tile_reqs, lt_tile_req);

            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.og_lt), lt_tile_or));
            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.rt_lt), lt_tile_or));
            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.up_lt), lt_tile_or));
            Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_value, lang->path.dn_lt), lt_tile_or));
          }
        }
      }
    }
  }
}

//

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

  lang->anima.tile_row_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "anima_row"), 1, (Z3_sort[1]){lang->anima.sort}, lang->u8.sort);
  lang->anima.tile_col_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "anima_col"), 1, (Z3_sort[1]){lang->anima.sort}, lang->u8.sort);
}

void Lang_assert_anima_locations(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, SmtWorld *world) {

  for (size_t anima_idx = 0; anima_idx < ANIMA_COUNT; ++anima_idx) {

    auto anima_location = atomic_load(&world->anima[anima_idx].location);
    Z3_ast anima_ast = Z3_mk_app(ctx, lang->anima.enum_consts[anima_idx], 0, 0);

    Z3_optimize_assert(ctx, optimizer, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, lang->anima.tile_row_f, anima_ast), Z3_mk_int(ctx, (int)anima_location.y, lang->u8.sort)));
    Z3_optimize_assert(ctx, optimizer, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, lang->anima.tile_col_f, anima_ast), Z3_mk_int(ctx, (int)anima_location.x, lang->u8.sort)));
  }
}

// Require a non-origin tile on non-anima tiles
void Lang_assert_all_non_anima_are_non_origin(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, SmtWorld *world, Maze *maze) {

  Z3_ast u8_col_row[2] = {};

  for (uint32_t row = 0; row < maze->size.y; row++) {
    u8_col_row[1] = Z3_mk_int(ctx, (int)row, lang->u8.sort);

    for (uint32_t col = 0; col < maze->size.x; col++) {
      u8_col_row[0] = Z3_mk_int(ctx, (int)col, lang->u8.sort);

      for (uint8_t anima_idx = 0; anima_idx < ANIMA_COUNT; ++anima_idx) {
        auto location = atomic_load(&world->anima[anima_idx].location);

        if (location.x == col && location.y == row) {
          goto skip_tile_assertion;
        }
      }

      Z3_ast tile_path_value = Z3_mk_app(ctx, lang->path.tile_is_f, ARRAY_LEN(u8_col_row), u8_col_row);

      Z3_ast value_is_non_origin[7] = {
          Z3_mk_eq(ctx, tile_path_value, lang->path.up_dn),
          Z3_mk_eq(ctx, tile_path_value, lang->path.rt_lt),
          Z3_mk_eq(ctx, tile_path_value, lang->path.up_rt),
          Z3_mk_eq(ctx, tile_path_value, lang->path.dn_rt),
          Z3_mk_eq(ctx, tile_path_value, lang->path.up_lt),
          Z3_mk_eq(ctx, tile_path_value, lang->path.dn_lt),
          Z3_mk_eq(ctx, tile_path_value, lang->path.et_et),
      };

      Z3_optimize_assert(ctx, optimizer, Z3_mk_or(ctx, ARRAY_LEN(value_is_non_origin), value_is_non_origin));
    skip_tile_assertion:
    }
  }
}

void Lang_assert_all_anima_tiles_are_origin_tiles(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer) {

  for (size_t anima_idx = 0; anima_idx < ANIMA_COUNT; ++anima_idx) {

    Z3_ast anima_ast = Z3_mk_app(ctx, lang->anima.enum_consts[anima_idx], 0, 0);

    Z3_ast anima_col_row[2] = {z3_mk_unary_app(ctx, lang->anima.tile_col_f, anima_ast), z3_mk_unary_app(ctx, lang->anima.tile_row_f, anima_ast)};

    Z3_ast anima_tile_value = Z3_mk_app(ctx, lang->path.tile_is_f, ARRAY_LEN(anima_col_row), anima_col_row);

    Z3_ast value_is_origin[4] = {Z3_mk_eq(ctx, anima_tile_value, lang->path.og_up),
                                 Z3_mk_eq(ctx, anima_tile_value, lang->path.og_rt),
                                 Z3_mk_eq(ctx, anima_tile_value, lang->path.og_dn),
                                 Z3_mk_eq(ctx, anima_tile_value, lang->path.og_lt)};

    Z3_optimize_assert(ctx, optimizer, Z3_mk_or(ctx, ARRAY_LEN(value_is_origin), value_is_origin));
  }
}

// Unused
void Lang_assert_all_origin_are_anima(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, Maze *maze) {

  Z3_ast u8_col_row[2] = {};

  for (uint32_t r = 0; r < maze->size.y; r++) {
    u8_col_row[1] = Z3_mk_int(ctx, (int)r, lang->u8.sort);

    for (uint32_t c = 0; c < maze->size.x; c++) {
      u8_col_row[0] = Z3_mk_int(ctx, (int)c, lang->u8.sort);

      Z3_ast path_origin;
      Z3_ast some_anima_location;

      { // Path origin disjunct
        Z3_ast tile_is = Z3_mk_app(ctx, lang->path.tile_is_f, 2, u8_col_row);

        Z3_ast value_is_origin[4] = {
            Z3_mk_eq(ctx, tile_is, lang->path.og_up),
            Z3_mk_eq(ctx, tile_is, lang->path.og_rt),
            Z3_mk_eq(ctx, tile_is, lang->path.og_dn),
            Z3_mk_eq(ctx, tile_is, lang->path.og_lt),
        };

        path_origin = Z3_mk_or(ctx, ARRAY_LEN(value_is_origin), value_is_origin);
      }

      { // Anima location disjunct
        Z3_ast anima_ands[ANIMA_COUNT];
        for (size_t anima_idx = 0; anima_idx < ANIMA_COUNT; ++anima_idx) {
          Z3_ast anima_ast = Z3_mk_app(ctx, lang->anima.enum_consts[anima_idx], 0, 0);

          Z3_ast anima_row_col_eq[2] = {
              Z3_mk_eq(ctx, z3_mk_unary_app(ctx, lang->anima.tile_col_f, anima_ast), u8_col_row[0]),
              Z3_mk_eq(ctx, z3_mk_unary_app(ctx, lang->anima.tile_row_f, anima_ast), u8_col_row[1]),
          };

          anima_ands[anima_idx] = Z3_mk_and(ctx, ARRAY_LEN(anima_row_col_eq), anima_row_col_eq);
        }
        some_anima_location = Z3_mk_or(ctx, ANIMA_COUNT, anima_ands);
      }

      Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, path_origin, some_anima_location));
    }
  }
}

void Lang_facing_setup(struct z3_lang *lang, Z3_context ctx) {

  {
    lang->direction.enum_names[0] = Z3_mk_string_symbol(ctx, "up");
    lang->direction.enum_names[1] = Z3_mk_string_symbol(ctx, "rt");
    lang->direction.enum_names[2] = Z3_mk_string_symbol(ctx, "dn");
    lang->direction.enum_names[3] = Z3_mk_string_symbol(ctx, "lt");
  }

  lang->direction.sort = Z3_mk_enumeration_sort(ctx,
                                                Z3_mk_string_symbol(ctx, "facing"),
                                                ARRAY_LEN(lang->direction.enum_names),
                                                lang->direction.enum_names,
                                                lang->direction.enum_consts,
                                                lang->direction.enum_testers);

  lang->anima.is_facing = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "anima_is_facing"), 1, (Z3_sort[1]){lang->anima.sort}, lang->direction.sort);
}

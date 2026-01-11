#include <limits.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>

#include "SML/logic.h"
#include "generic/pairs.h"
#include "macro.h"

Z3_context z3_mk_anima_ctx() {

  Z3_config cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "model", "true");

  Z3_context ctx = Z3_mk_context(cfg);
  Z3_set_error_handler(ctx, error_handler);

  Z3_del_config(cfg);

  return ctx;
}

void Lang_setup_base(Language *lang, Z3_context ctx) {
  lang->u8.sort = Z3_mk_bv_sort(ctx, 6);
}

// Path fns

void Lang_setup_path(Language *lang, Z3_context ctx) {

  {
    lang->path.enum_names[0] = Z3_mk_string_symbol(ctx, "o_n");
    lang->path.enum_names[1] = Z3_mk_string_symbol(ctx, "o_e");
    lang->path.enum_names[2] = Z3_mk_string_symbol(ctx, "o_s");
    lang->path.enum_names[3] = Z3_mk_string_symbol(ctx, "o_w");

    lang->path.enum_names[4] = Z3_mk_string_symbol(ctx, "n_s");
    lang->path.enum_names[5] = Z3_mk_string_symbol(ctx, "e_w");

    lang->path.enum_names[6] = Z3_mk_string_symbol(ctx, "n_e");
    lang->path.enum_names[7] = Z3_mk_string_symbol(ctx, "s_e");
    lang->path.enum_names[8] = Z3_mk_string_symbol(ctx, "s_w");
    lang->path.enum_names[9] = Z3_mk_string_symbol(ctx, "n_w");

    lang->path.enum_names[10] = Z3_mk_string_symbol(ctx, "et_et");
  }

  lang->path.sort = Z3_mk_enumeration_sort(ctx, Z3_mk_string_symbol(ctx, "path"), PATH_VARIANTS, lang->path.enum_names, lang->path.enum_consts, lang->path.enum_testers);

  lang->path.token.o_n = Z3_mk_app(ctx, lang->path.enum_consts[0], 0, 0);
  lang->path.token.o_e = Z3_mk_app(ctx, lang->path.enum_consts[1], 0, 0);
  lang->path.token.o_s = Z3_mk_app(ctx, lang->path.enum_consts[2], 0, 0);
  lang->path.token.o_w = Z3_mk_app(ctx, lang->path.enum_consts[3], 0, 0);

  lang->path.token.n_s = Z3_mk_app(ctx, lang->path.enum_consts[4], 0, 0);
  lang->path.token.e_w = Z3_mk_app(ctx, lang->path.enum_consts[5], 0, 0);

  lang->path.token.n_e = Z3_mk_app(ctx, lang->path.enum_consts[6], 0, 0);
  lang->path.token.s_e = Z3_mk_app(ctx, lang->path.enum_consts[7], 0, 0);
  lang->path.token.s_w = Z3_mk_app(ctx, lang->path.enum_consts[8], 0, 0);
  lang->path.token.n_w = Z3_mk_app(ctx, lang->path.enum_consts[9], 0, 0);

  lang->path.token.x_x = Z3_mk_app(ctx, lang->path.enum_consts[10], 0, 0);

  Z3_sort col_row[2] = {lang->u8.sort, lang->u8.sort};
  lang->path.tile_is_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "path_v"), ARRAY_LEN(col_row), col_row, lang->path.sort);

  lang->path.penatly = Z3_mk_string_symbol(ctx, "path_p");
}

/// Shortest paths are found by placing a penatly on the assignment of a non empty path value to each potentiial path tile.
/// So long as a path is required and optimisation is enforced, no shorter path can exist on SAT.
void Lang_assert_shortest_path_empty_hints(const Language *lang, Z3_context ctx, Z3_optimize otz, const Maze *maze) {

  Z3_ast col_row[2] = {};

  for (uint8_t row = 0; row < maze->size.y; ++row) {
    col_row[1] = Z3_mk_int(ctx, row, lang->u8.sort);

    for (uint8_t col = 0; col < maze->size.x; ++col) {
      col_row[0] = Z3_mk_int(ctx, col, lang->u8.sort);

      if (Maze_is_path(maze, col, row)) {
        Z3_ast tile_path_val = Z3_mk_app(ctx, lang->path.tile_is_f, ARRAY_LEN(col_row), col_row);
        Z3_optimize_assert_soft(ctx, otz, Z3_mk_eq(ctx, tile_path_val, lang->path.token.x_x), "1", lang->path.penatly);
      } else {
        Z3_ast tile_path_val = Z3_mk_app(ctx, lang->path.tile_is_f, ARRAY_LEN(col_row), col_row);
        Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, tile_path_val, lang->path.token.x_x));
      }
    }
  }
}

void Lang_assert_path_non_empty_hints(const Language *lang, Z3_context ctx, Z3_optimize otz, const Maze *maze) {

  Z3_ast col_row[2] = {};

  for (uint8_t row = 0; row < maze->size.y; row++) {
    col_row[1] = Z3_mk_int(ctx, row, lang->u8.sort);

    for (uint8_t col = 0; col < maze->size.x; col++) {
      col_row[0] = Z3_mk_int(ctx, col, lang->u8.sort);

      if (Maze_is_path(maze, col, row)) {
        Z3_ast tile_path_val = Z3_mk_app(ctx, lang->path.tile_is_f, 2, col_row);

        if (0 < row) {
          Z3_ast tile_n[2] = {
              Z3_mk_int(ctx, col, lang->u8.sort),
              Z3_mk_int(ctx, (row - 1), lang->u8.sort),
          };

          uint32_t reqs_n = 0;
          Z3_ast req_n[4] = {};

          req_n[reqs_n++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_n), lang->path.token.o_s);
          req_n[reqs_n++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_n), lang->path.token.n_s);
          req_n[reqs_n++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_n), lang->path.token.s_e);
          req_n[reqs_n++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_n), lang->path.token.s_w);

          if (0 < reqs_n) {
            Z3_ast up_tile_or = Z3_mk_or(ctx, reqs_n, req_n);

            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.o_n), up_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.n_w), up_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.n_s), up_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.n_e), up_tile_or));
          }
        }

        if (col + 1 < maze->size.x) {
          Z3_ast tile_e[2] = {
              Z3_mk_int(ctx, (col + 1), lang->u8.sort),
              Z3_mk_int(ctx, row, lang->u8.sort),
          };

          uint32_t reqs_e = 0;
          Z3_ast req_e[4] = {};

          req_e[reqs_e++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_e), lang->path.token.o_w);
          req_e[reqs_e++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_e), lang->path.token.e_w);
          req_e[reqs_e++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_e), lang->path.token.s_w);
          req_e[reqs_e++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_e), lang->path.token.n_w);

          if (0 < reqs_e) {
            Z3_ast rt_tile_or = Z3_mk_or(ctx, reqs_e, req_e);

            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.o_e), rt_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.e_w), rt_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.n_e), rt_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.s_e), rt_tile_or));
          }
        }

        if (row + 1 < maze->size.y) {
          Z3_ast tile_s[2] = {
              Z3_mk_int(ctx, col, lang->u8.sort),
              Z3_mk_int(ctx, (row + 1), lang->u8.sort),
          };

          uint32_t reqs_s = 0;
          Z3_ast req_s[4] = {};

          req_s[reqs_s++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_s), lang->path.token.o_n);
          req_s[reqs_s++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_s), lang->path.token.n_s);
          req_s[reqs_s++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_s), lang->path.token.n_e);
          req_s[reqs_s++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_s), lang->path.token.n_w);

          if (0 < reqs_s) {
            Z3_ast tile_s_or = Z3_mk_or(ctx, reqs_s, req_s);

            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.o_s), tile_s_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.n_s), tile_s_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.s_e), tile_s_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.s_w), tile_s_or));
          }
        }

        if (0 < col) {
          Z3_ast tile_w[2] = {
              Z3_mk_int(ctx, (col - 1), lang->u8.sort),
              Z3_mk_int(ctx, row, lang->u8.sort),
          };

          uint32_t reqs_w = 0;
          Z3_ast req_w[4] = {};

          req_w[reqs_w++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_w), lang->path.token.o_e);
          req_w[reqs_w++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_w), lang->path.token.e_w);
          req_w[reqs_w++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_w), lang->path.token.s_e);
          req_w[reqs_w++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, tile_w), lang->path.token.n_e);

          if (0 < reqs_w) {
            Z3_ast lt_tile_or = Z3_mk_or(ctx, reqs_w, req_w);

            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.o_w), lt_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.e_w), lt_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.n_w), lt_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.token.s_w), lt_tile_or));
          }
        }
      }
    }
  }
}

/// Anima fns

void Lang_setup_animas(Language *lang, Z3_context ctx, size_t anima_count) {

  if (1 <= anima_count) {
    lang->anima.enum_names[0] = Z3_mk_string_symbol(ctx, "gottlob");
  }
  if (2 <= anima_count) {
    lang->anima.enum_names[1] = Z3_mk_string_symbol(ctx, "bertrand");
  }
  if (3 <= anima_count) {
    lang->anima.enum_names[2] = Z3_mk_string_symbol(ctx, "herbrand");
  }
  if (4 <= anima_count) {
    lang->anima.enum_names[3] = Z3_mk_string_symbol(ctx, "lob");
  }

  assert(anima_count < UINT_MAX);
  lang->anima.sort = Z3_mk_enumeration_sort(ctx,
                                            Z3_mk_string_symbol(ctx, "anima"),
                                            (unsigned int)anima_count,
                                            lang->anima.enum_names,
                                            lang->anima.enum_consts,
                                            lang->anima.enum_testers);

  { // Anima row fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "anima_row");
    Z3_sort domain[1] = {lang->anima.sort};
    Z3_sort range = lang->u8.sort;
    lang->anima.tile_row_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }

  { // Anima col fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "anima_col");
    Z3_sort domain[1] = {lang->anima.sort};
    Z3_sort range = lang->u8.sort;
    lang->anima.tile_col_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }
}

void Lang_assert_anima_location(const Language *lang, Z3_context ctx, Z3_optimize otz, const Situation *situation, const uint8_t id) {

  Pair_uint8 anima_location = atomic_load(&situation->animas[id].location);
  slog_display(SLOG_DEBUG, 0, "Asserted anima %d at %dx%d\n", id, anima_location.x, anima_location.y);
  Z3_ast anima_ast = Z3_mk_app(ctx, lang->anima.enum_consts[id], 0, 0);

  {
    Z3_ast z3_row = z3_mk_unary_app(ctx, lang->anima.tile_row_f, anima_ast);
    Z3_ast abstract_row = Z3_mk_int(ctx, anima_location.y, lang->u8.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_row, abstract_row));
  }
  {
    Z3_ast z3_col = z3_mk_unary_app(ctx, lang->anima.tile_col_f, anima_ast);
    Z3_ast abstract_col = Z3_mk_int(ctx, anima_location.x, lang->u8.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_col, abstract_col));
  }
}

void Lang_anima_tile_is_origin(const Language *lang, Z3_context ctx, Z3_optimize otz, uint8_t id) {

  Z3_ast anima_ast = Z3_mk_app(ctx, lang->anima.enum_consts[id], 0, 0);

  Z3_ast anima_col_row[2] = {z3_mk_unary_app(ctx, lang->anima.tile_col_f, anima_ast),
                             z3_mk_unary_app(ctx, lang->anima.tile_row_f, anima_ast)};

  Z3_ast anima_tile_value = Z3_mk_app(ctx, lang->path.tile_is_f, ARRAY_LEN(anima_col_row), anima_col_row);

  Z3_ast value_is_origin[4] = {Z3_mk_eq(ctx, anima_tile_value, lang->path.token.o_n),
                               Z3_mk_eq(ctx, anima_tile_value, lang->path.token.o_e),
                               Z3_mk_eq(ctx, anima_tile_value, lang->path.token.o_s),
                               Z3_mk_eq(ctx, anima_tile_value, lang->path.token.o_w)};

  Z3_optimize_assert(ctx, otz, Z3_mk_or(ctx, ARRAY_LEN(value_is_origin), value_is_origin));
}

/// Persona fns

void Lang_setup_persona(Language *lang, Z3_context ctx) {

  lang->persona.enum_name = Z3_mk_string_symbol(ctx, "smt-man");

  lang->persona.sort = Z3_mk_enumeration_sort(ctx,
                                              Z3_mk_string_symbol(ctx, "persona"),
                                              1,
                                              &lang->persona.enum_name,
                                              &lang->persona.enum_const,
                                              &lang->persona.enum_tester);

  { // Persona row fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "persona_row");
    Z3_sort domain[1] = {lang->persona.sort};
    Z3_sort range = lang->u8.sort;
    lang->persona.tile_row_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }

  { // Persona col fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "persona_col");
    Z3_sort domain[1] = {lang->persona.sort};
    Z3_sort range = lang->u8.sort;
    lang->persona.tile_col_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }
}

void Lang_persona_tile_is_origin(const Language *lang, Z3_context ctx, Z3_optimize otz) {

  Z3_ast persona_ast = Z3_mk_app(ctx, lang->persona.enum_const, 0, 0);

  Z3_ast persona_col_row[2] = {z3_mk_unary_app(ctx, lang->persona.tile_col_f, persona_ast),
                               z3_mk_unary_app(ctx, lang->persona.tile_row_f, persona_ast)};

  Z3_ast persona_tile_value = Z3_mk_app(ctx, lang->path.tile_is_f, ARRAY_LEN(persona_col_row), persona_col_row);

  Z3_ast value_is_origin[4] = {Z3_mk_eq(ctx, persona_tile_value, lang->path.token.o_n),
                               Z3_mk_eq(ctx, persona_tile_value, lang->path.token.o_e),
                               Z3_mk_eq(ctx, persona_tile_value, lang->path.token.o_s),
                               Z3_mk_eq(ctx, persona_tile_value, lang->path.token.o_w)};

  Z3_optimize_assert(ctx, otz, Z3_mk_or(ctx, ARRAY_LEN(value_is_origin), value_is_origin));
}

void Lang_assert_persona_location(const Language *lang, Z3_context ctx, Z3_optimize otz, const Situation *situation) {

  auto persona_location = atomic_load(&situation->persona.location);
  printf("Asserted persona at %dx%d\n", persona_location.x, persona_location.y);
  Z3_ast persona_ast = Z3_mk_app(ctx, lang->persona.enum_const, 0, 0);

  {
    Z3_ast z3_row = z3_mk_unary_app(ctx, lang->persona.tile_row_f, persona_ast);
    Z3_ast abstract_row = Z3_mk_int(ctx, persona_location.y, lang->u8.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_row, abstract_row));
  }
  {
    Z3_ast z3_col = z3_mk_unary_app(ctx, lang->persona.tile_col_f, persona_ast);
    Z3_ast abstract_col = Z3_mk_int(ctx, persona_location.x, lang->u8.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_col, abstract_col));
  }
}

/// Link

// Require a non-origin tile on non-anima tiles
void Lang_assert_link_reqs(const Language *lang, Z3_context ctx, Z3_optimize otz, const Situation *situation, const Maze *maze, const uint8_t id) {

  Pair_uint8 anima_location = atomic_load(&situation->animas[id].location);
  Pair_uint8 persona_location = atomic_load(&situation->persona.location);

  Z3_ast col_row[2] = {};

  for (uint8_t row = 0; row < maze->size.y; row++) {
    col_row[1] = Z3_mk_int(ctx, row, lang->u8.sort);

    for (uint8_t col = 0; col < maze->size.x; col++) {
      col_row[0] = Z3_mk_int(ctx, col, lang->u8.sort);

      if ((anima_location.x == col && anima_location.y == row) || (persona_location.x == col && persona_location.y == row)) {
        goto skip_tile_assertion;
      }

      Z3_ast tile_path_value = Z3_mk_app(ctx, lang->path.tile_is_f, ARRAY_LEN(col_row), col_row);

      Z3_ast value_is_link[7] = {
          Z3_mk_eq(ctx, tile_path_value, lang->path.token.n_s),
          Z3_mk_eq(ctx, tile_path_value, lang->path.token.e_w),
          Z3_mk_eq(ctx, tile_path_value, lang->path.token.n_e),
          Z3_mk_eq(ctx, tile_path_value, lang->path.token.s_e),
          Z3_mk_eq(ctx, tile_path_value, lang->path.token.n_w),
          Z3_mk_eq(ctx, tile_path_value, lang->path.token.s_w),
          Z3_mk_eq(ctx, tile_path_value, lang->path.token.x_x),
      };

      Z3_optimize_assert(ctx, otz, Z3_mk_or(ctx, ARRAY_LEN(value_is_link), value_is_link));
    skip_tile_assertion:
    }
  }
}

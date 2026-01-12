#include <limits.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>

#include "SML/logic.h"
#include "generic/pairs.h"

Z3_ast direct_h(const Language *language, const Z3_context ctx, const Z3_ast col_row[2]) {

  Z3_ast conjuncts[2] = {
      Z3_mk_eq(ctx, Z3_mk_app(ctx, language->path.tile_h_f, 2, col_row), language->path.token.a),
      Z3_mk_eq(ctx, Z3_mk_app(ctx, language->path.tile_v_f, 2, col_row), language->path.token.x),
  };

  return Z3_mk_and(ctx, 2, conjuncts);
}

Z3_ast direct_v(const Language *language, const Z3_context ctx, const Z3_ast col_row[2]) {

  Z3_ast conjuncts[2] = {
      Z3_mk_eq(ctx, Z3_mk_app(ctx, language->path.tile_h_f, 2, col_row), language->path.token.x),
      Z3_mk_eq(ctx, Z3_mk_app(ctx, language->path.tile_v_f, 2, col_row), language->path.token.a),
  };

  return Z3_mk_and(ctx, 2, conjuncts);
}

Z3_context z3_mk_anima_ctx() {

  Z3_config cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "model", "true");

  Z3_context ctx = Z3_mk_context(cfg);
  Z3_set_error_handler(ctx, error_handler);

  Z3_del_config(cfg);

  return ctx;
}

void Lang_setup_base(Language *language, Z3_context ctx) {
  language->u8.sort = Z3_mk_bv_sort(ctx, 8);
}

// Path fns

void Lang_setup_path(Language *lang, Z3_context ctx) {

  {
    lang->path.enum_names[0] = Z3_mk_string_symbol(ctx, "o");
    lang->path.enum_names[1] = Z3_mk_string_symbol(ctx, "a");
    lang->path.enum_names[2] = Z3_mk_string_symbol(ctx, "b");
    lang->path.enum_names[3] = Z3_mk_string_symbol(ctx, "x");
  }

  lang->path.sort = Z3_mk_enumeration_sort(ctx, Z3_mk_string_symbol(ctx, "path"), PATH_VARIANTS, lang->path.enum_names, lang->path.enum_consts, lang->path.enum_testers);

  lang->path.token.o = Z3_mk_app(ctx, lang->path.enum_consts[0], 0, 0);
  lang->path.token.a = Z3_mk_app(ctx, lang->path.enum_consts[1], 0, 0);
  lang->path.token.b = Z3_mk_app(ctx, lang->path.enum_consts[2], 0, 0);
  lang->path.token.x = Z3_mk_app(ctx, lang->path.enum_consts[3], 0, 0);

  Z3_sort col_row[2] = {lang->u8.sort, lang->u8.sort};

  lang->path.tile_h_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "path_h"), 2, col_row, lang->path.sort);

  lang->path.tile_v_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "path_v"), 2, col_row, lang->path.sort);

  lang->path.penatly = Z3_mk_string_symbol(ctx, "path_p");
}

/// Shortest paths are found by placing a penatly on the assignment of a non empty path value to each potentiial path tile.
/// So long as a path is required and optimisation is enforced, no shorter path can exist on SAT.
void Lang_assert_shortest_path_empty_hints(const Language *lang, Z3_context ctx, Z3_optimize otz, const Maze *maze) {

  for (uint8_t row = 0; row < maze->size.y; ++row) {
    for (uint8_t col = 0; col < maze->size.x; ++col) {
      Z3_ast tile_x[2] = {
          Z3_mk_int(ctx, col, lang->u8.sort),
          Z3_mk_int(ctx, row, lang->u8.sort),
      };

      Z3_ast tile_x_h = Z3_mk_app(ctx, lang->path.tile_h_f, 2, tile_x);
      Z3_ast tile_x_v = Z3_mk_app(ctx, lang->path.tile_v_f, 2, tile_x);

      if (Maze_is_path(maze, col, row)) {
        Z3_optimize_assert_soft(ctx, otz, Z3_mk_eq(ctx, tile_x_h, lang->path.token.x), "1", lang->path.penatly);
        Z3_optimize_assert_soft(ctx, otz, Z3_mk_eq(ctx, tile_x_v, lang->path.token.x), "1", lang->path.penatly);
      } else {
        Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, tile_x_h, lang->path.token.x));
        Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, tile_x_v, lang->path.token.x));
      }
    }
  }
}

void Lang_assert_path_non_empty_hints(const Language *lang, Z3_context ctx, Z3_optimize otz, const Maze *maze) {

  for (uint8_t row = 0; row < maze->size.y; ++row) {
    for (uint8_t col = 0; col < maze->size.x; ++col) {

      Z3_ast tile_x[2] = {
          Z3_mk_int(ctx, col, lang->u8.sort),
          Z3_mk_int(ctx, row, lang->u8.sort),
      };

      if (Maze_is_path(maze, col, row)) {
        Z3_ast tile_x_h = Z3_mk_app(ctx, lang->path.tile_h_f, 2, tile_x);
        Z3_ast tile_x_v = Z3_mk_app(ctx, lang->path.tile_v_f, 2, tile_x);

        { // O H
          Z3_ast tile_e[2] = {
              Z3_mk_int(ctx, (col + 1), lang->u8.sort),
              Z3_mk_int(ctx, row, lang->u8.sort),
          };
          Z3_ast tile_w[2] = {
              Z3_mk_int(ctx, (col - 1), lang->u8.sort),
              Z3_mk_int(ctx, row, lang->u8.sort),
          };

          uint32_t option_count = 0;
          Z3_ast options[2] = {};

          if (0 < col) {
            options[option_count++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_h_f, 2, tile_w), lang->path.token.a);
          }
          if (col + 1 < maze->size.x) {
            options[option_count++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_h_f, 2, tile_e), lang->path.token.b);
          }

          Z3_ast origin_h_or = Z3_mk_or(ctx, option_count, options);
          Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_v, lang->path.token.o), origin_h_or));
        }

        { // O V
          Z3_ast tile_n[2] = {
              Z3_mk_int(ctx, col, lang->u8.sort),
              Z3_mk_int(ctx, (row - 1), lang->u8.sort),
          };
          Z3_ast tile_s[2] = {
              Z3_mk_int(ctx, col, lang->u8.sort),
              Z3_mk_int(ctx, (row + 1), lang->u8.sort),
          };

          uint32_t option_count = 0;
          Z3_ast options[2] = {};

          if (0 < row) {
            options[option_count++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_v_f, 2, tile_n), lang->path.token.b);
          }
          if (row + 1 < maze->size.y) {
            options[option_count++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_v_f, 2, tile_s), lang->path.token.a);
          }

          Z3_ast origin_v_or = Z3_mk_or(ctx, option_count, options);
          Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_h, lang->path.token.o), origin_v_or));
        }

        if (0 < row) { // N
          Z3_ast tile_n[2] = {
              Z3_mk_int(ctx, col, lang->u8.sort),
              Z3_mk_int(ctx, (row - 1), lang->u8.sort),
          };

          uint32_t option_count = 0;
          Z3_ast options[3] = {};

          Z3_ast tile_n_h = Z3_mk_app(ctx, lang->path.tile_h_f, 2, tile_n);

          options[option_count++] = Z3_mk_eq(ctx, tile_n_h, lang->path.token.o);
          if (col < maze->size.x - 1 && Maze_is_path(maze, col + 1, row - 1)) {
            options[option_count++] = Z3_mk_eq(ctx, tile_n_h, lang->path.token.a);
          }
          if (0 < col && Maze_is_path(maze, col - 1, row - 1)) {
            options[option_count++] = Z3_mk_eq(ctx, tile_n_h, lang->path.token.b);
          }

          if (0 < option_count) { // E
            Z3_ast options_conjunction[2] = {
                Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_v_f, 2, tile_n), lang->path.token.b),
                Z3_mk_or(ctx, option_count, options),
            };
            Z3_ast consequent = Z3_mk_and(ctx, 2, options_conjunction);
            if (1 < row && Maze_is_path(maze, col, row - 2)) {
              consequent = Z3_mk_or(ctx, 2, (Z3_ast[2]){
                                                consequent,
                                                direct_v(lang, ctx, tile_n),
                                            });
            }

            Z3_ast case_a = Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_v, lang->path.token.a), consequent);
            Z3_optimize_assert(ctx, otz, case_a);

            Z3_ast case_b = Z3_mk_implies(ctx, direct_v(lang, ctx, tile_x), consequent);
            Z3_optimize_assert(ctx, otz, case_b);
          }
        }

        if (col + 1 < maze->size.x) { // E
          Z3_ast tile_e[2] = {
              Z3_mk_int(ctx, (col + 1), lang->u8.sort),
              Z3_mk_int(ctx, row, lang->u8.sort),
          };

          uint32_t option_count = 0;
          Z3_ast options[3] = {};

          Z3_ast tile_e_v = Z3_mk_app(ctx, lang->path.tile_v_f, 2, tile_e);

          options[option_count++] = Z3_mk_eq(ctx, tile_e_v, lang->path.token.o);
          if (0 < row && Maze_is_path(maze, col + 1, row - 1)) {
            options[option_count++] = Z3_mk_eq(ctx, tile_e_v, lang->path.token.a);
          }
          if (row < maze->size.y - 1 && Maze_is_path(maze, col + 1, row + 1)) {
            options[option_count++] = Z3_mk_eq(ctx, tile_e_v, lang->path.token.b);
          }

          if (0 < option_count) {
            Z3_ast options_conjunction[2] = {
                Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_h_f, 2, tile_e), lang->path.token.b),
                Z3_mk_or(ctx, option_count, options),
            };
            Z3_ast consequent = Z3_mk_and(ctx, 2, options_conjunction);
            if (col + 2 < maze->size.x && Maze_is_path(maze, col + 2, row)) {
              consequent = Z3_mk_or(ctx, 2, (Z3_ast[2]){
                                                consequent,
                                                direct_h(lang, ctx, tile_e),
                                            });
            }

            Z3_ast case_a = Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_h, lang->path.token.a), consequent);
            Z3_optimize_assert(ctx, otz, case_a);

            Z3_ast case_b = Z3_mk_implies(ctx, direct_h(lang, ctx, tile_x), consequent);
            Z3_optimize_assert(ctx, otz, case_b);
          }
        }

        if (row + 1 < maze->size.y) { // S
          Z3_ast tile_s[2] = {
              Z3_mk_int(ctx, col, lang->u8.sort),
              Z3_mk_int(ctx, (row + 1), lang->u8.sort),
          };

          uint32_t option_count = 0;
          Z3_ast options[3] = {};

          Z3_ast tile_s_h = Z3_mk_app(ctx, lang->path.tile_h_f, 2, tile_s);

          options[option_count++] = Z3_mk_eq(ctx, tile_s_h, lang->path.token.o);
          if (col < maze->size.x - 1 && Maze_is_path(maze, col + 1, row + 1)) {
            options[option_count++] = Z3_mk_eq(ctx, tile_s_h, lang->path.token.a);
          }
          if (0 < col && Maze_is_path(maze, col - 1, row + 1)) {
            options[option_count++] = Z3_mk_eq(ctx, tile_s_h, lang->path.token.b);
          }

          if (0 < option_count) {

            Z3_ast options_conjunction[2] = {
                Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_v_f, 2, tile_s), lang->path.token.a),
                Z3_mk_or(ctx, option_count, options),
            };
            Z3_ast consequent = Z3_mk_and(ctx, 2, options_conjunction);
            if (row + 2 < maze->size.y && Maze_is_path(maze, col, row + 2)) {
              consequent = Z3_mk_or(ctx, 2, (Z3_ast[2]){
                                                consequent,
                                                direct_v(lang, ctx, tile_s),
                                            });
            }

            Z3_ast case_a = Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_v, lang->path.token.b), consequent);
            Z3_optimize_assert(ctx, otz, case_a);

            Z3_ast case_b = Z3_mk_implies(ctx, direct_v(lang, ctx, tile_x), consequent);
            Z3_optimize_assert(ctx, otz, case_b);
          }
        }

        if (0 < col) { // W
          Z3_ast tile_w[2] = {
              Z3_mk_int(ctx, (col - 1), lang->u8.sort),
              Z3_mk_int(ctx, row, lang->u8.sort),
          };

          uint32_t option_count = 0;
          Z3_ast options[3] = {};

          options[option_count++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_v_f, 2, tile_w), lang->path.token.o);
          if (0 < row && Maze_is_path(maze, col - 1, row - 1)) {
            options[option_count++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_v_f, 2, tile_w), lang->path.token.a);
          }
          if (row < maze->size.y - 1 && Maze_is_path(maze, col - 1, row + 1)) {
            options[option_count++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_v_f, 2, tile_w), lang->path.token.b);
          }

          if (0 < option_count) {
            Z3_ast options_conjunction[2] = {
                Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_h_f, 2, tile_w), lang->path.token.a),
                Z3_mk_or(ctx, option_count, options),
            };
            Z3_ast consequent = Z3_mk_and(ctx, 2, options_conjunction);

            if (0 < col - 1 && Maze_is_path(maze, col - 2, row)) {
              consequent = Z3_mk_or(ctx, 2, (Z3_ast[2]){
                                                consequent,
                                                direct_h(lang, ctx, tile_w),
                                            });
            }

            Z3_ast case_a = Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_h, lang->path.token.b), consequent);
            Z3_optimize_assert(ctx, otz, case_a);

            Z3_ast case_b = Z3_mk_implies(ctx, direct_h(lang, ctx, tile_x), consequent);
            Z3_optimize_assert(ctx, otz, case_b);
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

  { // col block
    Z3_ast z3_col = z3_mk_unary_app(ctx, lang->anima.tile_col_f, anima_ast);
    Z3_ast col = Z3_mk_int(ctx, anima_location.x, lang->u8.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_col, col));
  }
  { // row block
    Z3_ast z3_row = z3_mk_unary_app(ctx, lang->anima.tile_row_f, anima_ast);
    Z3_ast row = Z3_mk_int(ctx, anima_location.y, lang->u8.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_row, row));
  }
}

void Lang_anima_tile_is_origin(const Language *lang, Z3_context ctx, Z3_optimize otz, uint8_t id) {

  Z3_ast anima_ast = Z3_mk_app(ctx, lang->anima.enum_consts[id], 0, 0);

  Z3_ast anima_col_row[2] = {z3_mk_unary_app(ctx, lang->anima.tile_col_f, anima_ast),
                             z3_mk_unary_app(ctx, lang->anima.tile_row_f, anima_ast)};

  Z3_ast anima_h = Z3_mk_app(ctx, lang->path.tile_h_f, 2, anima_col_row);
  Z3_ast anima_v = Z3_mk_app(ctx, lang->path.tile_v_f, 2, anima_col_row);

  Z3_ast ho = Z3_mk_eq(ctx, anima_h, lang->path.token.o);
  Z3_ast vo = Z3_mk_eq(ctx, anima_v, lang->path.token.o);

  Z3_ast disjunct[2] = {
      Z3_mk_and(ctx, 2, (Z3_ast[2]){ho, Z3_mk_not(ctx, vo)}),
      Z3_mk_and(ctx, 2, (Z3_ast[2]){vo, Z3_mk_not(ctx, ho)}),
  };

  Z3_optimize_assert(ctx, otz, Z3_mk_or(ctx, 2, disjunct));
}

/// Persona fns

void Lang_setup_persona(Language *lang, Z3_context ctx) {

  lang->persona.enum_name[0] = Z3_mk_string_symbol(ctx, "smt-man");

  lang->persona.sort = Z3_mk_enumeration_sort(ctx,
                                              Z3_mk_string_symbol(ctx, "persona"),
                                              1,
                                              lang->persona.enum_name,
                                              lang->persona.enum_const,
                                              lang->persona.enum_tester);

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

  Z3_ast persona_ast = Z3_mk_app(ctx, lang->persona.enum_const[0], 0, 0);

  Z3_ast persona_col_row[2] = {z3_mk_unary_app(ctx, lang->persona.tile_col_f, persona_ast),
                               z3_mk_unary_app(ctx, lang->persona.tile_row_f, persona_ast)};

  Z3_ast persona_h = Z3_mk_app(ctx, lang->path.tile_h_f, 2, persona_col_row);
  Z3_ast persona_v = Z3_mk_app(ctx, lang->path.tile_v_f, 2, persona_col_row);

  Z3_ast ho = Z3_mk_eq(ctx, persona_h, lang->path.token.o);
  Z3_ast vo = Z3_mk_eq(ctx, persona_v, lang->path.token.o);

  Z3_ast disjunct[2];
  disjunct[0] = Z3_mk_and(ctx, 2, (Z3_ast[2]){ho, Z3_mk_not(ctx, vo)});
  disjunct[1] = Z3_mk_and(ctx, 2, (Z3_ast[2]){vo, Z3_mk_not(ctx, ho)});

  Z3_optimize_assert(ctx, otz, Z3_mk_or(ctx, 2, disjunct));
}

void Lang_assert_persona_location(const Language *lang, Z3_context ctx, Z3_optimize otz, const Situation *situation) {

  Pair_uint8 persona_location = atomic_load(&situation->persona.location);
  printf("Asserted persona at %dx%d\n", persona_location.x, persona_location.y);
  Z3_ast persona_ast = Z3_mk_app(ctx, lang->persona.enum_const[0], 0, 0);

  { // col block
    Z3_ast z3_col = z3_mk_unary_app(ctx, lang->persona.tile_col_f, persona_ast);
    Z3_ast col = Z3_mk_int(ctx, persona_location.x, lang->u8.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_col, col));
  }
  { // row block
    Z3_ast z3_row = z3_mk_unary_app(ctx, lang->persona.tile_row_f, persona_ast);
    Z3_ast row = Z3_mk_int(ctx, persona_location.y, lang->u8.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_row, row));
  }
}

/// Link

// ...
void Language_assert_constant_hints(const Language *lang, Z3_context ctx, Z3_optimize otz, const Maze *maze) {

  for (uint8_t row = 0; row < maze->size.y; row++) {
    for (uint8_t col = 0; col < maze->size.x; col++) {

      Z3_ast tile_x[2] = {Z3_mk_int(ctx, col, lang->u8.sort), Z3_mk_int(ctx, row, lang->u8.sort)};

      Z3_ast tile_x_h = Z3_mk_app(ctx, lang->path.tile_h_f, 2, tile_x);
      Z3_ast tile_x_v = Z3_mk_app(ctx, lang->path.tile_v_f, 2, tile_x);

      Z3_ast disjuncts_h[3] = {
          Z3_mk_eq(ctx, tile_x_h, lang->path.token.a),
          Z3_mk_eq(ctx, tile_x_h, lang->path.token.b),
          Z3_mk_eq(ctx, tile_x_h, lang->path.token.x),
      };
      Z3_ast disjunction_h = Z3_mk_or(ctx, 3, disjuncts_h);
      Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, tile_x_h, lang->path.token.o)), disjunction_h));

      Z3_ast disjuncts_v[3] = {
          Z3_mk_eq(ctx, tile_x_v, lang->path.token.a),
          Z3_mk_eq(ctx, tile_x_v, lang->path.token.b),
          Z3_mk_eq(ctx, tile_x_v, lang->path.token.x),
      };
      Z3_ast disjunction_v = Z3_mk_or(ctx, 3, disjuncts_v);
      Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, tile_x_v, lang->path.token.o)), disjunction_v));
    }
  }
}

void Language_assert_constant_origin_is_anima_or_persona(const Language *language, Z3_context ctx, Z3_optimize otz, const Maze *maze) {

  Z3_ast persona_ast = Z3_mk_app(ctx, language->persona.enum_const[0], 0, 0);

  for (uint8_t row = 0; row < maze->size.y; row++) {
    for (uint8_t col = 0; col < maze->size.x; col++) {

      Z3_ast tile_x[2] = {Z3_mk_int(ctx, col, language->u8.sort), Z3_mk_int(ctx, row, language->u8.sort)};
      Z3_ast tile_x_h = Z3_mk_app(ctx, language->path.tile_h_f, 2, tile_x);
      Z3_ast tile_x_v = Z3_mk_app(ctx, language->path.tile_v_f, 2, tile_x);

      Z3_ast persona_col = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, language->persona.tile_col_f, persona_ast), tile_x[0]);
      Z3_ast persona_row = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, language->persona.tile_row_f, persona_ast), tile_x[1]);

      unsigned int options_idx = 0;
      Z3_ast options[LANGUAGE_ANIMAS + 1];
      options[options_idx++] = Z3_mk_and(ctx, 2, (Z3_ast[2]){persona_col, persona_row});

      for (size_t anima_id = 0; anima_id < LANGUAGE_ANIMAS; ++anima_id) {

        Z3_ast anima_ast = Z3_mk_app(ctx, language->anima.enum_consts[anima_id], 0, 0);
        Z3_ast anima_col = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, language->anima.tile_col_f, anima_ast), tile_x[0]);
        Z3_ast anima_row = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, language->anima.tile_row_f, anima_ast), tile_x[1]);

        options[options_idx++] = Z3_mk_and(ctx, 2, (Z3_ast[2]){anima_col, anima_row});
      }

      Z3_ast options_disjunction = Z3_mk_or(ctx, options_idx, options);

      Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_h, language->path.token.o), options_disjunction));
      Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_v, language->path.token.o), options_disjunction));
    }
  }
}

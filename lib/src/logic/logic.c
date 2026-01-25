#include <limits.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>

#include "SML/logic.h"
#include "generic/pairs.h"

Z3_ast direct_h(const Lexicon *lexicon, const Z3_context ctx, const Z3_ast row_col[2]) {

  Z3_ast conjuncts[2] = {
      Z3_mk_eq(ctx, Z3_mk_app(ctx, lexicon->path.tile_h_f, 2, row_col), lexicon->path.token.a),
      Z3_mk_eq(ctx, Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, row_col), lexicon->path.token.x),
  };

  return Z3_mk_and(ctx, 2, conjuncts);
}

Z3_ast direct_v(const Lexicon *lexicon, const Z3_context ctx, const Z3_ast row_col[2]) {

  Z3_ast conjuncts[2] = {
      Z3_mk_eq(ctx, Z3_mk_app(ctx, lexicon->path.tile_h_f, 2, row_col), lexicon->path.token.x),
      Z3_mk_eq(ctx, Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, row_col), lexicon->path.token.a),
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

void Lexicon_setup_base(Lexicon *lexicon, Z3_context ctx) {
  lexicon->u6.sort = Z3_mk_bv_sort(ctx, 6);
}

// Path fns

void Lexicon_setup_path(Lexicon *lexicon, Z3_context ctx) {

  {
    lexicon->path.enum_names[0] = Z3_mk_string_symbol(ctx, "o");
    lexicon->path.enum_names[1] = Z3_mk_string_symbol(ctx, "a");
    lexicon->path.enum_names[2] = Z3_mk_string_symbol(ctx, "b");
    lexicon->path.enum_names[3] = Z3_mk_string_symbol(ctx, "x");
  }

  lexicon->path.sort = Z3_mk_enumeration_sort(ctx, Z3_mk_string_symbol(ctx, "path4_e"), PATH_VARIANTS, lexicon->path.enum_names, lexicon->path.enum_consts, lexicon->path.enum_testers);

  lexicon->path.token.o = Z3_mk_app(ctx, lexicon->path.enum_consts[0], 0, 0);
  lexicon->path.token.a = Z3_mk_app(ctx, lexicon->path.enum_consts[1], 0, 0);
  lexicon->path.token.b = Z3_mk_app(ctx, lexicon->path.enum_consts[2], 0, 0);
  lexicon->path.token.x = Z3_mk_app(ctx, lexicon->path.enum_consts[3], 0, 0);

  Z3_sort row_col[2] = {lexicon->u6.sort, lexicon->u6.sort};

  lexicon->path.tile_h_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "path4_type_h"), 2, row_col, lexicon->path.sort);

  lexicon->path.tile_v_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "path4_type_v"), 2, row_col, lexicon->path.sort);

  lexicon->path.penatly = Z3_mk_string_symbol(ctx, "path_penatly");
}

/// Shortest paths are found by placing a penatly on the assignment of a non empty path value to each potentiial path tile.
/// So long as a path is required and optimisation is enforced, no shorter path can exist on SAT.
void Lexicon_assert_shortest_path_empty_hints(const Lexicon *lexicon, Z3_context ctx, Z3_optimize otz, const Maze *maze) {

  for (uint8_t row = 0; row < maze->size.x; ++row) {
    for (uint8_t col = 0; col < maze->size.y; ++col) {
      Z3_ast tile_x[2] = {
          Z3_mk_int(ctx, row, lexicon->u6.sort),
          Z3_mk_int(ctx, col, lexicon->u6.sort),
      };

      Z3_ast tile_x_h = Z3_mk_app(ctx, lexicon->path.tile_h_f, 2, tile_x);
      Z3_ast tile_x_v = Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, tile_x);

      Z3_ast tile_x_h_is_X = Z3_mk_eq(ctx, tile_x_h, lexicon->path.token.x);
      Z3_ast tile_x_v_is_X = Z3_mk_eq(ctx, tile_x_v, lexicon->path.token.x);

      if (Maze_is_path(maze, row, col)) {
        Z3_ast empty_conjunction[2] = {
            tile_x_h_is_X,
            tile_x_v_is_X,
        };
        Z3_optimize_assert_soft(ctx, otz, Z3_mk_and(ctx, 2, empty_conjunction), "1", lexicon->path.penatly);
      } else {
        Z3_optimize_assert(ctx, otz, tile_x_h_is_X);
        Z3_optimize_assert(ctx, otz, tile_x_v_is_X);
      }
    }
  }
}

void Lexicon_assert_path_non_empty_hints(const Lexicon *lexicon, Z3_context ctx, Z3_optimize otz, const Maze *maze) {

  for (uint8_t row = 0; row < maze->size.x; ++row) {
    for (uint8_t col = 0; col < maze->size.y; ++col) {

      Z3_ast tile_x[2] = {
          Z3_mk_int(ctx, row, lexicon->u6.sort),
          Z3_mk_int(ctx, col, lexicon->u6.sort),
      };

      if (Maze_is_path(maze, row, col)) {
        Z3_ast tile_x_h = Z3_mk_app(ctx, lexicon->path.tile_h_f, 2, tile_x);
        Z3_ast tile_x_v = Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, tile_x);

        { // O H
          Z3_ast tile_e[2] = {
              Z3_mk_int(ctx, row, lexicon->u6.sort),
              Z3_mk_int(ctx, col + 1, lexicon->u6.sort),
          };
          Z3_ast tile_w[2] = {
              Z3_mk_int(ctx, row, lexicon->u6.sort),
              Z3_mk_int(ctx, col - 1, lexicon->u6.sort),
          };

          uint32_t option_count = 0;
          Z3_ast options[2] = {};

          if (0 < col) {
            options[option_count++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lexicon->path.tile_h_f, 2, tile_w), lexicon->path.token.a);
          }
          if (col + 1 < maze->size.y) {
            options[option_count++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lexicon->path.tile_h_f, 2, tile_e), lexicon->path.token.b);
          }

          Z3_ast origin_h_or = Z3_mk_or(ctx, option_count, options);
          Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_v, lexicon->path.token.o), origin_h_or));
        }

        { // O V
          Z3_ast tile_n[2] = {
              Z3_mk_int(ctx, row - 1, lexicon->u6.sort),
              Z3_mk_int(ctx, col, lexicon->u6.sort),
          };
          Z3_ast tile_s[2] = {
              Z3_mk_int(ctx, row + 1, lexicon->u6.sort),
              Z3_mk_int(ctx, col, lexicon->u6.sort),
          };

          uint32_t option_count = 0;
          Z3_ast options[2] = {};

          if (0 < row) {
            options[option_count++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, tile_n), lexicon->path.token.b);
          }
          if (row + 1 < maze->size.x) {
            options[option_count++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, tile_s), lexicon->path.token.a);
          }

          Z3_ast origin_v_or = Z3_mk_or(ctx, option_count, options);
          Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_h, lexicon->path.token.o), origin_v_or));
        }

        if (0 < row) { // N
          Z3_ast tile_n[2] = {
              Z3_mk_int(ctx, row - 1, lexicon->u6.sort),
              Z3_mk_int(ctx, col, lexicon->u6.sort),
          };

          uint32_t option_count = 0;
          Z3_ast options[3] = {};

          Z3_ast tile_n_h = Z3_mk_app(ctx, lexicon->path.tile_h_f, 2, tile_n);

          options[option_count++] = Z3_mk_eq(ctx, tile_n_h, lexicon->path.token.o);
          if (col + 1 < maze->size.y && Maze_is_path(maze, row - 1, col + 1)) {
            options[option_count++] = Z3_mk_eq(ctx, tile_n_h, lexicon->path.token.a);
          }
          if (0 < col && Maze_is_path(maze, row - 1, col - 1)) {
            options[option_count++] = Z3_mk_eq(ctx, tile_n_h, lexicon->path.token.b);
          }

          if (0 < option_count) { // E
            Z3_ast options_conjunction[2] = {
                Z3_mk_eq(ctx, Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, tile_n), lexicon->path.token.b),
                Z3_mk_or(ctx, option_count, options),
            };
            Z3_ast consequent = Z3_mk_and(ctx, 2, options_conjunction);
            if (1 < row && Maze_is_path(maze, row - 2, col)) {
              consequent = Z3_mk_or(ctx, 2, (Z3_ast[2]){
                                                consequent,
                                                direct_v(lexicon, ctx, tile_n),
                                            });
            }

            Z3_ast case_a = Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_v, lexicon->path.token.a), consequent);
            Z3_optimize_assert(ctx, otz, case_a);

            Z3_ast case_b = Z3_mk_implies(ctx, direct_v(lexicon, ctx, tile_x), consequent);
            Z3_optimize_assert(ctx, otz, case_b);
          }
        }

        if (col + 1 < maze->size.y) { // E
          Z3_ast tile_e[2] = {
              Z3_mk_int(ctx, row, lexicon->u6.sort),
              Z3_mk_int(ctx, col + 1, lexicon->u6.sort),
          };

          uint32_t option_count = 0;
          Z3_ast options[3] = {};

          Z3_ast tile_e_v = Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, tile_e);

          options[option_count++] = Z3_mk_eq(ctx, tile_e_v, lexicon->path.token.o);
          if (0 < row && Maze_is_path(maze, row - 1, col + 1)) {
            options[option_count++] = Z3_mk_eq(ctx, tile_e_v, lexicon->path.token.a);
          }
          if (row + 1 < maze->size.x && Maze_is_path(maze, row + 1, col + 1)) {
            options[option_count++] = Z3_mk_eq(ctx, tile_e_v, lexicon->path.token.b);
          }

          if (0 < option_count) {
            Z3_ast options_conjunction[2] = {
                Z3_mk_eq(ctx, Z3_mk_app(ctx, lexicon->path.tile_h_f, 2, tile_e), lexicon->path.token.b),
                Z3_mk_or(ctx, option_count, options),
            };
            Z3_ast consequent = Z3_mk_and(ctx, 2, options_conjunction);
            if (col + 2 < maze->size.y && Maze_is_path(maze, row, col + 2)) {
              consequent = Z3_mk_or(ctx, 2, (Z3_ast[2]){
                                                consequent,
                                                direct_h(lexicon, ctx, tile_e),
                                            });
            }

            Z3_ast case_a = Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_h, lexicon->path.token.a), consequent);
            Z3_optimize_assert(ctx, otz, case_a);

            Z3_ast case_b = Z3_mk_implies(ctx, direct_h(lexicon, ctx, tile_x), consequent);
            Z3_optimize_assert(ctx, otz, case_b);
          }
        }

        if (row + 1 < maze->size.x) { // S
          Z3_ast tile_s[2] = {
              Z3_mk_int(ctx, row + 1, lexicon->u6.sort),
              Z3_mk_int(ctx, col, lexicon->u6.sort),
          };

          uint32_t option_count = 0;
          Z3_ast options[3] = {};

          Z3_ast tile_s_h = Z3_mk_app(ctx, lexicon->path.tile_h_f, 2, tile_s);

          options[option_count++] = Z3_mk_eq(ctx, tile_s_h, lexicon->path.token.o);
          if (col + 1 < maze->size.y && Maze_is_path(maze, row + 1, col + 1)) {
            options[option_count++] = Z3_mk_eq(ctx, tile_s_h, lexicon->path.token.a);
          }
          if (0 < col && Maze_is_path(maze, row + 1, col - 1)) {
            options[option_count++] = Z3_mk_eq(ctx, tile_s_h, lexicon->path.token.b);
          }

          if (0 < option_count) {

            Z3_ast options_conjunction[2] = {
                Z3_mk_eq(ctx, Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, tile_s), lexicon->path.token.a),
                Z3_mk_or(ctx, option_count, options),
            };
            Z3_ast consequent = Z3_mk_and(ctx, 2, options_conjunction);
            if (row + 2 < maze->size.x && Maze_is_path(maze, row + 2, col)) {
              consequent = Z3_mk_or(ctx, 2, (Z3_ast[2]){
                                                consequent,
                                                direct_v(lexicon, ctx, tile_s),
                                            });
            }

            Z3_ast case_a = Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_v, lexicon->path.token.b), consequent);
            Z3_optimize_assert(ctx, otz, case_a);

            Z3_ast case_b = Z3_mk_implies(ctx, direct_v(lexicon, ctx, tile_x), consequent);
            Z3_optimize_assert(ctx, otz, case_b);
          }
        }

        if (0 < col) { // W
          Z3_ast tile_w[2] = {
              Z3_mk_int(ctx, row, lexicon->u6.sort),
              Z3_mk_int(ctx, col - 1, lexicon->u6.sort),
          };

          uint32_t option_count = 0;
          Z3_ast options[3] = {};

          options[option_count++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, tile_w), lexicon->path.token.o);
          if (0 < row && Maze_is_path(maze, row - 1, col - 1)) {
            options[option_count++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, tile_w), lexicon->path.token.a);
          }
          if (row + 1 < maze->size.x && Maze_is_path(maze, row + 1, col - 1)) {
            options[option_count++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, tile_w), lexicon->path.token.b);
          }

          if (0 < option_count) {
            Z3_ast options_conjunction[2] = {
                Z3_mk_eq(ctx, Z3_mk_app(ctx, lexicon->path.tile_h_f, 2, tile_w), lexicon->path.token.a),
                Z3_mk_or(ctx, option_count, options),
            };
            Z3_ast consequent = Z3_mk_and(ctx, 2, options_conjunction);

            if (1 < col && Maze_is_path(maze, row, col - 2)) {
              consequent = Z3_mk_or(ctx, 2, (Z3_ast[2]){
                                                consequent,
                                                direct_h(lexicon, ctx, tile_w),
                                            });
            }

            Z3_ast case_a = Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_h, lexicon->path.token.b), consequent);
            Z3_optimize_assert(ctx, otz, case_a);

            Z3_ast case_b = Z3_mk_implies(ctx, direct_h(lexicon, ctx, tile_x), consequent);
            Z3_optimize_assert(ctx, otz, case_b);
          }
        }
      }
    }
  }
}

/// Anima fns

void Lexicon_setup_animas(Lexicon *lexicon, Z3_context ctx, size_t anima_count) {

  if (1 <= anima_count) {
    lexicon->anima.enum_names[0] = Z3_mk_string_symbol(ctx, "anima_0");
  }
  if (2 <= anima_count) {
    lexicon->anima.enum_names[1] = Z3_mk_string_symbol(ctx, "bertrand");
  }
  if (3 <= anima_count) {
    lexicon->anima.enum_names[2] = Z3_mk_string_symbol(ctx, "herbrand");
  }
  if (4 <= anima_count) {
    lexicon->anima.enum_names[3] = Z3_mk_string_symbol(ctx, "lob");
  }

  assert(anima_count < UINT_MAX);
  lexicon->anima.sort = Z3_mk_enumeration_sort(ctx,
                                               Z3_mk_string_symbol(ctx, "anima_t"),
                                               (unsigned int)anima_count,
                                               lexicon->anima.enum_names,
                                               lexicon->anima.enum_consts,
                                               lexicon->anima.enum_testers);

  { // Anima row fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "anima_r");
    Z3_sort domain[1] = {lexicon->anima.sort};
    Z3_sort range = lexicon->u6.sort;
    lexicon->anima.tile_row_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }

  { // Anima col fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "anima_c");
    Z3_sort domain[1] = {lexicon->anima.sort};
    Z3_sort range = lexicon->u6.sort;
    lexicon->anima.tile_col_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }
}

void Lexicon_assert_anima_location(const Lexicon *lexicon, Z3_context ctx, Z3_optimize otz, const Situation *situation, const uint8_t id) {

  Pair_uint8 anima_location = atomic_load(&situation->animas[id].location);
  slog_display(SLOG_DEBUG, 0, "Asserted anima %d at %dx%d\n", id, anima_location.x, anima_location.y);
  Z3_ast anima_ast = Z3_mk_app(ctx, lexicon->anima.enum_consts[id], 0, 0);

  { // row block
    Z3_ast z3_row = z3_mk_unary_app(ctx, lexicon->anima.tile_row_f, anima_ast);
    Z3_ast row = Z3_mk_int(ctx, anima_location.x, lexicon->u6.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_row, row));
  }

  { // col block
    Z3_ast z3_col = z3_mk_unary_app(ctx, lexicon->anima.tile_col_f, anima_ast);
    Z3_ast col = Z3_mk_int(ctx, anima_location.y, lexicon->u6.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_col, col));
  }
}

void Lexicon_anima_tile_is_origin(const Lexicon *lexicon, Z3_context ctx, Z3_optimize otz, uint8_t id) {

  Z3_ast anima_ast = Z3_mk_app(ctx, lexicon->anima.enum_consts[id], 0, 0);

  Z3_ast anima_row_col[2] = {z3_mk_unary_app(ctx, lexicon->anima.tile_row_f, anima_ast),
                             z3_mk_unary_app(ctx, lexicon->anima.tile_col_f, anima_ast)};

  Z3_ast anima_h = Z3_mk_app(ctx, lexicon->path.tile_h_f, 2, anima_row_col);
  Z3_ast anima_v = Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, anima_row_col);

  Z3_ast ho = Z3_mk_eq(ctx, anima_h, lexicon->path.token.o);
  Z3_ast vo = Z3_mk_eq(ctx, anima_v, lexicon->path.token.o);

  Z3_ast disjunct[2] = {
      Z3_mk_and(ctx, 2, (Z3_ast[2]){ho, Z3_mk_not(ctx, vo)}),
      Z3_mk_and(ctx, 2, (Z3_ast[2]){vo, Z3_mk_not(ctx, ho)}),
  };

  Z3_optimize_assert(ctx, otz, Z3_mk_or(ctx, 2, disjunct));
}

/// Persona fns

void Lexicon_setup_persona(Lexicon *lexicon, Z3_context ctx) {

  lexicon->persona.enum_name[0] = Z3_mk_string_symbol(ctx, "persona");

  lexicon->persona.sort = Z3_mk_enumeration_sort(ctx,
                                                 Z3_mk_string_symbol(ctx, "persona_t"),
                                                 1,
                                                 lexicon->persona.enum_name,
                                                 lexicon->persona.enum_const,
                                                 lexicon->persona.enum_tester);

  { // Persona row fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "persona_r");
    Z3_sort domain[1] = {lexicon->persona.sort};
    Z3_sort range = lexicon->u6.sort;
    lexicon->persona.tile_row_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }

  { // Persona col fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "persona_c");
    Z3_sort domain[1] = {lexicon->persona.sort};
    Z3_sort range = lexicon->u6.sort;
    lexicon->persona.tile_col_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }
}

void Lexicon_persona_tile_is_origin(const Lexicon *lexicon, Z3_context ctx, Z3_optimize otz) {

  Z3_ast persona_ast = Z3_mk_app(ctx, lexicon->persona.enum_const[0], 0, 0);

  Z3_ast persona_row_col[2] = {z3_mk_unary_app(ctx, lexicon->persona.tile_row_f, persona_ast),
                               z3_mk_unary_app(ctx, lexicon->persona.tile_col_f, persona_ast)};

  Z3_ast persona_h = Z3_mk_app(ctx, lexicon->path.tile_h_f, 2, persona_row_col);
  Z3_ast persona_v = Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, persona_row_col);

  Z3_ast ho = Z3_mk_eq(ctx, persona_h, lexicon->path.token.o);
  Z3_ast vo = Z3_mk_eq(ctx, persona_v, lexicon->path.token.o);

  Z3_ast disjunct[2];
  disjunct[0] = Z3_mk_and(ctx, 2, (Z3_ast[2]){ho, Z3_mk_not(ctx, vo)});
  disjunct[1] = Z3_mk_and(ctx, 2, (Z3_ast[2]){vo, Z3_mk_not(ctx, ho)});

  Z3_optimize_assert(ctx, otz, Z3_mk_or(ctx, 2, disjunct));
}

void Lexicon_assert_persona_location(const Lexicon *lexicon, Z3_context ctx, Z3_optimize otz, const Situation *situation) {

  Pair_uint8 persona_location = atomic_load(&situation->persona.location);

  Z3_ast persona_ast = Z3_mk_app(ctx, lexicon->persona.enum_const[0], 0, 0);

  { // row block
    Z3_ast z3_row = z3_mk_unary_app(ctx, lexicon->persona.tile_row_f, persona_ast);
    Z3_ast row = Z3_mk_int(ctx, persona_location.x, lexicon->u6.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_row, row));
  }

  { // col block
    Z3_ast z3_col = z3_mk_unary_app(ctx, lexicon->persona.tile_col_f, persona_ast);
    Z3_ast col = Z3_mk_int(ctx, persona_location.y, lexicon->u6.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_col, col));
  }
}

/// Link

// ...
void Lexicon_assert_constant_hints(const Lexicon *lexicon, Z3_context ctx, Z3_optimize otz, const Maze *maze) {

  for (uint8_t row = 0; row < maze->size.x; ++row) {
    for (uint8_t col = 0; col < maze->size.y; ++col) {

      Z3_ast tile_x[2] = {Z3_mk_int(ctx, row, lexicon->u6.sort),
                          Z3_mk_int(ctx, col, lexicon->u6.sort)};

      Z3_ast tile_x_h = Z3_mk_app(ctx, lexicon->path.tile_h_f, 2, tile_x);
      Z3_ast tile_x_v = Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, tile_x);

      Z3_ast disjuncts_h[3] = {
          Z3_mk_eq(ctx, tile_x_h, lexicon->path.token.a),
          Z3_mk_eq(ctx, tile_x_h, lexicon->path.token.b),
          Z3_mk_eq(ctx, tile_x_h, lexicon->path.token.x),
      };
      Z3_ast disjunction_h = Z3_mk_or(ctx, 3, disjuncts_h);
      Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, tile_x_h, lexicon->path.token.o)), disjunction_h));

      Z3_ast disjuncts_v[3] = {
          Z3_mk_eq(ctx, tile_x_v, lexicon->path.token.a),
          Z3_mk_eq(ctx, tile_x_v, lexicon->path.token.b),
          Z3_mk_eq(ctx, tile_x_v, lexicon->path.token.x),
      };
      Z3_ast disjunction_v = Z3_mk_or(ctx, 3, disjuncts_v);
      Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, tile_x_v, lexicon->path.token.o)), disjunction_v));
    }
  }
}

void Lexicon_assert_origin_is_anima_or_persona(const Lexicon *lexicon, Z3_context ctx, Z3_optimize otz, const Maze *maze) {

  Z3_ast persona_ast = Z3_mk_app(ctx, lexicon->persona.enum_const[0], 0, 0);

  for (uint8_t row = 0; row < maze->size.x; ++row) {
    for (uint8_t col = 0; col < maze->size.y; ++col) {

      Z3_ast tile_x[2] = {Z3_mk_int(ctx, row, lexicon->u6.sort),
                          Z3_mk_int(ctx, col, lexicon->u6.sort)};

      Z3_ast tile_x_h = Z3_mk_app(ctx, lexicon->path.tile_h_f, 2, tile_x);
      Z3_ast tile_x_v = Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, tile_x);

      Z3_ast persona_row = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, lexicon->persona.tile_row_f, persona_ast), tile_x[0]);
      Z3_ast persona_col = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, lexicon->persona.tile_col_f, persona_ast), tile_x[1]);

      unsigned int options_idx = 0;
      Z3_ast options[LEXICON_ANIMAS + 1];
      options[options_idx++] = Z3_mk_and(ctx, 2, (Z3_ast[2]){persona_row, persona_col});

      for (size_t anima_id = 0; anima_id < LEXICON_ANIMAS; ++anima_id) {

        Z3_ast anima_ast = Z3_mk_app(ctx, lexicon->anima.enum_consts[anima_id], 0, 0);
        Z3_ast anima_row = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, lexicon->anima.tile_row_f, anima_ast), tile_x[0]);
        Z3_ast anima_col = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, lexicon->anima.tile_col_f, anima_ast), tile_x[1]);

        options[options_idx++] = Z3_mk_and(ctx, 2, (Z3_ast[2]){anima_row, anima_col});
      }

      Z3_ast options_disjunction = Z3_mk_or(ctx, options_idx, options);

      Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_h, lexicon->path.token.o), options_disjunction));
      Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_x_v, lexicon->path.token.o), options_disjunction));
    }
  }
}


#include "maze.h"
#include "misc.h"
#include "smt_z3.h"

#include "clog.h"
#include "utils/pairs.h"
#include "z3_api.h"

#include <assert.h>
#include <stddef.h>
#include <stdio.h>

void prove(Z3_context ctx, Z3_solver solver, Z3_ast statement) {
  Z3_model model = 0;

  Z3_solver_push(ctx, solver);

  Z3_solver_assert(ctx, solver, Z3_mk_not(ctx, statement));

  switch (Z3_solver_check(ctx, solver)) {
  case Z3_L_FALSE: {
    printf("VALID\n");
  } break;
  case Z3_L_UNDEF: {
    printf("UNKNOWN\n");
    model = Z3_solver_get_model(ctx, solver);
    if (model != 0) {
      Z3_model_inc_ref(ctx, model);
      INFO("\nPotential counterexample:\n%s\n", Z3_model_to_string(ctx, model));
    }
  } break;
  case Z3_L_TRUE: {
    printf("INVALID\n");
    model = Z3_solver_get_model(ctx, solver);
    if (model) {
      Z3_model_inc_ref(ctx, model);
      INFO("\nCounterexample:\n%s\n", Z3_model_to_string(ctx, model));
    }
  } break;
  }
  if (model) {
    Z3_model_dec_ref(ctx, model);
  }

  Z3_solver_pop(ctx, solver, 1);
}

Z3_context z3_mk_anima_ctx() {
  Z3_config cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "model", "true");

  Z3_context ctx = Z3_mk_context(cfg);
  Z3_set_error_handler(ctx, error_handler);

  Z3_del_config(cfg);
  return ctx;
}

void z3_tmp(Maze *maze) {
  Z3_context ctx = z3_mk_anima_ctx();

  Z3_solver solver = Z3_mk_solver(ctx);
  Z3_solver_inc_ref(ctx, solver);

  Z3_sort u8_s = Z3_mk_bv_sort(ctx, 8);

  Z3_func_decl mk_tuple_decl;
  Z3_func_decl u8_proj[2];
  Z3_sort u8p_s = Z3_mk_tuple_sort(ctx,
                                   Z3_mk_string_symbol(ctx, "mk_u8p"),
                                   2,
                                   (Z3_symbol[2]){Z3_mk_string_symbol(ctx, "prj_u8p_x"),
                                                  Z3_mk_string_symbol(ctx, "prj_u8p_y")},
                                   (Z3_sort[2]){u8_s, u8_s},
                                   &mk_tuple_decl,
                                   u8_proj);

  Z3_func_decl prj_u8p_x = u8_proj[0]; // get_x_decl(mk_pair(x,y)) = x
  Z3_func_decl prj_u8p_y = u8_proj[1]; // get_y_decl(mk_pair(x,y)) = y

  Z3_ast u8p_xy = z3_mk_binary_app(ctx,
                                   mk_tuple_decl,
                                   z3_mk_var(ctx, "x", u8_s),
                                   z3_mk_var(ctx, "y", u8_s));

  Z3_ast u8_0 = Z3_mk_numeral(ctx, "0", u8_s);
  Z3_ast u8_1 = Z3_mk_numeral(ctx, "1", u8_s);
  Z3_ast u8_2 = Z3_mk_numeral(ctx, "2", u8_s);
  Z3_ast u8_3 = Z3_mk_numeral(ctx, "3", u8_s);

  Z3_ast get_x = z3_mk_unary_app(ctx, prj_u8p_x, u8p_xy);
  Z3_ast get_y = z3_mk_unary_app(ctx, prj_u8p_y, u8p_xy);

  prove(ctx, solver, Z3_mk_eq(ctx, Z3_mk_bvor(ctx, get_x, get_y), u8_3));

  Z3_ast u8p_1_2 = z3_mk_binary_app(ctx, mk_tuple_decl, u8_1, u8_2);
  prove(ctx,
        solver,
        Z3_mk_eq(ctx,
                 Z3_mk_bvand(ctx,
                             z3_mk_unary_app(ctx, prj_u8p_x, u8p_1_2),
                             z3_mk_unary_app(ctx, prj_u8p_y, u8p_1_2)),
                 u8_3));

  Z3_ast u8p_1_3 = z3_mk_binary_app(ctx, mk_tuple_decl, u8_1, u8_3);
  prove(ctx,
        solver,
        Z3_mk_eq(ctx,
                 Z3_mk_bvand(ctx,
                             z3_mk_unary_app(ctx, prj_u8p_x, u8p_1_3),
                             z3_mk_unary_app(ctx, prj_u8p_y, u8p_1_3)),
                 u8_1));

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

  Z3_ast empty = Z3_mk_app(ctx, path_e_consts[10], 0, 0);

  prove(ctx, solver, Z3_mk_app(ctx, path_e_testers[0], 1, &origin_up));

  prove(ctx, solver, z3_mk_unary_app(ctx, path_e_testers[0], origin_left));
  prove(ctx, solver, Z3_mk_not(ctx, z3_mk_unary_app(ctx, path_e_testers[3], origin_left)));

  //

  Z3_func_decl tile_path_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "path_choice"), 1, (Z3_sort[1]){u8p_s}, tile_path_s);

  //
  printf("Creating tiles...\n");

  char r_buff[10] = {};
  char c_buff[10] = {};

  Z3_ast maze_pairs[PairI32_area(&maze->size)];

  printf("Creating tiles %d %d...\n", maze->size.x, maze->size.y);

  for (int32_t r = 0; r < maze->size.y; ++r) {
    sprintf(r_buff, "%d", r);
    for (int32_t c = 0; c < maze->size.x; ++c) {
      sprintf(c_buff, "%d", c);

      maze_pairs[r * maze->size.x + c] = z3_mk_binary_app(ctx,
                                                          mk_tuple_decl,
                                                          Z3_mk_numeral(ctx, c_buff, u8_s),
                                                          Z3_mk_numeral(ctx, r_buff, u8_s));

      if (Maze_abstract_at_xy(maze, c, r) != ' ') {
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, maze_pairs[r * maze->size.x + c]), empty));
      }

      printf("%c", Maze_abstract_at_xy(maze, c, r));
    }
    printf("\n");
  }

  Z3_mk_distinct(ctx, PairI32_area(&maze->size), maze_pairs);

  // Animas
  constexpr size_t ANIMA_VARIANTS = 3;

  Z3_symbol anima_e_names[ANIMA_VARIANTS] = {
      Z3_mk_string_symbol(ctx, "gottlob"),
      Z3_mk_string_symbol(ctx, "bertrand"),
      Z3_mk_string_symbol(ctx, "smt-man")};

  Z3_func_decl anima_e_consts[ANIMA_VARIANTS];
  Z3_func_decl anima_e_testers[ANIMA_VARIANTS];

  Z3_sort anima_s = Z3_mk_enumeration_sort(ctx,
                                           Z3_mk_string_symbol(ctx, "anima"),
                                           ANIMA_VARIANTS,
                                           anima_e_names,
                                           anima_e_consts,
                                           anima_e_testers);

  Z3_ast anima_gottlob = Z3_mk_app(ctx, anima_e_consts[0], 0, 0);
  Z3_ast anima_bertrand = Z3_mk_app(ctx, anima_e_consts[1], 0, 0);
  Z3_ast anima_smtman = Z3_mk_app(ctx, anima_e_consts[2], 0, 0);

  // Anima locations

  Z3_func_decl anima_tile_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "anima_loc"), 1, (Z3_sort[1]){anima_s}, u8p_s);

  Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, anima_tile_f, anima_gottlob), maze_pairs[1 * maze->size.x + 2]));
  Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, anima_tile_f, anima_gottlob), maze_pairs[26 * maze->size.x + 15]));

  // Cleanup

  Z3_solver_dec_ref(ctx, solver);
  Z3_del_context(ctx);
}

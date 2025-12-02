
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

/* void prove(Z3_context ctx, Z3_solver solver, Z3_ast statement) { */
/*   Z3_model model = 0; */

/*   Z3_solver_push(ctx, solver); */

/*   Z3_solver_assert(ctx, solver, Z3_mk_not(ctx, statement)); */

/*   switch (Z3_solver_check(ctx, solver)) { */
/*   case Z3_L_FALSE: { */
/*     printf("VALID\n"); */
/*   } break; */
/*   case Z3_L_UNDEF: { */
/*     printf("UNKNOWN\n"); */
/*     model = Z3_solver_get_model(ctx, solver); */
/*     if (model != 0) { */
/*       Z3_model_inc_ref(ctx, model); */
/*       INFO("\nPotential counterexample:\n%s\n", Z3_model_to_string(ctx, model)); */
/*     } */
/*   } break; */
/*   case Z3_L_TRUE: { */
/*     printf("INVALID\n"); */
/*     model = Z3_solver_get_model(ctx, solver); */
/*     if (model) { */
/*       Z3_model_inc_ref(ctx, model); */
/*       INFO("\nCounterexample:\n%s\n", Z3_model_to_string(ctx, model)); */
/*     } */
/*   } break; */
/*   } */
/*   if (model) { */
/*     Z3_model_dec_ref(ctx, model); */
/*   } */

/*   Z3_solver_pop(ctx, solver, 1); */
/* } */

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

  Z3_func_decl mk_u8p_decl;
  Z3_func_decl u8_proj[2];
  Z3_sort u8p_s = Z3_mk_tuple_sort(ctx,
                                   Z3_mk_string_symbol(ctx, "mk_u8p"),
                                   2,
                                   (Z3_symbol[2]){Z3_mk_string_symbol(ctx, "prj_u8p_x"),
                                                  Z3_mk_string_symbol(ctx, "prj_u8p_y")},
                                   (Z3_sort[2]){u8_s, u8_s},
                                   &mk_u8p_decl,
                                   u8_proj);

  Z3_func_decl prj_u8p_x = u8_proj[0]; // get_x_decl(mk_pair(x,y)) = x
  Z3_func_decl prj_u8p_y = u8_proj[1]; // get_y_decl(mk_pair(x,y)) = y

  Z3_ast u8p_xy = z3_mk_binary_app(ctx,
                                   mk_u8p_decl,
                                   z3_mk_var(ctx, "x", u8_s),
                                   z3_mk_var(ctx, "y", u8_s));

  Z3_ast u8_0 = Z3_mk_numeral(ctx, "0", u8_s);
  Z3_ast u8_1 = Z3_mk_numeral(ctx, "1", u8_s);
  Z3_ast u8_2 = Z3_mk_numeral(ctx, "2", u8_s);
  Z3_ast u8_3 = Z3_mk_numeral(ctx, "3", u8_s);

  Z3_ast get_x = z3_mk_unary_app(ctx, prj_u8p_x, u8p_xy);
  Z3_ast get_y = z3_mk_unary_app(ctx, prj_u8p_y, u8p_xy);

  /*
  prove(ctx, solver, Z3_mk_eq(ctx, Z3_mk_bvor(ctx, get_x, get_y), u8_3));

  Z3_ast u8p_1_2 = z3_mk_binary_app(ctx, mk_u8p_decl, u8_1, u8_2);
  prove(ctx,
        solver,
        Z3_mk_eq(ctx,
                 Z3_mk_bvand(ctx,
                             z3_mk_unary_app(ctx, prj_u8p_x, u8p_1_2),
                             z3_mk_unary_app(ctx, prj_u8p_y, u8p_1_2)),
                 u8_3));

  Z3_ast u8p_1_3 = z3_mk_binary_app(ctx, mk_u8p_decl, u8_1, u8_3);
  prove(ctx,
        solver,
        Z3_mk_eq(ctx,
                 Z3_mk_bvand(ctx,
                             z3_mk_unary_app(ctx, prj_u8p_x, u8p_1_3),
                             z3_mk_unary_app(ctx, prj_u8p_y, u8p_1_3)),
                             u8_1));
   */

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

  Z3_func_decl tile_path_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "path_choice"), 1, (Z3_sort[1]){u8p_s}, tile_path_s);

  //

  Z3_ast maze_pairs[PairI32_area(&maze->size)] = {};

  {
    char r_buff[20] = {};
    char c_buff[20] = {};

    for (int32_t r = 0; r < maze->size.y; ++r) {
      sprintf(r_buff, "%d", r);
      for (int32_t c = 0; c < maze->size.x; ++c) {
        sprintf(c_buff, "%d", c);

        maze_pairs[r * maze->size.x + c] = z3_mk_binary_app(ctx,
                                                            mk_u8p_decl,
                                                            Z3_mk_numeral(ctx, c_buff, u8_s),
                                                            Z3_mk_numeral(ctx, r_buff, u8_s));

        if (Maze_abstract_is_path(maze, c, r)) {
          Z3_optimize_assert_soft(ctx, optimizer, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, maze_pairs[r * maze->size.x + c]), no_path), "1", NULL);
        } else {
          Z3_optimize_assert(ctx, optimizer, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, maze_pairs[r * maze->size.x + c]), no_path));
        }
      }
    }
  }

  Z3_mk_distinct(ctx, PairI32_area(&maze->size), maze_pairs);

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

  Z3_func_decl anima_tile_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "anima_loc"), 1, (Z3_sort[1]){anima_s}, u8p_s);

  PairI32 gottlob_location = atomic_load(&world.anima[0].abstract_location);
  Z3_optimize_assert(ctx, optimizer, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, anima_tile_f, anima_gottlob), maze_pairs[gottlob_location.y * maze->size.x + gottlob_location.x]));
  PairI32 bertrand_location = atomic_load(&world.anima[1].abstract_location);
  Z3_optimize_assert(ctx, optimizer, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, anima_tile_f, anima_bertrand), maze_pairs[bertrand_location.y * maze->size.x + bertrand_location.x]));

  for (int32_t r = 0; r < maze->size.y; r++) {
    for (int32_t c = 0; c < maze->size.x; c++) {

      Z3_ast tile_path_value = z3_mk_unary_app(ctx, tile_path_f, maze_pairs[r * maze->size.x + c]);

      if (Maze_abstract_is_path(maze, c, r)) {

        Z3_ast up_tile = NULL;
        if (0 < r) {
          up_tile = maze_pairs[(r - 1) * maze->size.x + c];
        }

        Z3_ast rt_tile = NULL;
        if (c + 1 < maze->size.x) {
          rt_tile = maze_pairs[r * maze->size.x + (c + 1)];
        }

        Z3_ast dn_tile = NULL;
        if (r + 1 < maze->size.y) {
          dn_tile = maze_pairs[(r + 1) * maze->size.x + c];
        }

        Z3_ast lt_tile = NULL;
        if (0 < c) {
          lt_tile = maze_pairs[r * maze->size.x + (c - 1)];
        }

        size_t up_tile_reqs = 0;
        Z3_ast up_tile_req[4] = {};
        if (up_tile != NULL) {
          up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, up_tile), origin_down);
          up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, up_tile), up_down);
          up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, up_tile), down_right);
          up_tile_req[up_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, up_tile), down_left);
        }

        size_t rt_tile_reqs = 0;
        Z3_ast rt_tile_req[4] = {};
        if (rt_tile != NULL) {
          rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, rt_tile), origin_left);
          rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, rt_tile), right_left);
          rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, rt_tile), down_left);
          rt_tile_req[rt_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, rt_tile), up_left);
        }

        size_t dn_tile_reqs = 0;
        Z3_ast dn_tile_req[4] = {};
        if (dn_tile != NULL) {
          dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, dn_tile), origin_up);
          dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, dn_tile), up_down);
          dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, dn_tile), up_right);
          dn_tile_req[dn_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, dn_tile), up_left);
        }

        size_t lt_tile_reqs = 0;
        Z3_ast lt_tile_req[4] = {};
        if (lt_tile != NULL) {
          lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, lt_tile), origin_right);
          lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, lt_tile), right_left);
          lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, lt_tile), down_right);
          lt_tile_req[lt_tile_reqs++] = Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, lt_tile), up_right);
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
    for (int32_t c = 0; c < maze->size.x; c++) {

      Z3_ast tile_path_value = z3_mk_unary_app(ctx, tile_path_f, maze_pairs[r * maze->size.x + c]);

      Z3_ast some_anima_location = Z3_mk_or(ctx,
                                            2,
                                            (Z3_ast[2]){
                                                Z3_mk_eq(ctx, z3_mk_unary_app(ctx, anima_tile_f, anima_gottlob), maze_pairs[r * maze->size.x + c]),
                                                Z3_mk_eq(ctx, z3_mk_unary_app(ctx, anima_tile_f, anima_bertrand), maze_pairs[r * maze->size.x + c])});

      Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, maze_pairs[r * maze->size.x + c]), origin_up), some_anima_location));
      Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, maze_pairs[r * maze->size.x + c]), origin_right), some_anima_location));
      Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, maze_pairs[r * maze->size.x + c]), origin_down), some_anima_location));
      Z3_optimize_assert(ctx, optimizer, Z3_mk_implies(ctx, Z3_mk_eq(ctx, z3_mk_unary_app(ctx, tile_path_f, maze_pairs[r * maze->size.x + c]), origin_left), some_anima_location));
    }
  }

  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    auto anima_location = atomic_load(&world.anima[idx].abstract_location);
    Z3_ast tile_path_value = z3_mk_unary_app(ctx, tile_path_f, maze_pairs[anima_location.y * maze->size.x + anima_location.x]);

    Z3_optimize_assert(ctx,
                       optimizer,
                       Z3_mk_or(ctx,
                                4,
                                (Z3_ast[4]){Z3_mk_eq(ctx, tile_path_value, origin_up),
                                            Z3_mk_eq(ctx, tile_path_value, origin_right),
                                            Z3_mk_eq(ctx, tile_path_value, origin_down),
                                            Z3_mk_eq(ctx, tile_path_value, origin_left)}));
  }

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
  for (int32_t r = 0; r < maze->size.y; ++r) {
    for (int32_t c = 0; c < maze->size.x; ++c) {

      Z3_model_eval(ctx, model, z3_mk_unary_app(ctx, tile_path_f, maze_pairs[r * maze->size.x + c]), false, &tile_path);
      /* if (tile_path == no_path) { */
      /*   printf(" "); */
      /* } else { */
      /*   printf("x"); */
      /* } */
    }
    /* printf("\n"); */
  }

  // Cleanup

  Z3_model_dec_ref(ctx, model);
  Z3_optimize_dec_ref(ctx, optimizer);
  Z3_del_context(ctx);
}

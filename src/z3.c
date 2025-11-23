#include "misc.h"
#include "z3_api.h"
#include "z3_optimization.h"
#include <stdio.h>

Z3_ast mk_binary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y) {
  return Z3_mk_app(ctx, f, 2, (Z3_ast[2]){x, y});
}

void z3_tmp(Maze *maze) {

  int32_t width_less_one = maze->size.x - 1;
  int32_t height_less_one = maze->size.y - 1;

  Z3_config cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "model", "true");

  Z3_context ctx = Z3_mk_context(cfg);

  Z3_solver solver = Z3_mk_solver(ctx);

  auto u8_sort = Z3_mk_bv_sort(ctx, 8);
  auto u8_zero = Z3_mk_numeral(ctx, "0", u8_sort);
  auto u8_one = Z3_mk_numeral(ctx, "1", u8_sort);

  /* Z3_symbol fst_snd[2] = {Z3_mk_string_symbol(ctx, "fst"), Z3_mk_string_symbol(ctx, "snd")}; */
  /* Z3_constructor u8p_mk = Z3_mk_constructor(ctx, */
  /*                                           Z3_mk_string_symbol(ctx, "pair"), */
  /*                                           Z3_mk_string_symbol(ctx, "is_pair"), */
  /*                                           2, */
  /*                                           fst_snd, */
  /*                                           (Z3_sort[2]){u8_sort, u8_sort}, */
  /*                                           (unsigned[2]){0, 0}); */

  /* auto u8p_dt = Z3_mk_datatype(ctx, Z3_mk_string_symbol(ctx, "u8p_dt"), 1, &u8p_mk); */

  /* Z3_func_decl u8p_decl; */
  /* Z3_func_decl is_u8p_decl; */
  /* Z3_func_decl u8p_accessors[1]; */
  /* Z3_query_constructor(ctx, u8p_mk, 2, &u8p_decl, &is_u8p_decl, u8p_accessors); */

  /* Z3_symbol s = Z3_mk_string_symbol(ctx, "zo"); */
  /* Z3_ast zo = Z3_mk_const(ctx, s, u8p_dt); */

  /* Z3_ast p1 = mk_binary_app(ctx, u8p_decl, Z3_mk_numeral(ctx, "0", u8_sort), Z3_mk_numeral(ctx, "0", u8_sort)); */
  /* Z3_ast p2 = mk_binary_app(ctx, u8p_decl, Z3_mk_numeral(ctx, "0", u8_sort), Z3_mk_numeral(ctx, "0", u8_sort)); */

  Z3_ast eqp = Z3_mk_eq(ctx, u8_zero, u8_zero);

  Z3_solver_push(ctx, solver);
  Z3_solver_assert(ctx, solver, eqp);
  auto result = Z3_solver_check(ctx, solver);

  switch (result) {
  case Z3_L_FALSE: {
    printf("UNSAT");
  } break;
  case Z3_L_UNDEF: {
    printf("UNDEF");
  } break;
  case Z3_L_TRUE: {
    printf("SAT");
  } break;
  }
  printf("\n");

  Z3_solver_pop(ctx, solver, 1);
}

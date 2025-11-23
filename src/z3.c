#include "misc.h"
#include "z3_api.h"
#include "z3_optimization.h"
#include <stdio.h>

Z3_ast mk_binary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y) {
  return Z3_mk_app(ctx, f, 2, (Z3_ast[2]){x, y});
}

void error_handler(Z3_context c, Z3_error_code e) {
  printf("Error code: %d\n", e);
  exit(-3);
}

void z3_tmp(Maze *maze) {

  int32_t width_less_one = maze->size.x - 1;
  int32_t height_less_one = maze->size.y - 1;

  Z3_config cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "model", "true");

  Z3_context ctx = Z3_mk_context(cfg);

  Z3_del_config(cfg);

  Z3_set_error_handler(ctx, error_handler);

  Z3_solver solver = Z3_mk_solver(ctx);

  Z3_sort u8_sort = Z3_mk_bv_sort(ctx, 8);
  Z3_ast u8_zero = Z3_mk_numeral(ctx, "0", u8_sort);
  Z3_ast u8_one = Z3_mk_numeral(ctx, "1", u8_sort);

  unsigned int u8_sort_id = Z3_get_sort_id(ctx, u8_sort);
  printf("u8_sort_id: %u\n", u8_sort_id);
  printf("...\n");
  printf("u8_sort is of bv size: %u\n", Z3_get_bv_sort_size(ctx, u8_sort));

  Z3_symbol u8p_accessor_names[2] = {Z3_mk_string_symbol(ctx, "fst"), Z3_mk_string_symbol(ctx, "snd")};
  Z3_sort u8p_accessor_sorts[2] = {u8_sort, u8_sort};
  unsigned u8p_accessor_sort_refs[2] = {0, 0};

  Z3_constructor u8p_con;
  printf("c: %p", u8p_con);

  u8p_con = Z3_mk_constructor(ctx,
                              Z3_mk_string_symbol(ctx, "pair"),
                              Z3_mk_string_symbol(ctx, "is_pair"),
                              2,
                              u8p_accessor_names,
                              u8p_accessor_sorts,
                              u8p_accessor_sort_refs);

  printf("c: %u", Z3_constructor_num_fields(ctx, u8p_con));

  Z3_constructor constructors[1];
  constructors[0] = u8p_con;

  Z3_sort u8p_dt = Z3_mk_datatype(ctx, Z3_mk_string_symbol(ctx, "u8p_datatype"), 1, constructors);

  Z3_func_decl u8p_decl;
  Z3_func_decl is_u8p_decl;
  Z3_func_decl u8p_accessors[2];
  Z3_query_constructor(ctx, u8p_con, 2, &u8p_decl, &is_u8p_decl, u8p_accessors);
  Z3_del_constructor(ctx, u8p_con);

  /* Z3_symbol s = Z3_mk_string_symbol(ctx, "zo"); */
  /* Z3_ast zo = Z3_mk_const(ctx, s, u8p_dt); */

  /* Z3_ast p1 = mk_binary_app(ctx, u8p_decl, u8_zero, u8_zero); */
  /* Z3_ast p2 = mk_binary_app(ctx, u8p_decl, u8_zero, u8_zero); */

  Z3_ast eqp = Z3_mk_eq(ctx, u8_zero, u8_zero);

  /* Z3_solver_push(ctx, solver); */
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

  /* Z3_solver_pop(ctx, solver, 1); */
}

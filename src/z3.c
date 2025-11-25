
#include "z3.h"
#include "misc.h"

#include "z3.h"
#include "z3_api.h"

#include "clog.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

void error_handler(Z3_context c, Z3_error_code e) {
  ERROR("Z3 Error code: %d\n", e);
  exit(1);
}

Z3_ast mk_var(Z3_context ctx, const char *name, Z3_sort ty) {
  Z3_symbol symbol = Z3_mk_string_symbol(ctx, name);
  return Z3_mk_const(ctx, symbol, ty);
}

Z3_ast mk_unary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x) {
  Z3_ast args[1] = {x};
  return Z3_mk_app(ctx, f, 1, args);
}

Z3_ast mk_binary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y) {
  Z3_ast args[2] = {x, y};
  return Z3_mk_app(ctx, f, 2, args);
}

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

void z3_tmp() {
  Z3_config cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "model", "true");

  Z3_context ctx = Z3_mk_context(cfg);
  Z3_set_error_handler(ctx, error_handler);

  Z3_del_config(cfg);

  Z3_solver s = Z3_mk_solver(ctx);
  Z3_solver_inc_ref(ctx, s);

  Z3_sort u8_sort = Z3_mk_bv_sort(ctx, 8);

  Z3_symbol mk_tuple_name = Z3_mk_string_symbol(ctx, "mk_pair");

  Z3_symbol proj_names[2] = {Z3_mk_string_symbol(ctx, "get_x"),
                             Z3_mk_string_symbol(ctx, "get_y")};

  Z3_sort proj_sorts[2] = {u8_sort, u8_sort};

  Z3_func_decl mk_tuple_decl;
  Z3_func_decl proj_decls[2];
  Z3_sort pair_sort = Z3_mk_tuple_sort(ctx,
                                       mk_tuple_name,
                                       2,
                                       proj_names,
                                       proj_sorts,
                                       &mk_tuple_decl,
                                       proj_decls);

  Z3_func_decl get_x_decl = proj_decls[0]; // get_x_decl(mk_pair(x,y)) = x
  Z3_func_decl get_y_decl = proj_decls[1]; // get_y_decl(mk_pair(x,y)) = y

  Z3_ast a = mk_var(ctx, "x", u8_sort);
  Z3_ast b = mk_var(ctx, "y", u8_sort);
  Z3_ast u8p_xy = mk_binary_app(ctx, mk_tuple_decl, a, b);

  Z3_ast one = Z3_mk_numeral(ctx, "1", u8_sort);
  Z3_ast two = Z3_mk_numeral(ctx, "2", u8_sort);
  Z3_ast three = Z3_mk_numeral(ctx, "3", u8_sort);

  Z3_ast get_x = mk_unary_app(ctx, get_x_decl, u8p_xy);
  Z3_ast get_y = mk_unary_app(ctx, get_y_decl, u8p_xy);

  prove(ctx, s, Z3_mk_eq(ctx, Z3_mk_bvor(ctx, get_x, get_y), three));

  Z3_ast u8p_onetwo = mk_binary_app(ctx, mk_tuple_decl, one, two);
  prove(ctx, s, Z3_mk_eq(ctx, Z3_mk_bvand(ctx, mk_unary_app(ctx, get_x_decl, u8p_onetwo), mk_unary_app(ctx, get_y_decl, u8p_onetwo)), three));

  Z3_ast u8p_onethree = mk_binary_app(ctx, mk_tuple_decl, one, three);
  prove(ctx, s, Z3_mk_eq(ctx, Z3_mk_bvand(ctx, mk_unary_app(ctx, get_x_decl, u8p_onethree), mk_unary_app(ctx, get_y_decl, u8p_onethree)), one));
}

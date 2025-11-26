#include "clog.h"
#include "z3.h"
#include <stdlib.h>

static inline void error_handler(Z3_context ctx, Z3_error_code error) {
  ERROR("Z3 Error code: %d\n", error);
  exit(3);
}

static inline Z3_ast z3_mk_var(Z3_context ctx, const char *name, Z3_sort ty) {
  Z3_symbol symbol = Z3_mk_string_symbol(ctx, name);
  return Z3_mk_const(ctx, symbol, ty);
}

static inline Z3_ast z3_mk_unary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x) {
  Z3_ast args[1] = {x};
  return Z3_mk_app(ctx, f, 1, args);
}

static inline Z3_ast z3_mk_binary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y) {
  Z3_ast args[2] = {x, y};
  return Z3_mk_app(ctx, f, 2, args);
}

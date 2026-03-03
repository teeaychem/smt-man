#pragma once

#include <slog.h>
#include <stdlib.h>
#include <z3.h>

#include "SML/lexicon.h"

// Establish `parser` and `lexicon` for `ctx`.
void parser_fundamentals(Z3_context ctx, Z3_parser_context parser, lexicon_s *lexicon);

// Read an smt2 file located at `smt_path` into `ctx` and `opz`, given an establised `parser` and `lexicon`.
void read_smt2(Z3_context ctx, Z3_optimize opz, Z3_parser_context parser, char *smt_path);

Z3_context smt_mk_ctx();

/// Static inlines

static inline void z3_error_handler(Z3_context ctx, Z3_error_code code) {
  slog_display(SLOG_ERROR, 0, "Z3 Error (#%d): %s\n", code, Z3_get_error_msg(ctx, code));
  exit(3);
}

static inline Z3_ast z3_mk_var(Z3_context ctx, const char *name, Z3_sort typ) {
  return Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name), typ);
}

static inline Z3_ast z3_mk_unary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x) {
  return Z3_mk_app(ctx, f, 1, (Z3_ast[1]){x});
}

static inline Z3_ast z3_mk_binary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y) {
  return Z3_mk_app(ctx, f, 2, (Z3_ast[2]){x, y});
}

//

#pragma once

#include <slog.h>
#include <stdlib.h>
#include <z3.h>

#include "SML/logic/situation.h"
#include "SML/maze.h"

constexpr size_t PATH_VARIANTS = 11;
struct z3_lang {

  struct {
    Z3_sort sort;
  } u8;

  struct {
    size_t count;

    Z3_sort sort;

    Z3_symbol *enum_names;
    Z3_func_decl *enum_consts;
    Z3_func_decl *enum_testers;

    /// anima -> u8
    Z3_func_decl tile_row_f;

    /// anima -> u8
    Z3_func_decl tile_col_f;
  } anima;

  struct {
    Z3_sort sort;

    Z3_symbol enum_name;
    Z3_func_decl enum_const;
    Z3_func_decl enum_tester;

    /// persona -> u8
    Z3_func_decl tile_row_f;

    /// persona -> u8
    Z3_func_decl tile_col_f;
  } persona;

  struct {
    Z3_sort sort;
    Z3_symbol penatly;

    Z3_symbol enum_names[PATH_VARIANTS];
    Z3_func_decl enum_consts[PATH_VARIANTS];
    Z3_func_decl enum_testers[PATH_VARIANTS];

    struct {
      /// PATH_ON
      Z3_ast o_n;
      /// PATH_OE
      Z3_ast o_e;
      /// PATH_OS
      Z3_ast o_s;
      /// PATH_OS
      Z3_ast o_w;

      /// PATH_NS
      Z3_ast n_s;
      /// PATH_EW
      Z3_ast e_w;

      /// PATH_NE
      Z3_ast n_e;
      /// PATH_SE
      Z3_ast s_e;
      /// PATH_SE
      Z3_ast s_w;
      /// PATH_NW
      Z3_ast n_w;

      /// PATH_XX
      Z3_ast x_x;

    } token;

    /// (u8, u8) -> path.sort
    Z3_func_decl tile_is_f;
  } path;
};
typedef struct z3_lang Lang;

//

void Lang_setup_base(Lang *lang, Z3_context ctx);
void Lang_setup_path(Lang *lang, Z3_context ctx);
void Lang_setup_animas(Lang *lang, Z3_context ctx, size_t count);
void Lang_setup_persona(Lang *lang, Z3_context ctx);

void Lang_assert_shortest_path_empty_hints(const Lang *lang, Z3_context ctx, Z3_optimize optimizer, const Maze *maze);
void Lang_assert_path_non_empty_hints(const Lang *lang, Z3_context ctx, Z3_optimize optimizer, const Maze *maze);

//

/// Assert the row and column values for each anima
void Lang_assert_anima_location(const Lang *lang, Z3_context ctx, Z3_optimize otz, const Situation *situation, const uint8_t id);

/// For each tile which is not the location of an anima is a link tile.
void Lang_assert_link_reqs(const Lang *lang, Z3_context ctx, Z3_optimize otz, const Situation *situation, const Maze *maze, const uint8_t id);
void Lang_anima_tile_is_origin(const Lang *lang, Z3_context ctx, Z3_optimize optimizer, const uint8_t id);

//

void Lang_persona_tile_is_origin(const Lang *lang, Z3_context ctx, Z3_optimize otz);
void Lang_assert_persona_location(const Lang *lang, Z3_context ctx, Z3_optimize otz, const Situation *situation);

//

Z3_context z3_mk_anima_ctx();

/// Static inline

static inline void error_handler(Z3_context ctx, Z3_error_code code) {
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

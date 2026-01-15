#pragma once

#include <slog.h>
#include <stdlib.h>
#include <z3.h>

#include "SML/logic/situation.h"
#include "SML/maze.h"

constexpr size_t PATH_VARIANTS = 4;
constexpr size_t LEXICON_ANIMAS = 1;

struct z3_lexicon_4 {

  struct {
    Z3_sort sort;
  } u6;

  struct {
    size_t count;

    Z3_sort sort;

    Z3_symbol enum_names[LEXICON_ANIMAS];
    Z3_func_decl enum_consts[LEXICON_ANIMAS];
    Z3_func_decl enum_testers[LEXICON_ANIMAS];

    /// anima -> u8
    Z3_func_decl tile_row_f;

    /// anima -> u8
    Z3_func_decl tile_col_f;
  } anima;

  struct {
    Z3_sort sort;

    Z3_symbol enum_name[1];
    Z3_func_decl enum_const[1];
    Z3_func_decl enum_tester[1];

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
      Z3_ast o;
      /// PATH_OE
      Z3_ast a;
      /// PATH_OS
      Z3_ast b;
      /// PATH_OS
      Z3_ast x;
    } token;

    /// (u8, u8) -> path.sort
    Z3_func_decl tile_h_f;
    /// (u8, u8) -> path.sort
    Z3_func_decl tile_v_f;
  } path;
};
typedef struct z3_lexicon_4 Lexicon;

//

void Lexicon_setup_base(Lexicon *lexicon, Z3_context ctx);
void Lexicon_setup_path(Lexicon *lexicon, Z3_context ctx);
void Lexicon_setup_animas(Lexicon *lexicon, Z3_context ctx, size_t count);
void Lexicon_setup_persona(Lexicon *lexicon, Z3_context ctx);

void Lexicon_assert_shortest_path_empty_hints(const Lexicon *lexicon, Z3_context ctx, Z3_optimize optimizer, const Maze *maze);
void Lexicon_assert_path_non_empty_hints(const Lexicon *lexicon, Z3_context ctx, Z3_optimize optimizer, const Maze *maze);

//

/// Assert the row and column values for each anima
void Lexicon_assert_anima_location(const Lexicon *lexicon, Z3_context ctx, Z3_optimize otz, const Situation *situation, const uint8_t id);

/// For each tile which is not the location of an anima is a link tile.
void Lexicon_assert_constant_hints(const Lexicon *lexicon, Z3_context ctx, Z3_optimize otz, const Maze *maze);
void Lexicon_anima_tile_is_origin(const Lexicon *lexicon, Z3_context ctx, Z3_optimize optimizer, const uint8_t id);

void Lexicon_assert_origin_is_anima_or_persona(const Lexicon *lexicon, Z3_context ctx, Z3_optimize otz, const Maze *maze);

//

void Lexicon_persona_tile_is_origin(const Lexicon *lexicon, Z3_context ctx, Z3_optimize otz);
void Lexicon_assert_persona_location(const Lexicon *lexicon, Z3_context ctx, Z3_optimize otz, const Situation *situation);

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

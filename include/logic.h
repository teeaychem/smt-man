#pragma once

#include <glib.h>
#include <z3.h>

#include "constants.h"
#include "logic/situation.h"
#include "maze.h"

constexpr size_t PATH_VARIANTS = 11;
struct z3_lang {
  struct {
    Z3_sort sort;
  } u8;

  struct {
    Z3_sort sort;

    Z3_symbol enum_names[ANIMA_COUNT];
    Z3_func_decl enum_consts[ANIMA_COUNT];
    Z3_func_decl enum_testers[ANIMA_COUNT];

    /// anima -> u8
    Z3_func_decl tile_row_f;

    /// anima -> u8
    Z3_func_decl tile_col_f;

    /// anima -> direction
    Z3_func_decl is_facing;
  } anima;

  struct {
    Z3_sort sort;

    Z3_symbol enum_names[PERSONA_COUNT];
    Z3_func_decl enum_consts[PERSONA_COUNT];
    Z3_func_decl enum_testers[PERSONA_COUNT];

    /// persona -> u8
    Z3_func_decl tile_row_f;

    /// persona -> u8
    Z3_func_decl tile_col_f;

    /// persona -> direction
    Z3_func_decl is_facing;
  } persona;

  struct direction {
    Z3_sort sort;

    Z3_symbol enum_names[4];
    Z3_func_decl enum_consts[4];
    Z3_func_decl enum_testers[4];
  } direction;

  struct {
    Z3_sort sort;
    Z3_symbol penatly;

    Z3_symbol enum_names[PATH_VARIANTS];
    Z3_func_decl enum_consts[PATH_VARIANTS];
    Z3_func_decl enum_testers[PATH_VARIANTS];

    /// Origin north
    Z3_ast o_n;
    /// Origin east
    Z3_ast o_e;
    /// Origin south
    Z3_ast o_s;
    /// Origin west
    Z3_ast o_w;

    /// North south
    Z3_ast n_s;
    /// East west
    Z3_ast e_w;

    /// North east
    Z3_ast n_e;
    /// South east
    Z3_ast s_e;
    /// South west
    Z3_ast s_w;
    /// North west
    Z3_ast n_w;

    /// Empty empty
    Z3_ast x_x;

    /// (u8, u8) -> path.sort
    Z3_func_decl tile_is_f;
  } path;
};
typedef struct z3_lang Lang;

//

void Lang_setup_base(Lang *lang, Z3_context ctx);
void Lang_setup_path(Lang *lang, Z3_context ctx);
void Lang_setup_animas(Lang *lang, Z3_context ctx);
void Lang_setup_persona(Lang *lang, Z3_context ctx);
void Lang_setup_facing(Lang *lang, Z3_context ctx);

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
  g_log(nullptr, G_LOG_LEVEL_ERROR, "Z3 Error (#%d): %s", code, Z3_get_error_msg(ctx, code));
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

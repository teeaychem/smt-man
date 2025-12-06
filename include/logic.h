#pragma once

#include "glib.h"
#include "z3.h"

#include "constants.h"
#include "maze.h"
#include "utils.h"

constexpr size_t PATH_VARIANTS = 11;
struct z3_lang {
  struct u8 {
    Z3_sort sort;
  } u8;

  struct anima {
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

  struct direction {
    Z3_sort sort;

    Z3_symbol enum_names[4];
    Z3_func_decl enum_consts[4];
    Z3_func_decl enum_testers[4];
  } direction;

  struct path {
    Z3_sort sort;
    Z3_symbol penatly;

    Z3_symbol enum_names[PATH_VARIANTS];
    Z3_func_decl enum_consts[PATH_VARIANTS];
    Z3_func_decl enum_testers[PATH_VARIANTS];

    /// Origin up
    Z3_ast og_up;
    /// Origin right
    Z3_ast og_rt;
    /// Origin down
    Z3_ast og_dn;
    /// Origin left
    Z3_ast og_lt;

    Z3_ast up_dn;
    Z3_ast rt_lt;

    Z3_ast up_rt;
    Z3_ast dn_rt;
    Z3_ast dn_lt;
    Z3_ast up_lt;

    /// Empty empty
    Z3_ast et_et;

    /// (u8, u8) -> path.sort
    Z3_func_decl tile_is_f;
  } path;
};

//

constexpr size_t SMT_INPUT_BUFFER_SIZE = 1024;

typedef enum anima_status_t AnimaStatus;
enum anima_status_t {
  ANIMA_STATUS_SEARCH,
};

// World things

typedef struct smt_world_anima_t SmtWorldAnima;
struct smt_world_anima_t {
  _Atomic(PairI32) location;

  _Atomic(Direction) intent;
  _Atomic(Direction) momentum;

  _Atomic(AnimaStatus) status;

  _Atomic(int8_t) velocity;
};

typedef struct smt_world_t SmtWorld;
struct smt_world_t {
  SmtWorldAnima anima[ANIMA_COUNT];
};

//

void Lang_base_setup(struct z3_lang *lang, Z3_context ctx);
void Lang_path_setup(struct z3_lang *lang, Z3_context ctx);
void Lang_assert_shortest_path_empty_hints(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, Maze *maze);
void Lang_assert_path_non_empty_hints(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, Maze *maze);

//

void Lang_anima_setup(struct z3_lang *lang, Z3_context ctx);
void Lang_assert_anima_locations(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, SmtWorld *world);
void Lang_assert_all_non_anima_are_non_origin(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, SmtWorld *world, Maze *maze);
void Lang_assert_all_anima_tiles_are_origin_tiles(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, SmtWorld *world, Maze *maze);
void Lang_assert_all_origin_are_anima(struct z3_lang *lang, Z3_context ctx, Z3_optimize optimizer, SmtWorld *world, Maze *maze);

//

void Lang_facing_setup(struct z3_lang *lang, Z3_context ctx);

//

static inline void error_handler(Z3_context ctx, Z3_error_code code) {
  g_log(NULL, G_LOG_LEVEL_ERROR, "Z3 Error (#%d): %s\n", code, Z3_get_error_msg(ctx, code));
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

Z3_context z3_mk_anima_ctx();

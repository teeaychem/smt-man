#pragma once

#include <slog.h>
#include <stdlib.h>
#include <z3.h>

#include "SML/logic/situation.h"
#include "SML/maze.h"

constexpr size_t PATH_VARIANTS = 4;

struct z3_lexicon_4_t {

  struct {
    Z3_sort sort;
  } tile_offset_bv_sort;

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
typedef struct z3_lexicon_4_t lexicon_s;

void lexicon_ctor(lexicon_s *self);

void lexicon_dtor(lexicon_s *self);

void lexicon_setup(lexicon_s *lexicon, Z3_context ctx, size_t anima_count);

/// Shortest paths are found by placing a penatly on the assignment of a non empty path value to each potentiial path tile.
/// So long as a path is required and optimisation is enforced, no shorter path can exist on SAT.
void lexicon_setup_shortest_path_empty_hints(const lexicon_s *lexicon, Z3_context ctx, Z3_optimize optimizer, const maze_s *maze);

// Assert the row and column values for animas
void lexicon_assert_anima_location(const lexicon_s *lexicon, Z3_context ctx, Z3_optimize otz, const situation_s *situation, const uint8_t id);

// For each tile which is not the location of an anima is a link tile.
void lexicon_assert_constant_hints(const lexicon_s *lexicon, Z3_context ctx, Z3_optimize otz, const maze_s *maze);

// Assert the row and column values for persona
void lexicon_assert_persona_location(const lexicon_s *lexicon, Z3_context ctx, Z3_optimize otz, const situation_s *situation);

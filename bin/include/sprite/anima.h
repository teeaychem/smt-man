#pragma once

#include <pthread.h>
#include <stdint.h>
#include <z3.h>

#include "SML/logic.h"
#include "SML/maze.h"
#include "SML/maze_path.h"

/// Something which performs deductions
struct anima_t {
  /// Uniqie identifier
  uint8_t id;
  /// Incremented on each tick an action is performed
  uint8_t tick_action;

  /// Path
  maze_path_s path;

  struct {
    /// The situation
    Situation *situation;
    /// Context of a solve
    Z3_context ctx;
    /// Optimizer used to solve
    Z3_optimize opz;
    /// Parser used to detail a context
    Z3_parser_context parser;
    /// A DSL for solves
    lexicon_s lexicon;

  } smt;
};
typedef struct anima_t anima_s;

// Methods

void anima_ctor(anima_s *self, Situation *situation, const uint8_t id, const maze_s *maze);

void anima_dtor(anima_s *self);

///
void anima_parse_fundamentals(anima_s *self, char *smt_path);

/// Generate consequences without deduction
void anima_instinct(anima_s *self);

/// Generate consequences from deduction
Z3_lbool anima_solve(anima_s *self);

Result anima_path_from_model(anima_s *self, const maze_s *maze);

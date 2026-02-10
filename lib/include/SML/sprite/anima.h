#pragma once

#include <pthread.h>
#include <stdint.h>
#include <z3.h>

#include "SML/logic.h"
#include "SML/maze.h"
#include "SML/maze_path.h"
#include "generic/enums.h"
#include "generic/pairs.h"

/// Tools for contacting the anima from a different thread
struct anima_contact_t {
  _Atomic(bool) flag_suspend;

  pthread_mutex_t mtx_suspend;

  pthread_cond_t cond_resume;
};
typedef struct anima_contact_t AnimaContact;

/// Something which performs deductions
struct anima_t {
  /// Uniqie identifier
  uint8_t id;
  /// Incremented on each tick an action is performed
  uint8_t tick_action;

  Cardinal direction_intent;
  /// Tools for contacting the anima from a different thread
  AnimaContact contact;

  /// Path
  MazePath path;

  struct {
    /// Point of view, on the situation
    Situation situation;
    /// Context of a solve
    Z3_context ctx;
    /// Optimizer used to solve
    Z3_optimize opz;
    /// Parser used to detail a context
    Z3_parser_context parser;
    /// A DSL for solves
    Lexicon lexicon;

  } smt;
};
typedef struct anima_t Anima;

// Methods

/// Initialize an anima with `id`, at grid `location`, facing `direction`
void Anima_init(Anima *self, const uint8_t id, const Pair_uint8 location, const Cardinal direction, const Maze *maze);

/// Drop an anima
void Anima_drop(Anima *self);

///
void Anima_touch(Anima *self, size_t anima_count);

///
void Anima_parse_fundamentals(Anima *self, char *smt_path);

/// Generate consequences without deduction
void Anima_instinct(Anima *self);

/// Generate consequences from deduction
Result Anima_deduct(Anima *self, const Maze *maze);

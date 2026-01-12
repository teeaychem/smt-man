#include <stdatomic.h>
#include <stdint.h>

#include <slog.h>

#include "SML/sprite/anima.h"
#include "generic/enums.h"
#include "generic/pairs.h"
#include "random.h"

void Anima_init(Anima *self, const uint8_t id, const Pair_uint8 location, const Cardinal direction, const Maze *maze) {
  slog_display(SLOG_DEBUG, 0, "Creating anima: %d", id);

  self->id = id;
  self->tick_action = 0;
  self->contact = (AnimaContact){
      .cond_resume = PTHREAD_COND_INITIALIZER,
      .mtx_suspend = PTHREAD_MUTEX_INITIALIZER,
  },

  assert(0 < self->smt.situation.anima_count);

  self->id = id;
  self->direction_intent = direction;

  atomic_init(&self->smt.situation.animas[id].direction_actual, direction);

  atomic_init(&self->smt.situation.animas[id].location, location);

  atomic_init(&self->smt.situation.animas[id].status, ANIMA_STATUS_SEARCH);

  atomic_init(&self->smt.situation.animas[id].movement_pattern, 0x552a552a);

  Z3_context ctx = z3_mk_anima_ctx();
  Z3_optimize optimizer = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, optimizer);
  self->smt.ctx = ctx;
  self->smt.opz = optimizer;

  atomic_init(&self->contact.flag_suspend, false);

  MazePath_init(&self->path, maze->size);
}

void Anima_drop(Anima *self) {
  assert(self != nullptr);
}

void Anima_instinct(Anima *self) {
  assert(self != nullptr);
}

void Anima_touch(Anima *self, const Maze *maze, size_t anima_count) {
  assert(self != nullptr);

  Lang_setup_base(&self->smt.language, self->smt.ctx);
  Lang_setup_path(&self->smt.language, self->smt.ctx);
  Lang_setup_animas(&self->smt.language, self->smt.ctx, anima_count);
  Lang_setup_persona(&self->smt.language, self->smt.ctx);

  Lang_anima_tile_is_origin(&self->smt.language, self->smt.ctx, self->smt.opz, self->id);
  Lang_persona_tile_is_origin(&self->smt.language, self->smt.ctx, self->smt.opz);

  Lang_assert_shortest_path_empty_hints(&self->smt.language, self->smt.ctx, self->smt.opz, maze);
  Lang_assert_path_non_empty_hints(&self->smt.language, self->smt.ctx, self->smt.opz, maze);
}

Result Anima_deduct(Anima *self, const Maze *maze) {

  Z3_optimize_push(self->smt.ctx, self->smt.opz);

  auto anima_location = atomic_load(&self->smt.situation.animas[self->id].location);

  Lang_assert_anima_location(&self->smt.language, self->smt.ctx, self->smt.opz, &self->smt.situation, self->id);
  Lang_assert_persona_location(&self->smt.language, self->smt.ctx, self->smt.opz, &self->smt.situation);
  Lang_assert_link_reqs(&self->smt.language, self->smt.ctx, self->smt.opz, &self->smt.situation, maze, self->id);

  switch (Z3_optimize_check(self->smt.ctx, self->smt.opz, 0, nullptr)) {
  case Z3_L_FALSE: {
    slog_display(SLOG_TRACE, 0, "\nStatus:\n%s\n", Z3_optimize_to_string(self->smt.ctx, self->smt.opz));
    slog_display(SLOG_ERROR, 0, "UNSAT deduction %d\n", self->id);
    return RESULT_KO;
  } break;
  case Z3_L_UNDEF: {
    slog_display(SLOG_ERROR, 0, "UNKNOWN deduction %d\n", self->id);
    return RESULT_KO;
  } break;
  case Z3_L_TRUE: {
    slog_display(SLOG_DEBUG, 0, "SAT");
  } break;
  }

  Z3_model model = Z3_optimize_get_model(self->smt.ctx, self->smt.opz);
  Z3_model_inc_ref(self->smt.ctx, model);

  MazePath_clear(&self->path);
  MazePath_read(&self->path, &self->smt.language, self->smt.ctx, model, maze);

  Z3_ast anima_origin = nullptr;

  Z3_ast row_col[2] = {
      Z3_mk_int(self->smt.ctx, anima_location.x, self->smt.language.u8.sort),
      Z3_mk_int(self->smt.ctx, anima_location.y, self->smt.language.u8.sort),
  };
  auto tile = Z3_mk_app(self->smt.ctx, self->smt.language.path.tile_is_f, 2, row_col);
  Z3_model_eval(self->smt.ctx, model, tile, false, &anima_origin);

  if (anima_origin == self->smt.language.path.token.o_n) {
    self->direction_intent = CARDINAL_N;
  }

  else if (anima_origin == self->smt.language.path.token.o_e) {
    self->direction_intent = CARDINAL_E;
  }

  else if (anima_origin == self->smt.language.path.token.o_s) {
    self->direction_intent = CARDINAL_S;
  }

  else if (anima_origin == self->smt.language.path.token.o_w) {
    self->direction_intent = CARDINAL_W;
  }

  else {
    // Backup
    switch (random_in_range(1, 4)) {
    case 1: {
      self->direction_intent = CARDINAL_N;
    } break;
    case 2: {
      self->direction_intent = CARDINAL_E;
    } break;
    case 3: {
      self->direction_intent = CARDINAL_S;
    } break;
    case 4: {
      self->direction_intent = CARDINAL_W;
    } break;
    default: {
      assert(false && "No direction");
    } break;
    }
  }

  Z3_model_dec_ref(self->smt.ctx, model);
  Z3_optimize_pop(self->smt.ctx, self->smt.opz);

  return RESULT_OK;
}

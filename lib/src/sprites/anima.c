#include <stdatomic.h>
#include <stdint.h>

#include <slog.h>

#include "SML/enums.h"
#include "SML/sprite/anima.h"
#include "generic/pairs.h"
#include "random.h"

void Anima_default(Anima *anima, const uint8_t id, const Pair_uint8 location, const Direction direction, uint32_t offset_n) {
  slog_display(SLOG_DEBUG, 0, "Creating anima: %d", id);

  anima->id = id;
  anima->tick_action = 0;
  anima->contact = (AnimaContact){
      .cond_resume = PTHREAD_COND_INITIALIZER,
      .mtx_suspend = PTHREAD_MUTEX_INITIALIZER,
  },

  assert(0 < anima->situation.anima_count);

  anima->id = id;
  anima->direction_intent = direction;

  atomic_init(&anima->situation.animas[id].direction_actual, direction);

  atomic_init(&anima->situation.animas[id].location, location);

  atomic_init(&anima->situation.animas[id].status, ANIMA_STATUS_SEARCH);

  atomic_init(&anima->situation.animas[id].movement_pattern, 0x552a552a);

  Z3_context ctx = z3_mk_anima_ctx();
  Z3_optimize optimizer = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, optimizer);
  anima->ctx = ctx;
  anima->opz = optimizer;

  atomic_init(&anima->contact.flag_suspend, false);
}

void Anima_destroy(Anima *self) {
  assert(self != nullptr);
}

void Anima_instinct(Anima *self) {
  assert(self != nullptr);
}

void Anima_touch(Anima *self, const Maze *maze, size_t anima_count) {
  assert(self != nullptr);

  Lang_setup_base(&self->lang, self->ctx);
  Lang_setup_path(&self->lang, self->ctx);
  Lang_setup_animas(&self->lang, self->ctx, anima_count);
  Lang_setup_persona(&self->lang, self->ctx);
  /* Lang_setup_facing(&self->lang, self->ctx); */

  Lang_anima_tile_is_origin(&self->lang, self->ctx, self->opz, self->id);
  Lang_persona_tile_is_origin(&self->lang, self->ctx, self->opz);

  Lang_assert_shortest_path_empty_hints(&self->lang, self->ctx, self->opz, maze);
  Lang_assert_path_non_empty_hints(&self->lang, self->ctx, self->opz, maze);
}

void Anima_deduct(Anima *self, const Maze *maze) {

  Z3_optimize_push(self->ctx, self->opz);

  auto anima_location = atomic_load(&self->situation.animas[self->id].location);

  Lang_assert_anima_location(&self->lang, self->ctx, self->opz, &self->situation, self->id);
  Lang_assert_persona_location(&self->lang, self->ctx, self->opz, &self->situation);
  Lang_assert_link_reqs(&self->lang, self->ctx, self->opz, &self->situation, maze, self->id);

  switch (Z3_optimize_check(self->ctx, self->opz, 0, nullptr)) {
  case Z3_L_FALSE: {
    slog_display(SLOG_INFO, 0, "\nStatus:\n%s\n", Z3_optimize_to_string(self->ctx, self->opz));
    slog_display(SLOG_ERROR, 0, "UNSAT deduction %d\n", self->id);
    exit(-3);
  } break;
  case Z3_L_UNDEF: {
    slog_display(SLOG_ERROR, 0, "UNKNOWN deduction %d\n", self->id);
    exit(-3);
  } break;
  case Z3_L_TRUE: {
    slog_display(SLOG_DEBUG, 0, "SAT");
  } break;
  }

  Z3_model model = Z3_optimize_get_model(self->ctx, self->opz);
  Z3_model_inc_ref(self->ctx, model);

  Z3_ast anima_origin = nullptr;

  Z3_ast row_col[2] = {
      Z3_mk_int(self->ctx, anima_location.x, self->lang.u8.sort),
      Z3_mk_int(self->ctx, anima_location.y, self->lang.u8.sort),
  };
  auto tile = Z3_mk_app(self->ctx, self->lang.path.tile_is_f, 2, row_col);
  Z3_model_eval(self->ctx, model, tile, false, &anima_origin);

  if (anima_origin == self->lang.path.o_n) {
    self->direction_intent = DIRECTION_N;
  }

  else if (anima_origin == self->lang.path.o_e) {
    self->direction_intent = DIRECTION_E;
  }

  else if (anima_origin == self->lang.path.o_s) {
    self->direction_intent = DIRECTION_S;
  }

  else if (anima_origin == self->lang.path.o_w) {
    self->direction_intent = DIRECTION_W;
  }

  else {
    // Backup
    switch (random_in_range(1, 4)) {
    case 1: {
      self->direction_intent = DIRECTION_N;
    } break;
    case 2: {
      self->direction_intent = DIRECTION_E;
    } break;
    case 3: {
      self->direction_intent = DIRECTION_S;
    } break;
    case 4: {
      self->direction_intent = DIRECTION_W;
    } break;
    default: {
      assert(false && "No direction");
    } break;
    }
  }

  Z3_model_dec_ref(self->ctx, model);
  Z3_optimize_pop(self->ctx, self->opz);
}

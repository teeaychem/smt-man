/// Generic struct setup
#include "macro.h"
#define ARITHMETIC_IMPLEMENTATION
#include "generic/arithmetic.h"
#undef ARITHMETIC_IMPLEMENTATION

#define BITVEC_IMPLEMENTATION
#include "generic/bitvec.h"
#undef BITVEC_IMPLEMENTATION

#define PAIR_IMPLEMENTATION
#include "generic/pairs.h"
#undef PAIR_IMPLEMENTATION

#define PALETTE_IMPLEMENTATION
#include "render/palette.h"
#undef PALETTE_IMPLEMENTATION

/// Other setup
#include "setup.h"

#include <pthread.h>
#include <stdatomic.h>
#include <unistd.h>

#include <cwalk.h>
#include <whereami.h>

// Set the source path for resources, etc.
void source_path_build(char **source_path, int *length) {

  *length = wai_getExecutablePath(nullptr, 0, nullptr) + 1;
  assert(*length >= 0);
  *source_path = malloc((size_t)*length * sizeof(*source_path));

  int dirname_length;
  wai_getExecutablePath(*source_path, *length - 1, &dirname_length);
  (*source_path)[dirname_length] = '\0';
}

void *spirit_ctor(void *void_setup_struct) {

  struct spirit_setup_t *setup_struct = void_setup_struct;
  anima_s *anima = setup_struct->anima;

  anima_touch(anima, setup_struct->anima_count);
  /* Anima_restrict(anima, setup_struct->maze); */

  {
    char constraints_path[32];
    sprintf(constraints_path, "resources/anima_%d.smt2", anima->id);

    char smt_path[FILENAME_MAX];
    cwk_path_join(setup_struct->source_path, constraints_path, smt_path, FILENAME_MAX);
    anima_parse_fundamentals(anima, smt_path);
  }

  lexicon_setup_shortest_path_empty_hints(&anima->smt.lexicon, anima->smt.ctx, anima->smt.opz, setup_struct->maze);

  bool sat = true;

  pthread_mutex_lock(&setup_struct->mtx_spirit);
  while (sat) {

    pthread_cond_wait(&setup_struct->cond_frame, &setup_struct->mtx_spirit);

    Z3_optimize_push(anima->smt.ctx, anima->smt.opz);
    Z3_lbool result = anima_solve(anima);

    // Other work within the push / pop
    if (result == Z3_L_TRUE) {
      anima_path_from_model(anima, setup_struct->maze);
    }

    Z3_optimize_pop(anima->smt.ctx, anima->smt.opz);

    switch (result) {
    case Z3_L_FALSE: {
      /* slog_display(SLOG_TRACE, 0, "\nStatus:\n%s\n", Z3_optimize_to_string(self->smt.ctx, self->smt.opz)); */
      slog_display(SLOG_ERROR, 0, "UNSAT deduction %d\n", anima->id);
      sat = false;

    } break;
    case Z3_L_UNDEF: {
      slog_display(SLOG_ERROR, 0, "UNKNOWN deduction %d\n", anima->id);
      exit(323);

    } break;
    case Z3_L_TRUE: {
      slog_display(SLOG_INFO, 0, "SAT\n");
    } break;
    }
  }
  pthread_mutex_unlock(&setup_struct->mtx_spirit);

  return 0;
}

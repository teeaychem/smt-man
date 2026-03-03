#include "cwalk.h"

#include "spirit.h"

void *spirit_ctor(void *void_setup_struct) {

  struct spirit_setup_t *setup_struct = void_setup_struct;
  anima_s *anima = setup_struct->anima;

  lexicon_setup(&anima->smt.lexicon, anima->smt.ctx, setup_struct->anima_count);

  {
    char constraints_path[32];
    sprintf(constraints_path, "resources/anima_%d.smt2", anima->id);

    char smt_path[FILENAME_MAX];
    cwk_path_join(setup_struct->source_path, constraints_path, smt_path, FILENAME_MAX);
    anima_parse_fundamentals(anima, smt_path);
  }

  lexicon_setup_shortest_path_empty_hints(&anima->smt.lexicon, anima->smt.ctx, anima->smt.opz, setup_struct->maze);

  bool sat = true;

  // Each spirit holds a snapshot of The Situation, taken prior to the start of any solve.
  // A successful solve generates a path for the anima, which is then used to update The Situation.
  // So, with the exception of the snapshot, a local situation is only read from.
  situation_s local_situation = {
      .animas = {
          .count = setup_struct->anima_count,
          .data = alloca(setup_struct->anima_count * sizeof(*local_situation.animas.data)),
      },

  };

  pthread_mutex_lock(&setup_struct->mtx_spirit);
  while (sat) {
    if (*setup_struct->hold) {
      printf("Hold prior to wait %d\n", setup_struct->anima->id);
      pthread_cond_broadcast(&setup_struct->cond_held);
    }

    pthread_cond_wait(&setup_struct->cond_frame, &setup_struct->mtx_spirit);

    situation_copy(setup_struct->the_situation, &local_situation);

    Z3_optimize_push(anima->smt.ctx, anima->smt.opz);
    Z3_lbool result = anima_solve(anima, &local_situation);

    // Other work within the push / pop
    if (result == Z3_L_TRUE) {
      anima_path_from_model(anima, setup_struct->maze, &local_situation);
    }

    Z3_optimize_pop(anima->smt.ctx, anima->smt.opz);

    switch (result) {
    case Z3_L_FALSE: { // UNSAT
      /* slog_display(SLOG_TRACE, 0, "\nStatus:\n%s\n", Z3_optimize_to_string(self->smt.ctx, self->smt.opz)); */
      slog_display(SLOG_ERROR, 0, "UNSAT deduction %d\n", anima->id);
      *setup_struct->hold = true;
      printf("Hold on UNSAT %d\n", setup_struct->anima->id);
      pthread_cond_broadcast(&setup_struct->cond_held);
    } break;
    case Z3_L_UNDEF: { // UNKNOWN
      slog_display(SLOG_ERROR, 0, "UNKNOWN deduction %d\n", anima->id);
      exit(323);

    } break;
    case Z3_L_TRUE: { // SAT
      slog_display(SLOG_INFO, 0, "SAT\n");
    } break;
    }
  }
  pthread_mutex_unlock(&setup_struct->mtx_spirit);

  return 0;
}

#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>

#include <z3.h>

#include "SML/logic.h"
#include "SML/logic/synchronization.h"
#include "SML/maze.h"
#include "SML/maze_path.h"
#include "SML/sprite/anima.h"
#include "SML/sprite/persona.h"

#include "setup.h"

constexpr size_t ANIMA_COUNT = 1;

pthread_t ANIMA_THREADS[ANIMA_COUNT];

void z3_display_path(const Lexicon *lexicon, Z3_context ctx, Z3_model model, const Maze *maze);
void z3_tmp(const Maze *maze, const Situation *situation);

int main() {

  char *source_path;
  { // Set source path, kept until exit
    int source_path_length;
    set_source_path(&source_path, &source_path_length);
  }

  AbstractAnima situation_animas[ANIMA_COUNT] = {};
  Situation situation = {
      .anima_count = ANIMA_COUNT,
      .animas = situation_animas,
  };

  Anima animas[ANIMA_COUNT];

  AbstractAnima mind_animas[ANIMA_COUNT][ANIMA_COUNT];
  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    animas[idx].smt.situation.anima_count = ANIMA_COUNT;
    animas[idx].smt.situation.animas = mind_animas[idx];
  }

  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    printf("\t%zu\n", animas[idx].smt.situation.anima_count);
  }

  Persona persona;

  const Maze maze = setup_maze(source_path);
  { // Setup block
    setup_situation(&situation, (Pair_uint8){.x = 13, .y = 17});

    Persona_default(&persona, &situation);

    setup_animas(animas, ANIMA_THREADS, nullptr, &maze, ANIMA_COUNT);
  }

  Sync_update_animas(&situation, animas);
  Sync_update_situation(&situation, animas);

  z3_tmp(&maze, &situation);
}

void z3_display_path(const Lexicon *lexicon, const Z3_context ctx, const Z3_model model, const Maze *maze) {

  MazePath maze_path = {  };

  MazePath_init(&maze_path, maze->size);
  MazePath_read(&maze_path, lexicon, ctx, model, maze);

  /* MazePath_clear(&z3_maze); */
  MazePath_display(&maze_path, lexicon);
}

void z3_tmp(const Maze *maze, const Situation *situation) {
  Z3_context ctx = z3_mk_anima_ctx();

  Lexicon lexicon = {};

  Z3_optimize optimizer = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, optimizer);

  uint8_t anima_id = 0;

  Lexicon_setup_base(&lexicon, ctx);
  Lexicon_setup_path(&lexicon, ctx);
  Lexicon_setup_animas(&lexicon, ctx, ANIMA_COUNT);
  Lexicon_setup_persona(&lexicon, ctx);

  Lexicon_anima_tile_is_origin(&lexicon, ctx, optimizer, anima_id);
  Lexicon_persona_tile_is_origin(&lexicon, ctx, optimizer);

  Lexicon_assert_constant_hints(&lexicon, ctx, optimizer, maze);
  Lexicon_assert_origin_is_anima_or_persona(&lexicon, ctx, optimizer, maze);

  Lexicon_assert_shortest_path_empty_hints(&lexicon, ctx, optimizer, maze);
  Lexicon_assert_path_non_empty_hints(&lexicon, ctx, optimizer, maze);

  Lexicon_assert_anima_location(&lexicon, ctx, optimizer, situation, anima_id);
  Lexicon_assert_persona_location(&lexicon, ctx, optimizer, situation);

  /* g_log(nullptr, G_LOG_LEVEL_INFO, "\nPre-model:\n%s", Z3_optimize_to_string(ctx, optimizer)); */
  /* exit(0); */

  // Checks
  switch (Z3_optimize_check(ctx, optimizer, 0, nullptr)) {
  case Z3_L_FALSE: {
    printf("UNSAT");
  } break;
  case Z3_L_UNDEF: {
    printf("UNKNOWN");
  } break;
  case Z3_L_TRUE: {
    printf("SAT");
  } break;
  }

  Z3_model model = Z3_optimize_get_model(ctx, optimizer);
  Z3_model_inc_ref(ctx, model);

  printf("\nModel:\n%s", Z3_model_to_string(ctx, model));
  z3_display_path(&lexicon, ctx, model, maze);

  // Cleanup

  Z3_model_dec_ref(ctx, model);
  Z3_optimize_dec_ref(ctx, optimizer);
  Z3_del_context(ctx);
  slog_destroy();
}

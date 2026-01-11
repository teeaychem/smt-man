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

void z3_display_path(const Lang *lang, Z3_context ctx, Z3_model model, const Maze *maze);
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

  Z3_symbol lang_anima_enum_names[ANIMA_COUNT][ANIMA_COUNT] = {};
  Z3_func_decl lang_anima_enum_consts[ANIMA_COUNT][ANIMA_COUNT] = {};
  Z3_func_decl lang_anima_enum_testers[ANIMA_COUNT][ANIMA_COUNT] = {};

  Z3_symbol lang_persona_enum_names[ANIMA_COUNT] = {};
  Z3_func_decl lang_persona_enum_consts[ANIMA_COUNT] = {};
  Z3_func_decl lang_persona_enum_testers[ANIMA_COUNT] = {};

  AbstractAnima mind_animas[ANIMA_COUNT][ANIMA_COUNT];
  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    animas[idx].situation.anima_count = ANIMA_COUNT;
    animas[idx].situation.animas = mind_animas[idx];

    animas[idx].lang = (Lang){
        .anima.count = ANIMA_COUNT,
        .anima.enum_names = lang_anima_enum_names[idx],
        .anima.enum_consts = lang_anima_enum_consts[idx],
        .anima.enum_testers = lang_anima_enum_testers[idx],
        .persona.enum_name = lang_persona_enum_names[idx],
        .persona.enum_const = lang_persona_enum_consts[idx],
        .persona.enum_tester = lang_persona_enum_testers[idx],

    };
  }

  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    printf("\t%zu\n", animas[idx].situation.anima_count);
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

void z3_display_path(const Lang *lang, const Z3_context ctx, const Z3_model model, const Maze *maze) {

  MazePath maze_path;
  MazePath_init(&maze_path, maze->size);
  MazePath_read(&maze_path, lang, ctx, model, maze);

  /* MazePath_clear(&z3_maze); */
  MazePath_display(&maze_path, lang);
}

void z3_tmp(const Maze *maze, const Situation *situation) {
  Z3_context ctx = z3_mk_anima_ctx();

  Z3_symbol lang_enun_names[ANIMA_COUNT] = {};
  Z3_func_decl lang_enun_consts[ANIMA_COUNT] = {};
  Z3_func_decl lang_enun_testers[ANIMA_COUNT] = {};
  struct z3_lang lang = {
      .anima.enum_names = lang_enun_names,
      .anima.enum_consts = lang_enun_consts,
      .anima.enum_testers = lang_enun_testers,
  };

  Z3_optimize optimizer = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, optimizer);

  uint8_t anima_id = 0;

  Lang_setup_base(&lang, ctx);
  Lang_setup_path(&lang, ctx);
  Lang_setup_animas(&lang, ctx, ANIMA_COUNT);
  Lang_setup_persona(&lang, ctx);

  Lang_anima_tile_is_origin(&lang, ctx, optimizer, anima_id);
  Lang_persona_tile_is_origin(&lang, ctx, optimizer);

  Lang_assert_link_reqs(&lang, ctx, optimizer, situation, maze, anima_id);

  Lang_assert_shortest_path_empty_hints(&lang, ctx, optimizer, maze);
  Lang_assert_path_non_empty_hints(&lang, ctx, optimizer, maze);

  Lang_assert_anima_location(&lang, ctx, optimizer, situation, anima_id);
  Lang_assert_persona_location(&lang, ctx, optimizer, situation);

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
  z3_display_path(&lang, ctx, model, maze);

  // Cleanup

  Z3_model_dec_ref(ctx, model);
  Z3_optimize_dec_ref(ctx, optimizer);
  Z3_del_context(ctx);
  slog_destroy();
}

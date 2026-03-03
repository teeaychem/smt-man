#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>

#include <z3.h>

#include "SML/logic.h"
#include "SML/maze.h"
#include "SML/maze_path.h"

#include "cwalk.h"
#include "setup.h"

constexpr size_t ANIMA_COUNT = 1;

pthread_t ANIMA_THREADS[ANIMA_COUNT];

void z3_read_and_display_path(const lexicon_s *lexicon, Z3_context ctx, Z3_model model, const maze_s *maze);
void z3_tmp(Z3_context ctx, lexicon_s *lexicon, Z3_optimize optimizer, const maze_s *maze, const Situation *situation, uint8_t anima_id);

int main() {

  { // slog setup
    uint16_t slog_level_flags = SLOG_FLAGS_ALL;
    slog_init("logfile", slog_level_flags, 1);
  }

  char *source_path;
  { // Set source path, kept until exit
    int source_path_length;
    source_path_build(&source_path, &source_path_length);
  }

  Situation situation = {};

  situation.animas.count = ANIMA_COUNT;
  situation.animas.data = alloca(ANIMA_COUNT * sizeof(*situation.animas.data));

  persona_s persona;

  maze_s maze = {};
  {
    char path_buffer[FILENAME_MAX];
    cwk_path_join(source_path, "resources/maze/source.txt", path_buffer, FILENAME_MAX);
    maze_ctor_from_path(&maze, path_buffer);
  }
  { // Setup block
    situation_ctor(&situation, ANIMA_COUNT);

    persona_ctor(&persona, &situation);

    /* setup_animas(animas, ANIMA_THREADS, &maze, ANIMA_COUNT, source_path); */
  }
  char *maze_string = maze_as_string(&maze);
  printf("%s", maze_string);
  free(maze_string);

  Z3_context ctx = z3_mk_anima_ctx();

  lexicon_s lexicon = {};
  lexicon_ctor(&lexicon);

  Z3_optimize opz = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, opz);

  lexicon_setup(&lexicon, ctx, ANIMA_COUNT);

  { // Parse
    Z3_parser_context parser = Z3_mk_parser_context(ctx);
    Z3_parser_context_inc_ref(ctx, parser);

    parser_fundamentals(ctx, parser, &lexicon);

    {
      char path_buffer[FILENAME_MAX];
      cwk_path_join(source_path, "resources/anima_0.smt2", path_buffer, FILENAME_MAX);
      read_smt2(ctx, opz, parser, &lexicon, path_buffer);
    }

    Z3_parser_context_dec_ref(ctx, parser);
  }

  z3_tmp(ctx, &lexicon, opz, &maze, &situation, 0);
}

void z3_read_and_display_path(const lexicon_s *lexicon, const Z3_context ctx, const Z3_model model, const maze_s *maze) {

  maze_path_s maze_path = {};

  maze_path_ctor(&maze_path, maze->dimensions);

  maze_path_read(&maze_path, lexicon, ctx, model, maze);

  maze_path_display(&maze_path, lexicon);

  maze_path_dtor(&maze_path);
}

void z3_tmp(Z3_context ctx, lexicon_s *lexicon, Z3_optimize optimizer, const maze_s *maze, const Situation *situation, uint8_t anima_id) {

  lexicon_setup_shortest_path_empty_hints(lexicon, ctx, optimizer, maze);

  lexicon_assert_anima_location(lexicon, ctx, optimizer, situation, anima_id);
  lexicon_assert_persona_location(lexicon, ctx, optimizer, situation);

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
  z3_read_and_display_path(lexicon, ctx, model, maze);

  // Cleanup

  Z3_model_dec_ref(ctx, model);
  Z3_optimize_dec_ref(ctx, optimizer);
  Z3_del_context(ctx);
  slog_destroy();
}

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

#include "cwalk.h"
#include "setup.h"

constexpr size_t ANIMA_COUNT = 1;

pthread_t ANIMA_THREADS[ANIMA_COUNT];

void z3_display_path(const Lexicon *lexicon, Z3_context ctx, Z3_model model, const Maze *maze);
void z3_tmp(Z3_context ctx, Lexicon *lexicon, Z3_optimize optimizer, const Maze *maze, const Situation *situation, uint8_t anima_id);

int main() {

  { // slog setup
    uint16_t slog_level_flags = SLOG_FLAGS_ALL;
    slog_init("logfile", slog_level_flags, 1);
  }

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

  Persona persona;

  const Maze maze = setup_maze(source_path);
  { // Setup block
    setup_situation(&situation, (Pair_uint8){.x = 1, .y = 12});

    Persona_default(&persona, &situation);

    setup_animas(animas, ANIMA_THREADS, nullptr, &maze, ANIMA_COUNT);
  }
  Maze_display(&maze);

  Sync_update_animas(&situation, animas);
  Sync_update_situation(&situation, animas);

  Z3_context ctx = z3_mk_anima_ctx();

  Lexicon lexicon = {};

  Lexicon_setup_base(&lexicon, ctx);
  Lexicon_setup_path(&lexicon, ctx);
  Lexicon_setup_animas(&lexicon, ctx, ANIMA_COUNT);
  Lexicon_setup_persona(&lexicon, ctx);

  Z3_optimize optimizer = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, optimizer);

  Z3_parser_context parser = Z3_mk_parser_context(ctx);
  Z3_parser_context_inc_ref(ctx, parser);

  {

    Z3_parser_context_add_sort(ctx, parser, lexicon.u6.sort);

    {
      /* Z3_parser_context_add_sort(ctx, parser, lexicon.path.sort); */
      for (size_t idx = 0; idx < PATH_VARIANTS; ++idx) {
        Z3_parser_context_add_decl(ctx, parser, lexicon.path.enum_consts[idx]);
      }
      Z3_parser_context_add_decl(ctx, parser, lexicon.path.tile_h_f);
      Z3_parser_context_add_decl(ctx, parser, lexicon.path.tile_v_f);
    }

    {
      Z3_parser_context_add_sort(ctx, parser, lexicon.anima.sort);

      /* Z3_parser_context_add_decl(ctx, parser, lexicon.anima.enum_consts); */
      /* Z3_parser_context_add_decl(ctx, parser, lexicon.anima.enum_testers[0]); */

      Z3_parser_context_add_decl(ctx, parser, lexicon.anima.tile_row_f);
      Z3_parser_context_add_decl(ctx, parser, lexicon.anima.tile_col_f);
    }

    {
      Z3_parser_context_add_sort(ctx, parser, lexicon.persona.sort);
      /* Z3_parser_context_add_decl(ctx, parser, lexicon.persona.enum_const[0]); */
      Z3_parser_context_add_decl(ctx, parser, lexicon.persona.tile_row_f);
      Z3_parser_context_add_decl(ctx, parser, lexicon.persona.tile_col_f);
    }
  }

  { // Read smt2
    char path_buffer[FILENAME_MAX];
    cwk_path_join(source_path, "../../anima.smt2", path_buffer, FILENAME_MAX);

    FILE *file_ptr;
    char *line_buffer = nullptr;
    size_t buffer_size = 0;
    ssize_t bytes_read;
    size_t line = 1;

    file_ptr = fopen(path_buffer, "r");
    if (file_ptr == nullptr) {
      slog_display(SLOG_ERROR, 0, "File missing: %s\n", path_buffer);
      exit(EXIT_FAILURE);
    }

    while (bytes_read = getline(&line_buffer, &buffer_size, file_ptr), 0 <= bytes_read) {
      if (1 < bytes_read) {
        line_buffer[bytes_read - 1] = '\0';
        Z3_ast_vector z3_vec = Z3_parser_context_from_string(ctx, parser, line_buffer);
        unsigned int vec_size = Z3_ast_vector_size(ctx, z3_vec);

        if (vec_size == 0) {
          /* printf("%zu: %s\n", line, line_buffer); */
        }

        for (unsigned int idx = 0; idx < vec_size; ++idx) {
          Z3_ast element = Z3_ast_vector_get(ctx, z3_vec, idx);

          /* Z3_ast_kind ast_kind = Z3_get_ast_kind(ctx, element); */
          Z3_optimize_assert(ctx, optimizer, element);
        }
      }
      line += 1;
    }

    fclose(file_ptr);
    if (line_buffer != nullptr) {
      free(line_buffer);
    }
  }

  Z3_parser_context_dec_ref(ctx, parser);

  z3_tmp(ctx, &lexicon, optimizer, &maze, &situation, 0);
}

void z3_display_path(const Lexicon *lexicon, const Z3_context ctx, const Z3_model model, const Maze *maze) {

  MazePath maze_path = {};

  MazePath_init(&maze_path, maze->size);
  MazePath_read(&maze_path, lexicon, ctx, model, maze);

  /* MazePath_clear(&z3_maze); */
  MazePath_display(&maze_path, lexicon);
}

void z3_tmp(Z3_context ctx, Lexicon *lexicon, Z3_optimize optimizer, const Maze *maze, const Situation *situation, uint8_t anima_id) {

  Lexicon_assert_shortest_path_empty_hints(lexicon, ctx, optimizer, maze);

  Lexicon_assert_anima_location(lexicon, ctx, optimizer, situation, anima_id);
  Lexicon_assert_persona_location(lexicon, ctx, optimizer, situation);

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
  z3_display_path(lexicon, ctx, model, maze);

  // Cleanup

  Z3_model_dec_ref(ctx, model);
  Z3_optimize_dec_ref(ctx, optimizer);
  Z3_del_context(ctx);
  slog_destroy();
}

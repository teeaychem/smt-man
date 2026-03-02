#include <stdatomic.h>
#include <stdint.h>

#include <slog.h>
#include <stdio.h>

#include "SML/sprite/anima.h"
#include "generic/enums.h"
#include "generic/pairs.h"

void Anima_ctor(Anima *self, const size_t anima_count, const uint8_t id, const maze_s *maze) {
  slog_display(SLOG_DEBUG, 0, "Creating anima: %d\n", id);

  *self = (Anima){
      .contact = (AnimaAtomics){
          .cond_resume = PTHREAD_COND_INITIALIZER,
          .mtx_suspend = PTHREAD_MUTEX_INITIALIZER,
      },
      .id = id,
      .tick_action = 0,

      .smt = {
          .ctx = z3_mk_anima_ctx(),
      },
  };

  situation_ctor(&self->smt.situation, anima_count);

  /* atomic_init(&self->smt.situation.animas.data[id].direction_actual, direction); */
  /* atomic_init(&self->smt.situation.animas.data[id].location, location); */
  /* atomic_init(&self->smt.situation.animas.data[id].status, ANIMA_STATUS_SEARCH); */
  /* atomic_init(&self->smt.situation.animas.data[id].movement_pattern, 0x552a552a); */

  self->smt.opz = Z3_mk_optimize(self->smt.ctx);
  Z3_optimize_inc_ref(self->smt.ctx, self->smt.opz);

  self->smt.parser = Z3_mk_parser_context(self->smt.ctx);
  Z3_parser_context_inc_ref(self->smt.ctx, self->smt.parser);

  atomic_init(&self->contact.flag_suspend, false);

  Lexicon_ctor(&self->smt.lexicon);

  maze_path_ctor(&self->path, maze->dimensions);
}

void Anima_dtor(Anima *self) {
  assert(self != nullptr);

  maze_path_dtor(&self->path);

  Z3_parser_context_dec_ref(self->smt.ctx, self->smt.parser);

  Z3_optimize_dec_ref(self->smt.ctx, self->smt.opz);
}

void Anima_instinct(Anima *self) {
  assert(self != nullptr);
}

void Anima_touch(Anima *self, size_t anima_count) {

  Lexicon_setup_base(&self->smt.lexicon, self->smt.ctx);
  Lexicon_setup_path(&self->smt.lexicon, self->smt.ctx);
  Lexicon_setup_animas(&self->smt.lexicon, self->smt.ctx, anima_count);
  Lexicon_setup_persona(&self->smt.lexicon, self->smt.ctx);
}

void Anima_parse_fundamentals(Anima *self, char *smt_path) {
  {

    { // Fundamental setup
      Z3_parser_context_add_sort(self->smt.ctx, self->smt.parser, self->smt.lexicon.u6.sort);
    }

    { // Path setup
      for (size_t idx = 0; idx < PATH_VARIANTS; ++idx) {
        Z3_parser_context_add_decl(self->smt.ctx, self->smt.parser, self->smt.lexicon.path.enum_consts[idx]);
      }
      Z3_parser_context_add_decl(self->smt.ctx, self->smt.parser, self->smt.lexicon.path.tile_h_f);
      Z3_parser_context_add_decl(self->smt.ctx, self->smt.parser, self->smt.lexicon.path.tile_v_f);
    }

    { // Anima setup
      Z3_parser_context_add_sort(self->smt.ctx, self->smt.parser, self->smt.lexicon.anima.sort);
      Z3_parser_context_add_decl(self->smt.ctx, self->smt.parser, self->smt.lexicon.anima.tile_row_f);
      Z3_parser_context_add_decl(self->smt.ctx, self->smt.parser, self->smt.lexicon.anima.tile_col_f);
    }

    { // Persona setup
      Z3_parser_context_add_sort(self->smt.ctx, self->smt.parser, self->smt.lexicon.persona.sort);
      Z3_parser_context_add_decl(self->smt.ctx, self->smt.parser, self->smt.lexicon.persona.tile_row_f);
      Z3_parser_context_add_decl(self->smt.ctx, self->smt.parser, self->smt.lexicon.persona.tile_col_f);
    }
  }

  { // Read smt2
    FILE *file_ptr;
    char *line_buffer = nullptr;
    size_t buffer_size = 0;
    ssize_t bytes_read;

    file_ptr = fopen(smt_path, "r");
    if (file_ptr == nullptr) {
      slog_display(SLOG_ERROR, 0, "File missing: %s\n", smt_path);
      exit(EXIT_FAILURE);
    }

    while (bytes_read = getline(&line_buffer, &buffer_size, file_ptr), 0 <= bytes_read) {
      if (1 < bytes_read) {
        line_buffer[bytes_read - 1] = '\0';
        Z3_ast_vector z3_vec = Z3_parser_context_from_string(self->smt.ctx, self->smt.parser, line_buffer);
        unsigned int vec_size = Z3_ast_vector_size(self->smt.ctx, z3_vec);

        if (vec_size == 0) {
          /* printf("%zu: %s\n", line, line_buffer); */
        }

        for (unsigned int idx = 0; idx < vec_size; ++idx) {
          Z3_ast element = Z3_ast_vector_get(self->smt.ctx, z3_vec, idx);

          /* Z3_ast_kind ast_kind = Z3_get_ast_kind(ctx, element); */
          Z3_optimize_assert(self->smt.ctx, self->smt.opz, element);
        }
      }
    }

    fclose(file_ptr);
    if (line_buffer != nullptr) {
      free(line_buffer);
    }
  }
}

Result Anima_deduct(Anima *self, const maze_s *maze) {

  Z3_optimize_push(self->smt.ctx, self->smt.opz);

  auto anima_location = atomic_load(&self->smt.situation.animas.data[self->id].location);

  Lexicon_assert_anima_location(&self->smt.lexicon, self->smt.ctx, self->smt.opz, &self->smt.situation, self->id);
  Lexicon_assert_persona_location(&self->smt.lexicon, self->smt.ctx, self->smt.opz, &self->smt.situation);

  switch (Z3_optimize_check(self->smt.ctx, self->smt.opz, 0, nullptr)) {
  case Z3_L_FALSE: {
    /* slog_display(SLOG_TRACE, 0, "\nStatus:\n%s\n", Z3_optimize_to_string(self->smt.ctx, self->smt.opz)); */
    slog_display(SLOG_ERROR, 0, "UNSAT deduction %d\n", self->id);
    return RESULT_KO;
  } break;
  case Z3_L_UNDEF: {
    slog_display(SLOG_ERROR, 0, "UNKNOWN deduction %d\n", self->id);
    return RESULT_KO;
  } break;
  case Z3_L_TRUE: {
    slog_display(SLOG_INFO, 0, "SAT\n");
  } break;
  }

  Z3_model model = Z3_optimize_get_model(self->smt.ctx, self->smt.opz);
  Z3_model_inc_ref(self->smt.ctx, model);

  maze_path_clear(&self->path);
  maze_path_read(&self->path, &self->smt.lexicon, self->smt.ctx, model, maze);

  Z3_ast anima_origin_h = nullptr;
  Z3_ast anima_origin_v = nullptr;

  Z3_ast row_col[2] = {
      Z3_mk_int(self->smt.ctx, anima_location.x, self->smt.lexicon.u6.sort),
      Z3_mk_int(self->smt.ctx, anima_location.y, self->smt.lexicon.u6.sort),
  };
  auto tile_h = Z3_mk_app(self->smt.ctx, self->smt.lexicon.path.tile_h_f, 2, row_col);
  Z3_model_eval(self->smt.ctx, model, tile_h, false, &anima_origin_h);

  auto tile_v = Z3_mk_app(self->smt.ctx, self->smt.lexicon.path.tile_v_f, 2, row_col);
  Z3_model_eval(self->smt.ctx, model, tile_v, false, &anima_origin_v);

  /* if (anima_origin == self->smt.lexicon.path.token.o_n) { */
  /*   self->direction_intent = CARDINAL_N; */
  /* } */

  /* else if (anima_origin == self->smt.lexicon.path.token.o_e) { */
  /*   self->direction_intent = CARDINAL_E; */
  /* } */

  /* else if (anima_origin == self->smt.lexicon.path.token.o_s) { */
  /*   self->direction_intent = CARDINAL_S; */
  /* } */

  /* else if (anima_origin == self->smt.lexicon.path.token.o_w) { */
  /*   self->direction_intent = CARDINAL_W; */
  /* } */

  /* else { */
  /*   // Backup */
  /*   switch (random_in_range(1, 4)) { */
  /*   case 1: { */
  /*     self->direction_intent = CARDINAL_N; */
  /*   } break; */
  /*   case 2: { */
  /*     self->direction_intent = CARDINAL_E; */
  /*   } break; */
  /*   case 3: { */
  /*     self->direction_intent = CARDINAL_S; */
  /*   } break; */
  /*   case 4: { */
  /*     self->direction_intent = CARDINAL_W; */
  /*   } break; */
  /*   default: { */
  /*     assert(false && "No direction"); */
  /*   } break; */
  /*   } */
  /* } */

  Z3_model_dec_ref(self->smt.ctx, model);
  Z3_optimize_pop(self->smt.ctx, self->smt.opz);

  return RESULT_OK;
}

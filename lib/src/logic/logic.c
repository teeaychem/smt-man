#include "SML/logic.h"
#include "z3_api.h"
#include <stdio.h>

void parser_fundamentals(Z3_context ctx, Z3_parser_context parser, lexicon_s *lexicon) {

  { // Foundation setup
    Z3_parser_context_add_sort(ctx, parser, lexicon->tile_offset_bv_sort.sort);
  }

  { // Path setup
    for (size_t idx = 0; idx < PATH_VARIANTS; ++idx) {
      Z3_parser_context_add_decl(ctx, parser, lexicon->path.enum_consts[idx]);
    }
    Z3_parser_context_add_decl(ctx, parser, lexicon->path.tile_h_f);
    Z3_parser_context_add_decl(ctx, parser, lexicon->path.tile_v_f);
  }

  { // Anima setup
    Z3_parser_context_add_sort(ctx, parser, lexicon->anima.sort);
    Z3_parser_context_add_decl(ctx, parser, lexicon->anima.tile_row_f);
    Z3_parser_context_add_decl(ctx, parser, lexicon->anima.tile_col_f);
  }

  { // Persona setup
    Z3_parser_context_add_sort(ctx, parser, lexicon->persona.sort);
    Z3_parser_context_add_decl(ctx, parser, lexicon->persona.tile_row_f);
    Z3_parser_context_add_decl(ctx, parser, lexicon->persona.tile_col_f);
  }
}

void read_smt2(Z3_context ctx, Z3_optimize opz, Z3_parser_context parser, lexicon_s *lexicon, char *smt_path) {
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
      Z3_ast_vector z3_vec = Z3_parser_context_from_string(ctx, parser, line_buffer);
      unsigned int vec_size = Z3_ast_vector_size(ctx, z3_vec);

      if (vec_size == 0) {
        /* printf("%zu: %s\n", line, line_buffer); */
      }

      for (unsigned int idx = 0; idx < vec_size; ++idx) {
        Z3_ast element = Z3_ast_vector_get(ctx, z3_vec, idx);

        /* Z3_ast_kind ast_kind = Z3_get_ast_kind(ctx, element); */
        Z3_optimize_assert(ctx, opz, element);
      }
    }
  }

  fclose(file_ptr);
  if (line_buffer != nullptr) {
    free(line_buffer);
  }
}

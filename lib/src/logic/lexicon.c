
#include <limits.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>

#include "generic/pairs.h"

#include "SML/lexicon.h"
#include "SML/logic.h"

// TODO: Inline
Z3_context z3_mk_anima_ctx() {

  Z3_config cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "model", "true");

  Z3_context ctx = Z3_mk_context(cfg);
  Z3_set_error_handler(ctx, z3_error_handler);

  Z3_del_config(cfg);

  return ctx;
}

void lexicon_ctor(lexicon_s *self) {

  *self = (lexicon_s){
      .anima = {
          .enum_consts = malloc(self->anima.count * sizeof(*self->anima.enum_consts)),
          .enum_names = malloc(self->anima.count * sizeof(*self->anima.enum_names)),
          .enum_testers = malloc(self->anima.count * sizeof(*self->anima.enum_testers)),
      },
  };
}

void lexicon_dtor(lexicon_s *self) {
  free(*self->anima.enum_testers);
  free(*self->anima.enum_names);
  free(*self->anima.enum_consts);
}

void lexicon_setup_base_type(lexicon_s *lexicon, Z3_context ctx) {
  lexicon->tile_offset_bv_sort.sort = Z3_mk_bv_sort(ctx, 6);
}

// Path fns

void lexicon_setup_path(lexicon_s *lexicon, Z3_context ctx) {

  {
    lexicon->path.enum_names[0] = Z3_mk_string_symbol(ctx, "o");
    lexicon->path.enum_names[1] = Z3_mk_string_symbol(ctx, "a");
    lexicon->path.enum_names[2] = Z3_mk_string_symbol(ctx, "b");
    lexicon->path.enum_names[3] = Z3_mk_string_symbol(ctx, "x");
  }

  lexicon->path.sort = Z3_mk_enumeration_sort(ctx, Z3_mk_string_symbol(ctx, "path4_e"), PATH_VARIANTS, lexicon->path.enum_names, lexicon->path.enum_consts, lexicon->path.enum_testers);

  lexicon->path.token.o = Z3_mk_app(ctx, lexicon->path.enum_consts[0], 0, 0);
  lexicon->path.token.a = Z3_mk_app(ctx, lexicon->path.enum_consts[1], 0, 0);
  lexicon->path.token.b = Z3_mk_app(ctx, lexicon->path.enum_consts[2], 0, 0);
  lexicon->path.token.x = Z3_mk_app(ctx, lexicon->path.enum_consts[3], 0, 0);

  Z3_sort row_col[2] = {lexicon->tile_offset_bv_sort.sort, lexicon->tile_offset_bv_sort.sort};

  lexicon->path.tile_h_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "path4_type_h"), 2, row_col, lexicon->path.sort);

  lexicon->path.tile_v_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "path4_type_v"), 2, row_col, lexicon->path.sort);

  lexicon->path.penatly = Z3_mk_string_symbol(ctx, "path_penatly");
}

void lexicon_setup_shortest_path_empty_hints(const lexicon_s *lexicon, Z3_context ctx, Z3_optimize otz, const maze_s *maze) {

  for (uint8_t row = 0; row < maze->dimensions.x; ++row) {
    for (uint8_t col = 0; col < maze->dimensions.y; ++col) {
      Z3_ast tile_x[2] = {
          Z3_mk_int(ctx, row, lexicon->tile_offset_bv_sort.sort),
          Z3_mk_int(ctx, col, lexicon->tile_offset_bv_sort.sort),
      };

      Z3_ast tile_x_h = Z3_mk_app(ctx, lexicon->path.tile_h_f, 2, tile_x);
      Z3_ast tile_x_v = Z3_mk_app(ctx, lexicon->path.tile_v_f, 2, tile_x);

      Z3_ast tile_x_h_is_X = Z3_mk_eq(ctx, tile_x_h, lexicon->path.token.x);
      Z3_ast tile_x_v_is_X = Z3_mk_eq(ctx, tile_x_v, lexicon->path.token.x);

      if (maze_is_path(maze, row, col)) {
        Z3_ast empty_conjunction[2] = {
            tile_x_h_is_X,
            tile_x_v_is_X,
        };
        Z3_optimize_assert_soft(ctx, otz, Z3_mk_and(ctx, 2, empty_conjunction), "1", lexicon->path.penatly);
      } else {
        Z3_optimize_assert(ctx, otz, tile_x_h_is_X);
        Z3_optimize_assert(ctx, otz, tile_x_v_is_X);
      }
    }
  }
}

/// Anima fns

void lexicon_setup_animas(lexicon_s *lexicon, Z3_context ctx, size_t anima_count) {

  { // Set the (abstract) anima names
    // Gottlob, Bertrand, Herbrand, Löb, etc.
    char *name_buffer = malloc(8 * sizeof(*name_buffer));
    for (uint8_t idx = 0; idx < anima_count; ++idx) {
      sprintf(name_buffer, "anima_%d", idx);
      lexicon->anima.enum_names[idx] = Z3_mk_string_symbol(ctx, name_buffer);
    }
    free(name_buffer);
  }

  assert(anima_count < UINT_MAX);
  lexicon->anima.sort = Z3_mk_enumeration_sort(ctx,
                                               Z3_mk_string_symbol(ctx, "anima_t"),
                                               (unsigned int)anima_count,
                                               lexicon->anima.enum_names,
                                               lexicon->anima.enum_consts,
                                               lexicon->anima.enum_testers);

  { // Anima row fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "anima_r");
    Z3_sort domain[1] = {lexicon->anima.sort};
    Z3_sort range = lexicon->tile_offset_bv_sort.sort;
    lexicon->anima.tile_row_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }

  { // Anima col fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "anima_c");
    Z3_sort domain[1] = {lexicon->anima.sort};
    Z3_sort range = lexicon->tile_offset_bv_sort.sort;
    lexicon->anima.tile_col_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }
}

void lexicon_setup_persona(lexicon_s *lexicon, Z3_context ctx) {

  lexicon->persona.enum_name[0] = Z3_mk_string_symbol(ctx, "persona");

  lexicon->persona.sort = Z3_mk_enumeration_sort(ctx,
                                                 Z3_mk_string_symbol(ctx, "persona_t"),
                                                 1,
                                                 lexicon->persona.enum_name,
                                                 lexicon->persona.enum_const,
                                                 lexicon->persona.enum_tester);

  { // Persona row fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "persona_r");
    Z3_sort domain[1] = {lexicon->persona.sort};
    Z3_sort range = lexicon->tile_offset_bv_sort.sort;
    lexicon->persona.tile_row_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }

  { // Persona col fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "persona_c");
    Z3_sort domain[1] = {lexicon->persona.sort};
    Z3_sort range = lexicon->tile_offset_bv_sort.sort;
    lexicon->persona.tile_col_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }
}

void lexicon_setup(lexicon_s *self, Z3_context ctx, size_t anima_count) {

  lexicon_setup_base_type(self, ctx);
  lexicon_setup_path(self, ctx);
  lexicon_setup_animas(self, ctx, anima_count);
  lexicon_setup_persona(self, ctx);
}

void lexicon_assert_anima_location(const lexicon_s *lexicon, Z3_context ctx, Z3_optimize otz, const situation_s *situation, const uint8_t id) {

  Pair_uint8 anima_location = atomic_load(&situation->animas.data[id].location);
  slog_display(SLOG_INFO, 0, "Asserted anima %d at %dx%d\n", id, anima_location.x, anima_location.y);
  Z3_ast anima_ast = Z3_mk_app(ctx, lexicon->anima.enum_consts[id], 0, 0);

  { // row block
    Z3_ast z3_row = z3_mk_unary_app(ctx, lexicon->anima.tile_row_f, anima_ast);
    Z3_ast row = Z3_mk_int(ctx, anima_location.x, lexicon->tile_offset_bv_sort.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_row, row));
  }

  { // col block
    Z3_ast z3_col = z3_mk_unary_app(ctx, lexicon->anima.tile_col_f, anima_ast);
    Z3_ast col = Z3_mk_int(ctx, anima_location.y, lexicon->tile_offset_bv_sort.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_col, col));
  }
}

void lexicon_assert_persona_location(const lexicon_s *lexicon, Z3_context ctx, Z3_optimize otz, const situation_s *situation) {

  Pair_uint8 persona_location = atomic_load(&situation->persona.location);

  Z3_ast persona_ast = Z3_mk_app(ctx, lexicon->persona.enum_const[0], 0, 0);

  { // row block
    Z3_ast z3_row = z3_mk_unary_app(ctx, lexicon->persona.tile_row_f, persona_ast);
    Z3_ast row = Z3_mk_int(ctx, persona_location.x, lexicon->tile_offset_bv_sort.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_row, row));
  }

  { // col block
    Z3_ast z3_col = z3_mk_unary_app(ctx, lexicon->persona.tile_col_f, persona_ast);
    Z3_ast col = Z3_mk_int(ctx, persona_location.y, lexicon->tile_offset_bv_sort.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_col, col));
  }
}

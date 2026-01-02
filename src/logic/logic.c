#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>

#include "generic/pairs.h"
#include "logic.h"
#include "macro.h"

Z3_context z3_mk_anima_ctx() {

  Z3_config cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "model", "true");

  Z3_context ctx = Z3_mk_context(cfg);
  Z3_set_error_handler(ctx, error_handler);

  Z3_del_config(cfg);

  return ctx;
}

void Lang_setup_base(Lang *lang, Z3_context ctx) {
  lang->u8.sort = Z3_mk_bv_sort(ctx, 8);
}

// Path fns

void Lang_setup_path(Lang *lang, Z3_context ctx) {

  {
    lang->path.enum_names[0] = Z3_mk_string_symbol(ctx, "og_up");
    lang->path.enum_names[1] = Z3_mk_string_symbol(ctx, "og_rt");
    lang->path.enum_names[2] = Z3_mk_string_symbol(ctx, "og_dn");
    lang->path.enum_names[3] = Z3_mk_string_symbol(ctx, "og_lt");

    lang->path.enum_names[4] = Z3_mk_string_symbol(ctx, "up_dn");
    lang->path.enum_names[5] = Z3_mk_string_symbol(ctx, "rt_lt");

    lang->path.enum_names[6] = Z3_mk_string_symbol(ctx, "up_rt");
    lang->path.enum_names[7] = Z3_mk_string_symbol(ctx, "dn_rt");
    lang->path.enum_names[8] = Z3_mk_string_symbol(ctx, "dn_lt");
    lang->path.enum_names[9] = Z3_mk_string_symbol(ctx, "up_lt");

    lang->path.enum_names[10] = Z3_mk_string_symbol(ctx, "et_et");
  }

  lang->path.sort = Z3_mk_enumeration_sort(ctx, Z3_mk_string_symbol(ctx, "path"), PATH_VARIANTS, lang->path.enum_names, lang->path.enum_consts, lang->path.enum_testers);

  lang->path.og_up = Z3_mk_app(ctx, lang->path.enum_consts[0], 0, 0);
  lang->path.og_rt = Z3_mk_app(ctx, lang->path.enum_consts[1], 0, 0);
  lang->path.og_dn = Z3_mk_app(ctx, lang->path.enum_consts[2], 0, 0);
  lang->path.og_lt = Z3_mk_app(ctx, lang->path.enum_consts[3], 0, 0);

  lang->path.up_dn = Z3_mk_app(ctx, lang->path.enum_consts[4], 0, 0);
  lang->path.rt_lt = Z3_mk_app(ctx, lang->path.enum_consts[5], 0, 0);

  lang->path.up_rt = Z3_mk_app(ctx, lang->path.enum_consts[6], 0, 0);
  lang->path.dn_rt = Z3_mk_app(ctx, lang->path.enum_consts[7], 0, 0);
  lang->path.dn_lt = Z3_mk_app(ctx, lang->path.enum_consts[8], 0, 0);
  lang->path.up_lt = Z3_mk_app(ctx, lang->path.enum_consts[9], 0, 0);

  lang->path.et_et = Z3_mk_app(ctx, lang->path.enum_consts[10], 0, 0);

  Z3_sort col_row[2] = {lang->u8.sort, lang->u8.sort};
  lang->path.tile_is_f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "path_choice"), ARRAY_LEN(col_row), col_row, lang->path.sort);

  lang->path.penatly = Z3_mk_string_symbol(ctx, "path_penatly");
}

/// Shortest paths are found by placing a penatly on the assignment of a non empty path value to each potentiial path tile.
/// So long as a path is required and optimisation is enforced, no shorter path can exist on SAT.
void Lang_assert_shortest_path_empty_hints(const Lang *lang, Z3_context ctx, Z3_optimize otz, const Maze *maze) {

  Z3_ast col_row[2] = {};

  for (uint8_t row = 0; row < maze->size.y; ++row) {
    col_row[1] = Z3_mk_int(ctx, row, lang->u8.sort);

    for (uint8_t col = 0; col < maze->size.x; ++col) {
      col_row[0] = Z3_mk_int(ctx, col, lang->u8.sort);

      if (Maze_abstract_is_path(maze, col, row)) {
        Z3_ast tile_path_val = Z3_mk_app(ctx, lang->path.tile_is_f, ARRAY_LEN(col_row), col_row);
        Z3_optimize_assert_soft(ctx, otz, Z3_mk_eq(ctx, tile_path_val, lang->path.et_et), "1", lang->path.penatly);
      } else {
        Z3_ast tile_path_val = Z3_mk_app(ctx, lang->path.tile_is_f, ARRAY_LEN(col_row), col_row);
        Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, tile_path_val, lang->path.et_et));
      }
    }
  }
}

void Lang_assert_path_non_empty_hints(const Lang *lang, Z3_context ctx, Z3_optimize otz, const Maze *maze) {

  Z3_ast col_row[2] = {};

  for (uint8_t row = 0; row < maze->size.y; row++) {
    col_row[1] = Z3_mk_int(ctx, row, lang->u8.sort);

    for (uint8_t col = 0; col < maze->size.x; col++) {
      col_row[0] = Z3_mk_int(ctx, col, lang->u8.sort);

      if (Maze_abstract_is_path(maze, col, row)) {
        Z3_ast tile_path_val = Z3_mk_app(ctx, lang->path.tile_is_f, 2, col_row);

        if (0 < row) {
          Z3_ast up_tile[2] = {
              Z3_mk_int(ctx, col, lang->u8.sort),
              Z3_mk_int(ctx, (row - 1), lang->u8.sort),
          };

          uint32_t up_reqs = 0;
          Z3_ast up_req[4] = {};

          up_req[up_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, up_tile), lang->path.og_dn);
          up_req[up_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, up_tile), lang->path.up_dn);
          up_req[up_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, up_tile), lang->path.dn_rt);
          up_req[up_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, up_tile), lang->path.dn_lt);

          if (0 < up_reqs) {
            Z3_ast up_tile_or = Z3_mk_or(ctx, up_reqs, up_req);

            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.og_up), up_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.up_lt), up_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.up_dn), up_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.up_rt), up_tile_or));
          }
        }

        if (col + 1 < maze->size.x) {
          Z3_ast rt_tile[2] = {
              Z3_mk_int(ctx, (col + 1), lang->u8.sort),
              Z3_mk_int(ctx, row, lang->u8.sort),
          };

          uint32_t rt_reqs = 0;
          Z3_ast rt_req[4] = {};

          rt_req[rt_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, rt_tile), lang->path.og_lt);
          rt_req[rt_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, rt_tile), lang->path.rt_lt);
          rt_req[rt_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, rt_tile), lang->path.dn_lt);
          rt_req[rt_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, rt_tile), lang->path.up_lt);

          if (0 < rt_reqs) {
            Z3_ast rt_tile_or = Z3_mk_or(ctx, rt_reqs, rt_req);

            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.og_rt), rt_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.rt_lt), rt_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.up_rt), rt_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.dn_rt), rt_tile_or));
          }
        }

        if (row + 1 < maze->size.y) {
          Z3_ast dn_tile[2] = {
              Z3_mk_int(ctx, col, lang->u8.sort),
              Z3_mk_int(ctx, (row + 1), lang->u8.sort),
          };

          uint32_t dn_reqs = 0;
          Z3_ast dn_req[4] = {};

          dn_req[dn_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, dn_tile), lang->path.og_up);
          dn_req[dn_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, dn_tile), lang->path.up_dn);
          dn_req[dn_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, dn_tile), lang->path.up_rt);
          dn_req[dn_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, dn_tile), lang->path.up_lt);

          if (0 < dn_reqs) {
            Z3_ast dn_tile_or = Z3_mk_or(ctx, dn_reqs, dn_req);

            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.og_dn), dn_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.up_dn), dn_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.dn_rt), dn_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.dn_lt), dn_tile_or));
          }
        }

        if (0 < col) {
          Z3_ast lt_tile[2] = {
              Z3_mk_int(ctx, (col - 1), lang->u8.sort),
              Z3_mk_int(ctx, row, lang->u8.sort),
          };

          uint32_t lt_reqs = 0;
          Z3_ast lt_req[4] = {};

          lt_req[lt_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, lt_tile), lang->path.og_rt);
          lt_req[lt_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, lt_tile), lang->path.rt_lt);
          lt_req[lt_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, lt_tile), lang->path.dn_rt);
          lt_req[lt_reqs++] = Z3_mk_eq(ctx, Z3_mk_app(ctx, lang->path.tile_is_f, 2, lt_tile), lang->path.up_rt);

          if (0 < lt_reqs) {
            Z3_ast lt_tile_or = Z3_mk_or(ctx, lt_reqs, lt_req);

            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.og_lt), lt_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.rt_lt), lt_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.up_lt), lt_tile_or));
            Z3_optimize_assert(ctx, otz, Z3_mk_implies(ctx, Z3_mk_eq(ctx, tile_path_val, lang->path.dn_lt), lt_tile_or));
          }
        }
      }
    }
  }
}

/// Anima fns

void Lang_setup_animas(Lang *lang, Z3_context ctx) {

  if (1 <= ANIMA_COUNT) {
    lang->anima.enum_names[0] = Z3_mk_string_symbol(ctx, "gottlob");
  }
  if (2 <= ANIMA_COUNT) {
    lang->anima.enum_names[1] = Z3_mk_string_symbol(ctx, "bertrand");
  }
  if (3 <= ANIMA_COUNT) {
    lang->anima.enum_names[2] = Z3_mk_string_symbol(ctx, "herbrand");
  }
  if (4 <= ANIMA_COUNT) {
    lang->anima.enum_names[3] = Z3_mk_string_symbol(ctx, "lob");
  }

  lang->anima.sort = Z3_mk_enumeration_sort(ctx,
                                            Z3_mk_string_symbol(ctx, "anima"),
                                            ANIMA_COUNT,
                                            lang->anima.enum_names,
                                            lang->anima.enum_consts,
                                            lang->anima.enum_testers);

  { // Persona row fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "anima_row");
    Z3_sort domain[1] = {lang->anima.sort};
    Z3_sort range = lang->u8.sort;
    lang->anima.tile_row_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }

  { // Persona col fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "anima_col");
    Z3_sort domain[1] = {lang->anima.sort};
    Z3_sort range = lang->u8.sort;
    lang->anima.tile_col_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }
}

void Lang_assert_anima_location(const Lang *lang, Z3_context ctx, Z3_optimize otz, const Situation *situation, const uint8_t id) {

  auto anima_location = atomic_load(&situation->anima[id].location);
  printf("Asserted anima %d at %dx%d\n", id, anima_location.x, anima_location.y);
  Z3_ast anima_ast = Z3_mk_app(ctx, lang->anima.enum_consts[id], 0, 0);

  {
    Z3_ast z3_row = z3_mk_unary_app(ctx, lang->anima.tile_row_f, anima_ast);
    Z3_ast abstract_row = Z3_mk_int(ctx, anima_location.y, lang->u8.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_row, abstract_row));
  }
  {
    Z3_ast z3_col = z3_mk_unary_app(ctx, lang->anima.tile_col_f, anima_ast);
    Z3_ast abstract_col = Z3_mk_int(ctx, anima_location.x, lang->u8.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_col, abstract_col));
  }
}

void Lang_anima_tile_is_origin(const Lang *lang, Z3_context ctx, Z3_optimize otz, uint8_t id) {

  Z3_ast anima_ast = Z3_mk_app(ctx, lang->anima.enum_consts[id], 0, 0);

  Z3_ast anima_col_row[2] = {z3_mk_unary_app(ctx, lang->anima.tile_col_f, anima_ast),
                             z3_mk_unary_app(ctx, lang->anima.tile_row_f, anima_ast)};

  Z3_ast anima_tile_value = Z3_mk_app(ctx, lang->path.tile_is_f, ARRAY_LEN(anima_col_row), anima_col_row);

  Z3_ast value_is_origin[4] = {Z3_mk_eq(ctx, anima_tile_value, lang->path.og_up),
                               Z3_mk_eq(ctx, anima_tile_value, lang->path.og_rt),
                               Z3_mk_eq(ctx, anima_tile_value, lang->path.og_dn),
                               Z3_mk_eq(ctx, anima_tile_value, lang->path.og_lt)};

  Z3_optimize_assert(ctx, otz, Z3_mk_or(ctx, ARRAY_LEN(value_is_origin), value_is_origin));
}

void Lang_setup_facing(Lang *lang, Z3_context ctx) {

  {
    lang->direction.enum_names[0] = Z3_mk_string_symbol(ctx, "up");
    lang->direction.enum_names[1] = Z3_mk_string_symbol(ctx, "rt");
    lang->direction.enum_names[2] = Z3_mk_string_symbol(ctx, "dn");
    lang->direction.enum_names[3] = Z3_mk_string_symbol(ctx, "lt");
  }

  lang->direction.sort = Z3_mk_enumeration_sort(ctx,
                                                Z3_mk_string_symbol(ctx, "facing"),
                                                ARRAY_LEN(lang->direction.enum_names),
                                                lang->direction.enum_names,
                                                lang->direction.enum_consts,
                                                lang->direction.enum_testers);

  { // Anima is facin fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "anima_is_facing");
    Z3_sort domain[1] = {lang->anima.sort};
    Z3_sort range = lang->direction.sort;
    lang->anima.is_facing = Z3_mk_func_decl(ctx, id, ARRAY_LEN(domain), domain, range);
  }
}

/// Persona fns

void Lang_setup_persona(Lang *lang, Z3_context ctx) {

  lang->persona.enum_names[0] = Z3_mk_string_symbol(ctx, "smt-man");

  lang->persona.sort = Z3_mk_enumeration_sort(ctx,
                                              Z3_mk_string_symbol(ctx, "persona"),
                                              PERSONA_COUNT,
                                              lang->persona.enum_names,
                                              lang->persona.enum_consts,
                                              lang->persona.enum_testers);

  { // Persona row fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "persona_row");
    Z3_sort domain[1] = {lang->persona.sort};
    Z3_sort range = lang->u8.sort;
    lang->persona.tile_row_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }

  { // Persona col fn
    Z3_symbol id = Z3_mk_string_symbol(ctx, "persona_col");
    Z3_sort domain[1] = {lang->persona.sort};
    Z3_sort range = lang->u8.sort;
    lang->persona.tile_col_f = Z3_mk_func_decl(ctx, id, 1, domain, range);
  }
}

void Lang_persona_tile_is_origin(const Lang *lang, Z3_context ctx, Z3_optimize otz) {

  Z3_ast persona_ast = Z3_mk_app(ctx, lang->persona.enum_consts[0], 0, 0);

  Z3_ast persona_col_row[2] = {z3_mk_unary_app(ctx, lang->persona.tile_col_f, persona_ast),
                               z3_mk_unary_app(ctx, lang->persona.tile_row_f, persona_ast)};

  Z3_ast persona_tile_value = Z3_mk_app(ctx, lang->path.tile_is_f, ARRAY_LEN(persona_col_row), persona_col_row);

  Z3_ast value_is_origin[4] = {Z3_mk_eq(ctx, persona_tile_value, lang->path.og_up),
                               Z3_mk_eq(ctx, persona_tile_value, lang->path.og_rt),
                               Z3_mk_eq(ctx, persona_tile_value, lang->path.og_dn),
                               Z3_mk_eq(ctx, persona_tile_value, lang->path.og_lt)};

  Z3_optimize_assert(ctx, otz, Z3_mk_or(ctx, ARRAY_LEN(value_is_origin), value_is_origin));
}

void Lang_assert_persona_location(const Lang *lang, Z3_context ctx, Z3_optimize otz, const Situation *situation) {

  auto persona_location = atomic_load(&situation->persona.location);
  printf("Asserted persona at %dx%d\n", persona_location.x, persona_location.y);
  Z3_ast persona_ast = Z3_mk_app(ctx, lang->persona.enum_consts[0], 0, 0);

  {
    Z3_ast z3_row = z3_mk_unary_app(ctx, lang->persona.tile_row_f, persona_ast);
    Z3_ast abstract_row = Z3_mk_int(ctx, persona_location.y, lang->u8.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_row, abstract_row));
  }
  {
    Z3_ast z3_col = z3_mk_unary_app(ctx, lang->persona.tile_col_f, persona_ast);
    Z3_ast abstract_col = Z3_mk_int(ctx, persona_location.x, lang->u8.sort);
    Z3_optimize_assert(ctx, otz, Z3_mk_eq(ctx, z3_col, abstract_col));
  }
}

/// Link

// Require a non-origin tile on non-anima tiles
void Lang_assert_link_reqs(const Lang *lang, Z3_context ctx, Z3_optimize otz, const Situation *situation, const Maze *maze, const uint8_t id) {

  Pair_uint8 anima_location = atomic_load(&situation->anima[id].location);
  Pair_uint8 persona_location = atomic_load(&situation->persona.location);

  Z3_ast col_row[2] = {};

  for (uint8_t row = 0; row < maze->size.y; row++) {
    col_row[1] = Z3_mk_int(ctx, row, lang->u8.sort);

    for (uint8_t col = 0; col < maze->size.x; col++) {
      col_row[0] = Z3_mk_int(ctx, col, lang->u8.sort);

      if ((anima_location.x == col && anima_location.y == row) || (persona_location.x == col && persona_location.y == row)) {
        goto skip_tile_assertion;
      }

      Z3_ast tile_path_value = Z3_mk_app(ctx, lang->path.tile_is_f, ARRAY_LEN(col_row), col_row);

      Z3_ast value_is_link[7] = {
          Z3_mk_eq(ctx, tile_path_value, lang->path.up_dn),
          Z3_mk_eq(ctx, tile_path_value, lang->path.rt_lt),
          Z3_mk_eq(ctx, tile_path_value, lang->path.up_rt),
          Z3_mk_eq(ctx, tile_path_value, lang->path.dn_rt),
          Z3_mk_eq(ctx, tile_path_value, lang->path.up_lt),
          Z3_mk_eq(ctx, tile_path_value, lang->path.dn_lt),
          Z3_mk_eq(ctx, tile_path_value, lang->path.et_et),
      };

      Z3_optimize_assert(ctx, otz, Z3_mk_or(ctx, ARRAY_LEN(value_is_link), value_is_link));
    skip_tile_assertion:
    }
  }
}

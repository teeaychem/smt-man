#include "sprite/anima.h"
#include <stdatomic.h>
#include <stdint.h>

#include <slog.h>

#include "generic/bitvec.h"
#include "generic/pairs.h"

#include "random.h"
#include "render/sprite.h"

void anima_ctor(anima_s *self, situation_s *situation, const uint8_t id, const maze_s *maze) {
  slog_display(SLOG_DEBUG, 0, "Creating anima: %d\n", id);

  *self = (anima_s){
      .id = id,
      .tick_action = 0,

      .smt = {
          .ctx = z3_mk_anima_ctx(),
      },
  };

  self->smt.opz = Z3_mk_optimize(self->smt.ctx);
  Z3_optimize_inc_ref(self->smt.ctx, self->smt.opz);

  self->smt.parser = Z3_mk_parser_context(self->smt.ctx);
  Z3_parser_context_inc_ref(self->smt.ctx, self->smt.parser);

  lexicon_ctor(&self->smt.lexicon);

  maze_path_ctor(&self->path, maze->dimensions);
}

void anima_dtor(anima_s *self) {
  assert(self != nullptr);

  maze_path_dtor(&self->path);

  Z3_parser_context_dec_ref(self->smt.ctx, self->smt.parser);

  Z3_optimize_dec_ref(self->smt.ctx, self->smt.opz);
}

void anima_instinct(anima_s *self) {
  assert(self != nullptr);
}

void anima_parse_fundamentals(anima_s *self, char *smt_path) {

  parser_fundamentals(self->smt.ctx, self->smt.parser, &self->smt.lexicon);

  read_smt2(self->smt.ctx, self->smt.opz, self->smt.parser, &self->smt.lexicon, smt_path);
}

Z3_lbool anima_solve(anima_s *self, const situation_s *situation) {

  lexicon_assert_anima_location(&self->smt.lexicon, self->smt.ctx, self->smt.opz, situation, self->id);
  lexicon_assert_persona_location(&self->smt.lexicon, self->smt.ctx, self->smt.opz, situation);

  Z3_lbool result = Z3_optimize_check(self->smt.ctx, self->smt.opz, 0, nullptr);

  return result;
}

Result anima_path_from_model(anima_s *self, const maze_s *maze, const situation_s *situation) {

  auto anima_location = atomic_load(&situation->animas.data[self->id].location);

  Z3_model model = Z3_optimize_get_model(self->smt.ctx, self->smt.opz);
  Z3_model_inc_ref(self->smt.ctx, model);

  maze_path_clear(&self->path);
  maze_path_read(&self->path, &self->smt.lexicon, self->smt.ctx, model, maze);

  Z3_ast anima_origin_h = nullptr;
  Z3_ast anima_origin_v = nullptr;

  Z3_ast row_col[2] = {
      Z3_mk_int(self->smt.ctx, anima_location.x, self->smt.lexicon.tile_offset_bv_sort.sort),
      Z3_mk_int(self->smt.ctx, anima_location.y, self->smt.lexicon.tile_offset_bv_sort.sort),
  };
  auto tile_h = Z3_mk_app(self->smt.ctx, self->smt.lexicon.path.tile_h_f, 2, row_col);
  Z3_model_eval(self->smt.ctx, model, tile_h, false, &anima_origin_h);

  auto tile_v = Z3_mk_app(self->smt.ctx, self->smt.lexicon.path.tile_v_f, 2, row_col);
  Z3_model_eval(self->smt.ctx, model, tile_v, false, &anima_origin_v);

  Z3_model_dec_ref(self->smt.ctx, model);

  return RESULT_OK;
}

void anima_on_tile(anima_s *self, const situation_s *situation, Sprite *sprite, const maze_s *maze, Pair_uint8 maze_location) {

  /// Update location
  atomic_store(&situation->animas.data[self->id].location, maze_location);
}

void anima_update_direction(anima_s *self, const maze_s *maze, Pair_uint8 maze_location) {

  /// Update direction
}

void anima_on_frame(anima_s *self, const situation_s *situation, Sprite *sprite, const maze_s *maze, uint32_t tile_pixels, uint32_t offset_n) {

  uint32_t movement = atomic_load(&situation->animas.data[self->id].movement_pattern);
  movement = uint32_rotl1(movement);
  atomic_store(&situation->animas.data[self->id].movement_pattern, movement);

  if ((movement & 0x10000000) == 0) {
    return;
  }

  self->tick_action += 1;

  // Ensure coherence
  anima_instinct(self);

  if (Sprite_is_centered_on_tile(sprite->location, tile_pixels)) {
    Pair_uint8 maze_location = Sprite_maze_location(&sprite->location, tile_pixels, offset_n);

    anima_on_tile(self, situation, sprite, maze, maze_location);

    pthread_mutex_lock(&self->path.access_mutex);

    maze_tile_s tile_path = maze_path_at(&self->path, maze_location);
    cardinal_e direction_actual = atomic_load(&situation->animas.data[self->id].direction_actual);

    if (maze_is_intersection(maze, maze_location.x, maze_location.y)) {

      switch (tile_path.h) {
      case PATH_X: {
        switch (tile_path.v) {
        case PATH_A: {
          // Do nothing
        } break;
        case PATH_B: {
          // Do nothing
        } break;
        case PATH_X: {
          // TODO: Fixup path
          // The issue here is that the anima may no longer be on the current path,
          // as the current and previous may have diverged.
          direction_actual = CARDINAL_NONE;
        } break;
        default: {
          assert(false && "XO / OX");
        } break;
        }
      } break;

      case PATH_A: {
        switch (tile_path.v) {
        case PATH_X: {
          // Do nothing
        } break;
        case PATH_A: { // NE
          if (direction_actual == CARDINAL_S) {
            direction_actual = CARDINAL_E;
          } else {
            direction_actual = CARDINAL_N;
          }
        } break;
        case PATH_B: { // SE
          if (direction_actual == CARDINAL_N) {
            direction_actual = CARDINAL_E;
          } else {
            direction_actual = CARDINAL_S;
          }
        } break;
        case PATH_O: { // OE
          direction_actual = CARDINAL_E;
        } break;
        }
      } break;

      case PATH_B: {
        switch (tile_path.v) {
        case PATH_X: {
          // Do nothing
        } break;
        case PATH_A: { // NW
          if (direction_actual == CARDINAL_S) {
            direction_actual = CARDINAL_W;
          } else {
            direction_actual = CARDINAL_N;
          }
        } break;
        case PATH_B: { // SW
          if (direction_actual == CARDINAL_N) {
            direction_actual = CARDINAL_W;
          } else {
            direction_actual = CARDINAL_S;
          }
        } break;
        case PATH_O: { // OW
          direction_actual = CARDINAL_W;
        } break;
        }
      } break;

      case PATH_O: {
        switch (tile_path.v) {
        case PATH_A: { // ON
          direction_actual = CARDINAL_N;
        } break;
        case PATH_B: { // OS
          direction_actual = CARDINAL_S;
        } break;
        default: {
          assert(false && "Bad origin / h");
        } break;
        }
      } break;
      }

      atomic_store(&situation->animas.data[self->id].direction_actual, direction_actual);
    }

    pthread_mutex_unlock(&self->path.access_mutex);

    // TODO:
    while (!maze_tile_in_direction_is_path(maze, maze_location, direction_actual)) {
      int random_c = random_in_range(0, 4);
      switch (random_c) {
      case 0: {
        direction_actual = CARDINAL_N;
      } break;
      case 1: {
        direction_actual = CARDINAL_E;
      } break;
      case 2: {
        direction_actual = CARDINAL_S;
      } break;
      case 3: {
        direction_actual = CARDINAL_W;
      } break;
      default: {
      };
      }
    }

    atomic_store(&situation->animas.data[self->id].direction_actual, direction_actual);

    // TODO: Empty fn
    anima_update_direction(self, maze, maze_location);
  }

  switch (atomic_load(&situation->animas.data[self->id].direction_actual)) {
  case CARDINAL_NONE: {
    // Do nothing
  } break;
  case CARDINAL_N: {
    sprite->location.x -= SPRITE_VELOCITY;
  } break;
  case CARDINAL_E: {
    sprite->location.y += SPRITE_VELOCITY;
  } break;
  case CARDINAL_S: {
    sprite->location.x += SPRITE_VELOCITY;
  } break;
  case CARDINAL_W: {
    sprite->location.y -= SPRITE_VELOCITY;
  } break;
  }
}

void anima_handle_event(anima_s *self, const SDL_Event *event) {
  assert(self != nullptr && event != nullptr);
}

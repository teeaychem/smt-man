#include "stumpless/log.h"

#include "anima.h"
#include "logic.h"

#include "render/constants.h"
#include "utils.h"
#include "utils/pairs.h"
#include <stdint.h>

Anima Anima_default(uint8_t id, char *name, PairI32 position, Surface surface) {
  return Anima_create(id, name, position, DOWN, DOWN, surface);
}

Anima Anima_create(uint8_t id, char *name, PairI32 pos, Direction intent, Direction momentum, Surface surface) {
  stumplog(LOG_INFO, "Creating anima: %s", name);

  Anima self = {
      .cond_resume = PTHREAD_COND_INITIALIZER,
      .id = id,
      .location = pos,
      .mVel = 1,
      .mtx_suspend = PTHREAD_MUTEX_INITIALIZER,
      .name = name,
      .size = PairI32_create(16, 16),
      .status = ANIMA_STATUS_SEARCH,
      .status_tick = 0,
      .surface = surface,
      .surface_offset = PairI32_create(0, 0),
  };

  atomic_init(&self.momentum, momentum);
  atomic_init(&self.intent, intent);
  atomic_init(&self.flag_suspend, false);

  return self;
}

void Anima_destroy(Anima *self) {
  Surface_destroy(&self->surface);
}

void Anima_touch(Anima *self, Mind *mind) {

  Anima_mind_innate(self, mind);

  {
    char cvc5_input_buffer[1024];
    const char *cvc5_error_msg;

    sprintf(cvc5_input_buffer, "(is_facing %s up)", self->name);
    cvc5_parser_set_str_input(mind->parser, CVC5_LANG, cvc5_input_buffer, "");
    mind->lot.anima[self->id].facing.up = cvc5_parser_next_term(mind->parser, &cvc5_error_msg);

    sprintf(cvc5_input_buffer, "(is_facing %s right)", self->name);
    cvc5_parser_set_str_input(mind->parser, CVC5_LANG, cvc5_input_buffer, "");
    mind->lot.anima[self->id].facing.right = cvc5_parser_next_term(mind->parser, &cvc5_error_msg);

    sprintf(cvc5_input_buffer, "(is_facing %s down)", self->name);
    cvc5_parser_set_str_input(mind->parser, CVC5_LANG, cvc5_input_buffer, "");
    mind->lot.anima[self->id].facing.down = cvc5_parser_next_term(mind->parser, &cvc5_error_msg);

    sprintf(cvc5_input_buffer, "(is_facing %s left)", self->name);
    cvc5_parser_set_str_input(mind->parser, CVC5_LANG, cvc5_input_buffer, "");
    mind->lot.anima[self->id].facing.left = cvc5_parser_next_term(mind->parser, &cvc5_error_msg);
  }
};

void Anima_handle_event(Anima *self, SDL_Event *event) {

  if (event->type == SDL_EVENT_KEY_DOWN && !event->key.repeat) {

    switch (event->key.key) {
    case SDLK_UP: {
      atomic_store(&self->intent, UP);
    } break;
    case SDLK_DOWN: {
      atomic_store(&self->intent, DOWN);
    } break;
    case SDLK_LEFT: {
      atomic_store(&self->intent, LEFT);
    } break;
    case SDLK_RIGHT: {
      atomic_store(&self->intent, RIGHT);
    } break;
    }
  }
}

void Anima_move(Anima *self, Maze *maze) {

  Direction momentum = atomic_load(&self->momentum);

  if (self->location.x % kSPRITE == 0 && self->location.y % kSPRITE == 0) {
    momentum = atomic_load(&self->intent);
    atomic_store(&self->momentum, momentum);

    PairI32 destination;

    PairI32 boundry_pixel = self->location;

    if (momentum == RIGHT || momentum == DOWN) {
      boundry_pixel.x += self->size.x - 1;
      boundry_pixel.y += self->size.y - 1;
    }

    steps_in_direction(&boundry_pixel, momentum, 1, &destination);

    if (Maze_is_open(maze, &destination)) {
      self->mVel = 1;
    } else {
      self->mVel = 0;
    }
  }

  switch (momentum) {
  case UP: {
    self->location.y -= self->mVel;
  } break;
  case RIGHT: {
    self->location.x += self->mVel;
  } break;
  case DOWN: {
    self->location.y += self->mVel;
  } break;
  case LEFT: {
    self->location.x -= self->mVel;
  } break;
  }
}

void Anima_mind_innate(Anima *self, Mind *mind) {

  Cvc5Command cvc5_cmd;
  const char *cvc5_error_msg;

  cvc5_parser_set_str_input(
      mind->parser,
      CVC5_LANG,
      "(declare-sort Anima 0)"
      "(declare-sort Direction 0)"

      "(declare-const gottlob Anima)"
      "(declare-const bertrand Anima)"
      "(declare-const anima Anima)"

      "(declare-const up    Direction)"
      "(declare-const right Direction)"
      "(declare-const down  Direction)"
      "(declare-const left  Direction)"

      "(declare-fun is_facing (Anima Direction) Bool)"

      "(assert (distinct up right down left))"
      "(assert (forall ((anima Anima)) (xor (is_facing anima up) (xor (is_facing anima right) (xor (is_facing anima down) (is_facing anima left))))))",
      "anima_innate");
  do {
    cvc5_cmd = cvc5_parser_next_command(mind->parser, &cvc5_error_msg);
    if (cvc5_error_msg) {
      printf("%s", cvc5_error_msg), exit(-1);
    }
    if (cvc5_cmd) {
      cvc5_cmd_invoke(cvc5_cmd, mind->solver, mind->sm);
    }
  } while (cvc5_cmd);
}

void Anima_deduct(Anima *self, Mind *mind) {

  cvc5_push(mind->solver, 1);

  int tmp_direction = random_in_range(1, 4);

  switch (tmp_direction) {
  case 1: {
    cvc5_assert_formula(mind->solver, cvc5_mk_term(mind->tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){cvc5_mk_term(mind->tm, CVC5_KIND_OR, 3, (Cvc5Term[3]){mind->lot.anima[self->id].facing.right, mind->lot.anima[self->id].facing.down, mind->lot.anima[self->id].facing.left})}));
  } break;

  case 2: {
    cvc5_assert_formula(mind->solver, cvc5_mk_term(mind->tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){cvc5_mk_term(mind->tm, CVC5_KIND_OR, 3, (Cvc5Term[3]){mind->lot.anima[self->id].facing.up, mind->lot.anima[self->id].facing.down, mind->lot.anima[self->id].facing.left})}));
  } break;

  case 3: {
    cvc5_assert_formula(mind->solver, cvc5_mk_term(mind->tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){cvc5_mk_term(mind->tm, CVC5_KIND_OR, 3, (Cvc5Term[3]){mind->lot.anima[self->id].facing.up, mind->lot.anima[self->id].facing.right, mind->lot.anima[self->id].facing.left})}));
  } break;

  case 4: {
    cvc5_assert_formula(mind->solver, cvc5_mk_term(mind->tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){cvc5_mk_term(mind->tm, CVC5_KIND_OR, 3, (Cvc5Term[3]){mind->lot.anima[self->id].facing.up, mind->lot.anima[self->id].facing.right, mind->lot.anima[self->id].facing.down})}));
  } break;
  }

  cvc5_check_sat(mind->solver);

  if (cvc5_term_get_boolean_value(cvc5_get_value(mind->solver, mind->lot.anima[self->id].facing.up))) {
    atomic_store(&self->intent, UP);

  } else if (cvc5_term_get_boolean_value(cvc5_get_value(mind->solver, mind->lot.anima[self->id].facing.right))) {
    atomic_store(&self->intent, RIGHT);

  } else if (cvc5_term_get_boolean_value(cvc5_get_value(mind->solver, mind->lot.anima[self->id].facing.down))) {
    atomic_store(&self->intent, DOWN);

  } else if (cvc5_term_get_boolean_value(cvc5_get_value(mind->solver, mind->lot.anima[self->id].facing.left))) {
    atomic_store(&self->intent, LEFT);
  } else {
    stumplog(LOG_ERR, "No direction"), exit(-1);
  }

  cvc5_pop(mind->solver, 1);
};

void Anima_instinct(Anima *self) {
}

void Anima_update_surface_offset(Anima *self) {

  switch (self->status) {

  case ANIMA_STATUS_SEARCH: {
    if (self->status_tick % 15 == 0) {
      self->surface_offset.x = (self->surface_offset.x + self->size.x) % self->surface.size.x;
    }
  } break;
  }
}

void Anima_fresh_tick(Anima *self) {
  self->status_tick += 1;
}

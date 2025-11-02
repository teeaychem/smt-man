#include <assert.h>
#include <stdio.h>

#include "cvc5/c/cvc5.h"
#include "cvc5/c/cvc5_parser.h"

#include "stumpless/log.h"

#include "anima.h"
#include "logic.h"
#include "maze.h"
#include "render/constants.h"
#include "sprite.h"
#include "utils.h"
#include "utils/pairs.h"

Mind Mind_default() {

  Cvc5TermManager *tm = cvc5_term_manager_new();
  Cvc5SymbolManager *symbols = cvc5_symbol_manager_new(tm);
  Cvc5 *solver = cvc5_new(tm);
  Cvc5InputParser *parser = cvc5_parser_new(solver, symbols);

  cvc5_set_logic(solver, CVC5_LOGIC);

  cvc5_set_option(solver, "produce-models", "true");
  cvc5_set_option(solver, "finite-model-find", "true");
  cvc5_set_option(solver, "model-var-elim-uneval", "false");
  cvc5_set_option(solver, "print-success", "true");

  Mind mind = {
      .parser = parser,
      .sm = symbols,
      .solver = solver,
      .tm = tm};

  return mind;
}

Anima Anima_default(char *name, PairI32 position, Sprite sprite) {
  return Anima_create(name, position, DOWN, DOWN, sprite);
}

Anima Anima_create(char *name, PairI32 pos, Direction intent, Direction momentum, Sprite sprite) {
  stumplog(LOG_INFO, "Creating anima: %s", name);

  AnimaTerms terms = {};

  Anima self = {.name = name,
                .pos = pos,
                .intent = intent,
                .momentum = momentum,
                .mVel = 2,
                .sprite = sprite,
                .mind = Mind_default(),
                .terms = terms};

  Anima_mind_innate(&self);

  {
    char cvc5_input_buffer[1024];

    sprintf(cvc5_input_buffer, "(is_facing %s up)", self.name);
    cvc5_parser_set_str_input(self.mind.parser, CVC5_LANG, cvc5_input_buffer, "");
    self.terms.facing_up = cvc5_parser_next_term(self.mind.parser, &cvc5_error_msg);

    sprintf(cvc5_input_buffer, "(is_facing %s right)", self.name);
    cvc5_parser_set_str_input(self.mind.parser, CVC5_LANG, cvc5_input_buffer, "");
    self.terms.facing_right = cvc5_parser_next_term(self.mind.parser, &cvc5_error_msg);

    sprintf(cvc5_input_buffer, "(is_facing %s down)", self.name);
    cvc5_parser_set_str_input(self.mind.parser, CVC5_LANG, cvc5_input_buffer, "");
    self.terms.facing_down = cvc5_parser_next_term(self.mind.parser, &cvc5_error_msg);

    sprintf(cvc5_input_buffer, "(is_facing %s left)", self.name);
    cvc5_parser_set_str_input(self.mind.parser, CVC5_LANG, cvc5_input_buffer, "");
    self.terms.facing_left = cvc5_parser_next_term(self.mind.parser, &cvc5_error_msg);
  }

  self.sprite.pos = PairI32_create(self.pos.x * sprite.size.x, self.pos.y * sprite.size.y);

  return self;
}

void Anima_destory(Anima *self) {
  Sprite_destroy(&self->sprite);
}

void Anima_handle_event(Anima *self, SDL_Event *event) {

  if (event->type == SDL_EVENT_KEY_DOWN && !event->key.repeat) {

    switch (event->key.key) {
    case SDLK_UP:
      self->intent = UP;
      break;
    case SDLK_DOWN:
      self->intent = DOWN;
      break;
    case SDLK_LEFT:
      self->intent = LEFT;
      break;
    case SDLK_RIGHT:
      self->intent = RIGHT;
      break;
    }
  }
}

void Anima_move_within(Anima *self, Maze *maze) {

  if (self->sprite.pos.x % self->sprite.size.x == 0 && self->sprite.pos.y % self->sprite.size.y == 0) {
    self->pos.x = self->sprite.pos.x / kTILE;
    self->pos.y = self->sprite.pos.y / kTILE;

    self->momentum = self->intent;

    PairI32 destination;

    steps_in_direction(&self->pos, self->momentum, 1, &destination);

    if (Maze_is_open(maze, &destination)) {
      self->mVel = 1;
    } else {
      self->mVel = 0;
    }
  }

  switch (self->momentum) {
  case UP: {
    self->sprite.pos.y -= self->mVel;
  } break;
  case RIGHT: {
    self->sprite.pos.x += self->mVel;
  } break;
  case DOWN: {
    self->sprite.pos.y += self->mVel;
  } break;
  case LEFT: {
    self->sprite.pos.x -= self->mVel;
  } break;
  }
}

void Anima_deduct(Anima *self) {

  cvc5_push(self->mind.solver, 1);

  int tmp_direction = random_in_range(1, 4);

  switch (tmp_direction) {
  case 1: {
    cvc5_assert_formula(self->mind.solver, cvc5_mk_term(self->mind.tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){cvc5_mk_term(self->mind.tm, CVC5_KIND_OR, 3, (Cvc5Term[3]){self->terms.facing_right, self->terms.facing_down, self->terms.facing_left})}));
  } break;

  case 2: {
    cvc5_assert_formula(self->mind.solver, cvc5_mk_term(self->mind.tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){cvc5_mk_term(self->mind.tm, CVC5_KIND_OR, 3, (Cvc5Term[3]){self->terms.facing_up, self->terms.facing_down, self->terms.facing_left})}));
  } break;

  case 3: {
    cvc5_assert_formula(self->mind.solver, cvc5_mk_term(self->mind.tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){cvc5_mk_term(self->mind.tm, CVC5_KIND_OR, 3, (Cvc5Term[3]){self->terms.facing_up, self->terms.facing_right, self->terms.facing_left})}));
  } break;

  case 4: {
    cvc5_assert_formula(self->mind.solver, cvc5_mk_term(self->mind.tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){cvc5_mk_term(self->mind.tm, CVC5_KIND_OR, 3, (Cvc5Term[3]){self->terms.facing_up, self->terms.facing_right, self->terms.facing_down})}));
  } break;
  }

  cvc5_check_sat(self->mind.solver);

  if (cvc5_term_get_boolean_value(cvc5_get_value(self->mind.solver, self->terms.facing_up))) {
    self->intent = UP;

  } else if (cvc5_term_get_boolean_value(cvc5_get_value(self->mind.solver, self->terms.facing_right))) {
    self->intent = RIGHT;

  } else if (cvc5_term_get_boolean_value(cvc5_get_value(self->mind.solver, self->terms.facing_down))) {
    self->intent = DOWN;

  } else if (cvc5_term_get_boolean_value(cvc5_get_value(self->mind.solver, self->terms.facing_left))) {
    self->intent = LEFT;
  } else {
    stumplog(LOG_ERR, "No direction"), exit(-1);
  }

  cvc5_pop(self->mind.solver, 1);
};

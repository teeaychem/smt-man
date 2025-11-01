#include "anima.h"
#include "cvc5/c/cvc5.h"
#include "cvc5/c/cvc5_parser.h"
#include "logic.h"
#include "maze.h"
#include "sprite.h"
#include "utils.h"
#include "utils/pairs.h"
#include <assert.h>
#include <stdio.h>

Anima Anima_default(char *name, Sprite sprite) {
  return Anima_create(name, PairI32_create(1, 1), DOWN, DOWN, sprite);
}

Anima Anima_create(char *name, PairI32 pos, Direction intent, Direction momentum, Sprite sprite) {

  Cvc5TermManager *tm = cvc5_term_manager_new();

  Cvc5 *mind = cvc5_new(l_tm);
  auto reader = cvc5_parser_new(mind, NULL);
  auto symbols = cvc5_parser_get_sm(reader);

  cvc5_set_logic(mind, "UFLIA");

  cvc5_set_option(mind, "produce-models", "true");
  cvc5_set_option(mind, "finite-model-find", "true");
  cvc5_set_option(mind, "model-var-elim-uneval", "false");
  cvc5_set_option(mind, "print-success", "true");

  AnimaTerms terms = {};

  Anima self = {.name = name,
                .pos = pos,
                .intent = intent,
                .momentum = momentum,
                .mVel = 2,
                .sprite = sprite,
                .mind = mind,
                .reader = reader,
                .symbols = symbols,
                .terms = terms};

  Anima_mind_innate(&self);

  cvc5_parser_set_str_input(self.reader, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "(is_facing gottlob up)", "");
  self.terms.facing_up = cvc5_parser_next_term(self.reader, &cvc5_error_msg);

  cvc5_parser_set_str_input(self.reader, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "(is_facing gottlob right)", "");
  self.terms.facing_right = cvc5_parser_next_term(self.reader, &cvc5_error_msg);

  cvc5_parser_set_str_input(self.reader, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "(is_facing gottlob down)", "");
  self.terms.facing_down = cvc5_parser_next_term(self.reader, &cvc5_error_msg);

  cvc5_parser_set_str_input(self.reader, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "(is_facing gottlob left)", "");
  self.terms.facing_left = cvc5_parser_next_term(self.reader, &cvc5_error_msg);

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
    self->pos.x = self->sprite.pos.x / 16;
    self->pos.y = self->sprite.pos.y / 16;

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

  cvc5_push(self->mind, 1);

  int tmp_direction = random_in_range(1, 4);

  Cvc5Command cmd;

  switch (tmp_direction) {
  case 1: {
    cvc5_assert_formula(self->mind,
                        Logic_not(
                            Logic_or(
                                3,
                                (Cvc5Term[3]){self->terms.facing_right,
                                              self->terms.facing_down,
                                              self->terms.facing_left})));
  } break;

  case 2: {
    cvc5_assert_formula(self->mind,
                        Logic_not(
                            Logic_or(
                                3,
                                (Cvc5Term[3]){self->terms.facing_up,
                                              self->terms.facing_down,
                                              self->terms.facing_left})));
  } break;

  case 3: {
    cvc5_assert_formula(self->mind,
                        Logic_not(
                            Logic_or(
                                3,
                                (Cvc5Term[3]){self->terms.facing_up,
                                              self->terms.facing_right,
                                              self->terms.facing_left})));
  } break;

  case 4: {
    cvc5_assert_formula(self->mind,
                        Logic_not(
                            Logic_or(
                                3,
                                (Cvc5Term[3]){self->terms.facing_up,
                                              self->terms.facing_right,
                                              self->terms.facing_down})));
  } break;
  }

  cvc5_check_sat(self->mind);

  if (cvc5_term_get_boolean_value(cvc5_get_value(self->mind, self->terms.facing_up))) {
    self->intent = UP;

  } else if (cvc5_term_get_boolean_value(cvc5_get_value(self->mind, self->terms.facing_right))) {
    self->intent = RIGHT;

  } else if (cvc5_term_get_boolean_value(cvc5_get_value(self->mind, self->terms.facing_down))) {
    self->intent = DOWN;

  } else if (cvc5_term_get_boolean_value(cvc5_get_value(self->mind, self->terms.facing_left))) {
    self->intent = LEFT;
  } else {
    printf("No direction..."), exit(-1);
  }

  cvc5_pop(self->mind, 1);
};

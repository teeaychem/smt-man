#include "anima.h"
#include "cvc5/c/cvc5_parser.h"
#include "render/constants.h"
#include "stumpless/log.h"

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
      .tm = tm,
      .lot = {},
  };

  return mind;
}

void Anima_LoT_facing(Anima *self, Mind *mind) {
  char cvc5_input_buffer[CVC5_INPUT_BUFFER_SIZE];
  const char *cvc5_error_msg;

  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {

    snprintf(cvc5_input_buffer, CVC5_INPUT_BUFFER_SIZE, "(anima_is_facing %s up)", ANIMA_NAMES[idx]);
    cvc5_parser_set_str_input(mind->parser, CVC5_LANG, cvc5_input_buffer, "");
    mind->lot.anima[idx].facing.up = cvc5_parser_next_term(mind->parser, &cvc5_error_msg);

    snprintf(cvc5_input_buffer, CVC5_INPUT_BUFFER_SIZE, "(anima_is_facing %s right)", ANIMA_NAMES[idx]);
    cvc5_parser_set_str_input(mind->parser, CVC5_LANG, cvc5_input_buffer, "");
    mind->lot.anima[idx].facing.right = cvc5_parser_next_term(mind->parser, &cvc5_error_msg);

    snprintf(cvc5_input_buffer, CVC5_INPUT_BUFFER_SIZE, "(anima_is_facing %s down)", ANIMA_NAMES[idx]);
    cvc5_parser_set_str_input(mind->parser, CVC5_LANG, cvc5_input_buffer, "");
    mind->lot.anima[idx].facing.down = cvc5_parser_next_term(mind->parser, &cvc5_error_msg);

    snprintf(cvc5_input_buffer, CVC5_INPUT_BUFFER_SIZE, "(anima_is_facing %s left)", ANIMA_NAMES[idx]);
    cvc5_parser_set_str_input(mind->parser, CVC5_LANG, cvc5_input_buffer, "");
    mind->lot.anima[idx].facing.left = cvc5_parser_next_term(mind->parser, &cvc5_error_msg);
  }
}

void Anima_LoT_animas(Anima *self, Mind *mind) {

  char cvc5_input_buffer[CVC5_INPUT_BUFFER_SIZE];
  Cvc5Command cvc5_cmd;
  const char *cvc5_error_msg;

  cvc5_parser_set_str_input(
      mind->parser,
      CVC5_LANG,
      "(declare-sort Anima 0)"
      "(declare-const anima Anima)",
      "animas");
  do {
    cvc5_cmd = cvc5_parser_next_command(mind->parser, &cvc5_error_msg);
    if (cvc5_error_msg) {
      printf("%s", cvc5_error_msg), exit(-1);
    }
    if (cvc5_cmd) {
      cvc5_cmd_invoke(cvc5_cmd, mind->solver, mind->sm);
    }
  } while (cvc5_cmd);

  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    snprintf(cvc5_input_buffer, CVC5_INPUT_BUFFER_SIZE, "(declare-const %s Anima)", ANIMA_NAMES[idx]);
    cvc5_parser_set_str_input(mind->parser, CVC5_LANG, cvc5_input_buffer, "");
    cvc5_cmd_invoke(cvc5_parser_next_command(mind->parser, &cvc5_error_msg), mind->solver, mind->sm);
  }
}

void Anima_LoT_direction(Anima *self, Mind *mind) {

  Cvc5Command cvc5_cmd;
  const char *cvc5_error_msg;

  cvc5_parser_set_str_input(
      mind->parser,
      CVC5_LANG,
      "(declare-sort Direction 0)"

      "(declare-const up    Direction)"
      "(declare-const right Direction)"
      "(declare-const down  Direction)"
      "(declare-const left  Direction)"

      "(declare-fun anima_is_facing (Anima Direction) Bool)"

      "(assert (distinct up right down left))"
      "(assert (forall ((anima Anima)) (xor (anima_is_facing anima up) (xor (anima_is_facing anima right) (xor (anima_is_facing anima down) (anima_is_facing anima left))))))",
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

void Anima_touch(Anima *self, Mind *mind) {

  Anima_LoT_animas(self, mind);
  Anima_LoT_direction(self, mind);

  Anima_LoT_facing(self, mind);
};

// deduction

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
    atomic_store(&self->pov.anima[self->id].intent, UP);

  } else if (cvc5_term_get_boolean_value(cvc5_get_value(mind->solver, mind->lot.anima[self->id].facing.right))) {
    atomic_store(&self->pov.anima[self->id].intent, RIGHT);

  } else if (cvc5_term_get_boolean_value(cvc5_get_value(mind->solver, mind->lot.anima[self->id].facing.down))) {
    atomic_store(&self->pov.anima[self->id].intent, DOWN);

  } else if (cvc5_term_get_boolean_value(cvc5_get_value(mind->solver, mind->lot.anima[self->id].facing.left))) {
    atomic_store(&self->pov.anima[self->id].intent, LEFT);
  } else {
    stumplog(LOG_ERR, "No direction"), exit(-1);
  }

  cvc5_pop(mind->solver, 1);
};

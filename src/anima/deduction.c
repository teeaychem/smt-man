
#include "anima.h"
#include "logic.h"
#include <assert.h>
#include <stdio.h>

void Anima_mind_innate(Anima *self) {

  cvc5_parser_set_str_input(
      self->mind.parser,
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
    cvc5_cmd = cvc5_parser_next_command(self->mind.parser, &cvc5_error_msg);
    if (cvc5_error_msg) {
      printf("%s", cvc5_error_msg), exit(-1);
    }
    if (cvc5_cmd) {
      cvc5_cmd_invoke(cvc5_cmd, self->mind.solver, self->mind.sm);
    }
  } while (cvc5_cmd);
}

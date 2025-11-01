
#include "anima.h"
#include "logic.h"
#include <assert.h>
#include <stdio.h>

void Anima_mind_innate(Anima *self) {

  cvc5_parser_set_str_input(
      self->reader,
      CVC5_INPUT_LANGUAGE_SMT_LIB_2_6,
      "(declare-sort Anima 0)"
      "(declare-sort Direction 0)"

      "(declare-const gottlob Anima)"

      "(declare-const up Direction)"
      "(declare-const right Direction)"
      "(declare-const down Direction)"
      "(declare-const left Direction)"

      "(assert (distinct up right down left))"

      "(declare-fun is_facing (Anima Direction) Bool)"

      "(assert (forall ((a Anima)) (xor (is_facing a up) (xor (is_facing a right) (xor (is_facing a down) (is_facing a left))))))",
      "anima_innate");

  Cvc5Command cmd;
  do {
    cmd = cvc5_parser_next_command(self->reader, &cvc5_error_msg);
    if (cvc5_error_msg) {
      printf("%s", cvc5_error_msg), exit(-1);
    }
    if (cmd) {
      cvc5_cmd_invoke(cmd, self->mind, self->symbols);
    }
  } while (cmd);
}

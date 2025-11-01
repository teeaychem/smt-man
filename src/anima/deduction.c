
#include "anima.h"
#include "logic.h"
#include <assert.h>
#include <stdio.h>

void Anima_mind_innate(Anima *self) {

  cvc5_parser_set_str_input(
      self->parser,
      CVC5_LANG,
      "(assert (forall ((a Anima)) (xor (is_facing a up) (xor (is_facing a right) (xor (is_facing a down) (is_facing a left))))))",
      "anima_innate");
  do {
    cvc5_cmd = cvc5_parser_next_command(self->parser, &cvc5_error_msg);
    if (cvc5_error_msg) {
      printf("%s", cvc5_error_msg), exit(-1);
    }
    if (cvc5_cmd) {
      cvc5_cmd_invoke(cvc5_cmd, self->mind, l_symbols);
    }
  } while (cvc5_cmd);
}

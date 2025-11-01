
#include "anima.h"
#include "logic.h"
#include <assert.h>
#include <stdio.h>

void Anima_deduction_setup(Anima *self) {

  const char *error_msg;

  printf("Parsing k commands\n");
  fflush(stdout);

  cvc5_parser_set_str_input(
      self->reader,
      CVC5_INPUT_LANGUAGE_SMT_LIB_2_6,
      "(assert (forall ((a Anima)) (xor (is_facing a up) (xor (is_facing a right) (xor (is_facing a down) (is_facing a left))))))",
      "k");

  printf("Finished parsing k commands\n");

  Cvc5Command cmd;

  do {
    cmd = cvc5_parser_next_command(self->reader, &error_msg);
    if (error_msg != NULL) {
      printf("%s", error_msg);
      exit(-1);
    }

    if (cmd) {
      printf("Executing command %s:\n", cvc5_cmd_to_string(cmd));
      printf("%s", cvc5_cmd_invoke(cmd, self->mind, self->symbols));
    }

  } while (cmd);

  printf("Finished parsing commands\n");
  // now, check sat with the solver
  Cvc5Result r = cvc5_check_sat(self->mind);
  printf("expected: unsat\n");
  printf("result: %s\n", cvc5_result_to_string(r));
}

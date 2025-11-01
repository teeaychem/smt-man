#include "cvc5/c/cvc5.h"
#include "logic.h"
#include <assert.h>
#include <cvc5/c/cvc5_parser.h>
#include <stdio.h>

Cvc5TermManager *l_tm;
char cvc5_input_buffer[1024];

void logic_init() {
  l_tm = cvc5_term_manager_new();
}

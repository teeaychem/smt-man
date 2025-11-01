#include "cvc5/c/cvc5.h"
#include "logic.h"
#include <assert.h>
#include <cvc5/c/cvc5_parser.h>
#include <stdio.h>

Cvc5TermManager *l_tm;

void setup_logic() {
  l_tm = cvc5_term_manager_new();
}

Cvc5Term Logic_not(const Cvc5Term term) {
  return cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){term});
};

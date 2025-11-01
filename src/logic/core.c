#include "cvc5/c/cvc5.h"
#include "logic.h"
#include <assert.h>
#include <cvc5/c/cvc5_parser.h>
#include <stdio.h>

Cvc5TermManager *l_tm;

inline Cvc5Term Logic_not(const Cvc5Term term);

inline Cvc5Term Logic_or(size_t size, const Cvc5Term children[]);

void setup_logic() {
  l_tm = cvc5_term_manager_new();
}

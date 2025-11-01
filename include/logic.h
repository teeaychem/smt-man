#pragma once

#include "cvc5/c/cvc5.h"

extern Cvc5TermManager *l_tm;

struct anima_terms_t {
  Cvc5Term facing_up;
  Cvc5Term facing_right;
  Cvc5Term facing_down;
  Cvc5Term facing_left;
};

typedef struct anima_terms_t AnimaTerms;

void setup_logic();

Cvc5Term Logic_not(const Cvc5Term term);

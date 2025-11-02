#pragma once

#include "cvc5/c/cvc5.h"

static const Cvc5InputLanguage CVC5_LANG = CVC5_INPUT_LANGUAGE_SMT_LIB_2_6;
static const char *CVC5_LOGIC = "UFLIA";

struct anima_terms_t {
  Cvc5Term facing_up;
  Cvc5Term facing_right;
  Cvc5Term facing_down;
  Cvc5Term facing_left;
};

typedef struct anima_terms_t AnimaTerms;

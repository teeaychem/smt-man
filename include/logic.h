#pragma once

#include "cvc5/c/cvc5.h"
#include "cvc5/c/cvc5_parser.h"

static const Cvc5InputLanguage CVC5_LANG = CVC5_INPUT_LANGUAGE_SMT_LIB_2_6;
static const char *CVC5_LOGIC = "UFLIA";

const char *cvc5_error_msg;
Cvc5Command cvc5_cmd;
extern char cvc5_input_buffer[1024];

struct anima_terms_t {
  Cvc5Term facing_up;
  Cvc5Term facing_right;
  Cvc5Term facing_down;
  Cvc5Term facing_left;
};

typedef struct anima_terms_t AnimaTerms;

void logic_init();

#pragma once

#include "cvc5/c/cvc5.h"
#include "cvc5/c/cvc5_parser.h"

static const Cvc5InputLanguage CVC5_LANG = CVC5_INPUT_LANGUAGE_SMT_LIB_2_6;
static const char* CVC5_LOGIC = "UFLIA";

extern Cvc5TermManager *l_tm;
extern Cvc5SymbolManager *l_symbols;

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

void logic_setup_symbols();

void logic_setup_foundation(Cvc5 *cvc5, Cvc5InputParser *parser);

static inline Cvc5Term Logic_not(const Cvc5Term term) {
  return cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){term});
};

static inline Cvc5Term Logic_or(size_t size, const Cvc5Term children[]) {
  return cvc5_mk_term(l_tm, CVC5_KIND_OR, size, children);
};

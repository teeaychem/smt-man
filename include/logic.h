#pragma once

#include "cvc5/c/cvc5.h"

extern Cvc5TermManager *l_tm;

const char *cvc5_error_msg;

struct anima_terms_t {
  Cvc5Term facing_up;
  Cvc5Term facing_right;
  Cvc5Term facing_down;
  Cvc5Term facing_left;
};

typedef struct anima_terms_t AnimaTerms;

void logic_init();

void logic_setup_common();

static inline Cvc5Term Logic_not(const Cvc5Term term) {
    return cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){term});
};

static inline Cvc5Term Logic_or(size_t size, const Cvc5Term children[]) {
   return cvc5_mk_term(l_tm, CVC5_KIND_OR, size, children);
};

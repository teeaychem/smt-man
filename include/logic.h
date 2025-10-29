#pragma once

#include "cvc5/c/cvc5.h"

struct sorts_t {
  Cvc5Sort anima;
  Cvc5Sort direction;

  // One
  Cvc5Sort is_anima;

  // Two
  Cvc5Sort is_anima_facing;
};

struct language_t {
  struct sorts_t sorts;
};

extern Cvc5TermManager *l_tm;

extern struct language_t llang;

void setup_logic();

Cvc5 *cvc5_mind_default();

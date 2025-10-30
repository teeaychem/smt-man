#pragma once

#include "cvc5/c/cvc5.h"

struct l_direction_t {
  Cvc5Term up;
  Cvc5Term right;
  Cvc5Term down;
  Cvc5Term left;
};

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

  struct l_direction_t direction;

  Cvc5Term pFacing;
};

extern Cvc5TermManager *l_tm;

extern struct language_t llang;

void setup_logic();

Cvc5 *cvc5_mind_default();

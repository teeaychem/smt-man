#pragma once

#include "cvc5/c/cvc5.h"
#include "render/constants.h"

static const Cvc5InputLanguage CVC5_LANG = CVC5_INPUT_LANGUAGE_SMT_LIB_2_6;
static const char *CVC5_LOGIC = "UFLIA";

typedef struct smt_pov_facing_t SmtPovFacing;
struct smt_pov_facing_t {
  Cvc5Term up;
  Cvc5Term right;
  Cvc5Term down;
  Cvc5Term left;
};

typedef struct smt_anima_t SmtAnima;
struct smt_anima_t {
  SmtPovFacing facing;
};

typedef struct smt_lot_t SmtLot;
struct smt_lot_t {
  SmtAnima anima;
};

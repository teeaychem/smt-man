#pragma once

#include "cvc5/c/cvc5.h"
#include "constants.h"
#include "utils.h"

constexpr Cvc5InputLanguage CVC5_LANG = CVC5_INPUT_LANGUAGE_SMT_LIB_2_6;

constexpr size_t SMT_INPUT_BUFFER_SIZE = 1024;

typedef enum anima_status_t AnimaStatus;
enum anima_status_t {
  ANIMA_STATUS_SEARCH,
};

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
  SmtAnima anima[ANIMA_COUNT];
};

// World things

typedef struct smt_world_anima_t SmtWorldAnima;
struct smt_world_anima_t {
  _Atomic(PairI32) location;
  _Atomic(Direction) intent;
  _Atomic(Direction) momentum;
  _Atomic(AnimaStatus) status;
};

typedef struct smt_world_t SmtWorld;
struct smt_world_t {
  SmtWorldAnima anima[ANIMA_COUNT];
};

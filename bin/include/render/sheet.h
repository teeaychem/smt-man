#pragma once

#include "generic/pairs.h"

#include "sprite/anima.h"
#include "sprite/persona.h"

struct sheet_offsets_t {
  struct {
    struct {
      Pair_uint32 e[2];
      Pair_uint32 s[2];
      Pair_uint32 w[2];
      Pair_uint32 n[2];
    } direction;
    Pair_uint32 thinking[2];
  } anima;

  struct {
    Pair_uint32 eating[3];

  } persona;
};
typedef struct sheet_offsets_t SheetOffsets;

extern SheetOffsets sheet_data;

Pair_uint32 Sheet_anima_offset(const anima_s *anima, const Situation *situation);

Pair_uint32 Sheet_persona_offset(const persona_s *persona, const Situation *situation);

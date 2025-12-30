#pragma once

#include "generic/pairs.h"
#include "lyf/anima.h"
#include "lyf/persona.h"

struct sheet_offsets_t {
  struct {
    struct {
      Pair_uint32 rt[2];
      Pair_uint32 dn[2];
      Pair_uint32 lt[2];
      Pair_uint32 up[2];
    } direction;
    Pair_uint32 thinking[2];
  } anima;

  struct {
    Pair_uint32 eating[3];

  } persona;
};
typedef struct sheet_offsets_t SheetOffsets;

extern SheetOffsets sheet_data;

Pair_uint32 Sheet_anima_offset(const Anima *anima);

Pair_uint32 Sheet_persona_offset(const Persona *persona, Situation *situation);

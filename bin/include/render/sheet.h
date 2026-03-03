#pragma once

#include "generic/pairs.h"

#include "sprite/anima.h"
#include "sprite/persona.h"

struct sheet_offset_t {
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
typedef struct sheet_offset_t sheet_offset_s;

extern sheet_offset_s sheet_data;

Pair_uint32 sheet_offset_anima(const anima_s *anima, const situation_s *situation);

Pair_uint32 sheet_offset_persona(const persona_s *persona, const situation_s *situation);

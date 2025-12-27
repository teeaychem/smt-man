#pragma once

#include <stdint.h>

#include "lyf/anima.h"
#include "generic/pairs.h"

struct sheet_offsets_t {
  struct {
    uint32_t size;
    struct {
      uint32_t frames;
      Pair_uint32 rt[2];
      Pair_uint32 dn[2];
      Pair_uint32 lt[2];
      Pair_uint32 up[2];
    } direction;

  } anima;
};
typedef struct sheet_offsets_t SheetOffsets;

extern SheetOffsets sheet_data;

Pair_uint32 Sheet_anima_offset(const Anima *anima);

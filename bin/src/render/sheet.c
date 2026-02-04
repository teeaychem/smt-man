#include <stdatomic.h>

#include "macro.h"
#include "render/sheet.h"

SheetOffsets sheet_data = {
    .anima = {
        .direction = {
            .e = {{83, 1}, {83, 18}},
            .s = {{83, 35}, {83, 52}},
            .w = {{83, 69}, {83, 86}},
            .n = {{83, 103}, {83, 120}},
        },
        .thinking = {{83, 137}, {83, 154}},
    },

    .persona = {.eating = {{134, 1}, {134, 18}, {134, 35}}},
};

Pair_uint32 Sheet_anima_offset(const Anima *anima) {

  switch (atomic_load(&anima->smt.situation.animas[anima->id].direction_actual)) {
  case CARDINAL_NONE: {
    constexpr size_t thinking_frames = ARRAY_LEN(sheet_data.anima.thinking);
    return sheet_data.anima.thinking[anima->tick_action % thinking_frames];
  } break;
  case CARDINAL_N: {
    constexpr size_t fames_n = ARRAY_LEN(sheet_data.anima.direction.n);
    return sheet_data.anima.direction.n[anima->tick_action % fames_n];
  } break;
  case CARDINAL_E: {
    constexpr size_t fames_e = ARRAY_LEN(sheet_data.anima.direction.e);
    return sheet_data.anima.direction.e[anima->tick_action % fames_e];
  } break;
  case CARDINAL_S: {
    constexpr size_t fames_s = ARRAY_LEN(sheet_data.anima.direction.s);
    return sheet_data.anima.direction.s[anima->tick_action % fames_s];
  } break;
  case CARDINAL_W: {
    constexpr size_t fames_w = ARRAY_LEN(sheet_data.anima.direction.w);
    return sheet_data.anima.direction.w[anima->tick_action % fames_w];
  } break;
  }
}

Pair_uint32 Sheet_persona_offset(const Persona *persona, const Situation *situation) {
  constexpr size_t eating_frames = ARRAY_LEN(sheet_data.persona.eating);
  return sheet_data.persona.eating[persona->tick_action % eating_frames];
}

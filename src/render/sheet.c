#include <stdatomic.h>

#include "macro.h"
#include "render/sheet.h"

SheetOffsets sheet_data = {
    .anima = {
        .direction = {
            .rt = {{1, 83}, {18, 83}},
            .dn = {{35, 83}, {52, 83}},
            .lt = {{69, 83}, {86, 83}},
            .up = {{103, 83}, {120, 83}},
        },
        .thinking = {{137, 83}, {154, 83}},
    },

    .persona = {.eating = {{1, 134}, {18, 134}, {35, 134}}},
};

Pair_uint32 Sheet_anima_offset(const Anima *anima) {

  switch (atomic_load(&anima->mind.view.anima[anima->id].direction_actual)) {
  case DIRECTION_NONE: {
    constexpr size_t thinking_frames = ARRAY_LEN(sheet_data.anima.thinking);
    return sheet_data.anima.thinking[anima->tick_action % thinking_frames];
  } break;
  case DIRECTION_N: {
    constexpr size_t up_frames = ARRAY_LEN(sheet_data.anima.direction.up);
    return sheet_data.anima.direction.up[anima->tick_action % up_frames];
  } break;
  case DIRECTION_E: {
    constexpr size_t rt_frames = ARRAY_LEN(sheet_data.anima.direction.rt);
    return sheet_data.anima.direction.rt[anima->tick_action % rt_frames];
  } break;
  case DIRECTION_S: {
    constexpr size_t dn_frames = ARRAY_LEN(sheet_data.anima.direction.dn);
    return sheet_data.anima.direction.dn[anima->tick_action % dn_frames];
  } break;
  case DIRECTION_W: {
    constexpr size_t lt_frames = ARRAY_LEN(sheet_data.anima.direction.lt);
    return sheet_data.anima.direction.lt[anima->tick_action % lt_frames];
  } break;
  }
}

Pair_uint32 Sheet_persona_offset(const Persona *persona, const Situation *situation) {
  constexpr size_t eating_frames = ARRAY_LEN(sheet_data.persona.eating);
  return sheet_data.persona.eating[persona->tick_action % eating_frames];
}

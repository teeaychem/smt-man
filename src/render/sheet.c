#include "render/sheet.h"

SheetOffsets sheet_data = {
    .anima = {
        .size = 16,
        .direction = {
            .frames = 2,
            .rt = {{.x = 1, .y = 83}, {.x = 18, .y = 83}},
            .dn = {{.x = 35, .y = 83}, {.x = 52, .y = 83}},
            .lt = {{.x = 69, .y = 83}, {.x = 86, .y = 83}},
            .up = {{.x = 103, .y = 83}, {.x = 120, .y = 83}},
        }},
};

Pair_uint32 Sheet_anima_offset(const Anima *anima) {

  size_t offset = anima->tick_action % sheet_data.anima.direction.frames;

  switch (anima->momentum) {

  case NORTH: {
    return sheet_data.anima.direction.up[offset];
  } break;
  case EAST: {
    return sheet_data.anima.direction.rt[offset];
  } break;
  case SOUTH: {
    return sheet_data.anima.direction.dn[offset];
  } break;
  case WEST: {
    return sheet_data.anima.direction.lt[offset];
  } break;
  }
}

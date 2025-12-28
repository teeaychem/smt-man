#pragma once

#include "enums.h"
#include <stdint.h>

struct persona_t {
  uint8_t pixel_size;
  uint8_t tick_action;
  Direction direction_intent;
};
typedef struct persona_t Persona;

void Persona_default(Persona *persona, uint8_t pixel_size);

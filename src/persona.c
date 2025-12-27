#include "lyf/persona.h"

void Persona_default(Persona *persona, uint8_t pixel_size, Pair_uint8 location, Direction direction) {
  *persona = (Persona){
      .pixel_size = pixel_size,
      .direction = direction,
      .location = location,

      .tick.actions = 0,
      .tick.frames = 0,
      .tick.frames_per_action = 6,

  };
}

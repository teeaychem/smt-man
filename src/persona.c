#include "lyf/persona.h"

void Persona_default(Persona *persona, uint8_t pixel_size) {
  *persona = (Persona){
      .pixel_size = pixel_size,
      .tick_action = 0,
  };
}

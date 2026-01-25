#include <assert.h>
#include <stdatomic.h>

#include "SML/sprite/persona.h"

void Persona_default(Persona *persona, Situation *situation) {
  *persona = (Persona){
      .direction_intent = CARDINAL_E,
      .tick_action = 0,
  };
}

void Persona_drop(Persona *self) {
  assert(self != nullptr);
}

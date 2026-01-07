#include <assert.h>
#include <stdatomic.h>
#include <stdio.h>

#include "sprites/persona.h"

void Persona_default(Persona *persona, Situation *situation) {
  Pair_uint8 location = atomic_load(&situation->persona.location);

  printf("Setting up persona t location: %dx%d\n", location.x, location.y);

  *persona = (Persona){
      .direction_intent = DIRECTION_E,
      .tick_action = 0,
  };
}

void Persona_drop(Persona *self) {
  assert(self != nullptr);
}

#include <stdatomic.h>

#include "constants.h"
#include "generic/bitvec.h"
#include "sprites/persona.h"
#include "sprites/sprite.h"

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

void Persona_handle_event(Persona *self, const Maze *maze, Situation *situation, const SDL_Event *event) {
  if (event->type == SDL_EVENT_KEY_DOWN && !event->key.repeat) {

    switch (event->key.key) {
    case SDLK_UP: {
      self->direction_intent = DIRECTION_N;
    } break;
    case SDLK_DOWN: {
      self->direction_intent = DIRECTION_S;
    } break;
    case SDLK_LEFT: {
      self->direction_intent = DIRECTION_W;
    } break;
    case SDLK_RIGHT: {
      self->direction_intent = DIRECTION_E;
    } break;
    }
  }
}


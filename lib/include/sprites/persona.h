#pragma once

#include <stdint.h>

#include <SDL3/SDL_events.h>

#include "enums.h"
#include "logic/situation.h"
#include "maze.h"

struct persona_t {
  /// Incremented on each tick an action is performed
  uint8_t tick_action;

  Direction direction_intent;
};
typedef struct persona_t Persona;

void Persona_default(Persona *persona, Situation *situation);

void Persona_drop(Persona *self);

void Persona_handle_event(Persona *self, const Maze *maze, Situation *situation, const SDL_Event *event);

#pragma once

#include <stdint.h>

#include <SDL3/SDL_events.h>

#include "enums.h"
#include "generic/pairs.h"
#include "logic/situation.h"
#include "maze.h"
#include "render/palette.h"

struct persona_t {
  /// Size of the associated sprite, as a square
  uint8_t sprite_size;
  /// Incremented on each tick an action is performed
  uint8_t tick_action;
  /// Location of the anima sprite
  Pair_uint32 sprite_location;
  /// Pallette
  Pallete pallete;

  Direction direction_intent;
};
typedef struct persona_t Persona;

void Persona_default(Persona *persona, Situation *situation, uint8_t sprite_size);

void Persona_destroy(Persona *self);

void Persona_handle_event(Persona *self, Maze *maze, Situation *situation, SDL_Event *event);

void Persona_on_frame(Persona *self, Maze *maze, Situation *situation);

void Persona_on_tile(Persona *self, Maze *maze, Situation *situation);

void Persona_off_tile(Persona *self, Maze *maze, Situation *situation);

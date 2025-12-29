#pragma once

#include <stdint.h>

#include <SDL3/SDL_events.h>

#include "enums.h"
#include "generic/pairs.h"
#include "logic/situation.h"
#include "maze.h"

struct persona_t {
  uint8_t pixel_size;

  uint8_t tick_action;

  Direction direction_intent;
};
typedef struct persona_t Persona;

void Persona_default(Persona *persona, uint8_t pixel_size);

void Persona_destroy(Persona *self);

void Persona_handle_event(Persona *self, SDL_Event *event);

void Persona_on_frame(Persona *self, Maze *maze, Situation *situation, Pair_uint32 *sprite_location);

void Persona_on_tile(Persona *self, Maze *maze, Situation *situation, Pair_uint32 *sprite_location);

#pragma once

#include <stdint.h>

#include <SDL3/SDL_events.h>

#include "enums.h"
#include "generic/pairs.h"
#include "logic/situation.h"
#include "maze.h"

struct persona_t {
  /// Size of the associated sprite, as a square
  uint8_t sprite_size;
  /// Incremented on each tick an action is performed
  uint8_t tick_action;
  /// Location of the anima sprite
  Pair_uint32 sprite_location;

  Direction direction_intent;
};
typedef struct persona_t Persona;

void Persona_default(Persona *persona, Situation *situation, const uint8_t sprite_size, uint32_t offset_n);

void Persona_drop(Persona *self);

void Persona_handle_event(Persona *self, const Maze *maze, Situation *situation, const SDL_Event *event);

void Persona_on_frame(Persona *self, const Maze *maze, Situation *situation, uint32_t tile_pixels, uint32_t offset_n);

void Persona_on_tile(Persona *self, Situation *situation, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n);

void Persona_off_tile(Persona *self, Situation *situation, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n);

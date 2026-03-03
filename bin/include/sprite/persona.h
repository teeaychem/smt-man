#pragma once

#include <stdint.h>

#include "generic/enums.h"

#include "SML/logic/situation.h"
#include "SML/maze.h"

#include "render/sprite.h"

struct persona_t {
  /// Incremented on each tick an action is performed
  uint8_t tick_action;

  cardinal_e direction_intent;
};
typedef struct persona_t persona_s;

void persona_ctor(persona_s *self, Situation *situation);

void persona_dtor(persona_s *self);

void persona_on_frame(persona_s *self, Sprite *sprite, const maze_s *maze, Situation *situation, uint32_t tile_pixels, uint32_t offset_n);

void persona_handle_event(persona_s *self, Situation *situation, const SDL_Event *event);

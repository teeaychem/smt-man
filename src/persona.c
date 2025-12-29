#include "lyf/persona.h"
#include "constants.h"
#include "generic/bitvec.h"
#include <stdatomic.h>

void Persona_default(Persona *persona, Situation *situation, uint8_t pixel_size) {
  Pair_uint8 situation_location = atomic_load(&situation->persona.location);

  *persona = (Persona){
      .direction_intent = EAST,
      .sprite_location = {.x = ((uint32_t)situation_location.x) * TILE_PIXELS,
                          .y = ((uint32_t)situation_location.y) * TILE_PIXELS},
      .sprite_size = pixel_size,
      .pallete = {
          .a = 0x00000000,
          .b = 0x00000000,
          .c = 0x00000000,
          .d = 0xff808080,
      },
      .tick_action = 0,
  };
}

void Persona_destroy(Persona *self) {
  assert(self != nullptr);
}

void Persona_handle_event(Persona *self, Maze *maze, Situation *situation, SDL_Event *event) {
  if (event->type == SDL_EVENT_KEY_DOWN && !event->key.repeat) {

    switch (event->key.key) {
    case SDLK_UP: {
      self->direction_intent = NORTH;
    } break;
    case SDLK_DOWN: {
      self->direction_intent = SOUTH;
    } break;
    case SDLK_LEFT: {
      self->direction_intent = WEST;
    } break;
    case SDLK_RIGHT: {
      self->direction_intent = EAST;
    } break;
    }
  }
}

void Persona_on_frame(Persona *self, Maze *maze, Situation *situation) {

  uint32_t movement = atomic_load(&situation->persona.movement_pattern);
  movement = uint32_rotl1(movement);
  atomic_store(&situation->persona.movement_pattern, movement);

  if ((movement & 0x10000000) == 0) {
    return;
  }

  self->tick_action += 1;

  bool centred = self->sprite_location.x % TILE_PIXELS == 0 && self->sprite_location.y % TILE_PIXELS == 0;

  if (centred) {
    situation->persona.location = Maze_location_from_sprite(&self->sprite_location);

    if (Maze_tile_in_direction_is_path(maze, situation->persona.location, self->direction_intent)) {
      atomic_store(&situation->persona.direction_actual, self->direction_intent);
    } else {
      atomic_store(&situation->persona.direction_actual, DIRECTION_NONE);
    }
  }

  switch (atomic_load(&situation->persona.direction_actual)) {
  case DIRECTION_NONE: {
  } break;
  case NORTH: {
    self->sprite_location.y -= SPRITE_VELOCITY;
  } break;
  case EAST: {
    self->sprite_location.x += SPRITE_VELOCITY;
  } break;
  case SOUTH: {
    self->sprite_location.y += SPRITE_VELOCITY;
  } break;
  case WEST: {
    self->sprite_location.x -= SPRITE_VELOCITY;
  } break;
  }
}

void Persona_on_tile(Persona *self, Maze *maze, Situation *situation) {

  Pair_uint8 location = Maze_location_from_sprite(&self->sprite_location);
  /// Update location
  atomic_store(&situation->persona.location, location);

  /// Update direction
  if (Maze_tile_in_direction_is_path(maze, location, self->direction_intent)) {
    atomic_store(&situation->persona.direction_actual, self->direction_intent);
  } else {
    atomic_store(&situation->persona.direction_actual, DIRECTION_NONE);
  }
}

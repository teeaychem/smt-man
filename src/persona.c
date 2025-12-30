#include "lyf/persona.h"
#include "constants.h"
#include "generic/bitvec.h"
#include "render.h"
#include <stdatomic.h>

void Persona_default(Persona *persona, Situation *situation, uint8_t sprite_size) {
  Pair_uint8 situation_location = atomic_load(&situation->persona.location);

  *persona = (Persona){
      .direction_intent = DIRECTION_E,
      .sprite_location = {.x = ((uint32_t)situation_location.x) * TILE_PIXELS,
                          .y = ((uint32_t)situation_location.y) * TILE_PIXELS},
      .sprite_size = sprite_size,
      .pallete = {
          .a = 0x00000000,
          .b = 0x00000000,
          .c = 0x00000000,
          .d = 0xff00ffff,
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

void Persona_on_frame(Persona *self, Maze *maze, Situation *situation) {

  uint32_t movement = atomic_load(&situation->persona.movement_pattern);
  movement = uint32_rotl1(movement);
  atomic_store(&situation->persona.movement_pattern, movement);

  if ((movement & 0x10000000) == 0) {
    return;
  }

  self->tick_action += 1;

  if (Renderer_u32_location_is_tile(self->sprite_location)) {
    Persona_on_tile(self, maze, situation);
  } else {
    Persona_off_tile(self, maze, situation);
  }

  switch (atomic_load(&situation->persona.direction_actual)) {
  case DIRECTION_NONE: {
    // Do nothing
  } break;
  case DIRECTION_N: {
    self->sprite_location.y -= SPRITE_VELOCITY;
  } break;
  case DIRECTION_E: {
    self->sprite_location.x += SPRITE_VELOCITY;
  } break;
  case DIRECTION_S: {
    self->sprite_location.y += SPRITE_VELOCITY;
  } break;
  case DIRECTION_W: {
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
  } else if (Maze_tile_in_direction_is_path(maze, location, situation->persona.direction_actual)) {
    // Keep current direction.
  } else {
    atomic_store(&situation->persona.direction_actual, DIRECTION_NONE);
  }
}

void Persona_off_tile(Persona *self, Maze *maze, Situation *situation) {

  Pair_uint8 location = Maze_location_from_sprite(&self->sprite_location);

  if ((self->direction_intent | situation->persona.direction_actual) == (DIRECTION_E | DIRECTION_W) ||
      (self->direction_intent | situation->persona.direction_actual) == (DIRECTION_S | DIRECTION_N)) {
    /// Update direction
    if (Maze_tile_in_direction_is_path(maze, location, self->direction_intent)) {
      atomic_store(&situation->persona.direction_actual, self->direction_intent);
    } else if (Maze_tile_in_direction_is_path(maze, location, situation->persona.direction_actual)) {
      // Keep current direction.
    } else {
      atomic_store(&situation->persona.direction_actual, DIRECTION_NONE);
    }
  }
}

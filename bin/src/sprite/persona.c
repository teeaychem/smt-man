#include <assert.h>

#include "generic/bitvec.h"

#include "SML/maze.h"

#include "render/sprite.h"
#include "sprite/persona.h"

void persona_ctor(persona_s *self, __attribute__((__unused__)) situation_s *situation) {
  *self = (persona_s){
      .direction_intent = CARDINAL_NONE,
      .tick_action = 0,
  };
}

void persona_dtor(persona_s *self) {
  assert(self != nullptr);
}

void persona_on_tile(persona_s *self, situation_s *situation, const maze_s *maze, Pair_uint8 maze_location) {

  /// Update location
  atomic_store(&situation->persona.location, maze_location);

  /// Update direction
  if (maze_tile_in_direction_is_path(maze, maze_location, self->direction_intent)) {
    atomic_store(&situation->persona.direction_actual, self->direction_intent);
  } else if (maze_tile_in_direction_is_path(maze, maze_location, situation->persona.direction_actual)) {
    // Keep current direction.
  } else {
    atomic_store(&situation->persona.direction_actual, CARDINAL_NONE);
  }
}

void persona_off_tile(persona_s *self, situation_s *situation, const maze_s *maze, Pair_uint8 maze_location) {

  if ((self->direction_intent | situation->persona.direction_actual) == (CARDINAL_E | CARDINAL_W) ||
      (self->direction_intent | situation->persona.direction_actual) == (CARDINAL_S | CARDINAL_N)) {
    /// Update direction
    if (maze_tile_in_direction_is_path(maze, maze_location, self->direction_intent)) {
      atomic_store(&situation->persona.direction_actual, self->direction_intent);
    } else if (maze_tile_in_direction_is_path(maze, maze_location, situation->persona.direction_actual)) {
      // Keep current direction.
    } else {
      atomic_store(&situation->persona.direction_actual, CARDINAL_NONE);
    }
  }
}

void persona_on_frame(persona_s *self, sprite_s *sprite, const maze_s *maze, situation_s *situation, uint32_t tile_pixels, uint32_t offset_n) {

  uint32_t movement = atomic_load(&situation->persona.movement_pattern);
  movement = uint32_rotl1(movement);
  atomic_store(&situation->persona.movement_pattern, movement);

  if ((movement & 0x10000000) == 0) {
    return;
  }

  self->tick_action += 1;

  Pair_uint8 maze_location = sprite_maze_location(&sprite->location, tile_pixels, offset_n);

  if (sprite_is_centered_on_tile(sprite->location, tile_pixels)) {
    persona_on_tile(self, situation, maze, maze_location);
  } else {
    persona_off_tile(self, situation, maze, maze_location);
  }

  switch (atomic_load(&situation->persona.direction_actual)) {
  case CARDINAL_NONE: {
    // Do nothing
  } break;
  case CARDINAL_N: {
    sprite->location.x -= SPRITE_FRAME_VELOCITY;
  } break;
  case CARDINAL_E: {
    sprite->location.y += SPRITE_FRAME_VELOCITY;
  } break;
  case CARDINAL_S: {
    sprite->location.x += SPRITE_FRAME_VELOCITY;
  } break;
  case CARDINAL_W: {
    sprite->location.y -= SPRITE_FRAME_VELOCITY;
  } break;
  }
}

void persona_handle_event(persona_s *self, const SDL_Event *event) {
  if (event->type == SDL_EVENT_KEY_DOWN && !event->key.repeat) {

    switch (event->key.key) {
    case SDLK_UP: {
      self->direction_intent = CARDINAL_N;
    } break;
    case SDLK_DOWN: {
      self->direction_intent = CARDINAL_S;
    } break;
    case SDLK_LEFT: {
      self->direction_intent = CARDINAL_W;
    } break;
    case SDLK_RIGHT: {
      self->direction_intent = CARDINAL_E;
    } break;
    }
  }
}

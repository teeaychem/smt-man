#include "generic/bitvec.h"

#include "render/sprite.h"

void Persona_on_tile(Persona *self, Sprite *sprite, Situation *situation, const Maze *maze, Pair_uint8 maze_location) {

  /// Update location
  atomic_store(&situation->persona.location, maze_location);

  /// Update direction
  if (Maze_tile_in_direction_is_path(maze, maze_location, self->direction_intent)) {
    atomic_store(&situation->persona.direction_actual, self->direction_intent);
  } else if (Maze_tile_in_direction_is_path(maze, maze_location, situation->persona.direction_actual)) {
    // Keep current direction.
  } else {
    atomic_store(&situation->persona.direction_actual, CARDINAL_NONE);
  }
}

void Persona_off_tile(Persona *self, Sprite *sprite, Situation *situation, const Maze *maze, Pair_uint8 maze_location) {

  if ((self->direction_intent | situation->persona.direction_actual) == (CARDINAL_E | CARDINAL_W) ||
      (self->direction_intent | situation->persona.direction_actual) == (CARDINAL_S | CARDINAL_N)) {
    /// Update direction
    if (Maze_tile_in_direction_is_path(maze, maze_location, self->direction_intent)) {
      atomic_store(&situation->persona.direction_actual, self->direction_intent);
    } else if (Maze_tile_in_direction_is_path(maze, maze_location, situation->persona.direction_actual)) {
      // Keep current direction.
    } else {
      atomic_store(&situation->persona.direction_actual, CARDINAL_NONE);
    }
  }
}

void Persona_on_frame(Persona *self, Sprite *sprite, const Maze *maze, Situation *situation, uint32_t tile_pixels, uint32_t offset_n) {

  uint32_t movement = atomic_load(&situation->persona.movement_pattern);
  movement = uint32_rotl1(movement);
  atomic_store(&situation->persona.movement_pattern, movement);

  if ((movement & 0x10000000) == 0) {
    return;
  }

  self->tick_action += 1;

  Pair_uint8 maze_location = Sprite_maze_location(&sprite->location, tile_pixels, offset_n);

  if (Sprite_is_centered_on_tile(sprite->location, tile_pixels)) {
    Persona_on_tile(self, sprite, situation, maze, maze_location);
  } else {
    Persona_off_tile(self, sprite, situation, maze, maze_location);
  }

  switch (atomic_load(&situation->persona.direction_actual)) {
  case CARDINAL_NONE: {
    // Do nothing
  } break;
  case CARDINAL_N: {
    sprite->location.x -= SPRITE_VELOCITY;
  } break;
  case CARDINAL_E: {
    sprite->location.y += SPRITE_VELOCITY;
  } break;
  case CARDINAL_S: {
    sprite->location.x += SPRITE_VELOCITY;
  } break;
  case CARDINAL_W: {
    sprite->location.y -= SPRITE_VELOCITY;
  } break;
  }
}

void Persona_handle_event(Persona *self, const Maze *maze, Situation *situation, const SDL_Event *event) {
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

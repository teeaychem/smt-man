#include "lyf/persona.h"
#include "constants.h"
#include "generic/bitvec.h"
#include <stdatomic.h>

void Persona_default(Persona *persona, uint8_t pixel_size) {
  *persona = (Persona){
      .pixel_size = pixel_size,
      .tick_action = 0,
  };
}

void Persona_destroy(Persona *self) {
  assert(self != nullptr);
}

void Persona_handle_event(Persona *self, SDL_Event *event) {
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

void Persona_on_frame(Persona *self, Maze *maze, Situation *situation, Pair_uint32 *sprite_location) {

  uint32_t movement = atomic_load(&situation->persona.movement_pattern);
  movement = uint32_rotl1(movement);
  atomic_store(&situation->persona.movement_pattern, movement);

  if ((movement & 0x10000000) == 0) {
    return;
  }

  self->tick_action += 1;

  bool centred = sprite_location->x % TILE_PIXELS == 0 && sprite_location->y % TILE_PIXELS == 0;

  if (centred) {
  }

  switch (atomic_load(&situation->persona.direction)) {
  case DIRECTION_NONE: {
  } break;
  case NORTH: {
    sprite_location->y -= SPRITE_VELOCITY;
  } break;
  case EAST: {
    sprite_location->x += SPRITE_VELOCITY;
  } break;
  case SOUTH: {
    sprite_location->y += SPRITE_VELOCITY;
  } break;
  case WEST: {
    sprite_location->x -= SPRITE_VELOCITY;
  } break;
  }
}

void Persona_on_tile(Persona *self, Maze *maze, Situation *situation, Pair_uint32 *sprite_location) {
  /// Scale sprite location
  Pair_uint8 location = {.x = (uint8_t)(sprite_location->x / TILE_PIXELS),
                         .y = (uint8_t)(sprite_location->y / TILE_PIXELS)};

  bool intent_ok = false;
  switch (self->direction_intent) {
  case DIRECTION_NONE: {
    intent_ok = false;
  } break;
  case NORTH: {
    intent_ok = (location.y != Maze_first_row(maze)) && Maze_abstract_is_path(maze, location.x, location.y - 1);
  } break;
  case EAST: {
    intent_ok = (location.x + 2 < maze->size.x) && Maze_abstract_is_path(maze, location.x + 1, location.y);
  } break;
  case SOUTH: {
    intent_ok = (location.y != Maze_last_row(maze)) && Maze_abstract_is_path(maze, location.x, location.y + 1);
  } break;
  case WEST: {
    intent_ok = (0 < location.x) && Maze_abstract_is_path(maze, location.x - 1, location.y);
  } break;
  }

  Direction direction = DIRECTION_NONE;
  if (intent_ok) {
    direction = self->direction_intent;
  }

  { // Store block
    atomic_store(&situation->persona.direction, direction);
    atomic_store(&situation->persona.location, location);
  }
}

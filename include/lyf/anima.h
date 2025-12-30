#pragma once

#include <pthread.h>
#include <stdint.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "enums.h"
#include "generic/pairs.h"
#include "lyf/anima/mind.h"
#include "render/palette.h"

struct anima_t {
  /// Uniqie identifier in [0..ANIMA_COUNT]
  uint8_t id;
  /// Size of the associated sprite, as a square
  uint8_t sprite_size;
  /// Incremented on each tick an action is performed
  uint8_t tick_action;
  /// Location of the anima sprite
  Pair_uint32 sprite_location;
  /// Pallette
  Pallete pallete;

  /// Tools for contacting the anima from a different thread
  struct {
    _Atomic(bool) flag_suspend;

    pthread_mutex_t mtx_suspend;

    pthread_cond_t cond_resume;
  } contact;

  Mind mind;
};
typedef struct anima_t Anima;

// Methods

void Anima_default(Anima *anima, uint8_t id, uint8_t sprite_size, Pair_uint8 location, Direction direction);

void Anima_destroy(Anima *self);

void Anima_handle_event(Anima *self, SDL_Event *event);

void Anima_on_frame(Anima *self, Maze *maze);

void Anima_on_tile(Anima *self, Maze *maze);

void Anima_instinct(Anima *self);

#pragma once

#include <pthread.h>
#include <stdint.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "enums.h"
#include "generic/pairs.h"
#include "sprites/anima/mind.h"

struct anima_t {
  /// Uniqie identifier in [0..ANIMA_COUNT]
  uint8_t id;
  /// Size of the associated sprite, as a square
  uint8_t sprite_size;
  /// Incremented on each tick an action is performed
  uint8_t tick_action;
  /// Location of the anima sprite
  Pair_uint32 sprite_location;

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

void Anima_default(Anima *anima, const uint8_t id, const uint8_t sprite_size, const Pair_uint8 location, const Direction direction, uint32_t offset_n);

void Anima_destroy(Anima *self);

void Anima_handle_event(Anima *self, const SDL_Event *event);

void Anima_on_frame(Anima *self, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n);

void Anima_on_tile(Anima *self, const Maze *maze, uint32_t tile_pixels, uint32_t offset_n);

void Anima_instinct(Anima *self);

#pragma once

#include <pthread.h>
#include <stdint.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "anima/mind.h"
#include "enums.h"
#include "generic/pairs.h"

struct anima_t {
  // Identifier
  uint8_t id;
  uint8_t scale;
  struct {
    /// Increments each time an action is taken.
    uint8_t actions;
    /// Increments on each frame.
    uint8_t frames;
    /// The number of actions to take, per frame.
    uint8_t frames_per_action;
  } tick;
  Direction momentum;

  // Tools for contacting the anima from a different thread
  struct {
    _Atomic(bool) flag_suspend;
    pthread_mutex_t mtx_suspend;
    pthread_cond_t cond_resume;
  } contact;

  Mind mind;
};
typedef struct anima_t Anima;

// Methods

void Anima_default(Anima *anima, uint8_t id, uint8_t scale, Pair_uint8 location, Direction direction);

void Anima_destroy(Anima *self);

void Anima_handle_event(Anima *self, SDL_Event *event);

void Anima_on_frame(Anima *self, Maze *maze, Pair_uint32 *sprite_location);

void Anima_sync_abstract(Anima *self, Maze *maze, Pair_uint32 *sprite_location);

void Anima_instinct(Anima *self);

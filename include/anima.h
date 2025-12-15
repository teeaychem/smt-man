#pragma once

#include <pthread.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>
#include <stdint.h>

#include "anima/mind.h"
#include "generic/pairs.h"
#include "utils.h"

struct anima_t {
  // Identifier
  uint8_t id;
  uint32_t scale;
  uint8_t tick;

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

void Anima_default(Anima *anima, uint8_t id, uint32_t scale, Pair_uint8 location, Direction direction);

void Anima_destroy(Anima *self);

void Anima_handle_event(Anima *self, SDL_Event *event);

void Anima_on_frame(Anima *self, Maze *maze, Pair_uint32 *sprite_location);

void Anima_sync_abstract(Anima *self, Maze *maze);

void Anima_instinct(Anima *self);

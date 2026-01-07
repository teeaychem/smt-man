#pragma once

#include <pthread.h>
#include <stdint.h>

#include "enums.h"
#include "generic/pairs.h"
#include "sprites/anima/mind.h"

struct anima_t {
  /// Uniqie identifier in [0..ANIMA_COUNT]
  uint8_t id;
  /// Incremented on each tick an action is performed
  uint8_t tick_action;

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

void Anima_default(Anima *anima, const uint8_t id, const Pair_uint8 location, const Direction direction, uint32_t offset_n);

void Anima_destroy(Anima *self);

void Anima_instinct(Anima *self);

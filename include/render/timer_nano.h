#pragma once

#include <SDL3/SDL.h>

struct timer_nano_t {
  bool is_paused;
  uint64_t paused_ticks;

  bool is_started;
  uint64_t started_ticks;
};
typedef struct timer_nano_t TimerNano;

static inline TimerNano TimerNano_default() {
  TimerNano timer = {
      .is_paused = false,
      .paused_ticks = 0,

      .started_ticks = 0,
      .is_started = false,
  };
  return timer;
}

static inline void TimerNano_start(TimerNano *self) {
  self->is_paused = false;
  self->paused_ticks = 0;

  self->is_started = true;
  self->started_ticks = SDL_GetTicksNS();
}

static inline void TimerNano_stop(TimerNano *self) {
  self->is_paused = false;
  self->paused_ticks = 0;

  self->is_started = false;
  self->started_ticks = 0;
}

static inline void TimerNano_pause(TimerNano *self) {
  if (self->is_started && !self->is_paused) {
    self->is_paused = true;
    self->paused_ticks = SDL_GetTicksNS() - self->started_ticks;

    self->is_started = false;
    self->started_ticks = 0;
  }
}

static inline void TimerNano_resume(TimerNano *self) {
  if (self->is_started && self->is_paused) {
    self->is_paused = false;
    self->paused_ticks = 0;

    self->started_ticks = SDL_GetTicksNS() - self->paused_ticks;
  }
}

static inline uint64_t TimerNano_get_ticks(TimerNano *self) {
  if (self->is_started) {
    if (self->is_paused) {
      return self->paused_ticks;
    } else {
      return SDL_GetTicksNS() - self->started_ticks;
    }
  } else {
    return 0;
  }
}

static inline bool TimerNano_is_started(TimerNano *self) {
  return self->is_started;
}

static inline bool TimerNano_is_paused(TimerNano *self) {
  return self->is_paused && self->is_started;
}

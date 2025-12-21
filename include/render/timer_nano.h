#pragma once

#include <SDL3/SDL.h>

struct timer_nano_t {
  Uint64 mStartedTicks;
  Uint64 mPausedTicks;

  bool mPaused;
  bool mStarted;
};
typedef struct timer_nano_t TimerNano;

static inline TimerNano TimerNano_default() {
  TimerNano timer = {.mStartedTicks = 0, .mPausedTicks = 0, .mPaused = false, .mStarted = false};
  return timer;
}

static inline void TimerNano_start(TimerNano *self) {
  self->mStarted = true;
  self->mPaused = false;
  self->mStartedTicks = SDL_GetTicksNS();
  self->mPausedTicks = 0;
}

static inline void TimerNano_stop(TimerNano *self) {
  self->mStarted = false;
  self->mPaused = false;
  self->mStartedTicks = 0;
  self->mPausedTicks = 0;
}

static inline void TimerNano_pause(TimerNano *self) {
  if (self->mStarted && !self->mPaused) {
    self->mStarted = false;
    self->mPaused = true;
    self->mPausedTicks = SDL_GetTicksNS() - self->mStartedTicks;
    self->mStartedTicks = 0;
  }
}

static inline void TimerNano_resume(TimerNano *self) {
  if (self->mStarted && self->mPaused) {
    self->mPaused = false;
    self->mStartedTicks = SDL_GetTicksNS() - self->mPausedTicks;
    self->mPausedTicks = 0;
  }
}

static inline Uint64 TimerNano_get_ticks(TimerNano *self) {
  Uint64 time = 0;

  if (self->mStarted) {
    if (self->mPaused) {
      time = self->mPausedTicks;
    } else {
      time = SDL_GetTicksNS() - self->mStartedTicks;
    }
  }

  return time;
}

static inline bool TimerNano_is_started(TimerNano *self) {
  return self->mStarted;
}

static inline bool TimerNano_is_paused(TimerNano *self) {
  return self->mPaused && self->mStarted;
}

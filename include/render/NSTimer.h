#pragma once

#include <SDL3/SDL.h>

struct ns_timer_t {
  Uint64 mStartedTicks;
  Uint64 mPausedTicks;

  bool mPaused;
  bool mStarted;
};
typedef struct ns_timer_t NSTimer;

static inline NSTimer NSTimer_default() {
  NSTimer timer = {.mStartedTicks = 0, .mPausedTicks = 0, .mPaused = false, .mStarted = false};
  return timer;
}

static inline void NSTimer_start(NSTimer *self) {
  self->mStarted = true;
  self->mPaused = false;
  self->mStartedTicks = SDL_GetTicksNS();
  self->mPausedTicks = 0;
}

static inline void NSTimer_stop(NSTimer *self) {
  self->mStarted = false;
  self->mPaused = false;
  self->mStartedTicks = 0;
  self->mPausedTicks = 0;
}

static inline void NSTimer_pause(NSTimer *self) {
  if (self->mStarted && !self->mPaused) {
    self->mStarted = false;
    self->mPaused = true;
    self->mPausedTicks = SDL_GetTicksNS() - self->mStartedTicks;
    self->mStartedTicks = 0;
  }
}

static inline void NSTimer_unpause(NSTimer *self) {
  if (self->mStarted && self->mPaused) {
    self->mPaused = false;
    self->mStartedTicks = SDL_GetTicksNS() - self->mPausedTicks;
    self->mPausedTicks = 0;
  }
}

static inline Uint64 NSTimer_get_ticks(NSTimer *self) {
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

static inline bool NSTimer_is_started(NSTimer *self) {
  return self->mStarted;
}

static inline bool NSTimer_is_paused(NSTimer *self) {
  return self->mPaused && self->mStarted;
}

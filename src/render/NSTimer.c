#include "render/NSTimer.h"
#include <SDL3/SDL.h>

NSTimer NSTimer_default() {
  NSTimer timer = {.mStartedTicks = 0, .mPausedTicks = 0, .mPaused = false, .mStarted = false};
  return timer;
}

void NSTimer_start(NSTimer *self) {
  self->mStarted = true;
  self->mPaused = false;
  self->mStartedTicks = SDL_GetTicksNS();
  self->mPausedTicks = 0;
}

void NSTimer_stop(NSTimer *self) {
  self->mStarted = false;
  self->mPaused = false;
  self->mStartedTicks = 0;
  self->mPausedTicks = 0;
}

void NSTimer_pause(NSTimer *self) {
  if (self->mStarted && !self->mPaused) {
    self->mStarted = false;
    self->mPaused = true;
    self->mPausedTicks = SDL_GetTicksNS() - self->mStartedTicks;
    self->mStartedTicks = 0;
  }
}

void NSTimer_unpause(NSTimer *self) {
  if (self->mStarted && self->mPaused) {
    self->mPaused = false;
    self->mStartedTicks = SDL_GetTicksNS() - self->mPausedTicks;
    self->mPausedTicks = 0;
  }
}

Uint64 NSTimer_getTicksNS(NSTimer *self) {
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

bool NSTimer_isStarted(NSTimer *self) {
  return self->mStarted;
}

bool NSTimer_isPaused(NSTimer *self) {
  return self->mPaused && self->mStarted;
}

#include <SDL3/SDL.h>

#include "utils.hpp"

NSTimer::NSTimer() : mStartedTicks{0}, mPausedTicks{0}, mPaused{false}, mStarted{false} {};

void NSTimer::start() {
  this->mStarted = true;
  this->mPaused = false;
  this->mStartedTicks = SDL_GetTicksNS();
  this->mPausedTicks = 0;
}

void NSTimer::stop() {
  this->mStarted = false;
  this->mPaused = false;
  this->mStartedTicks = 0;
  this->mPausedTicks = 0;
}

void NSTimer::pause() {
  if (this->mStarted && !this->mPaused) {
    this->mStarted = false;
    this->mPaused = true;
    this->mPausedTicks = SDL_GetTicksNS() - mStartedTicks;
    this->mStartedTicks = 0;
  }
}

void NSTimer::unpause() {
  if (this->mStarted && this->mPaused) {
    this->mPaused = false;
    this->mStartedTicks = SDL_GetTicksNS() - mPausedTicks;
    this->mPausedTicks = 0;
  }
}

Uint64 NSTimer::getTicksNS() {
  Uint64 time{0};

  if (this->mStarted) {
    if (this->mPaused) {
      time = this->mPausedTicks;
    } else {
      time = SDL_GetTicksNS() - this->mStartedTicks;
    }
  }

  return time;
}

bool NSTimer::isStarted() {
  return mStarted;
}

bool NSTimer::isPaused() {
  return mPaused && mStarted;
}

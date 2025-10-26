#pragma once

#include <SDL3/SDL_main.h>

enum Direction {
  up,
  right,
  down,
  left,
};

struct NSTimer {
  NSTimer();

  void start();
  void stop();
  void pause();
  void unpause();

  Uint64 getTicksNS();

  bool isStarted();
  bool isPaused();

  Uint64 mStartedTicks;
  Uint64 mPausedTicks;

  bool mPaused;
  bool mStarted;
};

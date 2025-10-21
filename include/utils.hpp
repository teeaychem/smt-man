#pragma once

#include <SDL3/SDL_main.h>

enum Direction {
  up,
  right,
  down,
  left,
};

class Position {
public:
  int x;
  int y;

  Position(int x, int y) : x(x), y(y) {};
};

class NSTimer {
public:
  NSTimer();

  void start();
  void stop();
  void pause();
  void unpause();

  Uint64 getTicksNS();

  bool isStarted();
  bool isPaused();

private:
  Uint64 mStartedTicks;

  Uint64 mPausedTicks;

  bool mPaused;
  bool mStarted;
};

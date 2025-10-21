#pragma once

#include <SDL3/SDL_main.h>
#include <cstdint>

enum Direction {
  up,
  right,
  down,
  left,
};

class Position {
public:
  uint32_t x;
  uint32_t y;

  Position(uint32_t x, uint32_t y) : x(x), y(y) {};
};

struct Size {

  uint32_t w;
  uint32_t h;

  constexpr Size(uint32_t w_, uint32_t h_) : w(w_), h(h_) {};

  constexpr uint32_t area() const {
    return w * h;
  }

  constexpr Size scale(uint32_t value) const {
    return Size{this->w * value, this->h * value};
  };
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

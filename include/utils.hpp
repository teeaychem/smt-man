#pragma once

#include <SDL3/SDL_main.h>
#include <cstdint>
#include <string>

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

  std::string toString() {
    std::string out{};
    out.append(std::to_string(this->x));
    out.push_back(',');
    out.append(std::to_string(this->y));
    return out;
  }
};

struct Size {

  uint32_t H;
  uint32_t W;

  constexpr Size(uint32_t w_, uint32_t h_) : W(w_), H(h_) {};

  constexpr uint32_t area() const {
    return W * H;
  }

  constexpr Size scale(uint32_t value) const {
    return Size{this->W * value, this->H * value};
  };

  Size() : H(0), W(0) {}
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

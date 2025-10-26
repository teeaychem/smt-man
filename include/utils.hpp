#pragma once

#include "spdlog/spdlog.h"
#include <SDL3/SDL_main.h>
#include <cstdint>
#include <limits>
#include <string>
#include <vector>

enum Direction {
  up,
  right,
  down,
  left,
};

template <typename T>
struct NVec {
  std::vector<T> elements;

  ~NVec() {};

  NVec() { this->elements = std::vector<T>{}; };

  NVec(T a, T b) { this->elements = std::vector<T>{a, b}; }

  NVec(const NVec<T> &other) { this->elements = other.elements; }

  NVec(NVec<T> &&other) : elements(std::move(other.elements)) {}

  T elem(size_t index) const {
    if (index < this->elements.size()) {
      return this->elements[index];
    } else {
      spdlog::critical("Bad NVec element index {} of {}", index, this->elements.size());
      exit(-1);
    }
  }

  T x() const { return this->elem(0); }
  T y() const { return this->elem(1); }

  T area() const {
    T area{1};
    for (auto &elem : this->elements) {
      area *= elem;
    }
    return area;
  }

  void multiply(T value) {
    for (size_t idx{0}; idx < this->elements.size(); ++idx) {
      this->elements[idx] *= value;
    }
  }

  std::string toString() {
    std::string out{};
    size_t index = 0;
    for (; index < this->elements.size() - 1; ++index) {
      out.append(std::to_string(this->elements[index]));
      out.push_back(',');
    }
    out.append(std::to_string(this->elements[index]));
    return out;
  }
};

typedef NVec<uint32_t> Size;

struct Position {
  uint32_t x;
  uint32_t y;

  ~Position() {};

  Position(uint32_t x, uint32_t y) : x(x), y(y) {};

  Position inDirection(Direction direction, uint32_t steps) {
    Position todo = *this;

    switch (direction) {
    case up: {
      todo.y = (steps <= todo.y) ? (todo.y - steps) : 0;
    } break;
    case right: {
      todo.x = (steps <= (std::numeric_limits<uint32_t>::max() - todo.x)) ? todo.x + steps : std::numeric_limits<uint32_t>::max();
    } break;
    case down: {
      todo.y = (steps <= (std::numeric_limits<uint32_t>::max() - todo.y)) ? todo.y + steps : std::numeric_limits<uint32_t>::max();
    } break;
    case left: {
      todo.x = (steps <= todo.x) ? (todo.x - steps) : 0;
    } break;
    }

    return todo;
  }

  std::string toString() {
    std::string out{};
    out.append(std::to_string(this->x));
    out.push_back(',');
    out.append(std::to_string(this->y));
    return out;
  }
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

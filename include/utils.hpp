#pragma once

#include "stumpless/log.h"
#include <SDL3/SDL_main.h>
#include <cstdint>
#include <limits>
#include <string>
#include <sys/syslog.h>
#include <vector>

enum Direction {
  up,
  right,
  down,
  left,
};

typedef uint32_t nvec_t;

struct NVec {
  std::vector<nvec_t> elements;

  ~NVec() {};

  NVec() { this->elements = std::vector<nvec_t>{}; };

  NVec(nvec_t a, nvec_t b) { this->elements = std::vector<nvec_t>{a, b}; }

  NVec(const NVec &other) { this->elements = other.elements; }

  NVec(NVec &&other) : elements(std::move(other.elements)) {}

  nvec_t elem(size_t index) const {
    if (index < this->elements.size()) {
      return this->elements[index];
    } else {
      stumplog(LOG_CRIT, "Bad NVec element index {} of {}", index, this->elements.size());
      exit(-1);
    }
  }

  nvec_t x() const { return this->elem(0); }
  nvec_t y() const { return this->elem(1); }

  nvec_t area() const {
    nvec_t area{1};
    for (auto &elem : this->elements) {
      area *= elem;
    }
    return area;
  }

  void multiply(nvec_t value) {
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

inline NVec nvec_direction_steps(NVec nvec, Direction direction, uint32_t steps) {
  NVec todo = nvec;

  switch (direction) {
  case up: {
    todo.elements[1] = (steps <= todo.elements[1]) ? (todo.elements[1] - steps) : 0;
  } break;
  case right: {
    todo.elements[0] = (steps <= (std::numeric_limits<uint32_t>::max() - todo.elements[0])) ? todo.elements[0] + steps : std::numeric_limits<uint32_t>::max();
  } break;
  case down: {
    todo.elements[1] = (steps <= (std::numeric_limits<uint32_t>::max() - todo.elements[1])) ? todo.elements[1] + steps : std::numeric_limits<uint32_t>::max();
  } break;
  case left: {
    todo.elements[0] = (steps <= todo.elements[0]) ? (todo.elements[0] - steps) : 0;
  } break;
  }

  return todo;
}

typedef NVec Size;
typedef NVec Position;

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

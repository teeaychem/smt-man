#pragma once

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include <cstring>
#include <limits>
#include <random>

struct colour_thing {
  std::pair<Uint8, bool> state[3];
  Uint8 current{0};

  std::random_device rd{};
  std::minstd_rand0 gen{rd()};
  std::uniform_int_distribution<> distr{0, 2};

  int operator[](std::size_t i) const { return state[i].first; }

  void advance() {
    auto current = distr(gen);

    if (state[current].first == std::numeric_limits<Uint8>::max()) {
      state[current].second = false;
    } else if (state[current].first == std::numeric_limits<Uint8>::min()) {
      state[current].second = true;
    }

    if (state[current].second) {
      state[current].first = (state[current].first + 1);
    } else {
      state[current].first = (state[current].first - 1);
    }
  }
};

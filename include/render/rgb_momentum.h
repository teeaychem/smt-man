#pragma once

#include <stdint.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "random.h"

struct rgb_momentum_t {
  struct {
    uint8_t value;
    bool momentum;
  } state[3];
};
typedef struct rgb_momentum_t RGBMomentum;

static void rgb_momentum_advance(RGBMomentum *self) {
  int current = random_in_range(0, 2);

  if (self->state[current].value == UINT8_MAX) {
    self->state[current].momentum = false;
  } else if (self->state[current].value == 0) {
    self->state[current].momentum = true;
  }

  if (self->state[current].momentum) {
    self->state[current].value = (self->state[current].value + 1);
  } else {
    self->state[current].value = (self->state[current].value - 1);
  }
}

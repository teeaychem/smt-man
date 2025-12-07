#pragma once

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include <stdint.h>

struct ValueMomentum {
  Uint8 value;
  bool momentum;
};

struct rgbVM_t {
  struct ValueMomentum state[3];
};

typedef struct rgbVM_t rgbVM;

void rgbVM_advance(rgbVM *self);

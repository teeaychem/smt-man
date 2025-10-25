
#pragma once

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "sprite.hpp"
#include "unethical.hpp"
#include "utils.hpp"
#include "visual/textures.hpp"

struct Anima {

  static constexpr int kAnimaVelocity = 2;

  Anima();

  void handleEvent(SDL_Event &event);

  void move();

  const Position *position() const { return &this->pos; }


  Position pos;

  Direction intent;
  Direction momentum;

  int mVel;

  Sprite sprite;
};

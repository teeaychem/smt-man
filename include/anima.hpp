
#pragma once

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "visual/textures.hpp"

class Anima {
public:
  static constexpr int kAnimaHeight = 10;
  static constexpr int kAnimaWidth = 10;

  static constexpr int kAnimaVelocity = 1;

  Anima();

  void handleEvent(SDL_Event &event);

  void move();

  void render(SDL_Renderer *gRenderer);

  bool spawn(SDL_Renderer *gRenderer);

private:
  int mPosX;
  int mPosY;

  int mVelX;
  int mVelY;

  AnimaTexture gAnimaTexture;
};

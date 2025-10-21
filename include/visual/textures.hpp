#pragma once

#include "utils.hpp"
#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include <SDL3_image/SDL_image.h>

class AnimaTexture {
public:
  static constexpr float kOriginalSize = -1.f;

  AnimaTexture();

  ~AnimaTexture();

  void destroy();

  void setColor(Uint8 r, Uint8 g, Uint8 b);

  void setAlpha(Uint8 alpha);

  Size getSize() const;
  bool isLoaded() const;

private:
  SDL_Texture *aTexture;

  Size size;
};

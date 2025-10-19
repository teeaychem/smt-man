#pragma once

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include <SDL3_image/SDL_image.h>

class AnimaTexture {
public:
  static constexpr float kOriginalSize = -1.f;

  AnimaTexture();

  ~AnimaTexture();

  bool mkRectangle(SDL_Renderer *renderer, int w, int h);

  void destroy();

  void setColor(Uint8 r, Uint8 g, Uint8 b);

  void setAlpha(Uint8 alpha);

  void render(SDL_Renderer *gRenderer, float x, float y, float width = kOriginalSize, float height = kOriginalSize);

  int getWidth();
  int getHeight();
  bool isLoaded();

private:
  SDL_Texture *aTexture;

  int tWidth;
  int tHeight;
};

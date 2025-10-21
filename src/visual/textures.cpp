#include "visual/textures.hpp"
#include "unethical.hpp"

AnimaTexture::AnimaTexture() : aTexture{nullptr},
                               tWidth{tileSize},
                               tHeight{tileSize} {
}

AnimaTexture::~AnimaTexture() {
  destroy();
}

bool AnimaTexture::mkRectangle(SDL_Renderer *renderer, int w, int h) {
  destroy();

  SDL_Surface *gSurface = SDL_CreateSurface(w, h, SDL_PIXELFORMAT_RGBA8888);

  if (gSurface == nullptr) {
    SDL_Log("SDL error: %s\n", SDL_GetError());
    return false;
  }

  bool surfaceKeyOk = SDL_SetSurfaceColorKey(gSurface, true, SDL_MapSurfaceRGB(gSurface, 0xFF, 0xFF, 0xFF));

  if (!surfaceKeyOk) {
    SDL_Log("SDL error: %s\n", SDL_GetError());
    return false;
  }

  SDL_FillSurfaceRect(gSurface, nullptr, SDL_MapSurfaceRGBA(gSurface, 50, 50, 50, 128));

  aTexture = SDL_CreateTextureFromSurface(renderer, gSurface);

  if (aTexture == nullptr) {
    SDL_Log("SDL error: %s\n", SDL_GetError());
    return false;
  }

  tWidth = gSurface->w;
  tHeight = gSurface->h;

  SDL_DestroySurface(gSurface);

  return aTexture != nullptr;
}

void AnimaTexture::destroy() {
  SDL_DestroyTexture(aTexture);
  aTexture = nullptr;
  tWidth = 0;
  tHeight = 0;
}

void AnimaTexture::setColor(Uint8 r, Uint8 g, Uint8 b) {
  SDL_SetTextureColorMod(aTexture, r, g, b);
}

void AnimaTexture::setAlpha(Uint8 alpha) {
  SDL_SetTextureAlphaMod(aTexture, alpha);
}

void AnimaTexture::render(SDL_Renderer *gRenderer, float x, float y, float width, float height) {
  SDL_FRect dstRect{x, y, static_cast<float>(tWidth), static_cast<float>(tHeight)};

  if (width > 0) {
    dstRect.w = width;
  }
  if (height > 0) {
    dstRect.h = height;
  }

  SDL_RenderTexture(gRenderer, aTexture, nullptr, &dstRect);
}

int AnimaTexture::getWidth() {
  return tWidth;
}

int AnimaTexture::getHeight() {
  return tHeight;
}

bool AnimaTexture::isLoaded() {
  return aTexture != nullptr;
}

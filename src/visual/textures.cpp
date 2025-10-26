// #include "visual/textures.hpp"
// #include "unethical.hpp"

// AnimaTexture::AnimaTexture() : aTexture{nullptr},
//                                size{Size{kTileSize, kTileSize}} {
// }

// AnimaTexture::~AnimaTexture() {
//   destroy();
// }

// // bool AnimaTexture::mkRectangle(SDL_Renderer *renderer, int w, int h) {
// //   destroy();

// //   SDL_Surface *gSurface = SDL_CreateSurface(w, h, SDL_PIXELFORMAT_RGBA8888);

// //   if (gSurface == nullptr) {
// //     SDL_Log("SDL error: %s\n", SDL_GetError());
// //     return false;
// //   }

// //   bool surfaceKeyOk = SDL_SetSurfaceColorKey(gSurface, true, SDL_MapSurfaceRGB(gSurface, 0xFF, 0xFF, 0xFF));

// //   if (!surfaceKeyOk) {
// //     SDL_Log("SDL error: %s\n", SDL_GetError());
// //     return false;
// //   }

// //   SDL_FillSurfaceRect(gSurface, nullptr, SDL_MapSurfaceRGBA(gSurface, 50, 50, 50, 128));

// //   aTexture = SDL_CreateTextureFromSurface(renderer, gSurface);

// //   if (aTexture == nullptr) {
// //     SDL_Log("SDL error: %s\n", SDL_GetError());
// //     return false;
// //   }

// //   this->size.w = gSurface->w;
// //   this->size.h = gSurface->h;

// //   SDL_DestroySurface(gSurface);

// //   return aTexture != nullptr;
// // }

// void AnimaTexture::destroy() {
//   SDL_DestroyTexture(aTexture);
//   aTexture = nullptr;
//   size.multiply(0);
// }

// void AnimaTexture::setColor(Uint8 r, Uint8 g, Uint8 b) {
//   SDL_SetTextureColorMod(aTexture, r, g, b);
// }

// void AnimaTexture::setAlpha(Uint8 alpha) {
//   SDL_SetTextureAlphaMod(aTexture, alpha);
// }

// Size AnimaTexture::getSize() const {
//   return this->size;
// }

// bool AnimaTexture::isLoaded() const {
//   return aTexture != nullptr;
// }

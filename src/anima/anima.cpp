#include "anima.hpp"
#include "unethical.hpp"

Anima::Anima() : mPosX{0},
                 mPosY{0},
                 mVelX{0},
                 mVelY{0} {
}

void Anima::handleEvent(SDL_Event &event) {

  if (event.type == SDL_EVENT_KEY_DOWN && !event.key.repeat) {

    switch (event.key.key) {
    case SDLK_UP:
      mVelY -= kAnimaVelocity;
      break;
    case SDLK_DOWN:
      mVelY += kAnimaVelocity;
      break;
    case SDLK_LEFT:
      mVelX -= kAnimaVelocity;
      break;
    case SDLK_RIGHT:
      mVelX += kAnimaVelocity;
      break;
    }
  }

  else if (event.type == SDL_EVENT_KEY_UP && !event.key.repeat) {

    switch (event.key.key) {
    case SDLK_UP:
      mVelY += kAnimaVelocity;
      break;
    case SDLK_DOWN:
      mVelY -= kAnimaVelocity;
      break;
    case SDLK_LEFT:
      mVelX += kAnimaVelocity;
      break;
    case SDLK_RIGHT:
      mVelX -= kAnimaVelocity;
      break;
    }
  }
}

void Anima::move() {
  mPosX += mVelX;

  if ((mPosX < 0) || (mPosX + kAnimaHeight > kScreenWidth)) {
    mPosX -= mVelX;
  }

  mPosY += mVelY;

  if ((mPosY < 0) || (mPosY + kAnimaWidth > kScreenHeight)) {
    mPosY -= mVelY;
  }
}

void Anima::render(SDL_Renderer *gRenderer) {
  gAnimaTexture.render(gRenderer, mPosX, mPosY);
}

bool Anima::spawn(SDL_Renderer *gRenderer) {
  return gAnimaTexture.mkRectangle(gRenderer, kAnimaWidth, kAnimaHeight);
}

#include "anima.hpp"
#include "unethical.hpp"

Anima::Anima() : posC{Position(0, 0)},
                 posP{Position(0, 0)},
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
  posP = posC;

  posC.x += mVelX;

  if ((posC.x < 0) || (posC.x + kAnimaHeight > kScreenWidth)) {
    posC.x -= mVelX;
  }

  posC.y += mVelY;

  if ((posC.y < 0) || (posC.y + kAnimaWidth > kScreenHeight)) {
    posC.y -= mVelY;
  }
}

void Anima::toBuffer(int *gFrameBuffer, int colour) {

  int row;
  int col;
  int cel = 0;
  int yOffset;

  yOffset = posC.y * kScreenWidth + posC.x;

  for (row = 0; row < animaSize; ++row) {
    for (col = 0; col < animaSize; ++col, ++cel) {

      if (sprite[cel]) {
        gFrameBuffer[yOffset + col] = colour;
      }
    }
    yOffset += kScreenWidth;
  }
}

bool Anima::spawn(SDL_Renderer *gRenderer) {
  return true;
}

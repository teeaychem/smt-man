#include "anima.hpp"
#include "unethical.hpp"
#include "utils.hpp"

Anima::Anima() : posC{Position(0, 0)},
                 posP{Position(0, 0)},
                 intent{Direction::down},
                 momentum{Direction::down},
                 mVel{1} {
}

void Anima::handleEvent(SDL_Event &event) {

  if (event.type == SDL_EVENT_KEY_DOWN && !event.key.repeat) {

    switch (event.key.key) {
    case SDLK_UP:
      intent = Direction::up;
      break;
    case SDLK_DOWN:
      intent = Direction::down;
      break;
    case SDLK_LEFT:
      intent = Direction::left;
      break;
    case SDLK_RIGHT:
      intent = Direction::right;
      break;
    }
  }
}

void Anima::move() {
  posP = posC;

  if (posC.x % 16 == 0 && posC.y % 16 == 0) {
    momentum = intent;
  }

  switch (momentum) {
  case up: {
    posC.y -= mVel;
    break;
  }
  case right: {
    posC.x += mVel;
    break;
  }
  case down: {
    posC.y += mVel;
    break;
  }
  case left: {
    posC.x -= mVel;
    break;
  }
  }

  // posC.x += mVelX;

  // if ((posC.x < 0) || (posC.x + kAnimaHeight > kScreenWidth)) {
  //   posC.x -= mVelX;
  // }

  // posC.y += mVelY;

  // if ((posC.y < 0) || (posC.y + kAnimaWidth > kScreenHeight)) {
  //   posC.y -= mVelY;
  // }
}

void Anima::toBuffer(int *gFrameBuffer, int colour) {

  int row;
  int col;
  int cel = 0;
  int yOffset;

  yOffset = posC.y * kScreenWidth + posC.x;

  for (row = 0; row < tileSize; ++row) {
    for (col = 0; col < tileSize; ++col, ++cel) {

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

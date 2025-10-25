#include "anima.hpp"
#include "unethical.hpp"
#include "utils.hpp"
#include <iostream>

Anima::Anima() : pos{Position(6 * kTileSize, 16 * kTileSize)},

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

  if (pos.x % 16 == 0 && pos.y % 16 == 0) {
    momentum = intent;
  }

  switch (momentum) {
  case up: {
    pos.y -= mVel;
    break;
  }
  case right: {
    pos.x += mVel;
    break;
  }
  case down: {
    pos.y += mVel;
    break;
  }
  case left: {
    pos.x -= mVel;
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
